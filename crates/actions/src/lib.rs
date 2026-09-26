//! Semantic actions over the arena DOM: locate forms, collect fields,
//! submit over HTTP. Login flows without JavaScript start here.

use vigia_dom::{Dom, NodeData, NodeId};
use vigia_session::CookieJar;
use vigia_url::Url;

#[derive(Debug)]
pub enum ActionError {
    Css(vigia_css::CssError),
    Url(vigia_url::UrlError),
    Net(vigia_net::Error),
    /// Selector matched nothing / no <form> on the page.
    NotFound(&'static str),
    /// multipart/form-data is not implemented yet.
    Unsupported(&'static str),
}

impl std::fmt::Display for ActionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Css(e) => write!(f, "{e}"),
            Self::Url(e) => write!(f, "url: {e}"),
            Self::Net(e) => write!(f, "{e}"),
            Self::NotFound(m) => write!(f, "not found: {m}"),
            Self::Unsupported(m) => write!(f, "unsupported: {m}"),
        }
    }
}
impl std::error::Error for ActionError {}
impl From<vigia_css::CssError> for ActionError {
    fn from(e: vigia_css::CssError) -> Self {
        Self::Css(e)
    }
}
impl From<vigia_url::UrlError> for ActionError {
    fn from(e: vigia_url::UrlError) -> Self {
        Self::Url(e)
    }
}
impl From<vigia_net::Error> for ActionError {
    fn from(e: vigia_net::Error) -> Self {
        Self::Net(e)
    }
}

/// First <form>, or the element matching `selector` (must be a form).
pub fn find_form(
    dom: &Dom,
    selector: Option<&str>,
) -> Result<Option<NodeId>, ActionError> {
    match selector {
        Some(sel) => {
            let hits = vigia_css::query(dom, sel)?;
            Ok(hits
                .into_iter()
                .find(|&id| dom.tag_name(id) == Some("form")))
        }
        None => Ok((1..dom.nodes.len() as NodeId)
            .find(|&id| dom.tag_name(id) == Some("form"))),
    }
}

/// Descendants of `id`, document order.
fn descendants(dom: &Dom, id: NodeId, out: &mut Vec<NodeId>) {
    for &c in dom.children(id) {
        out.push(c);
        descendants(dom, c, out);
    }
}

/// Successful-controls collection, approximating HTML form submission rules:
/// named inputs except submit/button/file/reset/disabled; checkbox/radio only
/// when checked; select picks the selected option or the first; textarea uses
/// its text content.
pub fn form_fields(dom: &Dom, form: NodeId) -> Vec<(String, String)> {
    let mut order = Vec::new();
    descendants(dom, form, &mut order);
    let mut fields = Vec::new();

    for id in order {
        let Some(tag) = dom.tag_name(id) else { continue };
        if dom.attr(id, "disabled").is_some() {
            continue;
        }
        let Some(name) = dom.attr(id, "name") else { continue };
        if name.is_empty() {
            continue;
        }
        match tag {
            "input" => {
                let ty = dom.attr(id, "type").unwrap_or("text");
                match ty {
                    "submit" | "button" | "image" | "file" | "reset" => {}
                    "checkbox" | "radio" => {
                        if dom.attr(id, "checked").is_some() {
                            let v = dom.attr(id, "value").unwrap_or("on");
                            fields.push((name.to_string(), v.to_string()));
                        }
                    }
                    _ => {
                        let v = dom.attr(id, "value").unwrap_or("");
                        fields.push((name.to_string(), v.to_string()));
                    }
                }
            }
            "select" => {
                let mut opts = Vec::new();
                descendants(dom, id, &mut opts);
                let mut value = None;
                let mut first = None;
                for o in opts {
                    if dom.tag_name(o) != Some("option") {
                        continue;
                    }
                    let v = dom
                        .attr(o, "value")
                        .map(str::to_string)
                        .unwrap_or_else(|| text_content(dom, o));
                    if first.is_none() {
                        first = Some(v.clone());
                    }
                    if dom.attr(o, "selected").is_some() {
                        value = Some(v);
                        break;
                    }
                }
                fields.push((name.to_string(), value.or(first).unwrap_or_default()));
            }
            "textarea" => {
                fields.push((name.to_string(), text_content(dom, id)));
            }
            _ => {}
        }
    }
    fields
}

/// All descendant text, collapsed.
pub fn text_content(dom: &Dom, id: NodeId) -> String {
    let mut s = String::new();
    collect_text(dom, id, &mut s);
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn collect_text(dom: &Dom, id: NodeId, out: &mut String) {
    for &c in dom.children(id) {
        match &dom.node(c).data {
            NodeData::Text(t) => {
                out.push(' ');
                out.push_str(t);
            }
            _ => collect_text(dom, c, out),
        }
    }
}

/// application/x-www-form-urlencoded encoding.
pub fn urlencode(fields: &[(String, String)]) -> String {
    let mut out = String::new();
    for (i, (k, v)) in fields.iter().enumerate() {
        if i > 0 {
            out.push('&');
        }
        pct(k, &mut out);
        out.push('=');
        pct(v, &mut out);
    }
    out
}

fn pct(s: &str, out: &mut String) {
    for &b in s.as_bytes() {
        match b {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'*' | b'-' | b'.' | b'_' => {
                out.push(b as char)
            }
            b' ' => out.push('+'),
            _ => {
                let _ = std::fmt::Write::write_fmt(out, format_args!("%{b:02X}"));
            }
        }
    }
}

/// Submit the resolved form. `overrides` replace collected defaults by name
/// (or append new fields). Follows GET/POST method semantics including the
/// 301/302/303 POST-to-GET downgrade.
pub fn submit_form(
    dom: &Dom,
    page_url: &Url,
    selector: Option<&str>,
    overrides: &[(String, String)],
    jar: &mut CookieJar,
) -> Result<vigia_net::Response, ActionError> {
    let form = find_form(dom, selector)?.ok_or(ActionError::NotFound("no form"))?;
    submit_node(dom, page_url, form, overrides, jar)
}

/// Submit a specific form node.
pub fn submit_node(
    dom: &Dom,
    page_url: &Url,
    form: NodeId,
    overrides: &[(String, String)],
    jar: &mut CookieJar,
) -> Result<vigia_net::Response, ActionError> {

    let enctype = dom.attr(form, "enctype").unwrap_or("application/x-www-form-urlencoded");
    if enctype.to_ascii_lowercase().contains("multipart") {
        return Err(ActionError::Unsupported("multipart/form-data"));
    }

    let method = dom
        .attr(form, "method")
        .unwrap_or("get")
        .to_ascii_lowercase();
    let action = dom.attr(form, "action").unwrap_or("");
    let target = page_url.join(action.trim())?;

    let mut fields = form_fields(dom, form);
    for (k, v) in overrides {
        match fields.iter_mut().find(|(fk, _)| fk == k) {
            Some(slot) => slot.1 = v.clone(),
            None => fields.push((k.clone(), v.clone())),
        }
    }

    match method.as_str() {
        "post" => vigia_net::post_form(&target, &urlencode(&fields), jar).map_err(Into::into),
        _ => {
            let url = if fields.is_empty() {
                target
            } else {
                Url {
                    query: Some(urlencode(&fields)),
                    ..target
                }
            };
            vigia_net::fetch(&url.to_string(), jar).map_err(Into::into)
        }
    }
}

/// Follow interactive element `#n` (the ref shown in the snapshot).
/// link -> navigate; button/submit-input inside a form -> submit it.
pub fn click(
    dom: &Dom,
    page_url: &Url,
    ref_n: usize,
    overrides: &[(String, String)],
    jar: &mut CookieJar,
) -> Result<vigia_net::Response, ActionError> {
    let refs = vigia_snapshot::interactive_refs(dom);
    let node = refs
        .get(ref_n.saturating_sub(1))
        .copied()
        .ok_or(ActionError::NotFound("no element for ref"))?;

    match dom.tag_name(node) {
        Some("a") => {
            let href = dom
                .attr(node, "href")
                .ok_or(ActionError::NotFound("link has no href"))?;
            let target = page_url.join(href)?;
            vigia_net::fetch(&target.to_string(), jar).map_err(Into::into)
        }
        Some("button") | Some("input") | Some("summary") => {
            let mut cur = dom.parent(node);
            while let Some(p) = cur {
                if dom.tag_name(p) == Some("form") {
                    return submit_node(dom, page_url, p, overrides, jar);
                }
                cur = dom.parent(p);
            }
            Err(ActionError::NotFound("interactive element outside any form"))
        }
        Some("select") | Some("textarea") => {
            Err(ActionError::Unsupported("select/textarea need fill, not click"))
        }
        _ => Err(ActionError::NotFound("not interactive")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn collects_fields() {
        let mut dom = Dom::new();
        let form = dom.element(dom.root(), "form", vec![]);
        dom.element(
            form,
            "input",
            vec![("name".into(), "u".into()), ("value".into(), "x".into())],
        );
        dom.element(
            form,
            "input",
            vec![
                ("name".into(), "ok".into()),
                ("type".into(), "checkbox".into()),
                ("checked".into(), "".into()),
            ],
        );
        dom.element(
            form,
            "input",
            vec![
                ("name".into(), "off".into()),
                ("type".into(), "checkbox".into()),
            ],
        );
        let ta = dom.element(form, "textarea", vec![("name".into(), "n".into())]);
        dom.text(ta, "hello");
        dom.element(form, "input", vec![("type".into(), "submit".into())]);

        let f = form_fields(&dom, form);
        assert_eq!(
            f,
            vec![
                ("u".into(), "x".into()),
                ("ok".into(), "on".into()),
                ("n".into(), "hello".into())
            ]
        );
    }

    #[test]
    fn encodes() {
        assert_eq!(urlencode(&[("a".into(), "b c".into())]), "a=b+c");
        assert_eq!(urlencode(&[("e".into(), "ñ".into())]), "e=%C3%B1");
    }
}
