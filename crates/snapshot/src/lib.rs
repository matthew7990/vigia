//! Serialize the arena DOM into a compact semantic tree - the artifact an
//! agent consumes. Roles instead of tags (link, textbox, heading), accessible
//! names inlined, structural containers collapsed, `#n` refs on interactive
//! elements (the future action contract). Optimized for one metric: tokens
//! per unit of usable page information.

use std::fmt::Write as _;
use vigia_dom::{Dom, NodeData, NodeId};

const SKIP_TAGS: &[&str] = &["script", "style", "svg", "noscript", "template"];

/// Inline formatting elements: folded into their parent's text.
const INLINE_TAGS: &[&str] = &[
    "b", "i", "em", "strong", "u", "s", "small", "abbr", "code", "mark", "sub", "sup", "wbr", "br",
    "font", "q", "cite", "time", "kbd", "samp", "var",
];

/// Pure-structure containers: collapsed when they carry no kept attributes.
const COLLAPSE_TAGS: &[&str] = &[
    "html",
    "body",
    "head",
    "div",
    "span",
    "section",
    "article",
    "header",
    "footer",
    "main",
    "colgroup",
    "tbody",
    "thead",
    "tfoot",
    "tr",
    "dl",
    "dd",
    "dt",
    "figure",
    "figcaption",
    "picture",
    "fieldset",
    "legend",
    "center",
    "hgroup",
];

const KEPT_ATTRS: &[&str] = &[
    "id",
    "type",
    "name",
    "placeholder",
    "value",
    "role",
    "aria-label",
    "alt",
    "title",
];

/// Elements an agent can act on - they get `#n` refs.
const INTERACTIVE: &[&str] = &["a", "input", "button", "select", "textarea", "summary"];

/// Elements that keep their line even without attrs (containers with meaning).
const KEEP_LINE: &[&str] = &[
    "nav", "form", "table", "ul", "ol", "select", "iframe", "video", "audio", "details",
];

/// Semantic role for an element: the same names snapshot lines use
/// ("link", "textbox", "heading", ...). Public so `vigia serve` extract
/// results speak the same vocabulary as the snapshot.
pub fn role_of(tag: &str, attrs: &[(u32, String)], dom: &Dom) -> String {
    match tag {
        "a" => "link".into(),
        t if t.len() == 2 && t.starts_with('h') && t.as_bytes()[1].is_ascii_digit() => {
            "heading".into()
        }
        "p" => "paragraph".into(),
        "img" => "image".into(),
        "button" => "button".into(),
        "input" => {
            let ty = attrs
                .iter()
                .find(|(k, _)| dom.interner.resolve(*k) == "type")
                .map(|(_, v)| v.as_str())
                .unwrap_or("text");
            match ty {
                "submit" | "button" | "reset" | "image" => "button",
                "checkbox" => "checkbox",
                "radio" => "radio",
                "range" => "slider",
                "hidden" => "hidden-input",
                _ => "textbox",
            }
            .into()
        }
        "textarea" => "textbox".into(),
        "select" => "combobox".into(),
        "option" => "option".into(),
        "ul" | "ol" => "list".into(),
        "li" => "listitem".into(),
        "table" => "table".into(),
        "th" => "columnheader".into(),
        "td" => "cell".into(),
        "nav" => "navigation".into(),
        "label" => "label".into(),
        "hr" => "separator".into(),
        t => t.into(),
    }
}

/// Text owned by this node: direct text children + text inside inline elements.
fn inline_text(dom: &Dom, id: NodeId) -> String {
    let mut s = String::new();
    collect_inline(dom, id, &mut s);
    collapse_ws(&s)
}

fn collect_inline(dom: &Dom, id: NodeId, out: &mut String) {
    for &c in dom.children(id) {
        match &dom.node(c).data {
            NodeData::Text(t) => {
                out.push(' ');
                out.push_str(t);
            }
            NodeData::Element(el) if INLINE_TAGS.contains(&dom.interner.resolve(el.tag)) => {
                collect_inline(dom, c, out);
            }
            _ => {}
        }
    }
}

/// Interactive elements in the same order as `#n` refs appear in the
/// snapshot: document order, skipping SKIP_TAGS subtrees entirely. The
/// action layer resolves `#n` through this - both sides must stay aligned.
pub fn interactive_refs(dom: &Dom) -> Vec<NodeId> {
    let mut out = Vec::new();
    collect_refs(dom, dom.root(), &mut out);
    out
}

fn collect_refs(dom: &Dom, id: NodeId, out: &mut Vec<NodeId>) {
    if let NodeData::Element(el) = &dom.node(id).data {
        let tag = dom.interner.resolve(el.tag);
        if SKIP_TAGS.contains(&tag) {
            return;
        }
        if INTERACTIVE.contains(&tag) {
            out.push(id);
        }
    }
    for &c in dom.children(id) {
        collect_refs(dom, c, out);
    }
}

/// First <title> text in the document, if any.
fn find_title(dom: &Dom, id: NodeId, out: &mut Option<String>) {
    if out.is_some() {
        return;
    }
    if let NodeData::Element(el) = &dom.node(id).data {
        if dom.interner.resolve(el.tag) == "title" {
            *out = Some(inline_text(dom, id));
            return;
        }
    }
    for &c in dom.children(id) {
        find_title(dom, c, out);
    }
}

pub struct Snapshotter {
    next_ref: u32,
}

pub fn snapshot(dom: &Dom) -> String {
    let mut title = None;
    find_title(dom, dom.root(), &mut title);
    let mut out = String::new();
    match title.filter(|t| !t.is_empty()) {
        Some(t) => {
            let _ = writeln!(out, "page '{t}'");
        }
        None => out.push_str("page\n"),
    }
    let mut s = Snapshotter { next_ref: 1 };
    for &child in dom.children(dom.root()) {
        s.write_node(dom, child, 1, &mut out);
    }
    out
}

impl Snapshotter {
    fn write_node(&mut self, dom: &Dom, id: NodeId, depth: usize, out: &mut String) {
        let indent = "  ".repeat(depth);
        match &dom.node(id).data {
            NodeData::Document | NodeData::Fragment => {
                for &child in dom.children(id) {
                    self.write_node(dom, child, depth, out);
                }
            }
            NodeData::Element(el) => {
                let tag = dom.interner.resolve(el.tag);
                if SKIP_TAGS.contains(&tag) {
                    return;
                }
                if tag == "title" {
                    return; // already emitted as the page line
                }

                let has_kept_attrs = el.attrs.iter().any(|(k, v)| {
                    let n = dom.interner.resolve(*k);
                    (KEPT_ATTRS.contains(&n) || n == "href" || n == "src") && !v.is_empty()
                });
                let text = inline_text(dom, id);
                let interactive = INTERACTIVE.contains(&tag);

                // Pure-structure containers with no kept attrs never earn a
                // line - children surface at this depth, text as 'quoted' lines.
                if COLLAPSE_TAGS.contains(&tag) && !has_kept_attrs {
                    for &child in dom.children(id) {
                        self.write_node(dom, child, depth, out);
                    }
                    return;
                }
                // An element with no own payload (no direct text, no kept
                // attrs, not interactive, not a landmark) collapses too:
                // children surface at this depth. Collapse, not skip - the
                // subtree may hold interactive elements that interactive_refs
                // counts, and skipping them would misalign #n numbering.
                if text.is_empty()
                    && !has_kept_attrs
                    && !interactive
                    && !KEEP_LINE.contains(&tag)
                    && !INLINE_TAGS.contains(&tag)
                {
                    for &child in dom.children(id) {
                        self.write_node(dom, child, depth, out);
                    }
                    return;
                }

                let role = role_of(tag, &el.attrs, dom);
                let _ = write!(out, "{indent}- {role}");

                if interactive {
                    let r = self.next_ref;
                    self.next_ref += 1;
                    let _ = write!(out, " #{r}");
                }

                // link/image: href/src are the payload -> compact arrow form
                let href = el
                    .attrs
                    .iter()
                    .find(|(k, _)| dom.interner.resolve(*k) == "href")
                    .map(|(_, v)| v.clone());
                let src = el
                    .attrs
                    .iter()
                    .find(|(k, _)| dom.interner.resolve(*k) == "src")
                    .map(|(_, v)| v.clone());

                if !text.is_empty() {
                    let _ = write!(out, " '{}'", truncate_owned(&text, 120));
                }
                if let Some(h) = href {
                    let _ = write!(out, " -> {}", truncate_owned(&h, 120));
                }
                if let Some(sv) = src {
                    let _ = write!(out, " -> {}", truncate_owned(&sv, 120));
                }

                for (k, v) in &el.attrs {
                    let name = dom.interner.resolve(*k);
                    if KEPT_ATTRS.contains(&name) && !v.is_empty()
                        // placeholder/aria-label double as the name when no text
                        && !(matches!(name, "placeholder" | "aria-label" | "alt" | "title")
                            && !text.is_empty())
                    {
                        let _ = write!(out, " [{}={}]", name, truncate(v, 80));
                    }
                }
                let _ = writeln!(out);

                for &child in dom.children(id) {
                    // Skip children already absorbed into the name: inline
                    // elements and text are consumed by inline_text.
                    let absorbed = match &dom.node(child).data {
                        NodeData::Text(_) => true,
                        NodeData::Element(cel) => {
                            INLINE_TAGS.contains(&dom.interner.resolve(cel.tag))
                        }
                        _ => false,
                    };
                    if !absorbed {
                        self.write_node(dom, child, depth + 1, out);
                    }
                }
            }
            NodeData::Text(t) => {
                let trimmed = collapse_ws(t.trim());
                if !trimmed.is_empty() {
                    let _ = writeln!(out, "{indent}'{trimmed}'");
                }
            }
            NodeData::Comment(_) => {}
        }
    }
}

fn collapse_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn truncate(s: &str, max: usize) -> &str {
    if s.len() <= max {
        return s;
    }
    let mut end = max;
    while !s.is_char_boundary(end) {
        end -= 1;
    }
    &s[..end]
}

fn truncate_owned(s: &str, max: usize) -> &str {
    truncate(s, max)
}

#[cfg(test)]
mod tests {
    use super::*;
    use vigia_dom::Dom;

    #[test]
    fn renders_semantic_tree() {
        let mut dom = Dom::new();
        let root = dom.root();
        let body = dom.element(root, "body", vec![]);
        let a = dom.element(body, "a", vec![("href".into(), "/x".into())]);
        dom.text(a, "click me");
        let out = snapshot(&dom);
        assert!(out.contains("link #1 'click me' -> /x"), "got:\n{out}");
    }

    #[test]
    fn refs_match_snapshot_order() {
        let mut dom = Dom::new();
        let root = dom.root();
        let body = dom.element(root, "body", vec![]);
        dom.element(body, "a", vec![("href".into(), "/1".into())]);
        let ns = dom.element(body, "noscript", vec![]);
        dom.element(ns, "a", vec![("href".into(), "/hidden".into())]); // skipped
        dom.element(body, "input", vec![("name".into(), "q".into())]);
        dom.element(body, "button", vec![]);
        let refs = interactive_refs(&dom);
        assert_eq!(refs.len(), 3); // the noscript link is unreachable
        let out = snapshot(&dom);
        assert!(out.contains("#3"), "got:\n{out}");
        assert!(!out.contains("/hidden"), "got:\n{out}");
    }

    #[test]
    fn unknown_wrappers_collapse_not_skip() {
        // <custom-x><a> used to skip the whole subtree: the link was counted
        // by interactive_refs but never printed, so #1 resolved to nothing.
        let mut dom = Dom::new();
        let root = dom.root();
        let x = dom.element(root, "custom-x", vec![]);
        let a = dom.element(x, "a", vec![("href".into(), "/in".into())]);
        dom.text(a, "inside");
        let out = snapshot(&dom);
        assert!(out.contains("link #1 'inside' -> /in"), "got:\n{out}");
        assert_eq!(interactive_refs(&dom).len(), 1);
    }

    #[test]
    fn collapses_wrappers() {
        let mut dom = Dom::new();
        let root = dom.root();
        let mut parent = dom.element(root, "div", vec![]);
        for _ in 0..50 {
            parent = dom.element(parent, "div", vec![]);
        }
        dom.text(parent, "deep");
        let out = snapshot(&dom);
        assert!(out.contains("'deep'"), "got:\n{out}");
        assert!(!out.contains("- div"), "got:\n{out}");
    }
}
