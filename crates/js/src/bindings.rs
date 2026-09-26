//! DOM bindings. `set_dom` installs the page DOM plus `document`, `window`,
//! `navigator`, `location` globals; Obj::Dom wraps a NodeId into it. Property
//! and method dispatch happens here at the access/call site, same pattern as
//! call_str/call_arr for string/array builtins - no property-map entries.
//!
//! Mutations go straight into Interp::dom; callers take the (possibly
//! mutated) DOM back with take_dom() / run_scripts().

use vigia_dom::{Dom, NodeData, NodeId};

use crate::ast::Expr;
use crate::eval::{to_str, truthy};
use crate::{err, Interp, JsError, Obj, Value};

/// Same list as vigia-html: these never get a close tag when serializing.
const VOID: &[&str] = &[
    "area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source", "track",
    "wbr",
];

/// First element with `tag` still reachable from the root (detached/orphaned
/// arena nodes are skipped - the arena never frees, so callers must filter).
fn first_tag(dom: &Dom, tag: &str) -> Option<NodeId> {
    (1..dom.nodes.len() as NodeId)
        .find(|&i| dom.tag_name(i) == Some(tag) && is_desc(dom, dom.root(), i))
}

/// First <html>, else the first element under the document root.
fn doc_element(dom: &Dom) -> Option<NodeId> {
    first_tag(dom, "html").or_else(|| {
        dom.children(dom.root())
            .iter()
            .copied()
            .find(|&c| matches!(dom.node(c).data, NodeData::Element(_)))
    })
}

/// Is `n` a strict descendant of `anc`? anc = 0 (document) matches all.
fn is_desc(dom: &Dom, anc: NodeId, n: NodeId) -> bool {
    let mut cur = dom.parent(n);
    while let Some(p) = cur {
        if p == anc {
            return true;
        }
        cur = dom.parent(p);
    }
    false
}

/// Raw descendant text - no whitespace collapsing, so JS string literals
/// inside <script> survive intact (unlike actions::text_content).
fn raw_text(dom: &Dom, id: NodeId, out: &mut String) {
    for &c in dom.children(id) {
        match &dom.node(c).data {
            NodeData::Text(t) => out.push_str(t),
            NodeData::Element(_) => raw_text(dom, c, out),
            _ => {}
        }
    }
}

/// Inline <script> bodies in document order. Skipped: `src` (external) and
/// `type` values that are not javascript-ish (ld+json, templates, ...).
fn collect_scripts(dom: &Dom) -> Vec<String> {
    let mut out = Vec::new();
    for id in 1..dom.nodes.len() as NodeId {
        if dom.tag_name(id) != Some("script") {
            continue;
        }
        if dom.attr(id, "src").is_some() {
            continue;
        }
        let ty = dom
            .attr(id, "type")
            .unwrap_or("")
            .trim()
            .to_ascii_lowercase();
        if !matches!(ty.as_str(), "" | "text/javascript" | "application/javascript" | "module") {
            continue;
        }
        let mut s = String::new();
        raw_text(dom, id, &mut s);
        out.push(s);
    }
    out
}

fn esc_text(t: &str, out: &mut String) {
    for c in t.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            _ => out.push(c),
        }
    }
}

fn esc_attr(v: &str, out: &mut String) {
    for c in v.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '"' => out.push_str("&quot;"),
            _ => out.push(c),
        }
    }
}

/// innerHTML getter: children of `id` serialized as HTML.
fn serialize_into(dom: &Dom, id: NodeId, out: &mut String) {
    for &c in dom.children(id) {
        match &dom.node(c).data {
            NodeData::Element(el) => {
                let tag = dom.interner.resolve(el.tag);
                out.push('<');
                out.push_str(tag);
                for (k, v) in &el.attrs {
                    out.push(' ');
                    out.push_str(dom.interner.resolve(*k));
                    out.push_str("=\"");
                    esc_attr(v, out);
                    out.push('"');
                }
                out.push('>');
                if !VOID.contains(&tag) {
                    serialize_into(dom, c, out);
                    out.push_str("</");
                    out.push_str(tag);
                    out.push('>');
                }
            }
            NodeData::Text(t) => esc_text(t, out),
            NodeData::Comment(t) => {
                out.push_str("<!--");
                out.push_str(t);
                out.push_str("-->");
            }
            NodeData::Document => {}
        }
    }
}

impl Interp {
    /// Install `dom` plus the document/window/navigator/location globals.
    /// Call before run(). Re-installing replaces the DOM and the wrappers.
    pub fn set_dom(&mut self, dom: Dom) {
        self.dom = Some(dom);
        self.dom_objs.clear();
        self.install_builtins();
        // Heap-cap edges skip installs silently, same as install_builtins.
        let (Ok(doc), Ok(ua), Ok(href)) = (
            self.dom_wrap(0),
            self.heap.intern_str("vigia/0.1"),
            self.heap.intern_str(""),
        ) else {
            return;
        };
        self.env_declare(0, "document", doc);
        let (Ok(nav), Ok(loc)) = (
            self.heap
                .alloc_obj(Obj::Ordinary(vec![("userAgent".into(), Value::Str(ua))])),
            self.heap
                .alloc_obj(Obj::Ordinary(vec![("href".into(), Value::Str(href))])),
        ) else {
            return;
        };
        self.env_declare(0, "navigator", Value::Obj(nav));
        self.env_declare(0, "location", Value::Obj(loc));
        if let Ok(w) = self.heap.alloc_obj(Obj::Ordinary(vec![
            ("document".into(), doc),
            ("navigator".into(), Value::Obj(nav)),
            ("location".into(), Value::Obj(loc)),
        ])) {
            if let Obj::Ordinary(ps) = self.heap.obj_mut(w) {
                ps.push(("window".into(), Value::Obj(w)));
            }
            self.env_declare(0, "window", Value::Obj(w));
        }
    }

    /// Take the installed DOM back (mutated by any scripts that ran).
    pub fn take_dom(&mut self) -> Dom {
        self.dom.take().unwrap_or_default()
    }

    /// Run every runnable inline <script> in document order over one shared
    /// interp (globals persist across tags, like browsers). A script that
    /// throws does not abort the page: errors collect into the returned vec.
    pub fn run_scripts(&mut self, dom: Dom) -> (Dom, Vec<JsError>) {
        let scripts = collect_scripts(&dom);
        self.set_dom(dom);
        let mut errs = Vec::new();
        for src in &scripts {
            if let Err(e) = self.run(src) {
                errs.push(e);
            }
        }
        (self.take_dom(), errs)
    }

    pub(crate) fn dom_ref(&self) -> Result<&Dom, JsError> {
        self.dom.as_ref().ok_or_else(|| err("no DOM installed"))
    }

    fn dom_mut(&mut self) -> Result<&mut Dom, JsError> {
        self.dom.as_mut().ok_or_else(|| err("no DOM installed"))
    }

    /// NodeId if `v` is a DOM node handle.
    pub(crate) fn as_node(&self, v: Value) -> Option<NodeId> {
        if let Value::Obj(id) = v {
            if let Obj::Dom(n) = self.heap.obj(id) {
                return Some(*n);
            }
        }
        None
    }

    /// Wrap a node, reusing the cached wrapper so === identity holds.
    fn dom_wrap(&mut self, n: NodeId) -> Result<Value, JsError> {
        if let Some(&o) = self.dom_objs.get(&n) {
            return Ok(Value::Obj(o));
        }
        let o = self.heap.alloc_obj(Obj::Dom(n))?;
        self.dom_objs.insert(n, o);
        Ok(Value::Obj(o))
    }

    fn opt_node(&mut self, n: Option<NodeId>) -> Result<Value, JsError> {
        match n {
            Some(n) => self.dom_wrap(n),
            None => Ok(Value::Null),
        }
    }

    fn str_val(&mut self, s: String) -> Result<Value, JsError> {
        Ok(Value::Str(self.heap.alloc_str(s)?))
    }

    fn attr_val(&mut self, id: NodeId, name: &str) -> Result<Value, JsError> {
        let s = self.dom_ref()?.attr(id, name).unwrap_or("").to_string();
        self.str_val(s)
    }

    fn node_arr(&mut self, ids: Vec<NodeId>) -> Result<Value, JsError> {
        let mut vals = Vec::with_capacity(ids.len());
        for n in ids {
            vals.push(self.dom_wrap(n)?);
        }
        Ok(Value::Obj(self.heap.alloc_obj(Obj::Arr(vals))?))
    }

    /// CSS query scoped to the subtree rooted at `id` (id 0 = whole doc).
    fn select(&mut self, id: NodeId, sel: Value) -> Result<Vec<NodeId>, JsError> {
        let sel = to_str(&self.heap, sel);
        let dom = self.dom_ref()?;
        let hits = vigia_css::query(dom, &sel).map_err(|e| err(e.to_string()))?;
        Ok(hits.into_iter().filter(|&n| is_desc(dom, id, n)).collect())
    }

    /// Property read on a DOM node handle.
    pub(crate) fn dom_get(&mut self, id: NodeId, key: &str) -> Result<Value, JsError> {
        match key {
            "nodeType" => {
                let n = match self.dom_ref()?.node(id).data {
                    NodeData::Document => 9.0,
                    NodeData::Element(_) => 1.0,
                    NodeData::Text(_) => 3.0,
                    NodeData::Comment(_) => 8.0,
                };
                return Ok(Value::Num(n));
            }
            "parentElement" => {
                let p = {
                    let dom = self.dom_ref()?;
                    dom.parent(id)
                        .filter(|&p| matches!(dom.node(p).data, NodeData::Element(_)))
                };
                return self.opt_node(p);
            }
            "children" | "childNodes" => {
                let all = key == "childNodes";
                let ids: Vec<NodeId> = {
                    let dom = self.dom_ref()?;
                    dom.children(id)
                        .iter()
                        .copied()
                        .filter(|&c| all || matches!(dom.node(c).data, NodeData::Element(_)))
                        .collect()
                };
                return self.node_arr(ids);
            }
            _ => {}
        }
        match self.dom_ref()?.node(id).data {
            NodeData::Document => match key {
                "documentElement" => {
                    let n = doc_element(self.dom_ref()?);
                    self.opt_node(n)
                }
                "body" => {
                    let n = {
                        let d = self.dom_ref()?;
                        first_tag(d, "body").or_else(|| doc_element(d))
                    };
                    self.opt_node(n)
                }
                "title" => {
                    let t = {
                        let d = self.dom_ref()?;
                        first_tag(d, "title")
                            .map(|n| vigia_actions::text_content(d, n))
                            .unwrap_or_default()
                    };
                    self.str_val(t)
                }
                "textContent" => Ok(Value::Null),
                _ => Ok(Value::Undef),
            },
            NodeData::Text(_) | NodeData::Comment(_) => match key {
                "textContent" | "nodeValue" => {
                    let t = match &self.dom_ref()?.node(id).data {
                        NodeData::Text(t) | NodeData::Comment(t) => t.clone(),
                        _ => String::new(),
                    };
                    self.str_val(t)
                }
                _ => Ok(Value::Undef),
            },
            NodeData::Element(_) => match key {
                "textContent" => {
                    let t = vigia_actions::text_content(self.dom_ref()?, id);
                    self.str_val(t)
                }
                "innerHTML" => {
                    let mut s = String::new();
                    serialize_into(self.dom_ref()?, id, &mut s);
                    self.str_val(s)
                }
                "tagName" => {
                    let t = self.dom_ref()?.tag_name(id).unwrap_or("").to_ascii_uppercase();
                    self.str_val(t)
                }
                "id" => self.attr_val(id, "id"),
                "className" => self.attr_val(id, "class"),
                "value" => self.attr_val(id, "value"),
                "href" => self.attr_val(id, "href"),
                "checked" => Ok(Value::Bool(self.dom_ref()?.attr(id, "checked").is_some())),
                "disabled" => Ok(Value::Bool(self.dom_ref()?.attr(id, "disabled").is_some())),
                _ => Ok(Value::Undef),
            },
        }
    }

    /// Property write on a DOM node handle. Unknown keys are ignored (no
    /// expando map on node handles).
    pub(crate) fn dom_set(&mut self, id: NodeId, key: &str, v: Value) -> Result<(), JsError> {
        let data = &self.dom_ref()?.node(id).data;
        if matches!(data, NodeData::Document) {
            if key == "title" {
                let t = to_str(&self.heap, v);
                let dom = self.dom_mut()?;
                match first_tag(dom, "title") {
                    Some(te) => {
                        dom.clear_children(te);
                        dom.text(te, &t);
                    }
                    None => {
                        let parent = first_tag(dom, "head")
                            .or_else(|| first_tag(dom, "html"))
                            .unwrap_or_else(|| dom.root());
                        let te = dom.element(parent, "title", vec![]);
                        dom.text(te, &t);
                    }
                }
            }
            return Ok(());
        }
        if matches!(data, NodeData::Text(_) | NodeData::Comment(_)) {
            if matches!(key, "textContent" | "nodeValue") {
                let t = to_str(&self.heap, v);
                let node = &mut self.dom_mut()?.nodes[id as usize];
                node.data = if matches!(node.data, NodeData::Comment(_)) {
                    NodeData::Comment(t)
                } else {
                    NodeData::Text(t)
                };
            }
            return Ok(());
        }
        match key {
            "textContent" => {
                let t = to_str(&self.heap, v);
                let dom = self.dom_mut()?;
                dom.clear_children(id);
                dom.text(id, &t);
            }
            "innerHTML" => {
                let t = to_str(&self.heap, v);
                // Parse under a <div> wrapper in a scratch Dom, then adopt.
                let mut scratch = Dom::new();
                vigia_html::parse(&format!("<div>{t}</div>"), &mut scratch);
                let wrap = scratch.children(scratch.root()).first().copied();
                let dom = self.dom_mut()?;
                dom.clear_children(id);
                if let Some(w) = wrap {
                    dom.adopt_children(&scratch, w, id);
                }
            }
            "id" | "className" | "value" | "href" => {
                let name = if key == "className" { "class" } else { key };
                let t = to_str(&self.heap, v);
                self.dom_mut()?.set_attr(id, name, &t);
            }
            "checked" | "disabled" => {
                let on = truthy(&self.heap, v);
                let dom = self.dom_mut()?;
                if on {
                    dom.set_attr(id, key, key);
                } else {
                    dom.remove_attr(id, key);
                }
            }
            _ => {}
        }
        Ok(())
    }

    /// Method call on a DOM node handle (the `o.m()` call-site dispatch).
    pub(crate) fn call_dom(
        &mut self,
        id: NodeId,
        name: &str,
        env: u32,
        arg_es: &[Expr],
    ) -> Result<Value, JsError> {
        let args = self.eval_args(env, arg_es)?;
        let arg = |i: usize| args.get(i).copied().unwrap_or(Value::Undef);
        if matches!(self.dom_ref()?.node(id).data, NodeData::Document) {
            return match name {
                "getElementById" => {
                    let want = to_str(&self.heap, arg(0));
                    let hit = {
                        let d = self.dom_ref()?;
                        (1..d.nodes.len() as NodeId).find(|&i| {
                            matches!(d.node(i).data, NodeData::Element(_))
                                && is_desc(d, 0, i)
                                && d.attr(i, "id") == Some(want.as_str())
                        })
                    };
                    self.opt_node(hit)
                }
                "getElementsByTagName" => {
                    let want = to_str(&self.heap, arg(0)).to_ascii_lowercase();
                    let ids: Vec<NodeId> = {
                        let d = self.dom_ref()?;
                        (1..d.nodes.len() as NodeId)
                            .filter(|&i| {
                                matches!(d.node(i).data, NodeData::Element(_))
                                    && is_desc(d, 0, i)
                                    && (want == "*" || d.tag_name(i) == Some(want.as_str()))
                            })
                            .collect()
                    };
                    self.node_arr(ids)
                }
                "createElement" => {
                    let tag = to_str(&self.heap, arg(0)).to_ascii_lowercase();
                    if tag.is_empty() {
                        return Err(err("createElement needs a tag"));
                    }
                    let n = {
                        let d = self.dom_mut()?;
                        let root = d.root();
                        let n = d.element(root, &tag, vec![]);
                        d.detach(n);
                        n
                    };
                    self.dom_wrap(n)
                }
                "querySelector" => {
                    let hits = self.select(id, arg(0))?;
                    self.opt_node(hits.into_iter().next())
                }
                "querySelectorAll" => {
                    let hits = self.select(id, arg(0))?;
                    self.node_arr(hits)
                }
                _ => Err(err(format!("{name} is not a function"))),
            };
        }
        match name {
            "getAttribute" => {
                let n = to_str(&self.heap, arg(0));
                match self.dom_ref()?.attr(id, &n).map(str::to_string) {
                    Some(v) => self.str_val(v),
                    None => Ok(Value::Null),
                }
            }
            "hasAttribute" => {
                let n = to_str(&self.heap, arg(0));
                Ok(Value::Bool(self.dom_ref()?.attr(id, &n).is_some()))
            }
            "setAttribute" => {
                let n = to_str(&self.heap, arg(0));
                let v = to_str(&self.heap, arg(1));
                self.dom_mut()?.set_attr(id, &n, &v);
                Ok(Value::Undef)
            }
            "removeAttribute" => {
                let n = to_str(&self.heap, arg(0));
                self.dom_mut()?.remove_attr(id, &n);
                Ok(Value::Undef)
            }
            "appendChild" => {
                let a = arg(0);
                let Some(n) = self.as_node(a) else {
                    return Err(err("appendChild needs a node"));
                };
                {
                    let dom = self.dom_ref()?;
                    let mut cur = Some(id);
                    while let Some(p) = cur {
                        if p == n {
                            return Err(err("cyclic appendChild"));
                        }
                        cur = dom.parent(p);
                    }
                }
                let dom = self.dom_mut()?;
                dom.detach(n);
                dom.append_child_node(id, n);
                Ok(a)
            }
            "removeChild" => {
                let a = arg(0);
                let Some(n) = self.as_node(a) else {
                    return Err(err("removeChild needs a node"));
                };
                if self.dom_ref()?.parent(n) != Some(id) {
                    return Err(err("removeChild: not a child"));
                }
                self.dom_mut()?.detach(n);
                Ok(a)
            }
            "remove" => {
                self.dom_mut()?.detach(id);
                Ok(Value::Undef)
            }
            "querySelector" => {
                let hits = self.select(id, arg(0))?;
                self.opt_node(hits.into_iter().next())
            }
            "querySelectorAll" => {
                let hits = self.select(id, arg(0))?;
                self.node_arr(hits)
            }
            // no form submission / navigation in v1
            "click" => Ok(Value::Undef),
            _ => Err(err(format!("{name} is not a function"))),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn interp(html: &str) -> Interp {
        let mut d = Dom::new();
        vigia_html::parse(html, &mut d);
        let mut it = Interp::new();
        it.set_dom(d);
        it
    }

    /// Completion value, inspected (strings bare, objects JSON).
    fn ev(it: &mut Interp, src: &str) -> String {
        let v = it.run(src).unwrap();
        it.inspect(v)
    }

    fn errmsg(it: &mut Interp, src: &str) -> String {
        it.run(src).unwrap_err().0
    }

    const PAGE: &str = r#"<html><head><title>old</title></head><body>
        <div id=a class="x y"><p>one</p><p>two <b>bold</b></p></div>
        <input id=i value="v1" checked>
        <a id=l href="/next">go</a>
        </body></html>"#;

    #[test]
    fn globals() {
        let mut it = interp(PAGE);
        assert_eq!(ev(&mut it, "window.document === document"), "true");
        assert_eq!(ev(&mut it, "document.nodeType"), "9");
        assert_eq!(ev(&mut it, "navigator.userAgent"), "vigia/0.1");
        assert_eq!(ev(&mut it, "typeof location.href"), "string");
        assert_eq!(ev(&mut it, "document.body === document.body"), "true");
        assert_eq!(ev(&mut it, "document.body.nodeType"), "1");
        assert_eq!(ev(&mut it, "document.body.tagName"), "BODY");
        assert_eq!(ev(&mut it, "document.documentElement.tagName"), "HTML");
    }

    #[test]
    fn lookup() {
        let mut it = interp(PAGE);
        assert_eq!(ev(&mut it, "document.getElementById('a').id"), "a");
        assert_eq!(ev(&mut it, "document.getElementById('nope')"), "null");
        assert_eq!(ev(&mut it, "document.querySelector('#a p').textContent"), "one");
        assert_eq!(ev(&mut it, "document.querySelectorAll('#a p').length"), "2");
        assert_eq!(ev(&mut it, "document.querySelectorAll('.nope').length"), "0");
        assert_eq!(ev(&mut it, "document.getElementsByTagName('input').length"), "1");
        assert_eq!(ev(&mut it, "document.getElementsByTagName('*').length > 3"), "true");
        // element-scoped query sees only its own subtree
        assert_eq!(
            ev(&mut it, "document.getElementById('a').querySelectorAll('p').length"),
            "2"
        );
        assert_eq!(
            ev(&mut it, "document.getElementById('a').querySelectorAll('input').length"),
            "0"
        );
        assert!(errmsg(&mut it, "document.querySelector('[')").contains("css"));
    }

    #[test]
    fn text_content() {
        let mut it = interp(PAGE);
        assert_eq!(ev(&mut it, "document.getElementById('a').textContent"), "one two bold");
        it.run("document.getElementById('a').textContent = 'flat'").unwrap();
        let dom = it.take_dom();
        let a = vigia_css::query(&dom, "#a").unwrap()[0];
        assert_eq!(vigia_actions::text_content(&dom, a), "flat");
        assert_eq!(dom.children(a).len(), 1);
    }

    #[test]
    fn inner_html() {
        let mut it = interp("<body><div id=a><p>x &amp; y</p><br></div></body>");
        assert_eq!(
            ev(&mut it, "document.getElementById('a').innerHTML"),
            "<p>x &amp; y</p><br>"
        );
        it.run("document.body.innerHTML = '<h1>INJ</h1><p>t</p>'").unwrap();
        let dom = it.take_dom();
        let h1 = vigia_css::query(&dom, "h1").unwrap();
        assert_eq!(vigia_actions::text_content(&dom, h1[0]), "INJ");
        assert_eq!(vigia_css::query(&dom, "body > p").unwrap().len(), 1);
    }

    #[test]
    fn attributes() {
        let mut it = interp(PAGE);
        assert_eq!(ev(&mut it, "var e=document.getElementById('i');e.getAttribute('value')"), "v1");
        assert_eq!(ev(&mut it, "document.getElementById('i').hasAttribute('checked')"), "true");
        assert_eq!(ev(&mut it, "document.getElementById('i').hasAttribute('nope')"), "false");
        assert_eq!(ev(&mut it, "document.getElementById('i').getAttribute('nope')"), "null");
        it.run("var e=document.getElementById('i');e.setAttribute('data-k','7');e.removeAttribute('value')").unwrap();
        let dom = it.take_dom();
        let i = vigia_css::query(&dom, "#i").unwrap()[0];
        assert_eq!(dom.attr(i, "data-k"), Some("7"));
        assert_eq!(dom.attr(i, "value"), None);
    }

    #[test]
    fn element_props() {
        let mut it = interp(PAGE);
        assert_eq!(ev(&mut it, "document.getElementById('a').className"), "x y");
        assert_eq!(ev(&mut it, "document.getElementById('l').href"), "/next");
        assert_eq!(ev(&mut it, "document.getElementById('i').checked"), "true");
        assert_eq!(ev(&mut it, "document.getElementById('i').disabled"), "false");
        it.run(
            "var e=document.getElementById('i');e.id='j';e.value='v2';e.checked=false;e.disabled=true",
        )
        .unwrap();
        let dom = it.take_dom();
        let i = vigia_css::query(&dom, "#j").unwrap()[0];
        assert_eq!(dom.attr(i, "value"), Some("v2"));
        assert_eq!(dom.attr(i, "checked"), None);
        assert_eq!(dom.attr(i, "disabled"), Some("disabled"));
    }

    #[test]
    fn tree_walk() {
        let mut it = interp(PAGE);
        assert_eq!(ev(&mut it, "document.getElementById('a').children.length"), "2");
        assert_eq!(
            ev(&mut it, "document.getElementById('a').children[0].tagName"),
            "P"
        );
        // childNodes on <p>two <b>bold</b></p> mixes text + element
        assert_eq!(
            ev(&mut it, "document.querySelectorAll('#a p')[1].childNodes.length"),
            "2"
        );
        assert_eq!(
            ev(&mut it, "document.querySelectorAll('#a p')[1].childNodes[0].nodeType"),
            "3"
        );
        assert_eq!(
            ev(&mut it, "document.querySelectorAll('#a p')[1].childNodes[0].textContent"),
            "two "
        );
        assert_eq!(
            ev(&mut it, "document.querySelector('#a p').parentElement.id"),
            "a"
        );
        assert_eq!(ev(&mut it, "document.body.parentElement.tagName"), "HTML");
    }

    #[test]
    fn mutation() {
        let mut it = interp(PAGE);
        it.run(
            "var h=document.createElement('h1');h.textContent='INJ';document.body.appendChild(h)",
        )
        .unwrap();
        it.run("document.getElementById('a').appendChild(document.getElementById('l'))").unwrap();
        it.run("document.getElementById('i').remove()").unwrap();
        let dom = it.take_dom();
        let h1 = vigia_css::query(&dom, "body > h1").unwrap();
        assert_eq!(vigia_actions::text_content(&dom, h1[0]), "INJ");
        // moved, not copied: link is now inside #a
        assert_eq!(vigia_css::query(&dom, "#a > a").unwrap().len(), 1);
        // detached: orphan stays in the arena but query() skips unreachable
        assert!(vigia_css::query(&dom, "#i").unwrap().is_empty());

        // removeChild returns the detached node
        let mut it = interp("<body><div id=a><b id=b>x</b></div></body>");
        assert_eq!(
            ev(&mut it, "document.getElementById('a').removeChild(document.getElementById('b')).tagName"),
            "B"
        );
        assert_eq!(ev(&mut it, "document.getElementById('b')"), "null");
        let dom = it.take_dom();
        assert!(vigia_css::query(&dom, "#b").unwrap().is_empty());
        assert!(errmsg(&mut interp("<body></body>"), "document.body.appendChild(1)")
            .contains("needs a node"));
    }

    #[test]
    fn title_and_misc() {
        let mut it = interp(PAGE);
        assert_eq!(ev(&mut it, "document.title"), "old");
        it.run("document.title = 'new'").unwrap();
        let dom = it.take_dom();
        let t = vigia_css::query(&dom, "title").unwrap();
        assert_eq!(vigia_actions::text_content(&dom, t[0]), "new");
        // no title element: creates one under head/html
        let mut it = interp("<html><body></body></html>");
        it.run("document.title = 'made'").unwrap();
        let dom = it.take_dom();
        let t = vigia_css::query(&dom, "title").unwrap();
        assert_eq!(vigia_actions::text_content(&dom, t[0]), "made");
        // click is a no-op; unknown methods error
        let mut it = interp("<body></body>");
        assert_eq!(ev(&mut it, "document.body.click()"), "undefined");
        assert!(errmsg(&mut it, "document.body.fly()").contains("not a function"));
    }

    #[test]
    fn run_scripts_flow() {
        let mut d = Dom::new();
        vigia_html::parse(
            r#"<html><head>
                <script type="application/ld+json">{"skip":1}</script>
                <script src="ext.js"></script>
                <script>var g = 40;</script>
                </head><body>
                <script>document.body.innerHTML = '<h1>INJ</h1>'; g + 2;</script>
                <script>throwaway.undef()</script>
                <script>document.title = 'after'</script>
                </body></html>"#,
            &mut d,
        );
        let mut it = Interp::new();
        let (dom, errs) = it.run_scripts(d);
        assert_eq!(errs.len(), 1);
        assert!(errs[0].0.contains("throwaway"));
        // mutations from the scripts that ran are in the returned dom
        let h1 = vigia_css::query(&dom, "h1").unwrap();
        assert_eq!(vigia_actions::text_content(&dom, h1[0]), "INJ");
        let t = vigia_css::query(&dom, "title").unwrap();
        assert_eq!(vigia_actions::text_content(&dom, t[0]), "after");
        // innerHTML= orphaned the 3 body <script>s; head scripts stay put
        // (ld+json / external kept their text, unexecuted)
        assert_eq!(vigia_css::query(&dom, "script").unwrap().len(), 3);
        let ld = vigia_css::query(&dom, "script[type*=json]").unwrap();
        assert_eq!(vigia_actions::text_content(&dom, ld[0]), "{\"skip\":1}");
    }
}
