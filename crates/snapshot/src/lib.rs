//! Serialize the arena DOM into a compact, indented text tree — the artifact
//! an agent actually consumes. Skips markup that carries no signal for agents
//! (script/style/svg/comments) and keeps only the attributes worth reading.

use std::fmt::Write as _;
use vigia_dom::{Dom, NodeData, NodeId};

const SKIP_TAGS: &[&str] = &["script", "style", "svg", "noscript", "template"];

const KEPT_ATTRS: &[&str] = &[
    "href", "src", "alt", "id", "class", "type", "name", "placeholder", "value", "role",
    "aria-label",
];

pub fn snapshot(dom: &Dom) -> String {
    let mut out = String::new();
    for &child in dom.children(dom.root()) {
        write_node(dom, child, 0, &mut out);
    }
    out
}

fn write_node(dom: &Dom, id: NodeId, depth: usize, out: &mut String) {
    let indent = "  ".repeat(depth);
    match &dom.node(id).data {
        NodeData::Document => {
            for &child in dom.children(id) {
                write_node(dom, child, depth, out);
            }
        }
        NodeData::Element(el) => {
            let tag = dom.interner.resolve(el.tag);
            if SKIP_TAGS.contains(&tag) {
                return;
            }
            let _ = write!(out, "{}- {}", indent, tag);
            for (k, v) in &el.attrs {
                let name = dom.interner.resolve(*k);
                if KEPT_ATTRS.contains(&name) && !v.is_empty() {
                    let _ = write!(out, " [{}={}]", name, truncate(v, 80));
                }
            }
            let _ = writeln!(out);
            for &child in dom.children(id) {
                write_node(dom, child, depth + 1, out);
            }
        }
        NodeData::Text(t) => {
            let trimmed = t.trim();
            if !trimmed.is_empty() {
                let _ = writeln!(out, "{}{}", indent, collapse_ws(trimmed));
            }
        }
        NodeData::Comment(_) => {}
    }
}

fn collapse_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn truncate(s: &str, max: usize) -> &str {
    if s.len() <= max { s } else { &s[..max] }
}

#[cfg(test)]
mod tests {
    use super::*;
    use vigia_dom::Dom;

    #[test]
    fn renders_tree() {
        let mut dom = Dom::new();
        let root = dom.root();
        let html = dom.element(root, "html", vec![]);
        let body = dom.element(html, "body", vec![]);
        let a = dom.element(body, "a", vec![("href".into(), "/x".into())]);
        dom.text(a, "click me");
        let out = snapshot(&dom);
        assert!(out.contains("- a [href=/x]"));
        assert!(out.contains("click me"));
    }
}
