//! Arena DOM.
//!
//! Every node lives in a single `Vec`, addressed by `NodeId` (a `u32`).
//! Tag and attribute names are interned once per document. No `Rc`/`RefCell`
//! graphs and no per-node heap allocation beyond the node vector itself -
//! this is what keeps the footprint flat on big pages.

use std::collections::HashMap;

pub type NodeId = u32;

/// String interner. Frequent strings (tag names, attribute names) are stored once.
#[derive(Debug, Default)]
pub struct Interner {
    map: HashMap<Box<str>, u32>,
    strings: Vec<Box<str>>,
}

impl Interner {
    pub fn intern(&mut self, s: &str) -> u32 {
        if let Some(&id) = self.map.get(s) {
            return id;
        }
        let id = self.strings.len() as u32;
        let boxed: Box<str> = s.into();
        self.strings.push(boxed.clone());
        self.map.insert(boxed, id);
        id
    }

    pub fn resolve(&self, id: u32) -> &str {
        &self.strings[id as usize]
    }

    pub fn len(&self) -> usize {
        self.strings.len()
    }

    pub fn is_empty(&self) -> bool {
        self.strings.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    pub parent: Option<NodeId>,
    pub children: Vec<NodeId>,
    pub data: NodeData,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NodeData {
    Document,
    Element(ElementData),
    Text(String),
    Comment(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ElementData {
    /// Interned tag name.
    pub tag: u32,
    /// (interned name, value). Attribute values stay owned - interning them
    /// is a measurable tradeoff left for later.
    pub attrs: Vec<(u32, String)>,
}

#[derive(Debug)]
pub struct Dom {
    pub nodes: Vec<Node>,
    pub interner: Interner,
}

impl Default for Dom {
    fn default() -> Self {
        Self::new()
    }
}

impl Dom {
    pub fn new() -> Self {
        Dom {
            nodes: vec![Node {
                parent: None,
                children: Vec::new(),
                data: NodeData::Document,
            }],
            interner: Interner::default(),
        }
    }

    /// Root document node. Always id 0.
    pub fn root(&self) -> NodeId {
        0
    }

    pub fn node(&self, id: NodeId) -> &Node {
        &self.nodes[id as usize]
    }

    /// Create an element and append it under `parent`.
    pub fn element(&mut self, parent: NodeId, tag: &str, attrs: Vec<(String, String)>) -> NodeId {
        let tag_id = self.interner.intern(tag);
        let attrs = attrs
            .into_iter()
            .map(|(k, v)| (self.interner.intern(&k), v))
            .collect();
        let id = self.push(Node {
            parent: Some(parent),
            children: Vec::new(),
            data: NodeData::Element(ElementData { tag: tag_id, attrs }),
        });
        self.nodes[parent as usize].children.push(id);
        id
    }

    /// Append text under `parent`, merging into a trailing text sibling.
    pub fn text(&mut self, parent: NodeId, text: &str) {
        if text.is_empty() {
            return;
        }
        if let Some(&last) = self.nodes[parent as usize].children.last() {
            if let NodeData::Text(existing) = &mut self.nodes[last as usize].data {
                existing.push_str(text);
                return;
            }
        }
        let id = self.push(Node {
            parent: Some(parent),
            children: Vec::new(),
            data: NodeData::Text(text.to_string()),
        });
        self.nodes[parent as usize].children.push(id);
    }

    /// Append a comment under `parent`.
    pub fn comment(&mut self, parent: NodeId, text: &str) {
        let id = self.push(Node {
            parent: Some(parent),
            children: Vec::new(),
            data: NodeData::Comment(text.to_string()),
        });
        self.nodes[parent as usize].children.push(id);
    }

    /// Create a detached text node (document.createTextNode): no parent,
    /// no merging - the caller links it with append/insert.
    pub fn text_node(&mut self, text: &str) -> NodeId {
        self.push(Node {
            parent: None,
            children: Vec::new(),
            data: NodeData::Text(text.to_string()),
        })
    }

    /// Create a detached comment node (document.createComment).
    pub fn comment_node(&mut self, text: &str) -> NodeId {
        self.push(Node {
            parent: None,
            children: Vec::new(),
            data: NodeData::Comment(text.to_string()),
        })
    }

    fn push(&mut self, node: Node) -> NodeId {
        let id = self.nodes.len() as NodeId;
        self.nodes.push(node);
        id
    }

    pub fn children(&self, id: NodeId) -> &[NodeId] {
        &self.nodes[id as usize].children
    }

    pub fn parent(&self, id: NodeId) -> Option<NodeId> {
        self.nodes[id as usize].parent
    }

    /// Tag name of an element node, resolved through the interner.
    pub fn tag_name(&self, id: NodeId) -> Option<&str> {
        match &self.node(id).data {
            NodeData::Element(el) => Some(self.interner.resolve(el.tag)),
            _ => None,
        }
    }

    pub fn attr(&self, id: NodeId, name: &str) -> Option<&str> {
        match &self.node(id).data {
            NodeData::Element(el) => el
                .attrs
                .iter()
                .find(|(k, _)| self.interner.resolve(*k) == name)
                .map(|(_, v)| v.as_str()),
            _ => None,
        }
    }

    /// Set an attribute on an element, replacing the value of the existing
    /// attr with the same name. No-op on non-element nodes.
    pub fn set_attr(&mut self, id: NodeId, name: &str, value: &str) {
        if !matches!(self.nodes[id as usize].data, NodeData::Element(_)) {
            return;
        }
        let key = self.interner.intern(name);
        let NodeData::Element(el) = &mut self.nodes[id as usize].data else {
            return;
        };
        match el.attrs.iter_mut().find(|(k, _)| *k == key) {
            Some((_, v)) => *v = value.to_string(),
            None => el.attrs.push((key, value.to_string())),
        }
    }

    /// Remove an attribute by name. No-op on non-elements / missing names.
    pub fn remove_attr(&mut self, id: NodeId, name: &str) {
        let NodeData::Element(el) = &mut self.nodes[id as usize].data else {
            return;
        };
        el.attrs.retain(|(k, _)| self.interner.resolve(*k) != name);
    }

    /// Unlink `id` from its parent (children list + parent pointer). The
    /// node and its subtree stay in the arena.
    pub fn detach(&mut self, id: NodeId) {
        if let Some(p) = self.nodes[id as usize].parent.take() {
            self.nodes[p as usize].children.retain(|&c| c != id);
        }
    }

    /// Link an existing node under `parent`. Caller must detach first if
    /// the node is already linked.
    pub fn append_child_node(&mut self, parent: NodeId, id: NodeId) {
        self.nodes[id as usize].parent = Some(parent);
        self.nodes[parent as usize].children.push(id);
    }

    /// Link `id` under `parent` right before `before` (which must be a
    /// child of `parent`); `None` appends. Caller must detach first and
    /// check for cycles, like `append_child_node`.
    pub fn insert_before_node(&mut self, parent: NodeId, id: NodeId, before: Option<NodeId>) {
        self.nodes[id as usize].parent = Some(parent);
        let kids = &mut self.nodes[parent as usize].children;
        match before.and_then(|b| kids.iter().position(|&c| c == b)) {
            Some(i) => kids.insert(i, id),
            None => kids.push(id),
        }
    }

    /// Drop all children links; the child nodes stay in the arena, orphaned.
    pub fn clear_children(&mut self, id: NodeId) {
        for c in std::mem::take(&mut self.nodes[id as usize].children) {
            self.nodes[c as usize].parent = None;
        }
    }

    /// Deep-copy src's children under `dst_parent`, re-interning names.
    /// src and self must be different arenas (build a scratch Dom to parse
    /// fragments, then adopt).
    pub fn adopt_children(&mut self, src: &Dom, src_parent: NodeId, dst_parent: NodeId) {
        for &c in src.children(src_parent) {
            self.copy_subtree(src, c, dst_parent);
        }
    }

    fn copy_subtree(&mut self, src: &Dom, src_id: NodeId, dst_parent: NodeId) {
        match &src.node(src_id).data {
            NodeData::Element(el) => {
                let tag = src.interner.resolve(el.tag).to_string();
                let attrs: Vec<(String, String)> = el
                    .attrs
                    .iter()
                    .map(|(k, v)| (src.interner.resolve(*k).to_string(), v.clone()))
                    .collect();
                let new = self.element(dst_parent, &tag, attrs);
                for &c in src.children(src_id) {
                    self.copy_subtree(src, c, new);
                }
            }
            NodeData::Text(t) => self.text(dst_parent, t),
            NodeData::Comment(t) => self.comment(dst_parent, t),
            NodeData::Document => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn set_and_remove_attr() {
        let mut dom = Dom::new();
        let root = dom.root();
        let el = dom.element(root, "input", vec![("name".into(), "q".into())]);
        dom.set_attr(el, "value", "a");
        assert_eq!(dom.attr(el, "value"), Some("a"));
        dom.set_attr(el, "value", "b");
        assert_eq!(dom.attr(el, "value"), Some("b"));
        assert_eq!(dom.attr(el, "name"), Some("q"));
        dom.set_attr(el, "checked", "checked");
        dom.remove_attr(el, "checked");
        assert_eq!(dom.attr(el, "checked"), None);
        // Non-element nodes are a no-op.
        dom.set_attr(root, "value", "x");
        dom.remove_attr(root, "value");
    }
}
