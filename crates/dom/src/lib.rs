//! Arena DOM.
//!
//! Every node lives in a single `Vec`, addressed by `NodeId` (a `u32`).
//! Tag and attribute names are interned once per document. No `Rc`/`RefCell`
//! graphs and no per-node heap allocation beyond the node vector itself —
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
    /// (interned name, value). Attribute values stay owned — interning them
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
    pub fn element(
        &mut self,
        parent: NodeId,
        tag: &str,
        attrs: Vec<(String, String)>,
    ) -> NodeId {
        let tag_id = self.interner.intern(tag);
        let attrs = attrs
            .into_iter()
            .map(|(k, v)| (self.interner.intern(&k), v))
            .collect();
        let id = self.push(
            Node {
                parent: Some(parent),
                children: Vec::new(),
                data: NodeData::Element(ElementData { tag: tag_id, attrs }),
            },
        );
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
}
