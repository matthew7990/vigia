//! Own CSS selector engine — pragmatic subset tuned for scraping:
//! `tag`, `*`, `.class`, `#id`, `[attr]` `=` `~=` `|=` `^=` `$=` `*=`,
//! `:first-child` `:last-child` `:nth-child()` `:empty` `:not(compound)`,
//! combinators ` ` `>` `+` `~`, and `,` groups. Tag/attr names are
//! case-insensitive (HTML); class/id values are case-sensitive.

use vigia_dom::{Dom, NodeData, NodeId};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Combinator {
    Descendant,
    Child,
    NextSibling,
    Sibling,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AttrOp {
    Exists,
    Eq,
    Includes,   // ~=
    DashMatch,  // |=
    Prefix,     // ^=
    Suffix,     // $=
    Substring,  // *=
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pseudo {
    FirstChild,
    LastChild,
    OnlyChild,
    Empty,
    /// (a, b) of an+b.
    NthChild(i32, i32),
    Not(Box<Compound>),
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Compound {
    pub tag: Option<String>, // None = universal
    pub id: Option<String>,
    pub classes: Vec<String>,
    pub attrs: Vec<(String, AttrOp, String)>,
    pub pseudos: Vec<Pseudo>,
}

/// compounds[i] <combinators[i]> compounds[i+1]
#[derive(Debug, Clone)]
pub struct Selector {
    pub compounds: Vec<Compound>,
    pub combinators: Vec<Combinator>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CssError(pub String);

impl std::fmt::Display for CssError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "css: {}", self.0)
    }
}
impl std::error::Error for CssError {}

fn err<T>(m: &str) -> Result<T, CssError> {
    Err(CssError(m.to_string()))
}

/// Parse "a > b, c" into selector groups.
pub fn parse(input: &str) -> Result<Vec<Selector>, CssError> {
    let mut groups = Vec::new();
    for part in split_top(input, ',') {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }
        groups.push(parse_complex(part)?);
    }
    if groups.is_empty() {
        return err("empty selector");
    }
    Ok(groups)
}

/// Split on `c` at paren/bracket depth 0.
fn split_top(s: &str, c: char) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut cur = String::new();
    for ch in s.chars() {
        match ch {
            '[' | '(' => depth += 1,
            ']' | ')' => depth -= 1,
            _ => {}
        }
        if ch == c && depth == 0 {
            out.push(std::mem::take(&mut cur));
        } else {
            cur.push(ch);
        }
    }
    out.push(cur);
    out
}

fn parse_complex(s: &str) -> Result<Selector, CssError> {
    let chars: Vec<char> = s.chars().collect();
    let mut compounds = Vec::new();
    let mut combinators = Vec::new();
    let mut i = 0;
    let mut pending = Combinator::Descendant;

    loop {
        while i < chars.len() && chars[i].is_whitespace() {
            i += 1;
        }
        if i >= chars.len() {
            break;
        }
        match chars[i] {
            '>' => {
                pending = Combinator::Child;
                i += 1;
                continue;
            }
            '+' => {
                pending = Combinator::NextSibling;
                i += 1;
                continue;
            }
            '~' => {
                pending = Combinator::Sibling;
                i += 1;
                continue;
            }
            _ => {}
        }

        let (compound, next) = parse_compound(&chars, i)?;
        if !compounds.is_empty() {
            combinators.push(pending.clone());
        }
        compounds.push(compound);
        pending = Combinator::Descendant;
        i = next;
    }

    if compounds.is_empty() {
        return err("empty selector");
    }
    Ok(Selector { compounds, combinators })
}

/// Parse one compound starting at chars[i]. Returns (compound, next_index).
fn parse_compound(chars: &[char], mut i: usize) -> Result<(Compound, usize), CssError> {
    let mut c = Compound::default();

    // Optional tag or *.
    if i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '*' || chars[i] == '-' || chars[i] == '_') {
        let start = i;
        while i < chars.len()
            && (chars[i].is_ascii_alphanumeric() || matches!(chars[i], '-' | '_' | '*' | '|'))
        {
            i += 1;
        }
        let name: String = chars[start..i].iter().collect();
        c.tag = if name == "*" { None } else { Some(name.to_ascii_lowercase()) };
    }

    loop {
        if i >= chars.len() {
            break;
        }
        match chars[i] {
            '.' => {
                i += 1;
                let (name, next) = read_ident(chars, i)?;
                c.classes.push(name);
                i = next;
            }
            '#' => {
                i += 1;
                let (name, next) = read_ident(chars, i)?;
                c.id = Some(name);
                i = next;
            }
            '[' => {
                i += 1;
                let (attr, next) = read_attr(chars, i)?;
                c.attrs.push(attr);
                i = next;
            }
            ':' => {
                i += 1;
                let (pseudo, next) = read_pseudo(chars, i)?;
                c.pseudos.push(pseudo);
                i = next;
            }
            _ => break,
        }
    }

    if c.tag.is_none() && c.id.is_none() && c.classes.is_empty() && c.attrs.is_empty() && c.pseudos.is_empty() {
        return err("expected selector component");
    }
    Ok((c, i))
}

fn read_ident(chars: &[char], i: usize) -> Result<(String, usize), CssError> {
    let start = i;
    let mut j = i;
    while j < chars.len() && (chars[j].is_ascii_alphanumeric() || matches!(chars[j], '-' | '_')) {
        j += 1;
    }
    if j == start {
        return err("expected identifier");
    }
    Ok((chars[start..j].iter().collect(), j))
}

fn read_attr(chars: &[char], mut i: usize) -> Result<((String, AttrOp, String), usize), CssError> {
    while i < chars.len() && chars[i].is_whitespace() {
        i += 1;
    }
    let (name, mut i) = read_ident(chars, i)?;
    while i < chars.len() && chars[i].is_whitespace() {
        i += 1;
    }
    let mut op = AttrOp::Exists;
    let mut value = String::new();
    if i < chars.len() && chars[i] != ']' {
        let two = i + 1 < chars.len() && chars[i + 1] == '=';
        if two {
            op = match chars[i] {
                '~' => AttrOp::Includes,
                '|' => AttrOp::DashMatch,
                '^' => AttrOp::Prefix,
                '$' => AttrOp::Suffix,
                '*' => AttrOp::Substring,
                '=' => return err("bad attr operator"),
                _ => return err("bad attr operator"),
            };
            i += 2;
        } else if chars[i] == '=' {
            op = AttrOp::Eq;
            i += 1;
        } else {
            return err("bad attr selector");
        }
        while i < chars.len() && chars[i].is_whitespace() {
            i += 1;
        }
        if i < chars.len() && (chars[i] == '"' || chars[i] == '\'') {
            let q = chars[i];
            i += 1;
            let start = i;
            while i < chars.len() && chars[i] != q {
                i += 1;
            }
            value = chars[start..i].iter().collect();
            i += 1; // closing quote
        } else {
            // Bare value: read until whitespace or ']'. Wider than the spec
            // (allows / and . unquoted) — pragmatic for scraping selectors.
            let start = i;
            while i < chars.len() && !chars[i].is_whitespace() && chars[i] != ']' {
                i += 1;
            }
            value = chars[start..i].iter().collect();
        }
        while i < chars.len() && chars[i].is_whitespace() {
            i += 1;
        }
    }
    if i >= chars.len() || chars[i] != ']' {
        return err("unclosed attr selector");
    }
    Ok(((name.to_ascii_lowercase(), op, value), i + 1))
}

fn read_pseudo(chars: &[char], mut i: usize) -> Result<(Pseudo, usize), CssError> {
    let (name, mut next) = read_ident(chars, i)?;
    i = next;
    let p = match name.to_ascii_lowercase().as_str() {
        "first-child" => Pseudo::FirstChild,
        "last-child" => Pseudo::LastChild,
        "only-child" => Pseudo::OnlyChild,
        "empty" => Pseudo::Empty,
        "nth-child" => {
            if i >= chars.len() || chars[i] != '(' {
                return err("nth-child needs (n)");
            }
            i += 1;
            let start = i;
            while i < chars.len() && chars[i] != ')' {
                i += 1;
            }
            if i >= chars.len() {
                return err("unclosed nth-child");
            }
            let arg: String = chars[start..i].iter().collect();
            i += 1;
            {
                let (a, b) = parse_an_plus_b(&arg)?;
                Pseudo::NthChild(a, b)
            }
        }
        "not" => {
            if i >= chars.len() || chars[i] != '(' {
                return err("not needs (compound)");
            }
            i += 1;
            while i < chars.len() && chars[i].is_whitespace() {
                i += 1;
            }
            let (inner, next) = parse_compound(chars, i)?;
            i = next;
            while i < chars.len() && chars[i].is_whitespace() {
                i += 1;
            }
            if i >= chars.len() || chars[i] != ')' {
                return err("unclosed :not");
            }
            i += 1;
            Pseudo::Not(Box::new(inner))
        }
        _ => return err("unsupported pseudo"),
    };
    Ok((p, i))
}

/// Parse an+b: "3", "odd", "even", "2n+1", "-n+3", "n".
fn parse_an_plus_b(s: &str) -> Result<(i32, i32), CssError> {
    let s = s.trim().to_ascii_lowercase().replace(' ', "");
    match s.as_str() {
        "odd" => return Ok((2, 1)),
        "even" => return Ok((2, 0)),
        "n" => return Ok((1, 0)),
        "-n" => return Ok((-1, 0)),
        _ => {}
    }
    if let Ok(b) = s.parse::<i32>() {
        return Ok((0, b));
    }
    if let Some(npos) = s.find('n') {
        let (a_str, rest) = s.split_at(npos);
        let a: i32 = match a_str {
            "" | "+" => 1,
            "-" => -1,
            x => x.parse().map_err(|_| CssError("bad nth a".into()))?,
        };
        let b_str = &rest[1..];
        let b: i32 = if b_str.is_empty() {
            0
        } else {
            b_str.parse().map_err(|_| CssError("bad nth b".into()))?
        };
        return Ok((a, b));
    }
    err("bad nth-child")
}

/// All element nodes matching any selector group, in document order.
pub fn query(dom: &Dom, input: &str) -> Result<Vec<NodeId>, CssError> {
    let groups = parse(input)?;
    let mut out = Vec::new();
    for id in 1..dom.nodes.len() as NodeId {
        if !matches!(dom.node(id).data, NodeData::Element(_)) {
            continue;
        }
        if groups.iter().any(|g| matches_at(dom, id, g, g.compounds.len() - 1)) {
            out.push(id);
        }
    }
    Ok(out)
}

fn matches_at(dom: &Dom, id: NodeId, sel: &Selector, i: usize) -> bool {
    if !matches_compound(dom, id, &sel.compounds[i]) {
        return false;
    }
    if i == 0 {
        return true;
    }
    match sel.combinators[i - 1] {
        Combinator::Child => match dom.parent(id) {
            Some(p) => matches_at(dom, p, sel, i - 1),
            None => false,
        },
        Combinator::Descendant => {
            let mut cur = dom.parent(id);
            while let Some(p) = cur {
                if matches_at(dom, p, sel, i - 1) {
                    return true;
                }
                cur = dom.parent(p);
            }
            false
        }
        Combinator::NextSibling => match prev_element_sibling(dom, id) {
            Some(p) => matches_at(dom, p, sel, i - 1),
            None => false,
        },
        Combinator::Sibling => {
            let mut cur = prev_element_sibling(dom, id);
            while let Some(p) = cur {
                if matches_at(dom, p, sel, i - 1) {
                    return true;
                }
                cur = prev_element_sibling(dom, p);
            }
            false
        }
    }
}

fn prev_element_sibling(dom: &Dom, id: NodeId) -> Option<NodeId> {
    let parent = dom.parent(id)?;
    let mut prev = None;
    for &c in dom.children(parent) {
        if c == id {
            return prev;
        }
        if matches!(dom.node(c).data, NodeData::Element(_)) {
            prev = Some(c);
        }
    }
    None
}

/// Element sibling index, 1-based (for nth-child).
fn element_index(dom: &Dom, id: NodeId) -> (usize, usize) {
    let Some(parent) = dom.parent(id) else {
        return (1, 1);
    };
    let mut pos = 0usize;
    let mut total = 0usize;
    for &c in dom.children(parent) {
        if matches!(dom.node(c).data, NodeData::Element(_)) {
            total += 1;
            if c == id {
                pos = total;
            }
        }
    }
    (pos, total)
}

fn matches_compound(dom: &Dom, id: NodeId, c: &Compound) -> bool {
    let NodeData::Element(el) = &dom.node(id).data else {
        return false;
    };

    if let Some(t) = &c.tag {
        if dom.interner.resolve(el.tag) != t.as_str() {
            return false;
        }
    }
    if let Some(want) = &c.id {
        if dom.attr(id, "id") != Some(want.as_str()) {
            return false;
        }
    }
    if !c.classes.is_empty() {
        let have = dom.attr(id, "class").unwrap_or("");
        if !c.classes.iter().all(|cls| have.split_whitespace().any(|h| h == cls)) {
            return false;
        }
    }
    for (name, op, want) in &c.attrs {
        let have = match dom.attr(id, name) {
            Some(v) => v,
            None => return false,
        };
        let ok = match op {
            AttrOp::Exists => true,
            AttrOp::Eq => have == want,
            AttrOp::Includes => have.split_whitespace().any(|h| h == want),
            AttrOp::DashMatch => have == want || have.starts_with(&format!("{want}-")),
            AttrOp::Prefix => have.starts_with(want.as_str()),
            AttrOp::Suffix => have.ends_with(want.as_str()),
            AttrOp::Substring => have.contains(want.as_str()),
        };
        if !ok {
            return false;
        }
    }
    for p in &c.pseudos {
        let ok = match p {
            Pseudo::FirstChild => element_index(dom, id).0 == 1,
            Pseudo::LastChild => {
                let (pos, total) = element_index(dom, id);
                pos == total
            }
            Pseudo::OnlyChild => element_index(dom, id).1 == 1,
            Pseudo::Empty => dom.children(id).iter().all(|&ch| match &dom.node(ch).data {
                NodeData::Element(_) => false,
                NodeData::Text(t) => t.trim().is_empty(),
                _ => true,
            }),
            Pseudo::NthChild(a, b) => {
                let idx = element_index(dom, id).0 as i32;
                if *a == 0 {
                    idx == *b
                } else {
                    let k = idx - b;
                    k % a == 0 && k / a >= 0
                }
            }
            Pseudo::Not(inner) => !matches_compound(dom, id, inner),
        };
        if !ok {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dom_of(html: &str) -> Dom {
        let mut d = Dom::new();
        vigia_html::parse(html, &mut d);
        d
    }

    #[test]
    fn basic_selectors() {
        let d = dom_of("<div id=a><p class=x>t1</p><p>t2</p></div><p class=x>t3</p>");
        assert_eq!(query(&d, "p").unwrap().len(), 3);
        assert_eq!(query(&d, "#a p").unwrap().len(), 2);
        assert_eq!(query(&d, ".x").unwrap().len(), 2);
        assert_eq!(query(&d, "div > p").unwrap().len(), 2);
        assert_eq!(query(&d, "p + p").unwrap().len(), 1);
        assert_eq!(query(&d, "p:first-child").unwrap().len(), 1);
        assert_eq!(query(&d, "p:last-child").unwrap().len(), 2);
        assert_eq!(query(&d, "p:nth-child(2)").unwrap().len(), 2);
        assert_eq!(query(&d, "p:not(.x)").unwrap().len(), 1);
        assert_eq!(query(&d, "div, p.x").unwrap().len(), 3);
        assert!(query(&d, "p[noexist]").unwrap().is_empty());
        assert!(query(&d, "[").is_err());
    }

    #[test]
    fn attr_ops() {
        let d = dom_of(r#"<a href="/x" rel="a b c" lang="es-AR">x</a>"#);
        assert_eq!(query(&d, "[href]").unwrap().len(), 1);
        assert_eq!(query(&d, "[href=/x]").unwrap().len(), 1);
        assert_eq!(query(&d, "[rel~=b]").unwrap().len(), 1);
        assert_eq!(query(&d, "[lang|=es]").unwrap().len(), 1);
        assert_eq!(query(&d, "[href^=/]").unwrap().len(), 1);
        assert_eq!(query(&d, "[href$=x]").unwrap().len(), 1);
        assert_eq!(query(&d, "[href*=x]").unwrap().len(), 1);
        assert!(query(&d, "[href=/y]").unwrap().is_empty());
    }
}
