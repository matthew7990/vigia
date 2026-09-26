//! Own HTML parser: tokenizer + tree construction in one streaming pass.
//!
//! Deliberately a pragmatic subset - handles tags, attributes (quoted and
//! unquoted), text, comments, doctype, void elements, raw-text elements and a
//! minimal set of implied end tags. Malformed input is recovered, not rejected.
//! Full HTML5 tree-construction fidelity (adoption agency, foster parenting)
//! is a roadmap item; correctness bugs get fixed case by case.

use entities::decode;
use vigia_dom::Dom;

pub mod entities;

/// Elements that never have children or an end tag.
const VOID: &[&str] = &[
    "area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source", "track",
    "wbr",
];

/// Elements whose content is raw text up to their matching end tag.
const RAW_TEXT: &[&str] = &["script", "style", "title", "textarea"];

/// Start tags that implicitly close a previous sibling of the same tag.
const IMPLIED_END: &[&str] = &["li", "p", "tr", "td", "th", "dt", "dd", "option"];

/// Parse `input` into `dom`, returning the document root id.
pub fn parse(input: &str, dom: &mut Dom) -> u32 {
    let bytes = input.as_bytes();
    let mut pos = 0usize;
    let mut open: Vec<u32> = vec![dom.root()];

    while pos < bytes.len() {
        if bytes[pos] == b'<' {
            match peek(bytes, pos + 1) {
                Some(b'!') => {
                    if input[pos..].starts_with("<!--") {
                        let end = input[pos..]
                            .find("-->")
                            .map(|i| pos + i)
                            .unwrap_or(bytes.len());
                        let inner = &input[pos + 4..end.min(bytes.len())];
                        dom.comment(*open.last().unwrap(), inner);
                        pos = (end + 3).min(bytes.len());
                    } else {
                        pos = skip_past_gt(bytes, pos);
                    }
                }
                Some(b'?') => pos = skip_past_gt(bytes, pos),
                Some(b'/') => {
                    let (name, next) = read_name(bytes, pos + 2);
                    let name = name.to_ascii_lowercase();
                    if let Some(idx) = open
                        .iter()
                        .rposition(|&id| dom.tag_name(id) == Some(name.as_str()))
                    {
                        open.truncate(idx);
                    }
                    pos = skip_past_gt(bytes, next);
                }
                Some(c) if c.is_ascii_alphabetic() => {
                    let (name, mut next) = read_name(bytes, pos + 1);
                    let name = name.to_ascii_lowercase();
                    let (attrs, self_closing, after) = read_attrs(input, next);
                    next = after;

                    if IMPLIED_END.contains(&name.as_str()) {
                        if let Some(idx) = open
                            .iter()
                            .rposition(|&id| dom.tag_name(id) == Some(name.as_str()))
                        {
                            open.truncate(idx);
                        }
                    }

                    let parent = *open.last().unwrap();
                    let id = dom.element(parent, &name, attrs);
                    if !self_closing && !VOID.contains(&name.as_str()) {
                        if RAW_TEXT.contains(&name.as_str()) {
                            let close = format!("</{}", name);
                            let end = input[next..]
                                .find(&close)
                                .map(|i| next + i)
                                .unwrap_or(bytes.len());
                            let raw = &input[next..end.min(bytes.len())];
                            // RCDATA (title/textarea) decodes entities; script/style stay raw.
                            if matches!(name.as_str(), "title" | "textarea") {
                                dom.text(id, &decode(raw));
                            } else {
                                dom.text(id, raw);
                            }
                            pos = skip_past_gt(bytes, end);
                        } else {
                            open.push(id);
                            pos = next;
                        }
                    } else {
                        pos = next;
                    }
                }
                _ => {
                    // Stray '<' in text.
                    dom.text(*open.last().unwrap(), "<");
                    pos += 1;
                }
            }
        } else {
            let end = input[pos..]
                .find('<')
                .map(|i| pos + i)
                .unwrap_or(bytes.len());
            let text = &input[pos..end];
            if !text.trim().is_empty() {
                dom.text(*open.last().unwrap(), &decode(text));
            }
            pos = end;
        }
    }
    dom.root()
}

fn peek(bytes: &[u8], i: usize) -> Option<u8> {
    bytes.get(i).copied()
}

fn skip_past_gt(bytes: &[u8], from: usize) -> usize {
    match bytes[from..].iter().position(|&b| b == b'>') {
        Some(i) => from + i + 1,
        None => bytes.len(),
    }
}

/// Read an identifier (tag/attr name) starting at `from`. Returns (name, next_pos).
fn read_name(bytes: &[u8], from: usize) -> (&str, usize) {
    let mut end = from;
    while end < bytes.len()
        && !bytes[end].is_ascii_whitespace()
        && !matches!(bytes[end], b'/' | b'>' | b'=')
    {
        end += 1;
    }
    (std::str::from_utf8(&bytes[from..end]).unwrap_or(""), end)
}

/// Parse attributes after a tag name. Returns (attrs, self_closing, next_pos).
fn read_attrs(input: &str, from: usize) -> (Vec<(String, String)>, bool, usize) {
    let bytes = input.as_bytes();
    let mut pos = from;
    let mut attrs = Vec::new();
    loop {
        while pos < bytes.len() && bytes[pos].is_ascii_whitespace() {
            pos += 1;
        }
        match peek(bytes, pos) {
            None | Some(b'>') => return (attrs, false, (pos + 1).min(bytes.len())),
            Some(b'/') => {
                if peek(bytes, pos + 1) == Some(b'>') {
                    return (attrs, true, pos + 2);
                }
                pos += 1;
            }
            Some(_) => {
                let (name, next) = read_name(bytes, pos);
                pos = next;
                while pos < bytes.len() && bytes[pos].is_ascii_whitespace() {
                    pos += 1;
                }
                if peek(bytes, pos) == Some(b'=') {
                    pos += 1;
                    while pos < bytes.len() && bytes[pos].is_ascii_whitespace() {
                        pos += 1;
                    }
                    let value = match peek(bytes, pos) {
                        Some(q @ (b'"' | b'\'')) => {
                            let start = pos + 1;
                            let end = input[start..]
                                .find(q as char)
                                .map(|i| start + i)
                                .unwrap_or(bytes.len());
                            let v = decode(&input[start..end]).into_owned();
                            pos = (end + 1).min(bytes.len());
                            v
                        }
                        _ => {
                            let (v, p) = read_name(bytes, pos);
                            let v = decode(v).into_owned();
                            pos = p;
                            v
                        }
                    };
                    if !name.is_empty() {
                        attrs.push((name.to_string(), value));
                    }
                } else if !name.is_empty() {
                    attrs.push((name.to_string(), String::new()));
                }
                let _ = next;
            }
        }
    }
}
