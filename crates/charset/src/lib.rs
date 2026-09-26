//! Own charset detection and decoding to UTF-8. Detection order:
//! BOM -> declared (Content-Type) -> <meta charset>/http-equiv in first KiB
//! -> utf-8 default. Decoders: utf-8 (lossy), windows-1252 (with the
//! iso-8859-1/latin1/ascii aliases folded in, like browsers), utf-16le/be.

use std::borrow::Cow;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Encoding {
    Utf8,
    /// Also covers iso-8859-1 / latin1 / ascii (browser behavior).
    Win1252,
    Utf16Le,
    Utf16Be,
}

/// Full pipeline: pick an encoding, decode to UTF-8.
pub fn decode_auto(bytes: &[u8], declared: Option<&str>) -> String {
    decode(bytes, detect(bytes, declared))
}

pub fn detect(bytes: &[u8], declared: Option<&str>) -> Encoding {
    if bytes.starts_with(&[0xEF, 0xBB, 0xBF]) {
        return Encoding::Utf8;
    }
    if bytes.starts_with(&[0xFF, 0xFE]) {
        return Encoding::Utf16Le;
    }
    if bytes.starts_with(&[0xFE, 0xFF]) {
        return Encoding::Utf16Be;
    }
    if let Some(enc) = declared.and_then(parse_label) {
        return enc;
    }
    if let Some(enc) = sniff_meta(bytes) {
        return enc;
    }
    Encoding::Utf8
}

pub fn decode(bytes: &[u8], enc: Encoding) -> String {
    match enc {
        Encoding::Utf8 => String::from_utf8_lossy(bytes).into_owned(),
        Encoding::Win1252 => decode_win1252(bytes),
        Encoding::Utf16Le => decode_utf16(bytes, true),
        Encoding::Utf16Be => decode_utf16(bytes, false),
    }
}

/// Map a charset label ("utf-8", "iso-8859-1", "windows-1252", ...) to an Encoding.
pub fn parse_label(label: &str) -> Option<Encoding> {
    let l = label.trim().to_ascii_lowercase();
    match l.as_str() {
        "utf-8" | "utf8" | "unicode-1-1-utf-8" => Some(Encoding::Utf8),
        "windows-1252" | "iso-8859-1" | "iso8859-1" | "latin1" | "latin-1" | "us-ascii"
        | "ascii" | "iso-ir-6" => Some(Encoding::Win1252),
        "utf-16le" | "utf-16" => Some(Encoding::Utf16Le),
        "utf-16be" => Some(Encoding::Utf16Be),
        _ => None,
    }
}

/// Look for <meta charset=..> or content="..charset=.." in the head area.
fn sniff_meta(bytes: &[u8]) -> Option<Encoding> {
    let hay = &bytes[..bytes.len().min(1024)];
    let hay_lower: Vec<u8> = hay.iter().map(|b| b.to_ascii_lowercase()).collect();
    let mut search_from = 0;
    while let Some(i) = find_sub(&hay_lower[search_from..], b"charset") {
        let mut j = search_from + i + 7;
        // skip spaces and '=' or '"'/'\'' wrappers
        while j < hay.len() && matches!(hay[j], b' ' | b'=' | b'"' | b'\'') {
            j += 1;
        }
        let end = hay[j..]
            .iter()
            .position(|&b| !matches!(b, b'a'..=b'z' | b'0'..=b'9' | b'-' | b'_'))
            .map(|p| j + p)
            .unwrap_or(hay.len());
        let label = std::str::from_utf8(&hay[j..end]).ok()?;
        if let Some(enc) = parse_label(label) {
            return Some(enc);
        }
        search_from = j;
    }
    None
}

fn find_sub(hay: &[u8], needle: &[u8]) -> Option<usize> {
    hay.windows(needle.len()).position(|w| w == needle)
}

fn decode_win1252(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len());
    for &b in bytes {
        match b {
            0x00..=0x7F => out.push(b as char),
            0x80..=0x9F => match WIN1252_HIGH[(b - 0x80) as usize] {
                Some(s) => out.push_str(s),
                None => out.push(b as char), // undefined slots map through (latin-1)
            },
            _ => out.push(b as char), // 0xA0-0xFF identical to latin-1
        }
    }
    out
}

const WIN1252_HIGH: [Option<&'static str>; 32] = [
    Some("€"), None, Some("‚"), Some("ƒ"), Some("„"), Some("…"), Some("†"), Some("‡"),
    Some("ˆ"), Some("‰"), Some("Š"), Some("‹"), Some("Œ"), None, Some("Ž"), None,
    None, Some("‘"), Some("’"), Some("“"), Some("”"), Some("•"), Some("–"), Some("—"),
    Some("˜"), Some("™"), Some("š"), Some("›"), Some("œ"), None, Some("ž"), Some("Ÿ"),
];

fn decode_utf16(bytes: &[u8], little_endian: bool) -> String {
    let units: Vec<u16> = bytes
        .chunks_exact(2)
        .map(|c| {
            if little_endian {
                u16::from_le_bytes([c[0], c[1]])
            } else {
                u16::from_be_bytes([c[0], c[1]])
            }
        })
        .collect();
    let mut out = String::new();
    let mut i = 0;
    while i < units.len() {
        let u = units[i];
        if (0xD800..0xDC00).contains(&u) && i + 1 < units.len() {
            let u2 = units[i + 1];
            if (0xDC00..0xE000).contains(&u2) {
                let cp = 0x10000 + (((u as u32 - 0xD800) << 10) | (u2 as u32 - 0xDC00));
                out.push(char::from_u32(cp).unwrap_or('\u{FFFD}'));
                i += 2;
                continue;
            }
        }
        out.push(char::from_u32(u as u32).unwrap_or('\u{FFFD}'));
        i += 1;
    }
    out
}

/// Extract charset= from a Content-Type header value, if present.
pub fn charset_of(content_type: Option<&str>) -> Option<Cow<'_, str>> {
    let ct = content_type?;
    let pos = ct.to_ascii_lowercase().find("charset")?;
    let rest = &ct[pos + 7..];
    let rest = rest.trim_start_matches([' ', '=', '"', '\'']);
    let end = rest
        .find(|c: char| matches!(c, ';' | ' ' | '"' | '\''))
        .unwrap_or(rest.len());
    Some(Cow::Borrowed(&rest[..end]))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn win1252() {
        assert_eq!(decode(&[b'a', 0xE9, 0xF1], Encoding::Win1252), "aéñ");
        assert_eq!(decode(&[0x93, b'x', 0x94], Encoding::Win1252), "“x”");
    }

    #[test]
    fn sniffs_meta() {
        let h = b"<html><head><meta charset=iso-8859-1></head>";
        assert_eq!(detect(h, None), Encoding::Win1252);
        let h2 = b"<html><head><meta http-equiv=Content-Type content=\"text/html; charset=utf-8\">";
        assert_eq!(detect(h2, None), Encoding::Utf8);
    }

    #[test]
    fn header_wins() {
        let h = b"<meta charset=utf-8>";
        assert_eq!(detect(h, Some("windows-1252")), Encoding::Win1252);
    }
}
