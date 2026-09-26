//! HTML entity decoding. Named subset covering what real pages use
//! (esp. Spanish/Latin accented chars), plus numeric and hex references.
//! Full WHATWG table is ~2231 entries of generated data - roadmap item;
//! this covers the entities that actually appear in the wild.

use std::borrow::Cow;

/// Decode entities in `s`. Zero-alloc when no '&' is present.
pub fn decode(s: &str) -> Cow<'_, str> {
    if !s.contains('&') {
        return Cow::Borrowed(s);
    }
    let mut out = String::with_capacity(s.len());
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'&' {
            if let Some(len) = parse_entity(&s[i..], &mut out) {
                i += len;
                continue;
            }
        }
        let ch_len = utf8_len(bytes[i]);
        out.push_str(&s[i..i + ch_len]);
        i += ch_len;
    }
    Cow::Owned(out)
}

fn utf8_len(b: u8) -> usize {
    if b < 0x80 {
        1
    } else if b < 0xE0 {
        2
    } else if b < 0xF0 {
        3
    } else {
        4
    }
}

/// Parse the entity starting at `s` (s[0] == '&'), append decoded text to
/// `out`, return consumed length. None = not an entity, leave literal.
fn parse_entity(s: &str, out: &mut String) -> Option<usize> {
    let rest = &s[1..];
    if rest.starts_with('#') {
        return numeric(rest, out);
    }
    let name_end = rest
        .find(|c: char| !c.is_ascii_alphanumeric())
        .unwrap_or(rest.len());
    if name_end == 0 {
        return None;
    }
    let run = &rest[..name_end];
    if rest.as_bytes().get(name_end) == Some(&b';') {
        if let Some(v) = lookup(run) {
            out.push_str(v);
            return Some(1 + name_end + 1);
        }
    }
    // legacy no-semicolon: longest prefix that is a known entity
    let mut n = run.len().min(8);
    while n > 0 {
        if let Some((_, v)) = LEGACY_NOSEMI.iter().find(|(k, _)| *k == &run[..n]) {
            out.push_str(v);
            return Some(1 + n);
        }
        n -= 1;
    }
    None
}

fn numeric(rest: &str, out: &mut String) -> Option<usize> {
    let (digits, hex) = match rest.as_bytes().get(1) {
        Some(b'x') | Some(b'X') => (&rest[2..], true),
        _ => (&rest[1..], false),
    };
    let end = digits
        .find(|c: char| {
            !(if hex {
                c.is_ascii_hexdigit()
            } else {
                c.is_ascii_digit()
            })
        })
        .unwrap_or(digits.len());
    if end == 0 {
        return None;
    }
    let semi = usize::from(digits.as_bytes().get(end) == Some(&b';'));
    let n = u32::from_str_radix(&digits[..end], if hex { 16 } else { 10 }).ok()?;

    // Spec maps C1 controls (0x80-0x9F) through Windows-1252.
    if let Some((_, s)) = WIN1252_C1.iter().find(|(c, _)| *c == n) {
        out.push_str(s);
    } else {
        let valid = match n {
            0 | 0xD800..=0xDFFF => 0xFFFD,
            x if x > 0x10FFFF => 0xFFFD,
            x => x,
        };
        out.push(char::from_u32(valid)?);
    }
    Some(1 + 1 + usize::from(hex) + end + semi)
}

fn lookup(name: &str) -> Option<&'static str> {
    NAMED.iter().find(|(k, _)| *k == name).map(|(_, v)| *v)
}

/// Entities browsers accept without a semicolon (subset of the spec's list).
const LEGACY_NOSEMI: &[(&str, &str)] = &[
    ("amp", "&"),
    ("lt", "<"),
    ("gt", ">"),
    ("quot", "\""),
    ("nbsp", "\u{A0}"),
    ("copy", "©"),
    ("reg", "®"),
    ("trade", "™"),
    ("hellip", "…"),
    ("mdash", "—"),
    ("ndash", "–"),
    ("laquo", "«"),
    ("raquo", "»"),
    ("times", "×"),
    ("divide", "÷"),
    ("euro", "€"),
    ("pound", "£"),
    ("yen", "¥"),
    ("cent", "¢"),
    ("deg", "°"),
    ("plusmn", "±"),
    ("para", "¶"),
    ("sect", "§"),
    ("middot", "·"),
    ("bull", "•"),
    ("micro", "µ"),
];

/// Windows-1252 mapping for C1 control code points (&#128;-&#159;).
const WIN1252_C1: &[(u32, &str)] = &[
    (0x80, "€"),
    (0x82, "‚"),
    (0x83, "ƒ"),
    (0x84, "„"),
    (0x85, "…"),
    (0x86, "†"),
    (0x87, "‡"),
    (0x88, "ˆ"),
    (0x89, "‰"),
    (0x8A, "Š"),
    (0x8B, "‹"),
    (0x8C, "Œ"),
    (0x8E, "Ž"),
    (0x91, "‘"),
    (0x92, "’"),
    (0x93, "“"),
    (0x94, "”"),
    (0x95, "•"),
    (0x96, "–"),
    (0x97, "—"),
    (0x98, "˜"),
    (0x99, "™"),
    (0x9A, "š"),
    (0x9B, "›"),
    (0x9C, "œ"),
    (0x9E, "ž"),
    (0x9F, "Ÿ"),
];

/// Common named entities. Linear scan is fine at this size (~190 entries).
const NAMED: &[(&str, &str)] = &[
    ("amp", "&"),
    ("lt", "<"),
    ("gt", ">"),
    ("quot", "\""),
    ("apos", "'"),
    ("nbsp", "\u{A0}"),
    ("ensp", "\u{2002}"),
    ("emsp", "\u{2003}"),
    ("thinsp", "\u{2009}"),
    ("zwnj", "\u{200C}"),
    ("zwj", "\u{200D}"),
    ("shy", "\u{AD}"),
    ("hellip", "…"),
    ("mdash", "—"),
    ("ndash", "–"),
    ("lsquo", "‘"),
    ("rsquo", "’"),
    ("ldquo", "“"),
    ("rdquo", "”"),
    ("sbquo", "‚"),
    ("bdquo", "„"),
    ("dagger", "†"),
    ("Dagger", "‡"),
    ("bull", "•"),
    ("prime", "′"),
    ("Prime", "″"),
    ("lsaquo", "‹"),
    ("rsaquo", "›"),
    ("oline", "‾"),
    ("frasl", "⁄"),
    ("copy", "©"),
    ("reg", "®"),
    ("trade", "™"),
    ("euro", "€"),
    ("pound", "£"),
    ("yen", "¥"),
    ("cent", "¢"),
    ("curren", "¤"),
    ("deg", "°"),
    ("plusmn", "±"),
    ("times", "×"),
    ("divide", "÷"),
    ("micro", "µ"),
    ("para", "¶"),
    ("sect", "§"),
    ("middot", "·"),
    ("permil", "‰"),
    ("sup1", "¹"),
    ("sup2", "²"),
    ("sup3", "³"),
    ("frac14", "¼"),
    ("frac12", "½"),
    ("frac34", "¾"),
    ("iexcl", "¡"),
    ("iquest", "¿"),
    ("ordf", "ª"),
    ("ordm", "º"),
    ("laquo", "«"),
    ("raquo", "»"),
    ("not", "¬"),
    ("macr", "¯"),
    ("acute", "´"),
    ("cedil", "¸"),
    ("uml", "¨"),
    ("brvbar", "¦"),
    ("weierp", "℘"),
    ("image", "ℑ"),
    ("real", "ℜ"),
    ("alefsym", "ℵ"),
    ("spades", "♠"),
    ("clubs", "♣"),
    ("hearts", "♥"),
    ("diams", "♦"),
    ("larr", "←"),
    ("uarr", "↑"),
    ("rarr", "→"),
    ("darr", "↓"),
    ("harr", "↔"),
    ("forall", "∀"),
    ("part", "∂"),
    ("exist", "∃"),
    ("empty", "∅"),
    ("nabla", "∇"),
    ("isin", "∈"),
    ("notin", "∉"),
    ("prod", "∏"),
    ("sum", "∑"),
    ("minus", "−"),
    ("lowast", "∗"),
    ("radic", "√"),
    ("prop", "∝"),
    ("infin", "∞"),
    ("and", "∧"),
    ("or", "∨"),
    ("cap", "∩"),
    ("cup", "∪"),
    ("int", "∫"),
    ("there4", "∴"),
    ("sim", "∼"),
    ("cong", "≅"),
    ("asymp", "≈"),
    ("ne", "≠"),
    ("equiv", "≡"),
    ("le", "≤"),
    ("ge", "≥"),
    ("sub", "⊂"),
    ("sup", "⊃"),
    ("nsub", "⊄"),
    ("sube", "⊆"),
    ("supe", "⊇"),
    ("oplus", "⊕"),
    ("otimes", "⊗"),
    ("perp", "⊥"),
    ("sdot", "⋅"),
    ("Agrave", "À"),
    ("Aacute", "Á"),
    ("Acirc", "Â"),
    ("Atilde", "Ã"),
    ("Auml", "Ä"),
    ("Aring", "Å"),
    ("AElig", "Æ"),
    ("Ccedil", "Ç"),
    ("Egrave", "È"),
    ("Eacute", "É"),
    ("Ecirc", "Ê"),
    ("Euml", "Ë"),
    ("Igrave", "Ì"),
    ("Iacute", "Í"),
    ("Icirc", "Î"),
    ("Iuml", "Ï"),
    ("ETH", "Ð"),
    ("Ntilde", "Ñ"),
    ("Ograve", "Ò"),
    ("Oacute", "Ó"),
    ("Ocirc", "Ô"),
    ("Otilde", "Õ"),
    ("Ouml", "Ö"),
    ("Oslash", "Ø"),
    ("Ugrave", "Ù"),
    ("Uacute", "Ú"),
    ("Ucirc", "Û"),
    ("Uuml", "Ü"),
    ("Yacute", "Ý"),
    ("THORN", "Þ"),
    ("szlig", "ß"),
    ("agrave", "à"),
    ("aacute", "á"),
    ("acirc", "â"),
    ("atilde", "ã"),
    ("auml", "ä"),
    ("aring", "å"),
    ("aelig", "æ"),
    ("ccedil", "ç"),
    ("egrave", "è"),
    ("eacute", "é"),
    ("ecirc", "ê"),
    ("euml", "ë"),
    ("igrave", "ì"),
    ("iacute", "í"),
    ("icirc", "î"),
    ("iuml", "ï"),
    ("eth", "ð"),
    ("ntilde", "ñ"),
    ("ograve", "ò"),
    ("oacute", "ó"),
    ("ocirc", "ô"),
    ("otilde", "õ"),
    ("ouml", "ö"),
    ("oslash", "ø"),
    ("ugrave", "ù"),
    ("uacute", "ú"),
    ("ucirc", "û"),
    ("uuml", "ü"),
    ("yacute", "ý"),
    ("thorn", "þ"),
    ("yuml", "ÿ"),
    ("Alpha", "Α"),
    ("Beta", "Β"),
    ("Gamma", "Γ"),
    ("Delta", "Δ"),
    ("alpha", "α"),
    ("beta", "β"),
    ("gamma", "γ"),
    ("delta", "δ"),
    ("epsilon", "ε"),
    ("theta", "θ"),
    ("lambda", "λ"),
    ("mu", "μ"),
    ("pi", "π"),
    ("sigma", "σ"),
    ("phi", "φ"),
    ("omega", "ω"),
    ("Omega", "Ω"),
    ("Sigma", "Σ"),
    ("Pi", "Π"),
    ("Theta", "Θ"),
    ("Lambda", "Λ"),
    ("Phi", "Φ"),
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decodes() {
        assert_eq!(decode("a &amp; b"), "a & b");
        assert_eq!(decode("&lt;div&gt;"), "<div>");
        assert_eq!(decode("ni&ntilde;o"), "niño");
        assert_eq!(decode("caf&eacute;"), "café");
        assert_eq!(decode("&#65;&#x42;"), "AB");
        assert_eq!(decode("&quot;q&quot;"), "\"q\"");
        assert_eq!(decode("100&deg;"), "100°");
        assert_eq!(decode("sin entidades"), "sin entidades");
        assert_eq!(decode("a & b"), "a & b");
        assert_eq!(decode("&#150;"), "–");
        assert_eq!(decode("&amp"), "&");
        assert_eq!(decode("&ampx"), "&x");
    }
}
