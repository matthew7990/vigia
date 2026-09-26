//! vigia-json: own JSON parser/serializer. No serde.
//!
//! Value model preserves object key order (Vec of pairs) and keeps numbers
//! as f64 - sufficient for agent-side data extraction from embedded JSON
//! (`__NEXT_DATA__`, `ld+json`, API responses).

#[derive(Debug, Clone, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    Num(f64),
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(String, Json)>),
}

#[derive(Debug)]
pub struct JsonError(pub &'static str, pub usize);

impl std::fmt::Display for JsonError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "json: {} at byte {}", self.0, self.1)
    }
}
impl std::error::Error for JsonError {}

const MAX_DEPTH: u32 = 200;

impl Json {
    pub fn parse(text: &str) -> Result<Json, JsonError> {
        let b = text.as_bytes();
        let mut i = skip_ws(b, 0);
        let mut depth = 0;
        let v = value(b, &mut i, &mut depth)?;
        i = skip_ws(b, i);
        if i != b.len() {
            return Err(JsonError("trailing characters", i));
        }
        Ok(v)
    }

    /// Dotted path lookup: "props.pageProps.items.0.name".
    /// Numeric segments index arrays; other segments match object keys.
    pub fn get(&self, path: &str) -> Option<&Json> {
        let mut cur = self;
        for seg in path.split('.') {
            cur = match cur {
                Json::Obj(pairs) => &pairs.iter().find(|(k, _)| k == seg)?.1,
                Json::Arr(items) => items.get(seg.parse::<usize>().ok()?)?,
                _ => return None,
            };
        }
        Some(cur)
    }

    fn write(&self, out: &mut String) {
        match self {
            Json::Null => out.push_str("null"),
            Json::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            Json::Num(n) => {
                if n.fract() == 0.0 && n.abs() < 9e15 {
                    out.push_str(&(*n as i64).to_string());
                } else {
                    out.push_str(&n.to_string());
                }
            }
            Json::Str(s) => write_str(s, out),
            Json::Arr(items) => {
                out.push('[');
                for (i, v) in items.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    v.write(out);
                }
                out.push(']');
            }
            Json::Obj(pairs) => {
                out.push('{');
                for (i, (k, v)) in pairs.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    write_str(k, out);
                    out.push(':');
                    v.write(out);
                }
                out.push('}');
            }
        }
    }
}

impl std::fmt::Display for Json {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();
        self.write(&mut s);
        f.write_str(&s)
    }
}

fn write_str(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

fn skip_ws(b: &[u8], mut i: usize) -> usize {
    while i < b.len() && matches!(b[i], b' ' | b'\t' | b'\n' | b'\r') {
        i += 1;
    }
    i
}

fn value(b: &[u8], i: &mut usize, depth: &mut u32) -> Result<Json, JsonError> {
    *depth += 1;
    if *depth > MAX_DEPTH {
        return Err(JsonError("nesting too deep", *i));
    }
    let r = match b.get(*i).copied() {
        Some(b'{') => object(b, i, depth),
        Some(b'[') => array(b, i, depth),
        Some(b'"') => string(b, i).map(Json::Str),
        Some(b't') => literal(b, i, b"true", Json::Bool(true)),
        Some(b'f') => literal(b, i, b"false", Json::Bool(false)),
        Some(b'n') => literal(b, i, b"null", Json::Null),
        Some(c) if c == b'-' || c.is_ascii_digit() => number(b, i),
        Some(_) => Err(JsonError("unexpected character", *i)),
        None => Err(JsonError("unexpected end", *i)),
    };
    *depth -= 1;
    r
}

fn literal(b: &[u8], i: &mut usize, lit: &[u8], v: Json) -> Result<Json, JsonError> {
    if b[*i..].starts_with(lit) {
        *i += lit.len();
        Ok(v)
    } else {
        Err(JsonError("invalid literal", *i))
    }
}

fn number(b: &[u8], i: &mut usize) -> Result<Json, JsonError> {
    let start = *i;
    while *i < b.len() && matches!(b[*i], b'-' | b'+' | b'.' | b'e' | b'E' | b'0'..=b'9') {
        *i += 1;
    }
    std::str::from_utf8(&b[start..*i])
        .ok()
        .and_then(|s| s.parse::<f64>().ok())
        .map(Json::Num)
        .ok_or(JsonError("invalid number", start))
}

fn string(b: &[u8], i: &mut usize) -> Result<String, JsonError> {
    *i += 1; // opening quote
    let mut out = String::new();
    let mut chunk_start = *i;
    loop {
        match b.get(*i).copied() {
            None => return Err(JsonError("unterminated string", *i)),
            Some(b'"') => {
                out.push_str(
                    std::str::from_utf8(&b[chunk_start..*i])
                        .map_err(|_| JsonError("bad utf-8", *i))?,
                );
                *i += 1;
                return Ok(out);
            }
            Some(b'\\') => {
                out.push_str(
                    std::str::from_utf8(&b[chunk_start..*i])
                        .map_err(|_| JsonError("bad utf-8", *i))?,
                );
                *i += 1;
                let e = b
                    .get(*i)
                    .copied()
                    .ok_or(JsonError("unterminated escape", *i))?;
                *i += 1;
                match e {
                    b'"' => out.push('"'),
                    b'\\' => out.push('\\'),
                    b'/' => out.push('/'),
                    b'b' => out.push('\u{8}'),
                    b'f' => out.push('\u{c}'),
                    b'n' => out.push('\n'),
                    b'r' => out.push('\r'),
                    b't' => out.push('\t'),
                    b'u' => {
                        let hi = hex4(b, i)?;
                        if (0xD800..0xDC00).contains(&hi) {
                            // surrogate pair
                            if b.get(*i) == Some(&b'\\') && b.get(*i + 1) == Some(&b'u') {
                                *i += 2;
                                let lo = hex4(b, i)?;
                                let cp = 0x10000
                                    + ((hi - 0xD800) << 10)
                                    + (lo.wrapping_sub(0xDC00) & 0x3FF);
                                out.push(char::from_u32(cp).unwrap_or('\u{FFFD}'));
                            } else {
                                out.push('\u{FFFD}');
                            }
                        } else {
                            out.push(char::from_u32(hi).unwrap_or('\u{FFFD}'));
                        }
                    }
                    _ => return Err(JsonError("bad escape", *i)),
                }
                chunk_start = *i;
            }
            Some(_) => *i += 1,
        }
    }
}

fn hex4(b: &[u8], i: &mut usize) -> Result<u32, JsonError> {
    if *i + 4 > b.len() {
        return Err(JsonError("short \\u escape", *i));
    }
    let s = std::str::from_utf8(&b[*i..*i + 4]).map_err(|_| JsonError("bad \\u", *i))?;
    *i += 4;
    u32::from_str_radix(s, 16).map_err(|_| JsonError("bad \\u hex", *i))
}

fn array(b: &[u8], i: &mut usize, depth: &mut u32) -> Result<Json, JsonError> {
    *i += 1;
    let mut items = Vec::new();
    *i = skip_ws(b, *i);
    if b.get(*i) == Some(&b']') {
        *i += 1;
        return Ok(Json::Arr(items));
    }
    loop {
        *i = skip_ws(b, *i);
        items.push(value(b, i, depth)?);
        *i = skip_ws(b, *i);
        match b.get(*i).copied() {
            Some(b',') => *i += 1,
            Some(b']') => {
                *i += 1;
                return Ok(Json::Arr(items));
            }
            _ => return Err(JsonError("expected , or ]", *i)),
        }
    }
}

fn object(b: &[u8], i: &mut usize, depth: &mut u32) -> Result<Json, JsonError> {
    *i += 1;
    let mut pairs = Vec::new();
    *i = skip_ws(b, *i);
    if b.get(*i) == Some(&b'}') {
        *i += 1;
        return Ok(Json::Obj(pairs));
    }
    loop {
        *i = skip_ws(b, *i);
        if b.get(*i) != Some(&b'"') {
            return Err(JsonError("expected key", *i));
        }
        let k = string(b, i)?;
        *i = skip_ws(b, *i);
        if b.get(*i) != Some(&b':') {
            return Err(JsonError("expected :", *i));
        }
        *i += 1;
        *i = skip_ws(b, *i);
        let v = value(b, i, depth)?;
        pairs.push((k, v));
        *i = skip_ws(b, *i);
        match b.get(*i).copied() {
            Some(b',') => *i += 1,
            Some(b'}') => {
                *i += 1;
                return Ok(Json::Obj(pairs));
            }
            _ => return Err(JsonError("expected , or }", *i)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip() {
        let src = r#"{"a":1,"b":[true,null,"x\ny"],"c":{"d":-2.5}}"#;
        let v = Json::parse(src).unwrap();
        assert_eq!(
            v.to_string(),
            r#"{"a":1,"b":[true,null,"x\ny"],"c":{"d":-2.5}}"#
        );
    }

    #[test]
    fn unicode_escapes() {
        let v = Json::parse(r#""caf\u00e9 \ud83d\ude00""#).unwrap();
        assert_eq!(v, Json::Str("café \u{1F600}".into()));
    }

    #[test]
    fn get_path() {
        let v = Json::parse(r#"{"props":{"items":[{"name":"a"},{"name":"b"}]}}"#).unwrap();
        assert_eq!(v.get("props.items.1.name"), Some(&Json::Str("b".into())));
        assert_eq!(v.get("props.items.5"), None);
        assert_eq!(v.get("props.missing.x"), None);
    }

    #[test]
    fn rejects() {
        assert!(Json::parse("{").is_err());
        assert!(Json::parse("[1,]").is_err());
        assert!(Json::parse("\"abc").is_err());
        assert!(Json::parse("1 2").is_err());
        // depth cap
        let deep = "[".repeat(300) + &"]".repeat(300);
        assert!(Json::parse(&deep).is_err());
    }

    #[test]
    fn next_data_style() {
        let v = Json::parse(
            r#"{"props":{"pageProps":{"items":[1,2,3]}},"page":"/products","buildId":"abc"}"#,
        )
        .unwrap();
        assert_eq!(v.get("props.pageProps.items.2"), Some(&Json::Num(3.0)));
        assert_eq!(v.get("page"), Some(&Json::Str("/products".into())));
    }
}
