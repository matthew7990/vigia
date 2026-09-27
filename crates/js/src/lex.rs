//! Lexer: source -> tokens. Tracks byte offset per token and whether a
//! newline precedes it (for the parser's ASI-lite). No regex literals:
//! `/` is always division or comment start.

use crate::{err, JsError};

#[derive(Debug, Clone, PartialEq)]
pub enum Tok {
    Num(f64),
    Str(String),
    Ident(String),
    Kw(&'static str),
    P(&'static str),
    Regex { pat: String, flags: String },
    Eof,
}

#[derive(Debug, Clone)]
pub struct Token {
    pub t: Tok,
    /// byte offset of first char
    pub pos: usize,
    /// a newline (or a block comment containing one) precedes this token
    pub nl: bool,
}

const KWS: &[&str] = &[
    "var",
    "let",
    "const",
    "function",
    "return",
    "if",
    "else",
    "while",
    "for",
    "break",
    "continue",
    "true",
    "false",
    "null",
    "undefined",
    "typeof",
    "new",
    "in",
    "instanceof",
    "async",
    "await",
    "throw",
    "try",
    "catch",
    "finally",
];

/// Longest first: prefix order decides `>>>=` vs `>>>` vs `>>` vs `>`.
/// `?.` and `??` are lexed manually (digit guard for `?.`) and emitted as
/// `P("?.")` / `P("??")`.
const PUNCTS: &[&str] = &[
    ">>>=", "===", "!==", ">>>", "<<=", ">>=", "=>", "==", "!=", "<=", ">=", "++", "--", "+=",
    "-=", "*=", "/=", "%=", "&&", "||", "<<", ">>", "&=", "|=", "^=", "=", "<", ">", "+", "-", "*",
    "/", "%", "!", "~", "&", "|", "^", "(", ")", "[", "]", "{", "}", ",", ";", ".", "?", ":",
];

pub fn lex(src: &str) -> Result<Vec<Token>, JsError> {
    let b = src.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    let mut nl = false;
    while i < b.len() {
        match b[i] {
            b' ' | b'\t' | b'\r' => {
                i += 1;
                continue;
            }
            b'\n' => {
                i += 1;
                nl = true;
                continue;
            }
            b'/' if b.get(i + 1) == Some(&b'/') => {
                while i < b.len() && b[i] != b'\n' {
                    i += 1;
                }
                continue;
            }
            b'/' if b.get(i + 1) == Some(&b'*') => {
                i += 2;
                while i + 1 < b.len() && !(b[i] == b'*' && b[i + 1] == b'/') {
                    if b[i] == b'\n' {
                        nl = true;
                    }
                    i += 1;
                }
                if i + 1 >= b.len() {
                    return Err(err("unterminated comment"));
                }
                i += 2;
                continue;
            }
            _ => {}
        }
        let pos = i;
        let t = match b[i] {
            c if c.is_ascii_digit() => num(b, &mut i)?,
            b'.' if b.get(i + 1).is_some_and(|c| c.is_ascii_digit()) => num(b, &mut i)?,
            b'"' | b'\'' => string(b, &mut i)?,
            c if is_ident_start(c) => word(src, b, &mut i),
            b'/' if !matches!(b.get(i + 1), Some(b'/') | Some(b'*')) && regex_allowed(&out) => {
                regex(src, &mut i)?
            }
            b'?' if b.get(i + 1) == Some(&b'?') => {
                i += 2;
                Tok::P("??")
            }
            b'?' if b.get(i + 1) == Some(&b'.') => {
                // `a?.3:0` is a ternary, not an optional chain.
                if b.get(i + 2).is_some_and(|c| c.is_ascii_digit()) {
                    i += 1;
                    Tok::P("?")
                } else {
                    i += 2;
                    Tok::P("?.")
                }
            }
            _ => {
                let hit = PUNCTS.iter().find(|p| src[i..].starts_with(**p));
                match hit {
                    Some(p) => {
                        i += p.len();
                        Tok::P(p)
                    }
                    None => {
                        return Err(err(format!(
                            "unexpected character {:?} at byte {pos}",
                            b[i] as char
                        )))
                    }
                }
            }
        };
        out.push(Token { t, pos, nl });
        nl = false;
    }
    out.push(Token {
        t: Tok::Eof,
        pos: i,
        nl,
    });
    Ok(out)
}

fn is_ident_start(c: u8) -> bool {
    c.is_ascii_alphabetic() || c == b'_' || c == b'$'
}

fn is_ident(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_' || c == b'$'
}

fn num(b: &[u8], i: &mut usize) -> Result<Tok, JsError> {
    let start = *i;
    if b[*i] == b'0' {
        let radix = match b.get(*i + 1) {
            Some(b'x') | Some(b'X') => Some(16),
            Some(b'b') | Some(b'B') => Some(2),
            Some(b'o') | Some(b'O') => Some(8),
            _ => None,
        };
        if let Some(r) = radix {
            *i += 2;
            let s = *i;
            while *i < b.len() && (b[*i] as char).is_digit(r) {
                *i += 1;
            }
            return std::str::from_utf8(&b[s..*i])
                .ok()
                .and_then(|w| u64::from_str_radix(w, r).ok())
                .map(|n| Tok::Num(n as f64))
                .ok_or_else(|| err(format!("bad number at byte {start}")));
        }
    }
    while *i < b.len() && b[*i].is_ascii_digit() {
        *i += 1;
    }
    if b.get(*i) == Some(&b'.') {
        *i += 1;
        while *i < b.len() && b[*i].is_ascii_digit() {
            *i += 1;
        }
    }
    if matches!(b.get(*i), Some(b'e') | Some(b'E')) {
        let save = *i;
        *i += 1;
        if matches!(b.get(*i), Some(b'+') | Some(b'-')) {
            *i += 1;
        }
        if b.get(*i).is_some_and(|c| c.is_ascii_digit()) {
            while *i < b.len() && b[*i].is_ascii_digit() {
                *i += 1;
            }
        } else {
            *i = save; // `1e` is `1` followed by ident `e`
        }
    }
    std::str::from_utf8(&b[start..*i])
        .ok()
        .and_then(|w| w.parse::<f64>().ok())
        .map(Tok::Num)
        .ok_or_else(|| err(format!("bad number at byte {start}")))
}

fn hex(b: &[u8], i: &mut usize, n: usize) -> Result<u32, JsError> {
    if *i + n > b.len() {
        return Err(err("short \\u escape"));
    }
    let s = std::str::from_utf8(&b[*i..*i + n]).map_err(|_| err("bad \\u escape"))?;
    *i += n;
    u32::from_str_radix(s, 16).map_err(|_| err("bad \\u hex"))
}

fn string(b: &[u8], i: &mut usize) -> Result<Tok, JsError> {
    let q = b[*i];
    *i += 1;
    let mut s = String::new();
    let mut chunk = *i;
    loop {
        match b.get(*i).copied() {
            None | Some(b'\n') | Some(b'\r') => return Err(err("unterminated string")),
            Some(c) if c == q => {
                s.push_str(
                    std::str::from_utf8(&b[chunk..*i]).map_err(|_| err("bad utf-8 in string"))?,
                );
                *i += 1;
                return Ok(Tok::Str(s));
            }
            Some(b'\\') => {
                s.push_str(
                    std::str::from_utf8(&b[chunk..*i]).map_err(|_| err("bad utf-8 in string"))?,
                );
                *i += 1;
                let e = b
                    .get(*i)
                    .copied()
                    .ok_or_else(|| err("unterminated escape"))?;
                *i += 1;
                match e {
                    b'n' => s.push('\n'),
                    b't' => s.push('\t'),
                    b'r' => s.push('\r'),
                    b'b' => s.push('\u{8}'),
                    b'f' => s.push('\u{c}'),
                    b'v' => s.push('\u{b}'),
                    b'0' => s.push('\0'),
                    b'\\' => s.push('\\'),
                    b'\'' => s.push('\''),
                    b'"' => s.push('"'),
                    b'/' => s.push('/'),
                    b'\n' => {} // line continuation
                    b'\r' => {
                        if b.get(*i) == Some(&b'\n') {
                            *i += 1;
                        }
                    }
                    b'x' => {
                        let h = hex(b, i, 2)?;
                        s.push(char::from_u32(h).unwrap_or('\u{FFFD}'));
                    }
                    b'u' => {
                        let hi = hex(b, i, 4)?;
                        if (0xD800..0xDC00).contains(&hi)
                            && b.get(*i) == Some(&b'\\')
                            && b.get(*i + 1) == Some(&b'u')
                        {
                            *i += 2;
                            let lo = hex(b, i, 4)?;
                            let cp =
                                0x10000 + ((hi - 0xD800) << 10) + (lo.wrapping_sub(0xDC00) & 0x3FF);
                            s.push(char::from_u32(cp).unwrap_or('\u{FFFD}'));
                        } else {
                            s.push(char::from_u32(hi).unwrap_or('\u{FFFD}'));
                        }
                    }
                    // unknown escape = the char itself (JS sloppy rule)
                    other => s.push(other as char),
                }
                chunk = *i;
            }
            Some(_) => *i += 1,
        }
    }
}

fn word(src: &str, b: &[u8], i: &mut usize) -> Tok {
    let s = *i;
    while *i < b.len() && is_ident(b[*i]) {
        *i += 1;
    }
    let w = &src[s..*i];
    match KWS.iter().copied().find(|k| *k == w) {
        Some(k) => Tok::Kw(k),
        None => Tok::Ident(w.to_string()),
    }
}

/// `/` opens a regex when an operand is expected: start of input, or the
/// previous token is not a value-end (`)`, `]`, number, string, name) and
/// not a keyword that ends an expression.
fn regex_allowed(out: &[Token]) -> bool {
    let Some(prev) = out.last() else {
        return true;
    };
    match &prev.t {
        Tok::P(p) => !matches!(*p, ")" | "]"),
        Tok::Kw(k) => matches!(
            *k,
            "return"
                | "typeof"
                | "new"
                | "in"
                | "instanceof"
                | "throw"
                | "delete"
                | "void"
                | "do"
                | "else"
                | "case"
                | "yield"
        ),
        // Num/Str/Ident/Regex/Eof end a value: `/` divides.
        _ => false,
    }
}

/// Scan `/pat/flags` from the opening `/` (already confirmed not to be a
/// comment). Returns the Regex token.
fn regex(src: &str, i: &mut usize) -> Result<Tok, JsError> {
    let b = src.as_bytes();
    let start = *i + 1;
    *i += 1;
    let mut in_class = false;
    let mut class_first = false;
    loop {
        let Some(&c) = b.get(*i) else {
            return Err(err("unterminated regex"));
        };
        match c {
            b'\n' | b'\r' => return Err(err("newline in regex literal")),
            b'\\' => {
                *i += 1;
                match b.get(*i) {
                    None => return Err(err("unterminated regex")),
                    Some(b'\n') | Some(b'\r') => return Err(err("newline in regex literal")),
                    Some(_) => {
                        class_first = false;
                        *i += 1;
                    }
                }
            }
            b'[' if !in_class => {
                in_class = true;
                class_first = true;
                *i += 1;
            }
            b']' if in_class && !class_first => {
                in_class = false;
                *i += 1;
            }
            b'/' if !in_class => break,
            _ => {
                class_first = false;
                *i += 1;
            }
        }
    }
    let pat = src[start..*i].to_string();
    *i += 1; // closing '/'
    let fs = *i;
    while b.get(*i).is_some_and(|c| c.is_ascii_alphabetic()) {
        *i += 1;
    }
    Ok(Tok::Regex {
        pat,
        flags: src[fs..*i].to_string(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tt(src: &str) -> Vec<Tok> {
        lex(src)
            .unwrap()
            .into_iter()
            .map(|t| t.t)
            .filter(|t| *t != Tok::Eof)
            .collect()
    }

    #[test]
    fn numbers() {
        assert_eq!(
            tt("0x10 42 .5 1e3 2.5e-1 0b11 0o17"),
            vec![
                Tok::Num(16.0),
                Tok::Num(42.0),
                Tok::Num(0.5),
                Tok::Num(1000.0),
                Tok::Num(0.25),
                Tok::Num(3.0),
                Tok::Num(15.0),
            ]
        );
    }

    #[test]
    fn strings_and_escapes() {
        assert_eq!(
            tt(r#"'a\nb' "c\"d" 'A' 'x\ty'"#),
            vec![
                Tok::Str("a\nb".into()),
                Tok::Str("c\"d".into()),
                Tok::Str("A".into()),
                Tok::Str("x\ty".into()),
            ]
        );
    }

    #[test]
    fn comments_and_newlines() {
        let t = lex("a // hi\nb /* x\ny */ c").unwrap();
        assert_eq!(t.len() - 1, 3); // a b c + eof
        assert!(t[1].nl); // b follows the // line's newline
        assert!(t[2].nl); // c follows a /* */ containing a newline
    }

    #[test]
    fn punct_longest_match() {
        assert_eq!(
            tt("a===b a!==c a>>>=b a+=1"),
            vec![
                Tok::Ident("a".into()),
                Tok::P("==="),
                Tok::Ident("b".into()),
                Tok::Ident("a".into()),
                Tok::P("!=="),
                Tok::Ident("c".into()),
                Tok::Ident("a".into()),
                Tok::P(">>>="),
                Tok::Ident("b".into()),
                Tok::Ident("a".into()),
                Tok::P("+="),
                Tok::Num(1.0),
            ]
        );
    }

    #[test]
    fn keywords_vs_idents() {
        assert_eq!(
            tt("var letx functiony in"),
            vec![
                Tok::Kw("var"),
                Tok::Ident("letx".into()),
                Tok::Ident("functiony".into()),
                Tok::Kw("in"),
            ]
        );
    }

    #[test]
    fn regex_vs_division() {
        assert_eq!(
            tt("a/b"),
            vec![Tok::Ident("a".into()), Tok::P("/"), Tok::Ident("b".into())]
        );
        assert_eq!(
            tt("x=/ab+/gi"),
            vec![
                Tok::Ident("x".into()),
                Tok::P("="),
                Tok::Regex {
                    pat: "ab+".into(),
                    flags: "gi".into()
                },
            ]
        );
        assert_eq!(
            tt("return /x/.test(y)"),
            vec![
                Tok::Kw("return"),
                Tok::Regex {
                    pat: "x".into(),
                    flags: "".into()
                },
                Tok::P("."),
                Tok::Ident("test".into()),
                Tok::P("("),
                Tok::Ident("y".into()),
                Tok::P(")"),
            ]
        );
    }

    #[test]
    fn errors() {
        assert!(lex("'abc").is_err());
        assert!(lex("/* abc").is_err());
        assert!(lex("@").is_err());
        assert!(lex("a\n'b'").is_ok());
    }
}
