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
    Regex {
        pat: String,
        flags: String,
    },
    /// Template chunk: cooked text (None when an invalid escape poisons
    /// it - only legal on tagged templates per ES2018) plus the raw
    /// source text; `expr` means it ended in `${`, `head` means it opened
    /// with a backtick (a Tpl after an expression with head set is a
    /// tagged template; continuations never are).
    Tpl {
        cooked: Option<String>,
        raw: String,
        expr: bool,
        head: bool,
    },
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
    "switch",
    "case",
    "default",
    "do",
    "void",
    "delete",
    "class",
    "extends",
    "super",
];

/// Longest first: prefix order decides `>>>=` vs `>>>` vs `>>` vs `>`.
/// `?.` and `??` are lexed manually (digit guard for `?.`) and emitted as
/// `P("?.")` / `P("??")`.
const PUNCTS: &[&str] = &[
    ">>>=", "**=", "===", "!==", ">>>", "**", "<<=", ">>=", "=>", "==", "!=", "<=", ">=", "++",
    "--", "+=", "-=", "*=", "/=", "%=", "&&", "||", "<<", ">>", "&=", "|=", "^=", "=", "<", ">",
    "+", "-", "*", "/", "%", "!", "~", "&", "|", "^", "(", ")", "[", "]", "{", "}", ",", ";",
    "...", ".", "?", ":",
];

pub fn lex(src: &str) -> Result<Vec<Token>, JsError> {
    let b = src.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    let mut nl = false;
    // `{` push false; a `}` popping true resumes template scanning.
    let mut braces: Vec<bool> = Vec::new();
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
            // Identifier starting with a unicode escape (`\u0061bc`).
            b'\\' if b.get(i + 1) == Some(&b'u') => word(src, b, &mut i),
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
            b'`' => {
                i += 1;
                tpl_chunk(b, &mut i, &mut braces, true)?
            }
            b'}' if matches!(braces.last(), Some(true)) => {
                braces.pop();
                i += 1;
                tpl_chunk(b, &mut i, &mut braces, false)?
            }
            _ => {
                let hit = PUNCTS.iter().find(|p| src[i..].starts_with(**p));
                match hit {
                    Some(p) => {
                        i += p.len();
                        if *p == "{" {
                            braces.push(false);
                        } else if *p == "}" && braces.pop() != Some(false) {
                            // A `}` with no matching `{`: the template arm
                            // above owns `}` closing a substitution, so this
                            // is a genuine unbalanced brace.
                            return Err(err(format!("unbalanced '}}' at byte {pos}")));
                        }
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
                push_escape(b, &mut *i, &mut s)?;
                chunk = *i;
            }
            Some(_) => *i += 1,
        }
    }
}

/// One `\x` escape after the backslash was consumed. Shared by strings
/// and template literals (both also accept \` \$ etc. via the fallback).
fn push_escape(b: &[u8], i: &mut usize, s: &mut String) -> Result<(), JsError> {
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
                let cp = 0x10000 + ((hi - 0xD800) << 10) + (lo.wrapping_sub(0xDC00) & 0x3FF);
                s.push(char::from_u32(cp).unwrap_or('\u{FFFD}'));
            } else {
                s.push(char::from_u32(hi).unwrap_or('\u{FFFD}'));
            }
        }
        // unknown escape = the char itself (JS sloppy rule)
        other => s.push(other as char),
    }
    Ok(())
}

fn tpl_utf8(b: &[u8], a: usize, e: usize) -> Result<&str, JsError> {
    std::str::from_utf8(&b[a..e]).map_err(|_| err("bad utf-8 in template"))
}

/// One `\` escape inside a template: cooks into `s` (None-poison on
/// invalid escapes, which ES2018 allows on tagged templates) and advances
/// past the sequence. Returns whether the cooked value is now poisoned.
/// Unlike strings, templates accept `\u{...}` here.
fn tpl_escape(b: &[u8], i: &mut usize, s: &mut Option<String>) -> Result<bool, JsError> {
    let e = b
        .get(*i)
        .copied()
        .ok_or_else(|| err("unterminated template"))?;
    *i += 1;
    let mut bad = false;
    let mut push = |c: char| {
        if let Some(cooked) = s {
            cooked.push(c);
        }
    };
    match e {
        b'n' => push('\n'),
        b't' => push('\t'),
        b'r' => push('\r'),
        b'b' => push('\u{8}'),
        b'f' => push('\u{c}'),
        b'v' => push('\u{b}'),
        b'0' => push('\0'),
        b'\\' => push('\\'),
        b'\'' => push('\''),
        b'"' => push('"'),
        b'/' => push('/'),
        b'\n' => {} // line continuation cooks away
        b'\r' => {
            if b.get(*i) == Some(&b'\n') {
                *i += 1;
            }
        }
        b'x' => match hex2(b, *i) {
            Some(h) => {
                *i += 2;
                push(char::from_u32(h).unwrap_or('\u{FFFD}'));
            }
            None => bad = true, // raw keeps `\x`; rest lexes as literal text
        },
        b'u' => {
            if b.get(*i) == Some(&b'{') {
                match brace_hex(b, i) {
                    // well-formed but out of range poisons; consume it whole
                    Some(cp) if char::from_u32(cp).is_none() => bad = true,
                    Some(cp) => push(char::from_u32(cp).unwrap()),
                    // malformed: raw keeps text, rest lexes literally
                    None => bad = true,
                }
            } else if let Some(hi) = hexn(b, *i, 4) {
                *i += 4;
                if (0xD800..0xDC00).contains(&hi)
                    && b.get(*i) == Some(&b'\\')
                    && b.get(*i + 1) == Some(&b'u')
                    && hexn(b, *i + 2, 4)
                        .is_some_and(|lo| (0xDC00..0xE000).contains(&lo))
                {
                    *i += 2;
                    let lo = hexn(b, *i, 4).unwrap_or(0xDC00);
                    *i += 4;
                    let cp = 0x10000 + ((hi - 0xD800) << 10) + (lo - 0xDC00);
                    push(char::from_u32(cp).unwrap_or('\u{FFFD}'));
                } else {
                    push(char::from_u32(hi).unwrap_or('\u{FFFD}'));
                }
            } else {
                bad = true;
            }
        }
        // unknown escape = the char itself (JS sloppy rule)
        other => push(other as char),
    }
    if bad {
        *s = None;
    }
    Ok(bad)
}

/// Two hex digits at `o`, or None when absent/invalid (no error: the
/// caller poisons cooked instead of failing the lex).
fn hex2(b: &[u8], o: usize) -> Option<u32> {
    hexn(b, o, 2)
}

fn hexn(b: &[u8], o: usize, n: usize) -> Option<u32> {
    let w = std::str::from_utf8(b.get(o..o + n)?).ok()?;
    if !w.bytes().all(|c| c.is_ascii_hexdigit()) {
        return None;
    }
    u32::from_str_radix(w, 16).ok()
}

/// `\u{...}` body after the backslash-u was consumed and `{` peeked:
/// consumes through `}` on success, leaves `i` past `u` on failure.
fn brace_hex(b: &[u8], i: &mut usize) -> Option<u32> {
    let mut j = *i + 1;
    let h0 = j;
    while b.get(j).is_some_and(|c| c.is_ascii_hexdigit()) {
        j += 1;
    }
    if j == h0 || b.get(j) != Some(&b'}') {
        return None;
    }
    let cp = u32::from_str_radix(std::str::from_utf8(b.get(h0..j)?).ok()?, 16).ok()?;
    *i = j + 1;
    Some(cp)
}

/// Template body from after the backtick (or `}` closing `${`): cooked
/// text until the closing backtick (`expr: false`) or `${` (`expr: true`,
/// pushing a substitution context). Newlines normalize to `\n` in both
/// cooked and raw. Invalid escapes poison cooked (None) while raw keeps
/// the source text verbatim, per ES2018 tagged-template rules.
fn tpl_chunk(b: &[u8], i: &mut usize, braces: &mut Vec<bool>, head: bool) -> Result<Tok, JsError> {
    let mut cooked: Option<String> = Some(String::new());
    let mut raw = String::new();
    let mut chunk = *i;
    // Literal spans hold no backslash/CR (handled below), so the same
    // slice feeds both cooked and raw verbatim.
    let flush = |cooked: &mut Option<String>,
                     raw: &mut String,
                     from: usize,
                     e: usize|
     -> Result<(), JsError> {
        let lit = tpl_utf8(b, from, e)?;
        if let Some(c) = cooked {
            c.push_str(lit);
        }
        raw.push_str(lit);
        Ok(())
    };
    loop {
        match b.get(*i).copied() {
            None => return Err(err("unterminated template")),
            Some(b'`') => {
                flush(&mut cooked, &mut raw, chunk, *i)?;
                *i += 1;
                return Ok(Tok::Tpl {
                    cooked,
                    raw,
                    expr: false,
                    head,
                });
            }
            Some(b'$') if b.get(*i + 1) == Some(&b'{') => {
                flush(&mut cooked, &mut raw, chunk, *i)?;
                *i += 2;
                braces.push(true);
                return Ok(Tok::Tpl {
                    cooked,
                    raw,
                    expr: true,
                    head,
                });
            }
            Some(b'\\') => {
                flush(&mut cooked, &mut raw, chunk, *i)?;
                let es = *i;
                *i += 1;
                tpl_escape(b, &mut *i, &mut cooked)?;
                // raw keeps the escape verbatim (line continuations
                // normalize CRLF/CR to LF like other line endings)
                let text = tpl_utf8(b, es, *i)?;
                if text.contains('\r') {
                    raw.push_str(&text.replace("\r\n", "\n").replace('\r', "\n"));
                } else {
                    raw.push_str(text);
                }
                chunk = *i;
            }
            Some(b'\n') | Some(b'\r') => {
                flush(&mut cooked, &mut raw, chunk, *i)?;
                if b[*i] == b'\r' && b.get(*i + 1) == Some(&b'\n') {
                    *i += 1;
                }
                *i += 1;
                if let Some(c) = cooked.as_mut() {
                    c.push('\n');
                }
                raw.push('\n');
                chunk = *i;
            }
            Some(_) => *i += 1,
        }
    }
}

fn word(src: &str, b: &[u8], i: &mut usize) -> Tok {
    // Fast path: no backslash, slice straight out of the source.
    let s = *i;
    while *i < b.len() && is_ident(b[*i]) {
        *i += 1;
    }
    if b.get(*i) != Some(&b'\\') {
        let w = &src[s..*i];
        return match KWS.iter().copied().find(|k| *k == w) {
            Some(k) => Tok::Kw(k),
            None => Tok::Ident(w.to_string()),
        };
    }
    // Slow path: `\uXXXX` / `\u{...}` escapes inside the identifier
    // (`n.al\u00edcuota`). An escaped word is never a keyword per spec.
    let mut w = src[s..*i].to_string();
    loop {
        if b.get(*i) == Some(&b'\\') && b.get(*i + 1) == Some(&b'u') {
            *i += 2;
            let cp = if b.get(*i) == Some(&b'{') {
                *i += 1;
                let h0 = *i;
                while b.get(*i).is_some_and(|c| c.is_ascii_hexdigit()) {
                    *i += 1;
                }
                let h = u32::from_str_radix(&src[h0..*i], 16).unwrap_or(0xFFFD);
                if b.get(*i) != Some(&b'}') {
                    return Tok::Ident(w);
                }
                *i += 1;
                h
            } else {
                let h0 = *i;
                *i += 4;
                u32::from_str_radix(src.get(h0..*i).unwrap_or(""), 16).unwrap_or(0xFFFD)
            };
            w.push(char::from_u32(cp).unwrap_or('\u{FFFD}'));
        } else if *i < b.len() && is_ident(b[*i]) {
            w.push(b[*i] as char);
            *i += 1;
        } else {
            break;
        }
    }
    Tok::Ident(w)
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
/// comment). Returns the Regex token. In JS `]` always closes a class
/// (`[]` is the empty class, unlike most flavors where `[]]` holds a
/// literal bracket).
fn regex(src: &str, i: &mut usize) -> Result<Tok, JsError> {
    let b = src.as_bytes();
    let start = *i + 1;
    *i += 1;
    let mut in_class = false;
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
                    Some(_) => *i += 1,
                }
            }
            b'[' if !in_class => {
                in_class = true;
                *i += 1;
            }
            b']' if in_class => {
                in_class = false;
                *i += 1;
            }
            b'/' if !in_class => break,
            _ => *i += 1,
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
    fn template_chunks() {
        match tt("`a${b}c`").as_slice() {
            [Tok::Tpl {
                cooked: h,
                raw: hr,
                expr: true,
                head: true,
            }, Tok::Ident(b), Tok::Tpl {
                cooked: t,
                raw: tr,
                expr: false,
                head: false,
            }] => {
                assert_eq!((h.as_deref(), b.as_str(), t.as_deref()), (Some("a"), "b", Some("c")));
                assert_eq!((hr.as_str(), tr.as_str()), ("a", "c"));
            }
            t => panic!("{t:?}"),
        }
        // `${` in plain code is `$`-ident plus a block brace, not a template.
        assert_eq!(
            tt("a${b}"),
            vec![
                Tok::Ident("a$".into()),
                Tok::P("{"),
                Tok::Ident("b".into()),
                Tok::P("}"),
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
