//! `.vig` script runner: a sequence of agent ops executed in one process,
//! sharing the cookie jar and the live DOM. `snap` loads a page and emits
//! its snapshot; `click`/`submit` navigate and reparse; `fill` mutates a
//! form control in place; `extract`/`json`/`expect` observe.
//!
//! Grammar: one op per line, whitespace-separated tokens, `"..."` quoted
//! strings (with `\"`). Blank lines are skipped; a line whose first
//! non-whitespace char is `#` followed by a non-digit is a comment (so
//! `click #3` is never a comment).

use std::time::Instant;

use vigia_dom::Dom;
use vigia_session::CookieJar;
use vigia_url::Url;

#[derive(Debug, Clone, PartialEq)]
pub enum Op {
    Snap(String),
    Click(usize),
    Fill(usize, String),
    Submit {
        form: Option<String>,
        data: Vec<(String, String)>,
    },
    Extract(String),
    Json(Option<String>),
    Expect(String),
}

impl Op {
    pub fn name(&self) -> &'static str {
        match self {
            Self::Snap(_) => "snap",
            Self::Click(_) => "click",
            Self::Fill(..) => "fill",
            Self::Submit { .. } => "submit",
            Self::Extract(_) => "extract",
            Self::Json(_) => "json",
            Self::Expect(_) => "expect",
        }
    }

    /// Operand summary for the audit trail.
    pub fn arg(&self) -> String {
        match self {
            Self::Snap(u) => u.clone(),
            Self::Click(n) => format!("#{n}"),
            Self::Fill(n, v) => format!("#{n} {v}"),
            Self::Submit { form, data } => {
                let mut parts: Vec<String> = Vec::new();
                if let Some(f) = form {
                    parts.push(format!("-f {f}"));
                }
                for (k, v) in data {
                    parts.push(format!("-d {k}={v}"));
                }
                parts.join(" ")
            }
            Self::Extract(sel) => sel.clone(),
            Self::Json(path) => path.clone().unwrap_or_default(),
            Self::Expect(sub) => sub.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Stmt {
    pub op: Op,
    /// 1-based source line, for error messages and the audit trail.
    pub line: usize,
}

/// Line number + message. Parse errors carry the offending line; runtime
/// errors carry the stmt's line.
#[derive(Debug)]
pub struct RunError(pub usize, pub String);

impl std::fmt::Display for RunError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "line {}: {}", self.0, self.1)
    }
}
impl std::error::Error for RunError {}

pub struct AuditEntry {
    pub line: usize,
    pub op: &'static str,
    pub arg: String,
    /// HTTP status of the current page (0 before the first snap).
    pub status: u16,
    pub ms: f64,
    pub ok: bool,
}

/// Whitespace tokenizer with `"..."` quoting; `\` escapes the next char.
fn tokenize(line: &str) -> Result<Vec<String>, String> {
    let mut toks = Vec::new();
    let mut rest = line;
    loop {
        rest = rest.trim_start();
        if rest.is_empty() {
            break;
        }
        if let Some(q) = rest.strip_prefix('"') {
            let mut s = String::new();
            let mut end = None;
            let mut it = q.char_indices();
            while let Some((i, c)) = it.next() {
                match c {
                    '"' => {
                        end = Some(i + 1);
                        break;
                    }
                    '\\' => match it.next() {
                        Some((_, e)) => s.push(e),
                        None => return Err("unterminated quote".into()),
                    },
                    c => s.push(c),
                }
            }
            let Some(end) = end else {
                return Err("unterminated quote".into());
            };
            toks.push(s);
            rest = &q[end..];
        } else {
            let end = rest.find(char::is_whitespace).unwrap_or(rest.len());
            toks.push(rest[..end].to_string());
            rest = &rest[end..];
        }
    }
    Ok(toks)
}

fn parse_ref(tok: &str, line: usize) -> Result<usize, RunError> {
    tok.trim_start_matches('#')
        .parse()
        .map_err(|_| RunError(line, format!("bad ref: {tok}")))
}

/// The one operand of a fixed-arity op.
fn one_arg(toks: &[String], line: usize, op: &str) -> Result<String, RunError> {
    if toks.len() != 2 {
        return Err(RunError(line, format!("{op} takes one argument")));
    }
    Ok(toks[1].clone())
}

pub fn parse_script(src: &str) -> Result<Vec<Stmt>, RunError> {
    let mut stmts = Vec::new();
    for (i, raw) in src.lines().enumerate() {
        let line = i + 1;
        let t = raw.trim_start();
        if t.is_empty() {
            continue;
        }
        if t.starts_with('#') && !t.as_bytes().get(1).is_some_and(u8::is_ascii_digit) {
            continue; // comment: '#' + non-digit; '#3' falls through to an op error
        }
        let toks = tokenize(t).map_err(|m| RunError(line, m))?;
        let op = match toks[0].as_str() {
            "snap" => Op::Snap(one_arg(&toks, line, "snap")?),
            "click" => Op::Click(parse_ref(&one_arg(&toks, line, "click")?, line)?),
            "fill" => {
                if toks.len() != 3 {
                    return Err(RunError(line, "fill takes 2 args: #n value".into()));
                }
                Op::Fill(parse_ref(&toks[1], line)?, toks[2].clone())
            }
            "submit" => {
                let mut form = None;
                let mut data = Vec::new();
                let mut j = 1;
                while j < toks.len() {
                    match toks[j].as_str() {
                        "-f" | "--form" if j + 1 < toks.len() => {
                            form = Some(toks[j + 1].clone());
                            j += 2;
                        }
                        "-d" | "--data" if j + 1 < toks.len() => {
                            let Some((k, v)) = toks[j + 1].split_once('=') else {
                                return Err(RunError(line, "bad -d, want k=v".into()));
                            };
                            data.push((k.to_string(), v.to_string()));
                            j += 2;
                        }
                        other => {
                            return Err(RunError(line, format!("bad submit arg: {other}")));
                        }
                    }
                }
                Op::Submit { form, data }
            }
            "extract" => Op::Extract(one_arg(&toks, line, "extract")?),
            "json" => match toks.len() {
                1 => Op::Json(None),
                2 => Op::Json(Some(toks[1].clone())),
                _ => return Err(RunError(line, "json takes at most one argument".into())),
            },
            "expect" => Op::Expect(one_arg(&toks, line, "expect")?),
            other => return Err(RunError(line, format!("unknown op: {other}"))),
        };
        stmts.push(Stmt { op, line });
    }
    Ok(stmts)
}

/// Live page state: the DOM ops act on plus where it came from.
struct Page {
    dom: Dom,
    url: Url,
    status: u16,
}

fn load(res: vigia_net::Response) -> Page {
    let mut dom = Dom::new();
    vigia_html::parse(&res.text(), &mut dom);
    Page {
        dom,
        url: res.final_url,
        status: res.status,
    }
}

const NO_PAGE: &str = "no page yet (first op must be snap)";

const JSON_SELECTORS: &[&str] = &[
    "script#__NEXT_DATA__",
    "script[type=\"application/ld+json\"]",
    "script[type=\"application/json\"]",
];

fn exec(
    stmt: &Stmt,
    page: &mut Option<Page>,
    jar: &mut CookieJar,
    out: &mut dyn FnMut(&str),
) -> Result<(), String> {
    match &stmt.op {
        Op::Snap(url) => {
            let res = vigia_net::fetch(url, jar).map_err(|e| format!("fetch failed: {e}"))?;
            let p = load(res);
            out(&vigia_snapshot::snapshot(&p.dom));
            *page = Some(p);
        }
        Op::Click(n) => {
            let p = page.as_ref().ok_or(NO_PAGE)?;
            let res = vigia_actions::click(&p.dom, &p.url, *n, &[], jar)
                .map_err(|e| format!("click failed: {e}"))?;
            *page = Some(load(res));
        }
        Op::Submit { form, data } => {
            let p = page.as_ref().ok_or(NO_PAGE)?;
            let res = vigia_actions::submit_form(&p.dom, &p.url, form.as_deref(), data, jar)
                .map_err(|e| format!("submit failed: {e}"))?;
            *page = Some(load(res));
        }
        Op::Fill(n, value) => {
            let p = page.as_mut().ok_or(NO_PAGE)?;
            vigia_actions::fill(&mut p.dom, *n, value).map_err(|e| e.to_string())?;
        }
        Op::Extract(sel) => {
            let p = page.as_ref().ok_or(NO_PAGE)?;
            let hits = vigia_css::query(&p.dom, sel).map_err(|e| e.to_string())?;
            for id in hits {
                let tag = p.dom.tag_name(id).unwrap_or("?");
                let text = vigia_actions::text_content(&p.dom, id);
                let text: String = text.chars().take(120).collect();
                out(&format!("- {tag} '{text}'"));
            }
        }
        Op::Json(path) => {
            let p = page.as_ref().ok_or(NO_PAGE)?;
            let mut seen = Vec::new();
            for sel in JSON_SELECTORS {
                for id in vigia_css::query(&p.dom, sel).unwrap_or_default() {
                    if seen.contains(&id) {
                        continue;
                    }
                    seen.push(id);
                    let raw = vigia_actions::text_content(&p.dom, id);
                    match vigia_json::Json::parse(raw.trim()) {
                        Ok(v) => {
                            let body = match path {
                                Some(path) => v
                                    .get(path)
                                    .map(|x| x.to_string())
                                    .unwrap_or_else(|| "(no match for path)".into()),
                                None => v.to_string(),
                            };
                            out(&format!("== {sel}\n{body}"));
                        }
                        Err(e) => out(&format!("== {sel}\n(parse error: {e})")),
                    }
                }
            }
        }
        Op::Expect(sub) => {
            let p = page.as_ref().ok_or(NO_PAGE)?;
            if !vigia_snapshot::snapshot(&p.dom).contains(sub.as_str()) {
                return Err(format!("expect failed: '{sub}' not in snapshot"));
            }
        }
    }
    Ok(())
}

/// Execute `stmts` in order against a shared jar and live DOM. Emitted
/// text (snapshots, extract hits, json blocks) goes to `out`. Each executed
/// stmt appends one `AuditEntry` to `audit` - including the failed one -
/// then the first failure returns `Err`.
pub fn run(
    stmts: &[Stmt],
    jar: &mut CookieJar,
    audit: &mut Vec<AuditEntry>,
    out: &mut dyn FnMut(&str),
) -> Result<(), RunError> {
    let mut page = None;
    for stmt in stmts {
        let t0 = Instant::now();
        let r = exec(stmt, &mut page, jar, out);
        audit.push(AuditEntry {
            line: stmt.line,
            op: stmt.op.name(),
            arg: stmt.op.arg(),
            status: page.as_ref().map(|p| p.status).unwrap_or(0),
            ms: t0.elapsed().as_secs_f64() * 1000.0,
            ok: r.is_ok(),
        });
        if let Err(m) = r {
            return Err(RunError(stmt.line, m));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ops(src: &str) -> Vec<Op> {
        parse_script(src)
            .unwrap()
            .into_iter()
            .map(|s| s.op)
            .collect()
    }

    #[test]
    fn parses_ops() {
        let src = r#"
# a comment
   # indented comment
snap http://a.com/
click #3
click 4
fill #2 "hello world"
fill 2 bare
extract .item
extract "div > p.x"
json
json data.user.name
expect "found it"
expect bare
"#;
        let ops = ops(src);
        assert_eq!(
            ops,
            vec![
                Op::Snap("http://a.com/".into()),
                Op::Click(3),
                Op::Click(4),
                Op::Fill(2, "hello world".into()),
                Op::Fill(2, "bare".into()),
                Op::Extract(".item".into()),
                Op::Extract("div > p.x".into()),
                Op::Json(None),
                Op::Json(Some("data.user.name".into())),
                Op::Expect("found it".into()),
                Op::Expect("bare".into()),
            ]
        );
    }

    #[test]
    fn hash_digit_is_not_a_comment() {
        assert!(parse_script("#nope").unwrap().is_empty());
        assert!(parse_script("# trailing words").unwrap().is_empty());
        // '#3' is not a comment: it parses and fails as an unknown op.
        let e = parse_script("#3").unwrap_err();
        assert_eq!(e.0, 1);
        // While 'click #3' uses it as a ref.
        assert_eq!(ops("click #3"), vec![Op::Click(3)]);
    }

    #[test]
    fn quoted_escapes() {
        assert_eq!(
            ops(r#"expect "say \"hi\"""#),
            vec![Op::Expect("say \"hi\"".into())]
        );
        assert!(parse_script("expect \"unterminated").is_err());
    }

    #[test]
    fn submit_args() {
        assert_eq!(
            ops("submit"),
            vec![Op::Submit {
                form: None,
                data: vec![]
            }]
        );
        assert_eq!(
            ops(r#"submit -f #login -d user=a -d "pass=b c""#),
            vec![Op::Submit {
                form: Some("#login".into()),
                data: vec![("user".into(), "a".into()), ("pass".into(), "b c".into())],
            }]
        );
        assert!(parse_script("submit -d novalue").is_err());
        assert!(parse_script("submit -x").is_err());
        assert!(parse_script("submit -f").is_err());
    }

    #[test]
    fn arity_errors() {
        assert!(parse_script("snap").is_err());
        assert!(parse_script("snap a b").is_err());
        assert!(parse_script("fill #1").is_err());
        assert!(parse_script("click x").is_err());
        assert!(parse_script("bogus").is_err());
        // Error carries the source line.
        let e = parse_script("snap a\nsnap b\nbogus").unwrap_err();
        assert_eq!(e.0, 3);
    }

    #[test]
    fn ops_before_snap_fail() {
        let mut jar = CookieJar::new();
        let mut audit = Vec::new();
        let mut out = |_: &str| {};
        let stmts = parse_script("click #1\nexpect x").unwrap();
        let e = run(&stmts, &mut jar, &mut audit, &mut out).unwrap_err();
        assert_eq!(e.0, 1);
        assert_eq!(audit.len(), 1);
        assert!(!audit[0].ok);
        assert_eq!(audit[0].op, "click");
    }

    #[test]
    fn fill_updates_form_fields() {
        // The contract, end to end through the ops layer's numbering.
        let mut dom = Dom::new();
        let form = dom.element(dom.root(), "form", vec![]);
        dom.element(
            form,
            "input",
            vec![("name".into(), "u".into()), ("value".into(), "x".into())],
        );
        let ta = dom.element(form, "textarea", vec![("name".into(), "n".into())]);
        dom.text(ta, "initial");
        let sel = dom.element(form, "select", vec![("name".into(), "s".into())]);
        dom.element(sel, "option", vec![("value".into(), "a".into())]);
        dom.element(
            sel,
            "option",
            vec![("value".into(), "b".into()), ("selected".into(), "".into())],
        );
        dom.element(
            form,
            "input",
            vec![
                ("name".into(), "c".into()),
                ("type".into(), "checkbox".into()),
                ("value".into(), "1".into()),
            ],
        );
        // Refs: #1 input, #2 textarea, #3 select, #4 checkbox.
        vigia_actions::fill(&mut dom, 2, "filled").unwrap();
        vigia_actions::fill(&mut dom, 3, "a").unwrap();
        vigia_actions::fill(&mut dom, 4, "on").unwrap();
        let f = vigia_actions::form_fields(&dom, form);
        assert_eq!(
            f,
            vec![
                ("u".into(), "x".into()),
                ("n".into(), "filled".into()),
                ("s".into(), "a".into()),
                ("c".into(), "1".into()),
            ]
        );
    }
}
