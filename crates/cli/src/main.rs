use std::fmt::Write as _;
use std::time::Instant;

use vigia_dom::Dom;
use vigia_session::CookieJar;
use vigia_snapshot::snapshot;

#[global_allocator]
static ALLOC: vigia_mem::CountingAlloc = vigia_mem::CountingAlloc;

const USAGE: &str = "vigia - AI-native browser runtime

  vigia snap <url>                       fetch + parse + semantic snapshot
  vigia fetch <url>                      raw response body
  vigia dom <url>                        parsed DOM stats
  vigia extract <url> <css>              elements matching a CSS selector
  vigia click <url> <#n>                 follow snapshot ref (link/submit)
  vigia submit <url> [-f css] -d k=v..   fill + submit a form (login flows)
  vigia json <url> [a.b.0]               embedded JSON (__NEXT_DATA__, ld+json)
  vigia js <file.js> | -e \"<code>\"     run JavaScript (own interpreter)
  vigia run <file.vig> [--audit log.jsonl]  multi-step script + audit trail
                        [--tab name ...] [-D KEY=VAL | --var KEY=VAL]

  --profile <name>                       persistent cookie jar (~/.vigia/profiles)
  --js                                   run page <script>s before reading the DOM

Own HTTP/1.1 + URL parser + inflate + HTML parser + arena DOM.
Metrics on stderr: bytes in/out, ~tokens, ms per phase, heap peak, RSS peak.
";

fn est_tokens(bytes: usize) -> usize {
    bytes / 4
}

fn fmt_bytes(n: usize) -> String {
    if n >= 1024 * 1024 {
        format!("{:.1} MB", n as f64 / (1024.0 * 1024.0))
    } else if n >= 1024 {
        format!("{:.1} KB", n as f64 / 1024.0)
    } else {
        format!("{n} B")
    }
}

fn fmt_num(n: usize) -> String {
    let s = n.to_string();
    let mut out = String::new();
    for (i, c) in s.chars().enumerate() {
        if i > 0 && (s.len() - i) % 3 == 0 {
            out.push(',');
        }
        out.push(c);
    }
    out
}

fn fmt_ms(d: std::time::Duration) -> String {
    format!("{:.0}ms", d.as_secs_f64() * 1000.0)
}

fn report(extra: &str) {
    let mut line = String::from("[metrics]");
    if !extra.is_empty() {
        let _ = write!(line, " {extra}");
    }
    let _ = write!(line, " | heap peak {}", fmt_bytes(vigia_mem::peak_bytes()));
    if let Some(rss) = vigia_mem::rss_peak_bytes() {
        let _ = write!(line, " | rss peak {}", fmt_bytes(rss));
    }
    eprintln!("{line}");
}

fn fail(msg: impl std::fmt::Display) -> ! {
    eprintln!("{msg}");
    std::process::exit(2)
}

fn fetch_page(url: &str, jar: &mut CookieJar) -> vigia_net::Response {
    match vigia_net::fetch(url, jar) {
        Ok(r) => r,
        Err(e) => fail(format!("fetch failed: {e}")),
    }
}

fn report_fetch(res: &vigia_net::Response) {
    let t = &res.timings;
    eprintln!(
        "status {} | {} wire -> {} body | {} redirects | connect {} tls {} ttfb {} total {}",
        res.status,
        fmt_bytes(res.wire_bytes),
        fmt_bytes(res.body.len()),
        res.redirects,
        fmt_ms(t.connect),
        fmt_ms(t.tls),
        fmt_ms(t.ttfb),
        fmt_ms(t.total),
    );
}

/// Parse + optional script run. The jar passes through the interp so page
/// fetch() calls share cookies. Third return is a navigation a script's
/// click() asked for (v1 bridge) - the caller decides whether to follow.
fn parse_dom(
    res: &vigia_net::Response,
    js: bool,
    jar: &mut CookieJar,
) -> (Dom, std::time::Duration, Option<String>) {
    let t0 = Instant::now();
    let mut dom = Dom::new();
    vigia_html::parse(&res.text(), &mut dom);
    let mut nav = None;
    if js {
        let mut it = vigia_js::Interp::new();
        let out = it.run_scripts(
            dom,
            Some(vigia_js::NetCtx {
                base: res.final_url.clone(),
                jar: std::mem::take(jar),
            }),
        );
        dom = out.dom;
        nav = out.pending_nav;
        if let Some(j) = out.jar {
            *jar = j;
        }
        for e in out.errors {
            eprintln!("warn: js: {e}");
        }
    }
    (dom, t0.elapsed(), nav)
}

fn profile_path(name: &str) -> Option<std::path::PathBuf> {
    if name.is_empty() || !name.chars().all(|c| c.is_ascii_alphanumeric() || matches!(c, '-' | '_')) {
        return None;
    }
    let home = std::env::var_os("HOME")?;
    Some(std::path::PathBuf::from(home).join(".vigia/profiles").join(format!("{name}.jar")))
}

/// One audit entry as a JSONL line; `tab` adds the parallel-tab field.
fn audit_line(e: &vigia_run::AuditEntry, tab: Option<&str>) -> String {
    let mut f = vec![
        ("line".into(), vigia_json::Json::Num(e.line as f64)),
        ("op".into(), vigia_json::Json::Str(e.op.into())),
        ("arg".into(), vigia_json::Json::Str(e.arg.clone())),
    ];
    if let Some(t) = tab {
        f.push(("tab".into(), vigia_json::Json::Str(t.into())));
    }
    f.push(("status".into(), vigia_json::Json::Num(e.status as f64)));
    f.push((
        "ms".into(),
        vigia_json::Json::Num((e.ms * 1000.0).round() / 1000.0),
    ));
    f.push(("ok".into(), vigia_json::Json::Bool(e.ok)));
    vigia_json::Json::Obj(f).to_string()
}

fn write_audit(path: &str, text: &str) {
    if let Err(e) = std::fs::write(path, text) {
        eprintln!("warn: audit write failed: {e}");
    }
}

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();

    // --profile <name> anywhere in argv: load jar, save at exit.
    let mut jar_path = None;
    if let Some(i) = args.iter().position(|a| a == "--profile") {
        args.remove(i);
        match args.get(i).cloned() {
            Some(name) => {
                args.remove(i);
                jar_path = Some(profile_path(&name).unwrap_or_else(|| fail("bad profile name")));
            }
            None => fail("--profile needs a name"),
        }
    }

    // --js anywhere: run page scripts after every parse.
    let js = if let Some(i) = args.iter().position(|a| a == "--js") {
        args.remove(i);
        true
    } else {
        false
    };

    if args.len() < 2 {
        eprint!("{USAGE}");
        std::process::exit(1);
    }
    let has_tab = args.iter().any(|a| a == "--tab");
    let cmd = args.remove(0);
    let url = args.remove(0);
    if has_tab && cmd != "run" {
        fail("--tab only works with run");
    }

    let mut jar = jar_path
        .as_ref()
        .map(|p| CookieJar::load(p))
        .unwrap_or_default();

    match cmd.as_str() {
        "fetch" => {
            let res = fetch_page(&url, &mut jar);
            report_fetch(&res);
            print!("{}", res.text());
            report(&format!("~{} tokens", fmt_num(est_tokens(res.body.len()))));
        }
        "snap" | "dom" => {
            let mut res = fetch_page(&url, &mut jar);
            report_fetch(&res);
            let (mut dom, mut parse_ms, nav) = parse_dom(&res, js, &mut jar);
            if let Some(u) = nav {
                // v1 navigation bridge: a script's click() asked for a
                // page - follow it once, no chains.
                res = fetch_page(&u, &mut jar);
                report_fetch(&res);
                let (d, ms, _) = parse_dom(&res, js, &mut jar);
                dom = d;
                parse_ms += ms;
            }
            if cmd == "dom" {
                println!(
                    "{} nodes, {} interned strings, {} cookies",
                    dom.nodes.len(),
                    dom.interner.len(),
                    jar.len()
                );
                report(&format!("parse {}", fmt_ms(parse_ms)));
            } else {
                let t1 = Instant::now();
                let snap = snapshot(&dom);
                let snap_ms = t1.elapsed();
                print!("{snap}");
                report(&format!(
                    "parse {} snap {} | nodes {} | ~{} -> ~{} tokens",
                    fmt_ms(parse_ms),
                    fmt_ms(snap_ms),
                    fmt_num(dom.nodes.len()),
                    fmt_num(est_tokens(res.body.len())),
                    fmt_num(est_tokens(snap.len())),
                ));
            }
        }
        "extract" => {
            let sel = args.first().cloned().unwrap_or_else(|| {
                eprint!("{USAGE}");
                std::process::exit(1)
            });
            let res = fetch_page(&url, &mut jar);
            report_fetch(&res);
            let (dom, parse_ms, _) = parse_dom(&res, js, &mut jar);
            let hits = match vigia_css::query(&dom, &sel) {
                Ok(h) => h,
                Err(e) => fail(format!("{e}")),
            };
            for id in &hits {
                let tag = dom.tag_name(*id).unwrap_or("?");
                let text = vigia_actions::text_content(&dom, *id);
                let text = text.chars().take(120).collect::<String>();
                println!("- {tag} '{text}'");
            }
            report(&format!(
                "parse {} | {} matches",
                fmt_ms(parse_ms),
                hits.len()
            ));
        }
        "click" => {
            let ref_n: usize = args
                .first()
                .and_then(|s| s.trim_start_matches('#').parse().ok())
                .unwrap_or_else(|| fail("click needs a ref: vigia click <url> <#n>"));
            let res = fetch_page(&url, &mut jar);
            report_fetch(&res);
            let (dom, _, _) = parse_dom(&res, js, &mut jar);
            let res2 = match vigia_actions::click(&dom, &res.final_url, ref_n, &[], &mut jar) {
                Ok(r) => r,
                Err(e) => fail(format!("click failed: {e}")),
            };
            report_fetch(&res2);
            let (dom2, _, _) = parse_dom(&res2, js, &mut jar);
            print!("{}", snapshot(&dom2));
            report("");
        }
        "submit" => {
            let mut overrides = Vec::new();
            let mut form_sel = None;
            let mut i = 0;
            while i < args.len() {
                match args[i].as_str() {
                    "-d" | "--data" if i + 1 < args.len() => {
                        let kv = &args[i + 1];
                        match kv.split_once('=') {
                            Some((k, v)) => overrides.push((k.to_string(), v.to_string())),
                            None => fail("bad -d, want k=v"),
                        }
                        i += 2;
                    }
                    "-f" | "--form" if i + 1 < args.len() => {
                        form_sel = Some(args[i + 1].clone());
                        i += 2;
                    }
                    _ => fail(format!("bad arg: {}", args[i])),
                }
            }
            let res = fetch_page(&url, &mut jar);
            report_fetch(&res);
            let (dom, _, _) = parse_dom(&res, js, &mut jar);
            let res2 = match vigia_actions::submit_form(
                &dom,
                &res.final_url,
                form_sel.as_deref(),
                &overrides,
                &mut jar,
            ) {
                Ok(r) => r,
                Err(e) => fail(format!("submit failed: {e}")),
            };
            report_fetch(&res2);
            let (dom2, _, _) = parse_dom(&res2, js, &mut jar);
            print!("{}", snapshot(&dom2));
            report("");
        }
        "json" => {
            let path = args.first().map(|s| s.as_str());
            let res = fetch_page(&url, &mut jar);
            report_fetch(&res);
            let (dom, _, _) = parse_dom(&res, js, &mut jar);
            let mut found = 0;
            let mut seen = Vec::new();
            for sel in [
                "script#__NEXT_DATA__",
                "script[type=\"application/ld+json\"]",
                "script[type=\"application/json\"]",
            ] {
                let hits = vigia_css::query(&dom, sel).unwrap_or_default();
                for id in hits {
                    if seen.contains(&id) {
                        continue;
                    }
                    seen.push(id);
                    let raw = vigia_actions::text_content(&dom, id);
                    match vigia_json::Json::parse(raw.trim()) {
                        Ok(v) => {
                            found += 1;
                            let out = match path {
                                Some(p) => v.get(p).map(|x| x.to_string()),
                                None => Some(v.to_string()),
                            };
                            match out {
                                Some(s) => println!("== {sel}\n{s}"),
                                None => println!("== {sel}\n(no match for path)"),
                            }
                        }
                        Err(e) => eprintln!("warn: {sel}: {e}"),
                    }
                }
            }
            if found == 0 {
                eprintln!("no embedded JSON blocks found");
            }
            report(&format!("{} blocks", found));
        }
        "js" => {
            // url-position arg is the .js path, or -e for inline code.
            let src = if url == "-e" {
                match args.first() {
                    Some(s) => s.clone(),
                    None => fail("vigia js -e needs a code string"),
                }
            } else {
                std::fs::read_to_string(&url)
                    .unwrap_or_else(|e| fail(format!("cannot read {url}: {e}")))
            };
            let mut it = vigia_js::Interp::new();
            let r = it.run(&src);
            print!("{}", it.output());
            match r {
                Ok(v) => {
                    if v != vigia_js::Value::Undef {
                        println!("{}", it.inspect(v));
                    }
                    let (objs, strs) = it.heap.stats();
                    report(&format!("objs {objs} strs {strs}"));
                }
                Err(e) => fail(format!("js: {e}")),
            }
        }
        "run" => {
            // The url-position arg is the .vig script path here.
            let mut audit_path = None;
            let mut tab_names: Vec<String> = Vec::new();
            let mut raw_vars: Vec<String> = Vec::new();
            let mut i = 0;
            while i < args.len() {
                match args[i].as_str() {
                    "--audit" if i + 1 < args.len() => {
                        audit_path = Some(args[i + 1].clone());
                        i += 2;
                    }
                    "--tab" if i + 1 < args.len() => {
                        let name = args[i + 1].clone();
                        if profile_path(&name).is_none() {
                            fail("bad tab name");
                        }
                        if tab_names.contains(&name) {
                            fail(format!("duplicate tab: {name}"));
                        }
                        tab_names.push(name);
                        i += 2;
                    }
                    "-D" | "--var" if i + 1 < args.len() => {
                        raw_vars.push(args[i + 1].clone());
                        i += 2;
                    }
                    _ => fail(format!("bad arg: {}", args[i])),
                }
            }
            if tab_names.is_empty() {
                if !raw_vars.is_empty() {
                    fail("-D/--var need at least one --tab");
                }
            } else if jar_path.is_some() {
                // The tab name IS the profile; both jars would fight.
                fail("--profile does not combine with --tab");
            }
            let src = std::fs::read_to_string(&url)
                .unwrap_or_else(|e| fail(format!("cannot read {url}: {e}")));
            let stmts = match vigia_run::parse_script(&src) {
                Ok(s) => s,
                Err(e) => fail(format!("run failed at line {}: {}", e.0, e.1)),
            };
            if !tab_names.is_empty() {
                // Parallel tabs: same script, one thread each with its own
                // profile jar.
                // `alice.USER=x` scopes USER to tab alice (split on the
                // first '.' that names a declared tab); bare `USER=x`
                // reaches every tab. Scoped vars beat global ones.
                let vars: Vec<(Option<String>, String, String)> = raw_vars
                    .iter()
                    .map(|kv| {
                        let (k, v) = kv
                            .split_once('=')
                            .unwrap_or_else(|| fail("bad -D, want KEY=VAL"));
                        match k.split_once('.') {
                            Some((t, kk)) if tab_names.iter().any(|n| n == t) => {
                                (Some(t.to_string()), kk.to_string(), v.to_string())
                            }
                            _ => (None, k.to_string(), v.to_string()),
                        }
                    })
                    .collect();
                let specs: Vec<vigia_run::TabSpec> = tab_names
                    .iter()
                    .map(|n| {
                        let mut v: Vec<(String, String)> = vars
                            .iter()
                            .filter(|(t, _, _)| t.as_deref() == Some(n.as_str()))
                            .map(|(_, k, v)| (k.clone(), v.clone()))
                            .collect();
                        v.extend(
                            vars.iter()
                                .filter(|(t, _, _)| t.is_none())
                                .map(|(_, k, v)| (k.clone(), v.clone())),
                        );
                        vigia_run::TabSpec {
                            name: n.clone(),
                            vars: v,
                            jar_path: profile_path(n),
                        }
                    })
                    .collect();
                let outcomes = vigia_run::run_tabs(&stmts, &specs, js);
                let multi = outcomes.len() > 1;
                for o in &outcomes {
                    if multi {
                        println!("== tab {}", o.name);
                    }
                    print!("{}", o.out);
                    if !o.out.is_empty() && !o.out.ends_with('\n') {
                        println!();
                    }
                }
                if let Some(p) = &audit_path {
                    let mut text = String::new();
                    for o in &outcomes {
                        for e in &o.audit {
                            let _ = writeln!(text, "{}", audit_line(e, Some(&o.name)));
                        }
                    }
                    write_audit(p, &text);
                }
                for o in &outcomes {
                    if let Err(e) = &o.result {
                        eprintln!("tab {} failed at line {}: {}", o.name, e.0, e.1);
                    }
                }
                let n_ok = outcomes.iter().filter(|o| o.result.is_ok()).count();
                eprintln!("tabs: {} ok, {} failed", n_ok, outcomes.len() - n_ok);
                if n_ok != outcomes.len() {
                    std::process::exit(2);
                }
                report(&format!(
                    "{} steps",
                    outcomes.iter().map(|o| o.audit.len()).sum::<usize>()
                ));
                return;
            }
            let mut audit = Vec::new();
            let mut emit = |s: &str| {
                print!("{s}");
                if !s.ends_with('\n') {
                    println!();
                }
            };
            let result = vigia_run::run_with(&stmts, &mut jar, &mut audit, &mut emit, js);
            if let Some(p) = &audit_path {
                let mut text = String::new();
                for e in &audit {
                    let _ = writeln!(text, "{}", audit_line(e, None));
                }
                write_audit(p, &text);
            }
            match result {
                Ok(()) => report(&format!("{} steps", audit.len())),
                Err(e) => fail(format!("run failed at line {}: {}", e.0, e.1)),
            }
        }
        _ => {
            eprint!("{USAGE}");
            std::process::exit(1);
        }
    }

    if let Some(p) = &jar_path {
        if let Err(e) = jar.save(p) {
            eprintln!("warn: profile save failed: {e}");
        }
    }
}
