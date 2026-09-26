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

  --profile <name>                       persistent cookie jar (~/.vigia/profiles)

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

fn parse_dom(res: &vigia_net::Response) -> (Dom, std::time::Duration) {
    let t0 = Instant::now();
    let mut dom = Dom::new();
    vigia_html::parse(&res.text(), &mut dom);
    (dom, t0.elapsed())
}

fn profile_path(name: &str) -> Option<std::path::PathBuf> {
    if name.is_empty() || !name.chars().all(|c| c.is_ascii_alphanumeric() || matches!(c, '-' | '_')) {
        return None;
    }
    let home = std::env::var_os("HOME")?;
    Some(std::path::PathBuf::from(home).join(".vigia/profiles").join(format!("{name}.jar")))
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

    if args.len() < 2 {
        eprint!("{USAGE}");
        std::process::exit(1);
    }
    let cmd = args.remove(0);
    let url = args.remove(0);

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
            let res = fetch_page(&url, &mut jar);
            report_fetch(&res);
            let (dom, parse_ms) = parse_dom(&res);
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
            let (dom, parse_ms) = parse_dom(&res);
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
            let (dom, _) = parse_dom(&res);
            let res2 = match vigia_actions::click(&dom, &res.final_url, ref_n, &[], &mut jar) {
                Ok(r) => r,
                Err(e) => fail(format!("click failed: {e}")),
            };
            report_fetch(&res2);
            let (dom2, _) = parse_dom(&res2);
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
            let (dom, _) = parse_dom(&res);
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
            let (dom2, _) = parse_dom(&res2);
            print!("{}", snapshot(&dom2));
            report("");
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
