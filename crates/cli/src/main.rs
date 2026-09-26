use std::fmt::Write as _;
use std::time::Instant;

use vigia_dom::Dom;
use vigia_session::CookieJar;
use vigia_snapshot::snapshot;

#[global_allocator]
static ALLOC: vigia_mem::CountingAlloc = vigia_mem::CountingAlloc;

const USAGE: &str = "vigia - AI-native browser runtime

  vigia snap <url>    fetch + parse + agent snapshot to stdout
  vigia fetch <url>   raw response body to stdout
  vigia dom <url>     parsed DOM stats (nodes, interned strings)

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
    let heap = vigia_mem::peak_bytes();
    let _ = write!(line, " | heap peak {}", fmt_bytes(heap));
    if let Some(rss) = vigia_mem::rss_peak_bytes() {
        let _ = write!(line, " | rss peak {}", fmt_bytes(rss));
    }
    eprintln!("{line}");
}

fn main() {
    let mut args = std::env::args().skip(1);
    let cmd = args.next().unwrap_or_else(|| {
        eprint!("{USAGE}");
        std::process::exit(1);
    });
    let url = args.next().unwrap_or_else(|| {
        eprint!("{USAGE}");
        std::process::exit(1);
    });

    let mut jar = CookieJar::new();
    let res = match vigia_net::fetch(&url, &mut jar) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("fetch failed: {e}");
            std::process::exit(2);
        }
    };
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

    match cmd.as_str() {
        "fetch" => {
            print!("{}", String::from_utf8_lossy(&res.body));
            report(&format!("~{} tokens", fmt_num(est_tokens(res.body.len()))));
        }
        "snap" | "dom" => {
            let t0 = Instant::now();
            let mut dom = Dom::new();
            vigia_html::parse(&String::from_utf8_lossy(&res.body), &mut dom);
            let parse_ms = t0.elapsed();
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
        _ => {
            eprint!("{USAGE}");
            std::process::exit(1);
        }
    }
}
