use vigia_dom::Dom;
use vigia_session::CookieJar;
use vigia_snapshot::snapshot;

const USAGE: &str = "vigia — AI-native browser runtime

  vigia snap <url>    fetch + parse + agent snapshot to stdout
  vigia fetch <url>   raw response body to stdout
  vigia dom <url>     parsed DOM stats (nodes, interned strings)

Runs with no browser engine: vigia's own HTTP layer + HTML parser + arena DOM.
";

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
    eprintln!("status {} — {} bytes — {}", res.status, res.body.len(), res.final_url);

    match cmd.as_str() {
        "fetch" => print!("{}", res.body),
        "snap" | "dom" => {
            let mut dom = Dom::new();
            vigia_html::parse(&res.body, &mut dom);
            if cmd == "dom" {
                println!(
                    "{} nodes, {} interned strings, {} cookies",
                    dom.nodes.len(),
                    dom.interner.len(),
                    jar.len()
                );
            } else {
                print!("{}", snapshot(&dom));
            }
        }
        _ => {
            eprint!("{USAGE}");
            std::process::exit(1);
        }
    }
}
