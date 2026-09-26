# vigia

An AI-native browser written from scratch in Rust. No Chromium, no WebKit, no borrowed engine. Built for agents that scrape, log in, and act on the web, measured on two targets.

- **Cost.** Tokens per observed page, bytes of RAM per session.
- **Human speed.** Fetch -> snapshot -> action under human reaction time. No multi-second screenshot loops.

## Why from scratch

Every "browser for AI" embeds Chromium: roughly 300 MB before the first request, a render pipeline scraping never uses, and a resource ceiling you do not control. vigia's premise:

- **No layout, no paint, no compositor.** Agents read the DOM, not pixels. Skipping render removes most of a browser's memory cost.
- **Own HTTP/1.1, own URL parser, own inflate, own HTML parser, own arena DOM, own JS interpreter.** The load is measurable per crate. `vigia-mem` counts every allocation.
- **Sessions without a browser.** An RFC 6265-correct cookie jar persists auth without a rendered page.
- **JavaScript is a bounded module.** `vigia-js` is our own interpreter: lexer, parser, tree-walk evaluator, arena values behind a hard cap. It never owns a render loop.

Scope honesty: a full-spec web engine is a Servo or Ladybird-scale project. vigia's scope is what agents need: fetch, parse, DOM, extract, act, record.

## Quickstart

```bash
cargo build --release

./target/release/vigia snap <url>                  # semantic snapshot with #n action refs
./target/release/vigia fetch <url>                 # raw response body
./target/release/vigia dom <url>                   # parse stats
./target/release/vigia extract <url> "td.price"    # CSS selector extraction
./target/release/vigia click <url> 3               # follow snapshot ref #3
./target/release/vigia submit <url> -d user=x -d pass=y  # form login
./target/release/vigia json <url> [a.b.0]          # embedded JSON (__NEXT_DATA__, ld+json)
./target/release/vigia js <file.js> | -e "<code>"  # run JavaScript (own interpreter)
./target/release/vigia run <file.vig> [--audit log.jsonl]  # multi-step script + audit trail

# persistent session (cookies on disk)
./target/release/vigia snap <url> --profile work
```

A `.vig` script is one op per line, executed in a single process with a shared session:

```
# login.vig
snap https://example.com/login
fill #1 myuser
fill #2 "my password"
click #3
expect "Dashboard"
extract li.item
```

Every command reports cost and latency on stderr:

```
status 200 | 341 B wire -> 236 B body | connect 0ms tls 0ms ttfb 1ms total 1ms
[metrics] parse 0ms snap 0ms | nodes 20 | ~59 -> ~70 tokens | heap peak 7.9 KB | rss peak 2.6 MB
```

## Benchmark: vigia vs lightpanda

The comparison target is [lightpanda](https://github.com/lightpanda-io/browser), the only other browser for agents built without a borrowed engine. `bench/` generates a deterministic corpus and measures wall time, peak RSS (wait4), and output size of the agent-facing dump (`vigia snap` vs `lightpanda fetch --dump semantic_tree_text`).

```
page             tool              ms   rss_mb    out_b  ~tokens rc
article.html     vigia            5.3      9.6    54815    13703  0
article.html     lightpanda     325.4     22.2   232208    58052  0
small.html       vigia            3.2      9.6      172       43  0
small.html       lightpanda     295.4     21.8      152       38  0
table.html       vigia           10.5      9.6   188537    47134  0
table.html       lightpanda     452.0     26.3   100008    25002  0
```

- **Speed.** vigia is ~40-90x faster. Lightpanda boots a JS runtime per page; vigia has nothing to boot.
- **Memory.** vigia uses ~2.3x less RSS (9.6 MB vs ~22 MB).
- **Tokens.** vigia wins on content-heavy pages (4x smaller on article) and carries `-> href` and `#n` refs that lightpanda's text dump omits. On link/table-heavy pages lightpanda is smaller precisely because it drops link targets, which then cost a second CDP call to navigate.

Reproduce: `python3 -m http.server 8899 -d bench/corpus &`, then `python3 bench/run.py`. Regenerate fixtures with `python3 bench/gen_corpus.py`.

## Crates

| Crate | Responsibility |
|---|---|
| `vigia-net` | HTTP/1.1 on `std::net`: chunked, redirects, gzip. 8 MiB wire cap, per-phase timings |
| `vigia-url` | URL parser and relative resolution: dot-segments, percent-encoding |
| `vigia-inflate` | DEFLATE/zlib/gzip decoder (RFC 1950-1952), output cap against zip bombs |
| `vigia-tls` | TLS boundary. Opaque `TlsStream`, the one declared exception (rustls) |
| `vigia-html` | Tokenizer and tree builder, one streaming pass, no event buffer |
| `vigia-dom` | Arena DOM: flat `Vec<Node>`, interned strings, `u32` ids |
| `vigia-charset` | Bytes -> UTF-8: BOM, Content-Type, meta sniff (win-1252, utf-16) |
| `vigia-css` | Selector engine: tag, .class, #id, [attr ops], pseudos, combinators, groups |
| `vigia-session` | Cookie jar and persistent profiles (RFC 6265 host-only/domain rules) |
| `vigia-actions` | Forms, submit, click, fill: actions resolved by snapshot ref |
| `vigia-snapshot` | DOM -> semantic tree for agents: roles, inline names, `#n` refs |
| `vigia-json` | JSON parser/serializer, order-preserving values, dotted-path lookup |
| `vigia-js` | JS interpreter: lexer, parser, tree-walk eval, arena values, runaway guards |
| `vigia-run` | `.vig` script runner: sequential ops, shared session, JSONL audit |
| `vigia-mem` | Counting allocator and RSS peak: the total-load meter |
| `vigia` (cli) | All commands above. Metrics on stderr, always |

## Dependency policy

Everything is ours. The standard library and the OS (sockets, system DNS) are the floor. Third-party crates are the exception, declared, isolated, and temporary.

One exception today, behind `crates/tls` (`vigia_tls::connect`; nothing else names it): rustls + ring + webpki-roots. Homegrown crypto holding real credentials is the classic way to leak them. Own TLS 1.3 (X25519, AES-GCM, SHA-256, cert chain validation) replaces it, differential-tested against rustls as reference.

## Roadmap

Done:

- Own HTTP/1.1, URL parser, inflate, TLS boundary
- Semantic snapshot: roles, inlined names, `#n` interactive refs, collapsed wrappers
- Benchmark harness vs lightpanda (`bench/`)
- HTML entities (named, numeric, C1 -> win-1252) and charset decoding (win-1252, utf-16, meta sniff)
- Own CSS selector engine (tag, .class, #id, [attr ops], pseudos, combinators, groups)
- Forms: urlencoded GET/POST, hidden fields, redirects
- `vigia click`/`fill`/`submit`: actions resolved by snapshot ref against the live DOM
- Persistent profiles: cookie jars on disk (`--profile`, own TSV format)
- Embedded-JSON extraction (`__NEXT_DATA__`, `ld+json`): JS-free SPA reads
- `vigia-js` core: own lexer, parser, tree-walk eval, arena values, step/call/heap guards
- Replay: `.vig` scripts plus JSONL audit trail (`vigia run`)

Next:

- JS <-> DOM bindings (execute page scripts, `document.querySelector`, mutation)
- JS mark-sweep GC over the value arenas (hard cap already enforced)
- Own TLS 1.3 (replace the rustls exception)
- HTML5 tree-construction hardening (adoption agency, foster parenting)
- `vigia serve`: HTTP/MCP control surface for agent frameworks
- Keep-alive pooling; parallel fetch engine (thread pool, RSS budget)

## Docs and contributing

- `docs/architecture.md`: the load thesis, what is deliberately missing, the risk register.
- `AGENTS.md`: build/test commands and contribution conventions.
- `CONTRIBUTING.md`: how to propose changes.

## License

MIT
