# vigia

An AI-native browser, written from scratch in Rust — **no Chromium, no WebKit, no borrowed engine**. Built for agents: scraping, authenticated access, and reviewable automation at two target metrics:

- **Cost**: tokens per observed page + bytes of RAM per session.
- **Human speed**: fetch -> snapshot -> action under human reaction time, no multi-second screenshot loops.

## Why from scratch

Every "browser for AI" embeds Chromium: ~300 MB before the first request, a render pipeline scraping never uses, and a resource ceiling you don't control. vigia's premise:

- **No layout, no paint, no compositor.** Agents read DOM, not pixels. Skipping render removes most of a browser's memory cost.
- **Own HTTP/1.1, own URL parser, own inflate, own HTML parser, own arena DOM.** The load is measurable per crate — `vigia-mem` counts every allocation.
- **Sessions without a browser.** Cookie jars (RFC 6265-correct) persist auth without a rendered page.
- **JavaScript is a bounded module, not a monolith.** `vigia-js` will be our own interpreter (lexer/parser/tree-walker/GC) behind a feature flag — never a 300 MB runtime.

Scope honesty: a full-spec web engine is a Servo/Ladybird-scale project. vigia's scope is what agents actually need — fetch, parse, DOM, extract, act, record.

## Dependency policy

**Everything is ours.** The standard library and the OS (sockets, system DNS) are the floor; third-party crates are the exception.

Current sole exception, isolated behind `crates/tls` (`vigia_tls::connect` — nothing else names it): `rustls` + `ring` + `webpki-roots`, because homegrown crypto handling real credentials is the classic way to leak them. Own TLS 1.3 (X25519, AES-GCM, SHA-256, cert validation) replaces it in phase 2, validated against it as reference.

## Crates

| Crate | Responsibility | Lever |
|---|---|---|
| `vigia-net` | Own HTTP/1.1 on `std::net`: chunked, redirects, gzip | 8 MiB wire cap, timing split per phase |
| `vigia-url` | Own URL parser + relative resolution | dot-segments, percent-encoding |
| `vigia-inflate` | Own DEFLATE/zlib/gzip decoder | output cap (anti zip-bomb) |
| `vigia-tls` | TLS boundary (rustls, single exception) | opaque `TlsStream`, replaceable |
| `vigia-html` | Own tokenizer + tree builder, single streaming pass | no intermediate event buffer |
| `vigia-dom` | Arena DOM, interned strings | flat `Vec` + `u32` ids |
| `vigia-session` | Cookie jar (RFC 6265), profiles | host-only/domain-boundary correct |
| `vigia-snapshot` | DOM -> semantic tree (roles, `#n` refs) | collapses pure-structure wrappers |
| `vigia-css` | Own selector engine (query the DOM) | no stylesheet needed |
| `vigia-charset` | Bytes -> UTF-8 (win1252, utf-16, meta sniff) | ~200 lines, no ICU |
| `vigia-actions` | Form collection + submit, text extraction | urlencoded, GET/POST semantics |
| `vigia-mem` | Counting allocator + RSS peak | the total-load meter |
| `vigia` (cli) | `snap` / `fetch` / `dom` | metrics on stderr, always |

## Quickstart

```bash
cargo build --release

./target/release/vigia snap https://example.com    # agent snapshot
./target/release/vigia fetch https://example.com   # raw body
./target/release/vigia dom https://example.com     # parse stats
./target/release/vigia extract <url> "td.price"    # CSS selector extraction
./target/release/vigia click <url> 3               # follow snapshot ref #3
./target/release/vigia submit <url> -d user=x -d pass=y   # form login
./target/release/vigia snap <url> --profile work   # persistent session (cookies on disk)
```

Every command reports cost and latency on stderr:

```
status 200 | 341 B wire -> 236 B body | connect 0ms tls 0ms ttfb 1ms total 1ms
[metrics] parse 0ms snap 0ms | nodes 20 | ~59 -> ~70 tokens | heap peak 7.9 KB | rss peak 2.6 MB
```

## Benchmark: vigia vs lightpanda

The comparison target is [lightpanda](https://github.com/lightpanda-io/browser) —
the only other from-scratch AI browser. `bench/` generates a deterministic
corpus and measures wall time, peak RSS (wait4), and output size of the
agent-facing dump (`vigia snap` vs `lightpanda fetch --dump semantic_tree_text`).

```
page             tool              ms   rss_mb    out_b  ~tokens rc
article.html     vigia            5.3      9.6    54815    13703  0
article.html     lightpanda     325.4     22.2   232208    58052  0
small.html       vigia            3.2      9.6      172       43  0
small.html       lightpanda     295.4     21.8      152       38  0
table.html       vigia           10.5      9.6   188537    47134  0
table.html       lightpanda     452.0     26.3   100008    25002  0
```

- **Speed: vigia is ~40-90x faster.** Lightpanda boots a JS runtime per page; vigia has nothing to boot.
- **Memory: vigia uses ~2.3x less RSS** (9.6 MB vs ~22 MB).
- **Tokens: vigia wins on content-heavy pages** (4x smaller on article) and carries `-> href` / `#n` refs that lightpanda's text dump omits. On link/table-heavy pages lightpanda is smaller precisely because it drops link targets — a second CDP call is needed to actually navigate.

Run it: `python3 bench/gen_corpus.py`, serve `bench/corpus/` on :8899, `python3 bench/run.py`.

## Roadmap

- [x] Own HTTP/1.1 + URL parser + inflate + TLS boundary
- [x] Semantic snapshot v2: roles, inlined names, `#n` interactive refs, collapsed wrappers
- [x] Benchmark harness vs lightpanda (`bench/`)
- [x] HTML entities (named + numeric, C1->win1252) + charset decoding (win1252/utf-16/meta sniff)
- [x] Own CSS selector engine (tag/.class/#id/[attr ops]/pseudos/combinators/groups)
- [x] Form submission (urlencoded GET/POST, hidden fields, redirects)
- [x] `vigia click #n` — navigate by snapshot ref (links + form buttons)
- [x] Persistent profiles: cookie jars on disk (`--profile`, own TSV format)
- [ ] Own TLS 1.3 (replace the rustls exception)
- [ ] HTML5 tree-construction hardening (implied end tags, adoption agency)
- [x] Embedded-JSON extraction (`__NEXT_DATA__`, `ld+json`) — JS-free SPA reads
- [x] `vigia-js` core: own lexer + parser + tree-walking eval (ES5-ish subset, arena values, step/call/heap guards)
- [x] Action layer: click/fill/submit resolved by snapshot ref against the live DOM
- [x] Replay: `.vig` scripts + JSONL audit trail (`vigia run`)
- [ ] JS <-> DOM bindings (execute page scripts, document.querySelector, mutation)
- [ ] JS mark-sweep GC over the value arenas (hard cap already enforced)
- [ ] `vigia serve`: HTTP/MCP control surface for agent frameworks
- [ ] Keep-alive pooling; parallel fetch engine (thread pool, RSS budget)

## License

MIT
