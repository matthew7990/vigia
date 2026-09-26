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
| `vigia-snapshot` | DOM -> compact text tree for agents | skips script/style/svg subtrees |
| `vigia-mem` | Counting allocator + RSS peak | the total-load meter |
| `vigia` (cli) | `snap` / `fetch` / `dom` | metrics on stderr, always |

## Quickstart

```bash
cargo build --release

./target/release/vigia snap https://example.com    # agent snapshot
./target/release/vigia fetch https://example.com   # raw body
./target/release/vigia dom https://example.com     # parse stats
```

Every command reports cost and latency on stderr:

```
status 200 | 341 B wire -> 236 B body | connect 0ms tls 0ms ttfb 1ms total 1ms
[metrics] parse 0ms snap 0ms | nodes 20 | ~59 -> ~70 tokens | heap peak 7.9 KB | rss peak 2.6 MB
```

## Roadmap

- [x] Own HTTP/1.1 + URL parser + inflate + TLS boundary
- [ ] Own TLS 1.3 (replace the rustls exception)
- [ ] HTML entities + charset decoding (latin-1/win-1252 -> UTF-8)
- [ ] HTML5 tree-construction hardening (implied end tags, adoption agency)
- [ ] Own CSS selector engine (`div.item > a[href]`) for extraction and actions
- [ ] Form submission (urlencoded/multipart POST) — login flows without JS
- [ ] Persistent profiles on disk (own format, no serde)
- [ ] Embedded-JSON extraction (`__NEXT_DATA__`, `ld+json`) — JS-free SPA reads
- [ ] `vigia-js`: own interpreter behind a feature flag, GC with hard cap
- [ ] Action layer: semantic click/fill resolved against the DOM
- [ ] Recorder + replay artifacts for review
- [ ] `vigia serve`: HTTP/MCP control surface for agent frameworks
- [ ] Keep-alive pooling; parallel fetch engine (thread pool, RSS budget)

## License

MIT
