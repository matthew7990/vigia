# Architecture

## The load thesis

A Chromium session costs ~300 MB before the first byte: browser process, GPU process, renderers, compositor, layout, paint. For scraping and agent automation almost all of that is waste. vigia deletes those layers entirely and writes what remains itself:

```
agent / CLI
   |
 snapshot          DOM -> compact text tree (token-cost metric)
   |
 html              own tokenizer + tree builder (streaming, one pass)
   |
 dom               arena Vec<Node>, interned strings, u32 ids
   |
 net               own HTTP/1.1: chunked, redirects, gzip (vigia-inflate)
   |
 url               own parser + relative resolution (WHATWG subset)
   |
 session           cookie jar, RFC 6265 correct (host-only, boundaries)
   |
 tls               vigia-tls: single dep exception (rustls), own TLS 1.3 next
   |
   TCP
```

Total-process target: **single-digit MB per session**. `vigia-mem` is a counting `GlobalAlloc` — every crate's heap is measured, not estimated, and the CLI reports it per run. Same for speed: fetch timings split connect/tls/ttfb/total.

## What is deliberately missing

- **Layout/paint/compositing** — agents don't consume pixels. If a visual review mode is ever added it will be a separate, optional renderer.
- **JavaScript** — `vigia-js` will be our own interpreter (lexer, parser, tree-walking eval, mark-sweep GC with a hard heap cap), behind a feature flag, once DOM+actions are stable. It mutates the DOM; it never owns a render loop because there isn't one.
- **Async runtime** — sync I/O + thread pool. tokio's runtime cost buys nothing at scraping scale.
- **Keep-alive / HTTP/2** — `Connection: close` today; pooling and HTTP/2 are measured optimizations for later.

## Dependency policy

Everything is ours — std + OS as the floor. Exceptions are declared, isolated, and temporary:

| Exception | Crate | Exit |
|---|---|---|
| rustls + ring + webpki-roots | `vigia-tls` | own TLS 1.3 (X25519, AES-GCM, SHA-256, cert chain validation), validated against rustls as reference |

## Memory levers, ranked

1. No engine (done — architectural)
2. Arena DOM + interned strings (done — `vigia-dom`)
3. Capped wire/body reads (done — `vigia-net`: 8 MiB wire, 16 MiB decoded, anti zip-bomb cap in `vigia-inflate`)
4. Streaming tokenizer, no event buffer (done — `vigia-html`)
5. Counting allocator reports the truth (done — `vigia-mem`; measured ~8 KB heap peak on a small page, 2.6 MB RSS total)
6. Interned attribute values (roadmap — measure first)
7. JS engine instances pooled and GC-capped (roadmap — `vigia-js`)

## Risk register

- HTML5 tree-construction is adversarial (foster parenting, adoption agency). Current parser is a pragmatic subset; correctness bugs are fixed case-by-case with tests, not by growing the parser speculatively.
- JS-heavy SPAs return empty DOMs until `vigia-js` lands. Mitigation first: embedded-JSON extraction (`__NEXT_DATA__`, `ld+json`) covers a large SPA share with zero JS cost.
- Own TLS 1.3 is the largest single piece of remaining third-party surface to remove; it is also the riskiest to write. Plan is phased: implement alongside rustls, differential-test, swap.
