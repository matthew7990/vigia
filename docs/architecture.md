# Architecture

## The load thesis

A Chromium session costs ~300 MB before the first byte: browser process, GPU process, renderers, compositor, layout, paint. For scraping and agent automation almost all of that is waste. vigia deletes those layers entirely:

```
agent / CLI
   |
 snapshot          DOM -> compact text tree
   |
 html              own tokenizer + tree builder (streaming, one pass)
   |
 dom               arena Vec<Node>, interned strings, u32 ids
   |
 net               ureq: sync HTTP, capped reads, rustls
   |
 session           cookie jar, profiles
   |
   TCP/TLS
```

Total process target for v0.1: **single-digit MB per session**. Every crate reports its allocations so the budget is auditable, not aspirational.

## What is deliberately missing

- **Layout/paint/compositing** — agents don't consume pixels. If a visual review mode is ever added it will be a separate, optional renderer.
- **JavaScript** — `vigia-js` (Boa, pure Rust) lands behind a feature flag once DOM+net are stable. It will execute DOM-mutating scripts; it will never own the render loop because there isn't one.
- **Async runtime** — sync I/O + thread pool. tokio's runtime cost buys nothing at scraping scale.

## Memory levers, ranked

1. No engine (done — architectural)
2. Arena DOM + interned strings (done — `vigia-dom`)
3. Capped body reads, 8 MiB (done — `vigia-net`)
4. Streaming tokenizer, no event buffer (done — `vigia-html`)
5. Interned attribute values (roadmap — measure first)
6. JS engine instances pooled and capped (roadmap — `vigia-js`)

## Risk register

- HTML5 tree-construction is adversarial (foster parenting, adoption agency). Current parser is a pragmatic subset; correctness bugs are fixed case-by-case with tests, not by growing the parser speculatively.
- JS-heavy SPAs return empty DOMs until `vigia-js` lands. That is the known gap and the main reason the JS module exists on the roadmap.
