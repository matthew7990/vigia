# Architecture

## The load thesis

A Chromium session costs ~300 MB before the first byte: browser process, GPU process, renderers, compositor, layout, paint. For scraping and agent automation almost all of that is waste. vigia deletes those layers and writes what remains itself:

```
agent / CLI
   |
   run        .vig scripts: sequential ops, shared session, JSONL audit
   |
snapshot     DOM -> compact semantic tree (the observation an agent reads)
   |
actions      click / fill / submit / extract, resolved by snapshot ref
   |
css          own selector engine over the arena DOM
   |
html         own tokenizer + tree builder (streaming, one pass)
   |
dom          arena Vec<Node>, interned strings, u32 ids
   |
net          own HTTP/1.1: chunked, redirects, gzip (vigia-inflate)
   |
url          own parser + relative resolution (WHATWG subset)
   |
session      cookie jar, RFC 6265 correct (host-only, boundaries)
   |
tls          vigia-tls: single dep exception (rustls), own TLS 1.3 next
   |
   TCP

js           own interpreter: lexer, parser, tree-walk eval, arena values
json         own JSON parser (embedded-data extraction, .vig audit output)
mem          counting GlobalAlloc: per-crate heap and RSS truth
```

Total-process target: **single-digit MB per session**. `vigia-mem` is a counting `GlobalAlloc`: every crate's heap is measured, not estimated, and the CLI reports it per run. Same for speed: fetch timings split connect/tls/ttfb/total.

## What is deliberately missing

- **Layout, paint, compositing.** Agents do not consume pixels. If a visual review mode ever ships it will be a separate, optional renderer.
- **Async runtime.** Sync I/O plus a thread pool when needed. tokio's runtime cost buys nothing at scraping scale.
- **Keep-alive and HTTP/2.** `Connection: close` today. Pooling and HTTP/2 are measured optimizations for later.
- **Full JS semantics.** `vigia-js` runs an ES5-ish subset today: prototypes exist, classes and regex do not. Async is real but engine-synchronous: promises, microtasks, virtual-clock timers, async fns, and Promise-returning fetch all drain deterministically at script/event boundaries; pending `await` is unsupported (no suspension). A mark-sweep GC over the value arenas is the next milestone, not a different engine.

## Dependency policy

Everything is ours: std plus OS as the floor. Exceptions are declared, isolated, and temporary:

| Exception | Crate | Exit |
|---|---|---|
| rustls + ring + webpki-roots | `vigia-tls` | own TLS 1.3 (X25519, AES-GCM, SHA-256, cert chain validation), differential-tested against rustls as reference |

## Memory levers, ranked

1. No engine (done, architectural).
2. Arena DOM plus interned strings (done, `vigia-dom`).
3. Capped wire/body reads (done, `vigia-net`: 8 MiB wire, 16 MiB decoded; anti zip-bomb cap in `vigia-inflate`).
4. Streaming tokenizer, no event buffer (done, `vigia-html`).
5. Counting allocator reports the truth (done, `vigia-mem`; measured ~8 KB heap peak on a small page, 2.6 MB RSS total).
6. JS values in flat arenas with a hard slot cap (done, `vigia-js`; mark-sweep GC next).
7. Interned attribute values (roadmap; measure first).
8. JS engine instances pooled (roadmap).

## Risk register

- HTML5 tree-construction is adversarial (foster parenting, adoption agency). The parser is a pragmatic subset. Correctness bugs get fixed case by case with tests, not by growing the parser speculatively.
- JS-heavy SPAs return empty DOMs until JS <-> DOM bindings land. Two mitigations ship today: embedded-JSON extraction (`__NEXT_DATA__`, `ld+json`) covers a large SPA share with zero JS cost, and the interpreter core exists for scripting.
- Own TLS 1.3 is the largest remaining piece of third-party surface to remove, and the riskiest to write. The plan is phased: implement alongside rustls, differential-test, then swap.
