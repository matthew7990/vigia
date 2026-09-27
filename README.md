<p align="center">
  <img src="docs/assets/logo.svg" alt="vigia" height="160">
</p>
<h1 align="center">vigia</h1>
<p align="center">
<strong>A browser for agents, written from scratch in Rust.</strong><br>
No Chromium. No WebKit. No borrowed engine. No pixels.<br>
It fetches a page, parses it, runs its JavaScript, and hands back a
semantic snapshot the agent can act on by <code>#ref</code>.
</p>

<div align="center">

[![License](https://img.shields.io/github/license/matthew7990/vigia)](https://github.com/matthew7990/vigia/blob/master/LICENSE)
[![CI](https://img.shields.io/github/actions/workflow/status/matthew7990/vigia/ci.yml?branch=master)](https://github.com/matthew7990/vigia/actions/workflows/ci.yml)
[![Stars](https://img.shields.io/github/stars/matthew7990/vigia)](https://github.com/matthew7990/vigia/stargazers)

</div>

<div align="center">
  <img width="640" src="docs/assets/demo.svg" alt="vigia snap output">
</div>

Everything here serves two numbers: **tokens per observed page** and
**bytes of RAM per session**. On our benchmark corpus vigia runs
~40-90x faster and ~2.3x lighter than
[lightpanda](https://github.com/lightpanda-io/browser), while emitting
action refs and link targets a plain text dump doesn't carry. Details
below.

## Why build a browser from scratch

Every "browser for AI" embeds Chromium: around 300 MB before the first
request, a whole render pipeline that scraping never uses, and a memory
ceiling you don't control. vigia bets that agents don't need any of
that:

- **No layout, no paint, no compositor.** Agents read the DOM, not
  pixels. Dropping render removes most of a browser's memory cost.
- **Every layer is ours.** HTTP/1.1, URL parsing, inflate, HTML parsing,
  arena DOM, CSS engine, JavaScript interpreter. Each one is a crate
  with a measurable cost, and `vigia-mem` counts every allocation.
- **Sessions without a browser.** An RFC 6265 cookie jar keeps auth
  across runs, persisted to disk per profile. `--tab` runs the same
  script as parallel sessions.
- **JavaScript on a leash.** `vigia-js` is our own interpreter: arena
  values under a hard cap, mark-sweep GC, promises and timers on a
  deterministic virtual clock. It never touches a render loop.

To be clear about scope: a full-spec web engine is a Servo-sized
project. This one covers what agents actually do: fetch, parse, run
page scripts, extract, act, record.

## Install

Grab a release binary:

```console
curl -L -o vigia https://github.com/matthew7990/vigia/releases/latest/download/vigia-x86_64-linux
chmod a+x ./vigia
```

Or build it (stable Rust, nothing else needed):

```console
cargo build --release
./target/release/vigia snap https://example.com
```

## Quick start

```console
vigia snap <url>                  # semantic snapshot with #n action refs
vigia fetch <url>                 # raw response body
vigia extract <url> "td.price"    # CSS selector extraction
vigia click <url> 3               # follow snapshot ref #3 (gets a new page)
vigia submit <url> -d user=x -d pass=y   # form login
vigia req <url> -H 'K: V' -d '{..}'   # raw API call on the session jar
vigia json <url> [a.b.0]          # embedded JSON (__NEXT_DATA__, ld+json)
vigia js <file.js> | -e "<code>"  # run JavaScript (own interpreter)
vigia run <file.vig> [--audit log.jsonl] # multi-step script + audit trail

vigia --js snap <url>             # run the page's own <script>s first
vigia snap <url> --profile work   # persistent cookies on disk

# the same script in parallel tabs - one profile jar per tab:
vigia run login.vig --tab alice --tab bob \
  -D alice.USER=alice -D alice.PASS=x -D bob.USER=bob -D bob.PASS=y

vigia serve [--bind 127.0.0.1:8080]  # HTTP + MCP session API for agents
```

A `.vig` script is one operation per line, run in a single process
against a shared session:

```
# login.vig
snap https://example.com/login
fill #1 myuser
fill #2 "my password"
click #3
expect "Dashboard"
extract li.item
net    # every fetch() the page's JS fired (endpoint discovery)
req https://api.example.com/data -H "Content-Type: application/json" -d "{\"a\":1}"
```

Every command prints what it cost on stderr:

```
status 200 | 341 B wire -> 236 B body | connect 0ms tls 0ms ttfb 1ms total 1ms
[metrics] parse 0ms snap 0ms | nodes 20 | ~59 -> ~70 tokens | heap peak 7.9 KB | rss peak 2.6 MB
```

## Benchmark vs lightpanda

The comparison target is [lightpanda](https://github.com/lightpanda-io/browser),
the only other agent browser built without a borrowed engine.
`bench/` generates a deterministic corpus and measures wall time, peak
RSS (wait4), and the size of the agent-facing dump (`vigia snap` vs
`lightpanda fetch --dump semantic_tree_text`).

| Page | Tool | ms | RSS MB | out B | ~tokens |
|---|---|---:|---:|---:|---:|
| article | **vigia** | **5.3** | **9.6** | **54,815** | **13,703** |
| article | lightpanda | 325.4 | 22.2 | 232,208 | 58,052 |
| small | **vigia** | **3.2** | **9.6** | 172 | 43 |
| small | lightpanda | 295.4 | 21.8 | **152** | **38** |
| table | **vigia** | **10.5** | **9.6** | 142,537 | 35,634 |
| table | lightpanda | 452.0 | 26.3 | **100,008** | **25,002** |

What the numbers mean:

- **Speed.** vigia is ~40-90x faster here. Most of that gap is
  lightpanda booting a JS runtime per page; vigia's arena is already
  warm. Against a real site over TLS the gap shrinks — localhost
  flatters us.
- **Memory.** ~2.3x less RSS (9.6 MB vs ~22 MB).
- **Tokens.** vigia wins big on content-heavy pages (4x smaller on
  article). On link/table-heavy pages lightpanda's dump is smaller,
  but only because it drops link targets — which then cost a second
  call to resolve. vigia prints `-> href` and `#n` refs inline so the
  agent can act without round-tripping.

Reproduce it: `make bench` (needs the lightpanda binary at
`bench/bin/lightpanda`), or `python3 -m http.server 8899 -d bench/corpus &`
then `python3 bench/run.py`.

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
| `vigia-js` | JS interpreter: lexer, parser, tree-walk eval, prototypes, async, mark-sweep GC. Past ES5: `?.` `??` arrows `for-of/in` regex+RegExp templates spread/rest defaults destructuring `switch` `do-while` `void` methods/getters/setters Symbol Map/Set/WeakMap. No classes yet |
| `vigia-run` | `.vig` script runner: sequential ops, shared session, parallel tabs, JSONL audit |
| `vigia-mem` | Counting allocator and RSS peak: the total-load meter |
| `vigia` (cli) | All commands above. Metrics on stderr, always |

## Dependency policy

Almost everything is ours. The standard library plus the OS (sockets,
system DNS) is the floor. Anything else is an exception: declared,
isolated, and temporary.

There is exactly one today, behind `crates/tls`: rustls + ring +
webpki-roots. Rolling our own crypto around real credentials is the
classic way to leak them, so TLS 1.3 stays borrowed until our own
implementation (X25519, AES-GCM, SHA-256, cert validation) is ready,
differential-tested against rustls.

## Status

Working:

- Own HTTP/1.1, URL parser, inflate, TLS boundary
- Semantic snapshot: roles, inlined names, `#n` interactive refs, collapsed wrappers
- Benchmark harness vs lightpanda (`bench/`)
- Entities (named, numeric, C1 -> win-1252) and charset decoding
- Own CSS selector engine; forms (GET/POST, hidden fields, redirects)
- Actions by ref (`click`/`fill`/`submit`); persistent profiles; parallel tabs
- Embedded-JSON extraction (`__NEXT_DATA__`, `ld+json`)
- `vigia-js`: own lexer/parser/eval, prototypes, builtin methods,
  `new`/`instanceof`/`in`, DOM bindings (`getElementById`,
  `querySelector(All)`, `createElement`, `appendChild`, `insertBefore`,
  live `style` block, `classList`, `contains`/`closest`/`matches`),
  events with bubbling plus constructible `Event`/`CustomEvent`/
  `MouseEvent`/`KeyboardEvent` and `document.createEvent`,
  `document.cookie` read/write on the session jar, external `src=`
  scripts (static and dynamically injected, with `load`/`error`),
  Promise + microtasks + virtual-clock timers + `async`/`await`,
  Promise-returning `fetch`, `navigator.sendBeacon`, mark-sweep GC
- Browser persona (no layout engine behind it): `navigator` constants
  plus `userAgentData`, `plugins`/`mimeTypes`, `connection`,
  `geolocation`, `indexedDB`, hardware fields; `screen` + viewport dims;
  `performance.now`/`timeOrigin`; `MessageChannel` for schedulers;
  `document` props (`compatMode`,
  `hidden`, `hasFocus`, ...); `getComputedStyle` snapshot;
  `HTMLCanvasElement` 2d with real pixels (`fillRect`, `drawImage`,
  `getImageData`/`putImageData`, BMP `toDataURL`; paths, text and
  gradients stay stubs);
  zero-geometry `getBoundingClientRect`; WebGL persona (SwiftShader
  renderer string, no GPU); all-visible
  `IntersectionObserver`; fixed `America/Montevideo` timezone.
  `--stealth` sends the Chrome request profile (UA + `Sec-Fetch-*`)
  and syncs the JS `navigator` UA family to it
- WebForms basics: `form.submit()`, `__doPostBack` (injects
  `__EVENTTARGET`/`__EVENTARGUMENT`), `javascript:` hrefs run as page
  code — verified against a live postback round-trip
- Replay: `.vig` scripts plus JSONL audit trail
- `vigia serve`: HTTP session API + MCP `tools/call` surface (one
  worker thread per session, JSON in/out)

Still to do:

- JS: classes (`extends`/`super`), logical assignment, `**`, `delete`
- Canvas paths/text/gradients, CSS cascade behind `getComputedStyle`
- Own TLS 1.3 (replace the rustls exception)
- HTML5 tree-construction hardening (adoption agency, foster parenting)
- Keep-alive pooling; parallel fetch engine (thread pool, RSS budget)
- WebForms beyond postbacks: no UpdatePanel/AJAX

Honest limits: a `pending await` is an error, not a suspension (vigia
settles everything eagerly); events don't capture, only bubble; every
request is `Connection: close` for now. `--stealth` camouflages the
request profile, but there is no CAPTCHA solving here: when a site
puts up a bot-manager CAPTCHA, that's a wall, not a puzzle. The
strategy is valid sessions plus API replay (`net` shows the
endpoints, `req` replays them), not fingerprint spoofing.

## Docs and contributing

- `docs/architecture.md`: the load thesis, what's deliberately missing, the risk register.
- `docs/bitacora.md`: build log, milestone by milestone, with the live evidence.
- `AGENTS.md`: build/test commands and contribution conventions.
- `CONTRIBUTING.md`: how to propose changes.
- `SECURITY.md`: reporting vulnerabilities.

## License

MIT
