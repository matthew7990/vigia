# vigia - agent guide

## Project context

Open-source AI-native browser written **from scratch in Rust** — no Chromium/WebKit. Purpose: scraping, authenticated access, reviewable automation for AI agents. Target metrics: token cost per page + bytes of RAM per session + human-speed step latency. No render pipeline exists by design.

## Commands

- Build: `cargo build --release`
- Check: `cargo check` (run after every edit)
- Test: `cargo test`
- CLI: `cargo run -p vigia -- snap <url>`
- If `cargo` is not on PATH: `export PATH="$HOME/.cargo/bin:$PATH"`

## Conventions

- One crate per layer under `crates/`. Dependencies point inward: `cli -> run/actions/css/json/js/snapshot -> html/net -> dom/session/url`. `vigia-dom` has zero deps and stays that way.
- No async runtime. `vigia-net` is sync on purpose; parallelism, if added, is a thread pool - not tokio.
- **Everything is ours**: std + OS only. The single declared exception is `crates/tls` (`rustls`+`ring`+`webpki-roots`), isolated behind `vigia_tls::connect`, pending own TLS 1.3. Any other crate needs an explicit decision documented in the README.
- Third-party specs (RFCs, WHATWG) are reference material; implementations are ours.
- Unsafe code: only inside `vigia-mem` (the allocator shim). Nowhere else in v0.1.
- Code and docs in English. UI strings in Spanish only if/when a UI exists.
- Benchmark gate: after touching `vigia-html`, `vigia-dom`, or `vigia-snapshot`, re-run `python3 bench/run.py` against the local corpus server and compare wall time, RSS, and output tokens vs lightpanda before committing.
