# vigia — agent guide

## Project context

Open-source AI-native browser written **from scratch in Rust** — no Chromium/WebKit. Purpose: scraping, authenticated access, reviewable automation for AI agents. Design constraint #1: minimum, measurable memory. No render pipeline exists by design.

## Commands

- Build: `cargo build --release`
- Check: `cargo check` (run after every edit)
- Test: `cargo test`
- CLI: `cargo run -p vigia -- snap <url>`
- If `cargo` is not on PATH: `export PATH="$HOME/.cargo/bin:$PATH"`

## Conventions

- One crate per layer under `crates/`. Dependencies point inward: `cli -> snapshot/html/net -> dom/session`. `vigia-dom` has zero deps and stays that way.
- No async runtime. `vigia-net` is sync on purpose; parallelism, if added, is a thread pool — not tokio.
- New deps need justification against the memory floor. Parser code is ours; third-party parser crates (html5ever, cssparser) are acceptable as *reference*, not as dependencies, unless explicitly decided.
- Unsafe code: none in v0.1.
- Code and docs in English. UI strings in Spanish only if/when a UI exists.
