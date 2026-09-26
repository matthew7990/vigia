# Contributing

## Rules that do not bend

- Everything is ours. Rust std plus the OS are the floor. A new third-party crate needs a declared, isolated exception documented in `README.md`. The only one today is `vigia-tls` (rustls), pending own TLS 1.3.
- One crate per layer under `crates/`. Dependencies point inward, toward `vigia-dom`/`vigia-session`/`vigia-url`. `vigia-dom` keeps zero dependencies.
- No async runtime and no unsafe outside `vigia-mem`.
- Code, comments, and docs in English, ASCII only.

## Workflow

1. `cargo check` after every edit.
2. `cargo test` before committing. Tests live in the crate they cover.
3. If you touch `vigia-html`, `vigia-dom`, or `vigia-snapshot`, run the benchmark gate: `python3 -m http.server 8899 -d bench/corpus &` then `python3 bench/run.py`. Compare wall time, RSS, and output tokens against lightpanda and paste the table in the PR.
4. Keep commits small and ordered: the enabling layer lands before the feature that uses it.
5. Metrics stay honest. If a change makes snapshots smaller by dropping information an agent needs, that is a regression, not a win.

## What to work on

The roadmap in `README.md` is the source of truth. Good first contributions: corpus fixtures with expected outputs, RFC 6265 cookie edge cases, malformed-HTML crashers, JS conformance cases for `vigia-js`.
