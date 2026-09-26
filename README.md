# vigia

An AI-native browser, written from scratch in Rust — **no Chromium, no WebKit, no borrowed engine**. Built for agents: scraping, authenticated access, and reviewable automation with a memory floor we control byte by byte.

## Why from scratch

Every existing "browser for AI" embeds Chromium. That means ~300 MB before your first request, a render pipeline you don't need for scraping, and a resource ceiling you don't control. vigia's premise:

- **No layout, no paint, no compositor.** Agents read DOM, not pixels. Skipping render removes most of a browser's memory cost.
- **Own HTTP + HTML parser + arena DOM.** Strings interned, nodes in one flat `Vec`, no `Rc` graphs. The load is measurable per crate.
- **Sessions without a browser.** Cookie jars and profiles persist auth on disk — login flows don't need a rendered page until JavaScript becomes unavoidable.
- **JS arrives as a module, not a monolith.** `vigia-js` will embed a standalone engine (Boa — pure Rust) behind a feature flag, not a 300 MB runtime.

Scope honesty: a full-spec web engine is a Servo/Ladybird-scale project. vigia's scope is what agents actually need — fetch, parse, DOM, extract, act, record. Rendering and full HTML5 tree-construction fidelity are deliberately deferred.

## Crates

| Crate | Responsibility | Memory lever |
|---|---|---|
| `vigia-net` | HTTP client (sync, capped body reads, rustls) | 8 MiB body cap, no async runtime |
| `vigia-html` | Own tokenizer + tree builder, single streaming pass | no intermediate event buffer |
| `vigia-dom` | Arena DOM, interned strings | flat `Vec` + `u32` ids |
| `vigia-session` | Cookie jar, profiles | disk-backed, load-on-demand |
| `vigia-snapshot` | DOM → compact text tree for agents | skips script/style/svg subtree |
| `vigia` (cli) | `snap` / `fetch` / `dom` commands | — |

## Quickstart

```bash
cargo build --release

./target/release/vigia snap https://example.com    # agent snapshot
./target/release/vigia fetch https://example.com   # raw body
./target/release/vigia dom https://example.com     # parse stats
```

## Roadmap

- [ ] HTML5 spec fidelity hardening (implied end tags, adoption agency)
- [ ] CSS parsing + computed style subset (`vigia-css`) for visibility checks
- [ ] `vigia-js`: embed Boa behind a feature flag — execute scripts that mutate the DOM, without a render pipeline
- [ ] Action layer: semantic click/fill resolved against the DOM, form submission over HTTP
- [ ] Recorder + replay artifacts for review
- [ ] `vigia serve`: HTTP/MCP control surface for agent frameworks
- [ ] Parallel fetch engine (thread pool, no async runtime) with global RSS budget

## License

MIT
