# Bitácora de vigia

Registro de los pasos de construcción del browser propio, en orden. Cada
bloque cita el commit y lo que se verificó en vivo.

Contexto: vigia es un browser para agentes construido desde cero (sin
Chromium/WebKit/Puppeteer/Playwright). Benchmark target: lightpanda.
Excepción única declarada: `rustls` para TLS.

## 1. Base propia (commits b5b64d6 → 84eb6e1)

- Workspace de crates: net, url, html, dom, css, session, charset,
  inflate, json, snapshot, actions, run, js, serve, cli, mem.
- HTTP/1.1 propio sobre `std::net`: request line, headers, chunked,
  gzip/deflate (inflate propio), redirects con downgrade POST→GET.
- Parser HTML + DOM en arena (NodeId u32), interner de strings.
- Selectores CSS propios, formularios, entities, charset decoding.
- CLI: `vigia snap | fetch | dom | extract | click | submit | json`.
- Métricas en stderr: bytes wire/body, ms por fase, ~tokens, heap, RSS.

## 2. Snapshot semántico + benchmark vs lightpanda (0085941, 9da6b2e)

- Snapshot con refs `#n` para acciones, hrefs inline para navegación.
- `bench/`: corpus determinístico + runner que mide ms, RSS (wait4) y
  tamaño del dump vs `lightpanda fetch --dump semantic_tree_text`.
- Resultados medidos: vigia ~40-90x más rápido, ~2.3x menos RSS,
  ~4x menos tokens en páginas de contenido.
- Fix real encontrado en el medio: elementos con tag desconocido
  skipeaban el subárbol pero `interactive_refs` igual contaba sus links
  (refs desalineados) — ahora colapsan.
- `class` fuera del snapshot (ruido de styling): links.html -25%,
  table.html -24%.

## 3. Navegación y sesiones (ab5275a, cf9f1bb, 9da6b2e)

- `vigia run file.vig`: ops una por línea (snap/fill/click/submit/
  extract/json/expect), `--audit` JSONL por op.
- `--profile <name>`: jar persistente en `~/.vigia/profiles/<name>.jar`.
- `vigia json`: extracción de `__NEXT_DATA__` / ld+json.

## 4. Motor JS propio (ba0176b → 9abea42)

- `vigia-js`: lexer + parser + tree-walking evaluator, todo propio.
- `vigia --js`: corre los `<script>` inline de la página contra el DOM
  vivo. Bindings: `document.getElementById/querySelector/createElement`,
  `textContent`, `innerHTML`, `setAttribute`, `appendChild`, `remove`,
  `window/navigator/location`. Globals compartidos entre scripts.
- Eventos: `addEventListener`, `dispatchEvent`, `.click()`, bubbling
  target→document, `onclick` inline con `this`, `preventDefault`,
  `stopPropagation`, `DOMContentLoaded`.
- `fetch()` (inicialmente síncrono) + bridge de navegación: `el.click()`
  en `<a href>` registra `pending_nav` que el host sigue una vez.
- Scripts externos `<script src>` fetcheados con el jar de sesión, en
  orden de documento (914aebd). Cap 32/página.
- Prototypes + builtins (9abea42): cadena proto capada a 64 hops, `new`,
  `instanceof`, `in`; Array.prototype ×22, String.prototype ×20,
  Object.keys/values/entries/assign/create, call/apply, Math, Date,
  parseInt/Float.

## 5. Async (b2768b7)

- `Promise` completo: then/catch/finally, resolve/reject/all/race/
  allSettled. Microtasks FIFO. `async`/`await` sobre promises settled.
- Timers con **reloj virtual**: `setTimeout(fn, 5000)` no espera 5s —
  avanza `now_ms` al deadline y corre. Determinístico, cero idle.
- `fetch` devuelve Promise real (I/O eager por dentro); `.text()`/
  `.json()` devuelven promises.
- Deviation honesta documentada: `await` en pending promise no suspende
  el stack nativo — error claro.

## 6. Pestañas paralelas (50d753c)

- `vigia run login.vig --tab alice --tab bob -D tab.KEY=val`
- Un `std::thread` por tab: jar + DOM + interp propios, aislamiento
  total. El nombre de tab ES el profile (jar por tab).
- `$VAR`/`${VAR}` en scripts, `-D tab.KEY` gana sobre `-D KEY`,
  fallback env `VIGIA_NAME`. Audit gana campo `"tab"`.
- Verificado: dos logins paralelos con dashboards distintos, ~5.5 MB
  RSS las dos pestañas.

## 7. GC mark-sweep (e183b21)

- Mark-sweep sobre arenas de objetos/strings/envs; tombstones, free
  lists, handles estables.
- Safepoints solo con `call_depth == 0` y heap >70% del cap — un
  temporal Rust mid-expression nunca se barre (bug que se detectó en
  diseño: `mk() + churn()`).
- Roots: env chain, protos, microtasks, timers, listeners, wrapper
  cache, interned strings.
- Verificado: 2M iteraciones de churn completan (`gc 5`), heap acotado
  por live usage no por churn.

## 8. Errores JS (24168e9)

- `throw`/`try`/`catch`/`finally`, `Error` con `instanceof` real.
- `JsError::{Msg, Throw(Value), Fatal}`: errores internos materializan
  como Error objects (catchable), thrown values verbatim, guards del
  engine (step limit, call depth) = Fatal, nunca catchable.
- `finally` corre en return/break/continue/error.

## 9. `vigia serve` — HTTP + MCP (21fee6c)

- REST: `POST /session`, `GET /sessions`, `DELETE /session/:id`,
  `POST /session/:id/{snap,click,fill,submit,extract,eval,run,net}`,
  `GET /health`.
- MCP: `POST /mcp` JSON-RPC (initialize, tools/list, tools/call, batch,
  notificaciones 202). Tools: vigia_session_new/close, snap, click,
  fill, submit, extract, eval, net.
- Arquitectura: `Interp` es `!Send` (Rc<FnDef>) → un worker thread por
  sesión + canal mpsc (el canal ES el lock; serializa por sesión,
  paraleliza entre sesiones). LRU a 256 sesiones.
- Bind loopback por defecto; sin auth — el código advierte que
  exponerlo es RCE remota.

## 10. Repo público (c85c024, d2fb268) + release v0.1.0

- cargo fmt + clippy -D warnings a cero en todo el workspace.
- Logo propio (docs/assets/logo.svg), demo.svg, badges, benchmark
  table con números medidos, Makefile, SECURITY.md, issue/PR templates.
- Topics en GitHub. Release v0.1.0 con binario verificado (2.2 MB).
- Pendiente del usuario: `gh auth refresh -h github.com -s workflow`
  para poder pushear `.github/workflows/ci.yml` (queda local).

## 11. Caso real: FYSCAL3.0 exFiservPortal (3f7b819, 257d013)

Análisis de los scrapers de producción en FYSCAL3.0
(dist/constructors/workers/):

- `exFiservPortal3.mjs`: Puppeteer contra merchantcenter.fiservapp.com
  (Angular SPA). Login user/pass + TOTP → `setRequestInterception` →
  captura el POST que la SPA hace a
  `/settlement/Settlement/SettlementListPayMentReport` → replica ese
  POST con `page.evaluate(fetch)` por día → `response.json()` → Mongo.
  El browser es solo bootstrap; el data-plane es API replay con cookies.
- `exNaranjaPortal2.js`: el caso duro — DOM puro sobre SPA (~700 líneas
  de waitForSelector + click por selector + códigos de verificación).
- `exPrismaPortal.js`: puppeteer-extra + stealth + proxy + axios.

Cambios en vigia a partir de eso:

- `vigia_net::req(url, method, headers, body, jar)`: request completo,
  headers custom sobre defaults, Content-Type propio.
- `vigia req` CLI + op `req` en `.vig` (-d implica POST; vars por tab
  se resuelven en url/headers/body).
- `fetch(url, {method, headers, body})` completo en page JS.
- **Net trace**: `NetCtx.trace` registra cada fetch() de la página como
  `NetEvent` (method, url resuelta, status, req/resp bodies ≤4K).
  Equivalente a page.on('request'/'response').
- Superficies: `vigia net <url>`, op `net` en `.vig` (imprime el trace +
  línea `replay: req ...` lista para copiar), `POST /session/:id/net`,
  MCP `vigia_net`.
- Verificado en vivo: página que hace fetch POST JSON → `net` captura
  endpoint+payload → `req` lo repite con payload modificado → el server
  recibió el replay exacto.

### Qué falta para Fiserv de verdad

| Gap | Por qué importa |
|---|---|
| Boot de SPAs (Angular/React) | el login JS-rendered necesita classes, for-of, destructuring, más DOM API |
| TOTP | externo al browser (FYSCAL lo genera aparte) |
| Anti-bot / stealth fingerprint | exPrisma usa stealth plugin; vigia no tiene evasión |
| waitForSelector (espera real) | hoy el engine no tiene tiempo real de espera |

## 12. Regex (en curso)

Scope definido por uso real en FYSCAL:
`.match(/<([^>]+@[^>]+)>/`, `.split(/[,;]/`, `.replace(/-/g,'+')`,
`/text\/plain|text\/html/i.test`, `\d{4,8}`, `\b`, capture groups,
flags i/g/m/s, lazy quantifiers. Literales `/x/` + `new RegExp` +
`test/exec/match/replace/split/search`. Sin backrefs ni lookarounds.
Motor propio backtracking con fuel cap.

## Estado de tests

141 tests verdes post net-trace (crece por milestone). Verificación
estándar: `cargo fmt --check`, `cargo check --workspace`,
`cargo clippy --workspace -- -D warnings`, `cargo test --workspace`,
más smoke live contra fixtures locales.
