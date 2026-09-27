//! vigia-serve: `vigia serve` - a session HTTP API plus a minimal
//! MCP-over-HTTP endpoint. std::net only, no async, no third-party deps.
//!
//! Threading: one thread per accepted connection (`Connection: close`), one
//! worker thread per session behind an mpsc channel. The channel is the
//! lock: ops on one session serialize, different sessions run in parallel.
//! Interp is !Send (its heap holds Rc) - pinning each Session to a worker
//! thread keeps the unsafe-free rule (vigia-mem is the only unsafe home).
//!
//! No auth in v1: default bind is loopback. A remotely reachable listener
//! is remote code execution - it fetches URLs and evaluates JS on request.

use std::collections::HashMap;
use std::io::{Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc::{channel, Receiver, Sender};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use vigia_dom::{Dom, NodeData};
use vigia_json::Json;
use vigia_session::CookieJar;
use vigia_url::Url;

mod mcp;

const MAX_SESSIONS: usize = 256;
const MAX_BODY: usize = 1024 * 1024;
const MAX_HEAD: usize = 32 * 1024;
const IO_TIMEOUT: Duration = Duration::from_secs(30);
const NO_PAGE: &str = "no current page (snap first)";

/// The page ops act on. vigia-run keeps its own identical Page private;
/// duplicating three fields beats widening that crate's API.
struct Page {
    dom: Dom,
    url: Url,
    status: u16,
    /// fetch() calls the page's JS made (load + later eval calls).
    net_events: Vec<vigia_js::NetEvent>,
}

/// Owned by its worker thread end to end - nothing here crosses threads.
struct Session {
    jar: CookieJar,
    page: Option<Page>,
    /// Live JS ctx for the current page; globals persist across eval calls.
    interp: Option<vigia_js::Interp>,
    /// `interp` has document/window globals installed (set_dom ran).
    interp_globals: bool,
    js: bool,
    vars: Vec<(String, String)>,
}

/// The Send-able view of a session: /sessions lists it, LRU eviction reads
/// last_used. The worker refreshes it around every op.
struct Meta {
    url: Option<String>,
    status: u16,
    js: bool,
    last_used: Instant,
}

struct Handle {
    tx: Sender<Req>,
    meta: Arc<Mutex<Meta>>,
}

/// One op for a session worker; `reply` is a oneshot carrying (status, body).
struct Req {
    name: String,
    args: Json,
    reply: Sender<(u16, Json)>,
}

pub struct Server {
    sessions: Mutex<HashMap<u64, Handle>>,
    next: AtomicU64,
    started: Instant,
    listener: TcpListener,
}

impl Server {
    /// Bind without accepting yet; call `serve` (blocking) or `start`.
    pub fn listen(addr: &str) -> std::io::Result<Arc<Server>> {
        let listener = TcpListener::bind(addr)?;
        Ok(Arc::new(Server {
            sessions: Mutex::new(HashMap::new()),
            next: AtomicU64::new(1),
            started: Instant::now(),
            listener,
        }))
    }

    /// Bind + spawn the accept loop on its own thread (tests, embedding).
    pub fn start(addr: &str) -> std::io::Result<Arc<Server>> {
        let srv = Self::listen(addr)?;
        let me = srv.clone();
        std::thread::spawn(move || me.serve());
        Ok(srv)
    }

    pub fn addr(&self) -> SocketAddr {
        self.listener
            .local_addr()
            .unwrap_or_else(|_| "127.0.0.1:0".parse().unwrap())
    }

    /// Accept loop: spawn a thread per connection, forever.
    pub fn serve(self: &Arc<Self>) {
        for conn in self.listener.incoming() {
            match conn {
                Ok(stream) => {
                    let me = self.clone();
                    std::thread::spawn(move || me.handle_conn(stream));
                }
                Err(_) => continue, // transient accept failure: keep serving
            }
        }
    }

    fn handle_conn(&self, mut stream: TcpStream) {
        let _ = stream.set_read_timeout(Some(IO_TIMEOUT));
        let _ = stream.set_write_timeout(Some(IO_TIMEOUT));
        let (status, body) = match read_request(&mut stream) {
            Ok(req) => self.route(&req),
            Err((status, msg)) => (status, err_json(&msg).to_string()),
        };
        write_response(&mut stream, status, &body);
    }

    /// REST routing. Returns (status, body); every body is JSON except the
    /// 202 empty-body notification ack from /mcp.
    fn route(&self, req: &Request) -> (u16, String) {
        let path = req.path.split('?').next().unwrap_or("");
        let m = req.method.as_str();
        if !matches!(m, "GET" | "POST" | "DELETE") {
            return jsend(405, err_json("method not allowed"));
        }
        match path {
            "/" | "/health" => {
                if m != "GET" {
                    return jsend(405, err_json("method not allowed"));
                }
                let n = self.sessions.lock().unwrap().len();
                jsend(
                    200,
                    Json::Obj(vec![
                        ("ok".into(), Json::Bool(true)),
                        ("sessions".into(), Json::Num(n as f64)),
                        (
                            "uptime_ms".into(),
                            Json::Num(self.started.elapsed().as_millis() as f64),
                        ),
                    ]),
                )
            }
            "/mcp" => {
                if m != "POST" {
                    return jsend(405, err_json("method not allowed"));
                }
                self.mcp(&req.body)
            }
            "/session" => {
                if m != "POST" {
                    return jsend(405, err_json("method not allowed"));
                }
                match body_obj(&req.body) {
                    Ok(args) => jsend_pair(self.create_session(&args)),
                    Err(e) => jsend_pair(e),
                }
            }
            "/sessions" => {
                if m != "GET" {
                    return jsend(405, err_json("method not allowed"));
                }
                jsend(200, self.list_sessions())
            }
            _ => match path.strip_prefix("/session/") {
                None => jsend(404, err_json("unknown path")),
                Some(rest) => {
                    let segs: Vec<&str> = rest.split('/').collect();
                    match segs.as_slice() {
                        [id] => {
                            if m != "DELETE" {
                                return jsend(405, err_json("method not allowed"));
                            }
                            match id.parse::<u64>() {
                                Ok(id) => jsend_pair(self.delete_session(id)),
                                Err(_) => jsend(400, err_json("bad session id")),
                            }
                        }
                        [id, op] => {
                            if m != "POST" {
                                return jsend(405, err_json("method not allowed"));
                            }
                            const OPS: &[&str] = &[
                                "snap", "click", "fill", "submit", "extract", "eval", "run", "net",
                            ];
                            if !OPS.contains(op) {
                                return jsend(404, err_json("unknown op"));
                            }
                            let Ok(id) = id.parse::<u64>() else {
                                return jsend(400, err_json("bad session id"));
                            };
                            match body_obj(&req.body) {
                                Ok(args) => jsend_pair(self.call_op(id, op, args)),
                                Err(e) => jsend_pair(e),
                            }
                        }
                        _ => jsend(404, err_json("unknown path")),
                    }
                }
            },
        }
    }

    /// POST /session: spawn a worker, evicting the least-recently-used
    /// session first when the table is full.
    fn create_session(&self, args: &Json) -> (u16, Json) {
        let js = match args.get("js") {
            None | Some(Json::Null) => false,
            Some(Json::Bool(b)) => *b,
            _ => return (400, err_json("js must be a boolean")),
        };
        let vars = match args.get("vars") {
            None | Some(Json::Null) => Vec::new(),
            Some(Json::Obj(pairs)) => {
                let mut v = Vec::with_capacity(pairs.len());
                for (k, val) in pairs {
                    match val {
                        Json::Str(s) => v.push((k.clone(), s.clone())),
                        _ => return (400, err_json("vars values must be strings")),
                    }
                }
                v
            }
            _ => return (400, err_json("vars must be an object")),
        };

        let mut map = self.sessions.lock().unwrap();
        if map.len() >= MAX_SESSIONS {
            // LRU evict: dropping the handle closes the channel, the worker
            // thread exits, the session dies with it.
            let victim = map
                .iter()
                .map(|(id, h)| (*id, h.meta.lock().unwrap().last_used))
                .min_by_key(|(_, t)| *t)
                .map(|(id, _)| id);
            if let Some(id) = victim {
                map.remove(&id);
            }
        }
        let id = self.next.fetch_add(1, Ordering::Relaxed);
        let (tx, rx) = channel::<Req>();
        let meta = Arc::new(Mutex::new(Meta {
            url: None,
            status: 0,
            js,
            last_used: Instant::now(),
        }));
        let m2 = meta.clone();
        std::thread::spawn(move || session_worker(rx, m2, js, vars));
        map.insert(id, Handle { tx, meta });
        (200, Json::Obj(vec![("id".into(), Json::Num(id as f64))]))
    }

    fn delete_session(&self, id: u64) -> (u16, Json) {
        match self.sessions.lock().unwrap().remove(&id) {
            Some(_) => (200, Json::Obj(vec![("ok".into(), Json::Bool(true))])),
            None => (404, err_json("unknown session")),
        }
    }

    fn list_sessions(&self) -> Json {
        let map = self.sessions.lock().unwrap();
        let mut ids: Vec<u64> = map.keys().copied().collect();
        ids.sort_unstable();
        Json::Arr(
            ids.iter()
                .map(|id| {
                    let m = map[id].meta.lock().unwrap();
                    Json::Obj(vec![
                        ("id".into(), Json::Num(*id as f64)),
                        (
                            "url".into(),
                            m.url.clone().map(Json::Str).unwrap_or(Json::Null),
                        ),
                        ("status".into(), Json::Num(m.status as f64)),
                        ("js".into(), Json::Bool(m.js)),
                    ])
                })
                .collect(),
        )
    }

    /// Ship an op to a session worker and wait for its (status, body).
    /// Shared entry point for REST paths and MCP tools/call.
    fn call_op(&self, id: u64, name: &str, args: Json) -> (u16, Json) {
        let tx = self.sessions.lock().unwrap().get(&id).map(|h| h.tx.clone());
        let Some(tx) = tx else {
            return (404, err_json("unknown session"));
        };
        let (rtx, rrx) = channel();
        let req = Req {
            name: name.to_string(),
            args,
            reply: rtx,
        };
        if tx.send(req).is_err() {
            return (404, err_json("unknown session"));
        }
        match rrx.recv() {
            Ok(r) => r,
            Err(_) => (500, err_json("session worker died")),
        }
    }
}

/// The worker: owns Session for its whole life, serially serving ops until
/// the handle is dropped (delete/evict/shutdown), then exits.
fn session_worker(
    rx: Receiver<Req>,
    meta: Arc<Mutex<Meta>>,
    js: bool,
    vars: Vec<(String, String)>,
) {
    let mut sess = Session {
        jar: CookieJar::new(),
        page: None,
        interp: None,
        interp_globals: false,
        js,
        vars,
    };
    while let Ok(req) = rx.recv() {
        meta.lock().unwrap().last_used = Instant::now();
        let res = match op(&mut sess, &req.name, &req.args) {
            Ok(j) => (200, j),
            Err((st, msg)) => (st, err_json(&msg)),
        };
        {
            let mut m = meta.lock().unwrap();
            m.last_used = Instant::now();
            if let Some(p) = &sess.page {
                m.url = Some(p.url.to_string());
                m.status = p.status;
            }
        }
        let _ = req.reply.send(res);
    }
}

type OpResult = Result<Json, (u16, String)>;

fn bad(msg: impl Into<String>) -> (u16, String) {
    (400, msg.into())
}

/// The one op dispatcher both REST and MCP funnel through.
fn op(sess: &mut Session, name: &str, args: &Json) -> OpResult {
    match name {
        "snap" => {
            let url = arg_str(args, "url")?.to_string();
            let res = vigia_net::fetch(&url, &mut sess.jar)
                .map_err(|e| bad(format!("fetch failed: {e}")))?;
            Ok(finish_load(sess, res))
        }
        "click" => {
            let n = arg_ref(args, "ref")?;
            let res = {
                let p = sess.page.as_ref().ok_or((409, NO_PAGE.into()))?;
                vigia_actions::click(&p.dom, &p.url, n, &[], &mut sess.jar)
                    .map_err(|e| bad(format!("click failed: {e}")))?
            };
            Ok(finish_load(sess, res))
        }
        "fill" => {
            let n = arg_ref(args, "ref")?;
            let v = arg_str(args, "value")?.to_string();
            let p = sess.page.as_mut().ok_or((409, NO_PAGE.into()))?;
            vigia_actions::fill(&mut p.dom, n, &v).map_err(|e| bad(e.to_string()))?;
            Ok(Json::Obj(vec![("ok".into(), Json::Bool(true))]))
        }
        "submit" => {
            let form = match args.get("form") {
                None | Some(Json::Null) => None,
                Some(Json::Str(s)) => Some(s.clone()),
                _ => return Err(bad("form must be a string")),
            };
            let data = match args.get("data") {
                None | Some(Json::Null) => Vec::new(),
                Some(Json::Obj(pairs)) => pairs
                    .iter()
                    .map(|(k, v)| match v {
                        Json::Str(s) => Ok((k.clone(), s.clone())),
                        Json::Num(_) | Json::Bool(_) => Ok((k.clone(), v.to_string())),
                        _ => Err(bad("data values must be scalars")),
                    })
                    .collect::<Result<_, _>>()?,
                _ => return Err(bad("data must be an object")),
            };
            let res = {
                let p = sess.page.as_ref().ok_or((409, NO_PAGE.into()))?;
                vigia_actions::submit_form(&p.dom, &p.url, form.as_deref(), &data, &mut sess.jar)
                    .map_err(|e| bad(format!("submit failed: {e}")))?
            };
            Ok(finish_load(sess, res))
        }
        "extract" => {
            let css = arg_str(args, "css")?;
            let p = sess.page.as_ref().ok_or((409, NO_PAGE.into()))?;
            let hits = vigia_css::query(&p.dom, css).map_err(|e| bad(e.to_string()))?;
            let refs = vigia_snapshot::interactive_refs(&p.dom);
            let nodes = hits
                .iter()
                .map(|id| {
                    let r = refs
                        .iter()
                        .position(|r| r == id)
                        .map(|i| i + 1)
                        .unwrap_or(0);
                    let role = match &p.dom.node(*id).data {
                        NodeData::Element(el) => {
                            let tag = p.dom.interner.resolve(el.tag);
                            vigia_snapshot::role_of(tag, &el.attrs, &p.dom)
                        }
                        _ => "text".into(),
                    };
                    let text: String = vigia_actions::text_content(&p.dom, *id)
                        .chars()
                        .take(120)
                        .collect();
                    Json::Obj(vec![
                        ("ref".into(), Json::Num(r as f64)),
                        ("role".into(), Json::Str(role)),
                        ("text".into(), Json::Str(text)),
                    ])
                })
                .collect();
            Ok(Json::Obj(vec![("nodes".into(), Json::Arr(nodes))]))
        }
        "eval" => op_eval(sess, arg_str(args, "code")?),
        "run" => op_run(sess, arg_str(args, "script")?),
        "net" => {
            // fetch() calls the page's JS made, Puppeteer
            // page.on('request'/'response') style - endpoint discovery.
            let p = sess.page.as_ref().ok_or((400, NO_PAGE.to_string()))?;
            let events = p
                .net_events
                .iter()
                .map(|e| {
                    Json::Obj(vec![
                        ("method".into(), Json::Str(e.method.clone())),
                        ("url".into(), Json::Str(e.url.clone())),
                        ("status".into(), Json::Num(e.status as f64)),
                        (
                            "req_body".into(),
                            e.req_body.clone().map(Json::Str).unwrap_or(Json::Null),
                        ),
                        (
                            "resp_body".into(),
                            e.resp_body.clone().map(Json::Str).unwrap_or(Json::Null),
                        ),
                        (
                            "error".into(),
                            e.error.clone().map(Json::Str).unwrap_or(Json::Null),
                        ),
                    ])
                })
                .collect();
            Ok(Json::Obj(vec![("events".into(), Json::Arr(events))]))
        }
        _ => Err((404, "unknown op".into())),
    }
}

/// Perform a JS-captured form submit (mirrors submit_node semantics).
fn follow_submit(
    sub: &vigia_js::PendingSubmit,
    jar: &mut CookieJar,
) -> Result<vigia_net::Response, String> {
    let url = Url::parse(&sub.url).map_err(|e| e.to_string())?;
    let encoded = vigia_actions::urlencode(&sub.fields);
    if sub.method == "post" {
        vigia_net::post_form(&url, &encoded, jar).map_err(|e| e.to_string())
    } else {
        let u = if sub.fields.is_empty() {
            url
        } else {
            Url {
                query: Some(encoded),
                ..url
            }
        };
        vigia_net::fetch(&u.to_string(), jar).map_err(|e| e.to_string())
    }
}

/// Parse + optional script run over one response. When the session's `js`
/// flag is on, a fresh Interp runs the page <script>s (returned so the
/// session can keep it for eval); pending_nav is followed once, matching
/// the CLI bridge. Returns (page, interp, js warnings/errors as strings).
fn load_page(
    res: vigia_net::Response,
    js: bool,
    jar: &mut CookieJar,
) -> (Page, Option<vigia_js::Interp>, Vec<String>) {
    load_follow(res, js, jar, true)
}

fn load_follow(
    res: vigia_net::Response,
    js: bool,
    jar: &mut CookieJar,
    follow: bool,
) -> (Page, Option<vigia_js::Interp>, Vec<String>) {
    let mut dom = Dom::new();
    vigia_html::parse(&res.text(), &mut dom);
    let mut errs = Vec::new();
    let mut interp = None;
    let mut net_events = Vec::new();
    if js {
        let mut it = vigia_js::Interp::new();
        let trace = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
        // The jar moves in for the script run and comes back in the outcome,
        // so page fetch() calls share cookies.
        let out = it.run_scripts(
            dom,
            Some(vigia_js::NetCtx {
                base: res.final_url.clone(),
                jar: std::mem::take(jar),
                trace: Some(trace.clone()),
            }),
        );
        dom = out.dom;
        net_events = trace.borrow().clone();
        if let Some(j) = out.jar {
            *jar = j;
        }
        errs = out.errors.iter().map(|e| e.to_string()).collect();
        interp = Some(it);
        // v1 navigation bridge: a script's click() asked for a page -
        // follow it once, no chains.
        if let Some(nav) = out.pending_nav {
            if follow {
                match vigia_net::fetch(&nav, jar) {
                    Ok(res2) => {
                        let (p2, it2, e2) = load_follow(res2, js, jar, false);
                        errs.extend(e2);
                        return (p2, it2, errs);
                    }
                    Err(e) => errs.push(format!("js nav {nav}: {e}")),
                }
            } else {
                errs.push(format!("js: navigation to {nav} not followed"));
            }
        }
        // Same bridge for form.submit() / __doPostBack.
        if let Some(sub) = out.pending_submit {
            if follow {
                match follow_submit(&sub, jar) {
                    Ok(res2) => {
                        let (p2, it2, e2) = load_follow(res2, js, jar, false);
                        errs.extend(e2);
                        return (p2, it2, errs);
                    }
                    Err(e) => errs.push(format!("js submit {}: {e}", sub.url)),
                }
            } else {
                errs.push(format!("js: form submit to {} not followed", sub.url));
            }
        }
    }
    (
        Page {
            dom,
            url: res.final_url,
            status: res.status,
            net_events,
        },
        interp,
        errs,
    )
}

/// Store the fetched page + its interp on the session, emit the standard
/// {status, url, snapshot} body. `js_errors` appears only when non-empty.
fn finish_load(sess: &mut Session, res: vigia_net::Response) -> Json {
    let (page, interp, errs) = load_page(res, sess.js, &mut sess.jar);
    if let Some(it) = interp {
        sess.interp = Some(it);
        sess.interp_globals = true;
    }
    let mut fields = vec![
        ("status".into(), Json::Num(page.status as f64)),
        ("url".into(), Json::Str(page.url.to_string())),
        (
            "snapshot".into(),
            Json::Str(vigia_snapshot::snapshot(&page.dom)),
        ),
    ];
    if !errs.is_empty() {
        fields.push((
            "js_errors".into(),
            Json::Arr(errs.into_iter().map(Json::Str).collect()),
        ));
    }
    sess.page = Some(page);
    Json::Obj(fields)
}

/// JS in the session's Interp (created lazily). With a live page the dom is
/// installed before eval and taken back after, so DOM mutations persist
/// into session.page.dom; the jar rides along so eval'd fetch() shares
/// cookies. An interp that already ran page scripts gets the dom via direct
/// assignment, keeping its listeners/wrapper cache; a fresh one needs
/// set_dom for the document/window globals.
fn op_eval(sess: &mut Session, code: &str) -> OpResult {
    let it = sess.interp.get_or_insert_with(vigia_js::Interp::new);
    let has_page = sess.page.is_some();
    if has_page {
        let p = sess.page.as_mut().unwrap();
        let dom = std::mem::take(&mut p.dom);
        if sess.interp_globals {
            it.pending_nav = None;
            it.dom = Some(dom);
        } else {
            it.set_dom(dom);
            sess.interp_globals = true;
        }
        let trace = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
        it.net = Some(vigia_js::NetCtx {
            base: p.url.clone(),
            jar: std::mem::take(&mut sess.jar),
            trace: Some(trace.clone()),
        });
    }
    let r = it.run(code);
    if has_page {
        let p = sess.page.as_mut().unwrap();
        p.dom = it.take_dom();
        if let Some(ctx) = it.net.take() {
            sess.jar = ctx.jar;
            // fetch() calls made during eval join the page's trace.
            if let Some(t) = ctx.trace {
                p.net_events.extend(t.borrow().iter().cloned());
            }
        }
    }
    match r {
        Ok(v) => Ok(Json::Obj(vec![("result".into(), Json::Str(it.inspect(v)))])),
        Err(e) => Err(bad(format!("js: {e}"))),
    }
}

/// A .vig script over the session jar (and its `js` flag). The script
/// drives its own page state internally; session.page is left as-is.
/// Output is captured into `out`, the audit trail comes back as JSON.
fn op_run(sess: &mut Session, src: &str) -> OpResult {
    let stmts = vigia_run::parse_script(src)
        .map_err(|e| bad(format!("run failed at line {}: {}", e.0, e.1)))?;
    let stmts = subst_stmts(&stmts, &sess.vars);
    let mut audit = Vec::new();
    let mut out = String::new();
    let mut emit = |s: &str| {
        out.push_str(s);
        if !s.ends_with('\n') {
            out.push('\n');
        }
    };
    let result = vigia_run::run_with(&stmts, &mut sess.jar, &mut audit, &mut emit, sess.js);
    let audit_json: Vec<Json> = audit.iter().map(audit_json).collect();
    match result {
        Ok(()) => Ok(Json::Obj(vec![
            ("out".into(), Json::Str(out)),
            ("audit".into(), Json::Arr(audit_json)),
        ])),
        // runtime failure is a completed call, not bad input: 200 + ok:false
        Err(e) => Ok(Json::Obj(vec![
            ("ok".into(), Json::Bool(false)),
            ("error".into(), Json::Str(format!("line {}: {}", e.0, e.1))),
            ("out".into(), Json::Str(out)),
            ("audit".into(), Json::Arr(audit_json)),
        ])),
    }
}

fn audit_json(e: &vigia_run::AuditEntry) -> Json {
    Json::Obj(vec![
        ("line".into(), Json::Num(e.line as f64)),
        ("op".into(), Json::Str(e.op.into())),
        ("arg".into(), Json::Str(e.arg.clone())),
        ("status".into(), Json::Num(e.status as f64)),
        ("ms".into(), Json::Num((e.ms * 1000.0).round() / 1000.0)),
        ("ok".into(), Json::Bool(e.ok)),
    ])
}

// --- $VAR substitution: same semantics as vigia-run's private resolve(),
// duplicated here because run_with takes already-substituted stmts. ---

fn lookup(name: &str, vars: &[(String, String)]) -> Option<String> {
    vars.iter()
        .find(|(k, _)| k == name)
        .map(|(_, v)| v.clone())
        .or_else(|| std::env::var(format!("VIGIA_{name}")).ok())
}

/// Resolve `$NAME` / `${NAME}` in `arg`; `$$` is a literal `$`, unknown
/// names stay literal.
fn resolve(arg: &str, vars: &[(String, String)]) -> String {
    let mut out = String::with_capacity(arg.len());
    let b = arg.as_bytes();
    let mut i = 0;
    while i < arg.len() {
        if b[i] != b'$' {
            let next = arg[i + 1..]
                .find('$')
                .map(|j| i + 1 + j)
                .unwrap_or(arg.len());
            out.push_str(&arg[i..next]);
            i = next;
            continue;
        }
        let after = &arg[i + 1..];
        if after.starts_with('$') {
            out.push('$');
            i += 2;
            continue;
        }
        let (name, end) = if let Some(braced) = after.strip_prefix('{') {
            match braced.find('}') {
                Some(j) if j > 0 => (&braced[..j], i + 3 + j),
                _ => {
                    out.push('$');
                    i += 1;
                    continue;
                }
            }
        } else {
            let n: usize = after
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .map(char::len_utf8)
                .sum();
            if n == 0 {
                out.push('$');
                i += 1;
                continue;
            }
            (&after[..n], i + 1 + n)
        };
        match lookup(name, vars) {
            Some(v) => out.push_str(&v),
            None => out.push_str(&arg[i..end]),
        }
        i = end;
    }
    out
}

/// Clone `stmts` with session vars resolved into every string arg.
fn subst_stmts(stmts: &[vigia_run::Stmt], vars: &[(String, String)]) -> Vec<vigia_run::Stmt> {
    if vars.is_empty() {
        return stmts.to_vec();
    }
    stmts
        .iter()
        .map(|s| vigia_run::Stmt {
            line: s.line,
            op: match &s.op {
                vigia_run::Op::Snap(u) => vigia_run::Op::Snap(resolve(u, vars)),
                vigia_run::Op::Click(n) => vigia_run::Op::Click(*n),
                vigia_run::Op::Fill(n, v) => vigia_run::Op::Fill(*n, resolve(v, vars)),
                vigia_run::Op::Submit { form, data } => vigia_run::Op::Submit {
                    form: form.as_ref().map(|f| resolve(f, vars)),
                    data: data
                        .iter()
                        .map(|(k, v)| (k.clone(), resolve(v, vars)))
                        .collect(),
                },
                vigia_run::Op::Extract(sel) => vigia_run::Op::Extract(resolve(sel, vars)),
                vigia_run::Op::Json(p) => vigia_run::Op::Json(p.as_ref().map(|p| resolve(p, vars))),
                vigia_run::Op::Expect(t) => vigia_run::Op::Expect(resolve(t, vars)),
                vigia_run::Op::Net => vigia_run::Op::Net,
                vigia_run::Op::Req {
                    url,
                    method,
                    headers,
                    body,
                } => vigia_run::Op::Req {
                    url: resolve(url, vars),
                    method: method.clone(),
                    headers: headers
                        .iter()
                        .map(|(k, v)| (k.clone(), resolve(v, vars)))
                        .collect(),
                    body: body.as_ref().map(|b| resolve(b, vars)),
                },
            },
        })
        .collect()
}

// --- request/response plumbing -------------------------------------------

struct Request {
    method: String,
    path: String,
    body: Vec<u8>,
}

/// One request per connection (Connection: close). Headers capped at 32KB,
/// body at 1MB. `Expect: 100-continue` is acked so curl doesn't stall.
fn read_request(stream: &mut TcpStream) -> Result<Request, (u16, String)> {
    let mut buf = Vec::with_capacity(8192);
    let mut chunk = [0u8; 8192];
    let head_end = loop {
        match stream.read(&mut chunk) {
            Ok(0) => return Err((400, "eof before headers".into())),
            Ok(n) => buf.extend_from_slice(&chunk[..n]),
            Err(e) => return Err((400, format!("read: {e}"))),
        }
        if let Some(p) = find_sub(&buf, b"\r\n\r\n") {
            break p;
        }
        if buf.len() > MAX_HEAD {
            return Err((400, "headers too large".into()));
        }
    };

    let head =
        std::str::from_utf8(&buf[..head_end]).map_err(|_| (400, "bad header utf-8".to_string()))?;
    let mut lines = head.split("\r\n");
    let rl = lines.next().unwrap_or("");
    let mut parts = rl.split_whitespace();
    let (Some(method), Some(target), Some(version)) = (parts.next(), parts.next(), parts.next())
    else {
        return Err((400, "bad request line".into()));
    };
    if !version.starts_with("HTTP/") || parts.next().is_some() {
        return Err((400, "bad request line".into()));
    }
    let method = method.to_string();
    let target = target.to_string();

    let mut content_len = 0usize;
    let mut chunked = false;
    let mut expect_continue = false;
    for line in lines {
        if line.is_empty() {
            continue;
        }
        let Some((k, v)) = line.split_once(':') else {
            return Err((400, "bad header line".into()));
        };
        match k.trim().to_ascii_lowercase().as_str() {
            "content-length" => {
                content_len = v
                    .trim()
                    .parse()
                    .map_err(|_| (400, "bad content-length".to_string()))?;
                if content_len > MAX_BODY {
                    return Err((413, "body too large".into()));
                }
            }
            "transfer-encoding" => chunked = true,
            "expect" => expect_continue = v.trim().eq_ignore_ascii_case("100-continue"),
            _ => {}
        }
    }
    if chunked {
        return Err((400, "chunked bodies not supported".into()));
    }
    if expect_continue {
        let _ = stream.write_all(b"HTTP/1.1 100 Continue\r\n\r\n");
    }

    let mut body = buf.split_off(head_end + 4);
    while body.len() < content_len {
        match stream.read(&mut chunk) {
            Ok(0) => return Err((400, "eof inside body".into())),
            Ok(n) => body.extend_from_slice(&chunk[..n]),
            Err(e) => return Err((400, format!("read: {e}"))),
        }
    }
    body.truncate(content_len);
    Ok(Request {
        method,
        path: target,
        body,
    })
}

fn find_sub(hay: &[u8], needle: &[u8]) -> Option<usize> {
    hay.windows(needle.len()).position(|w| w == needle)
}

fn write_response(stream: &mut TcpStream, status: u16, body: &str) {
    let reason = match status {
        200 => "OK",
        202 => "Accepted",
        400 => "Bad Request",
        404 => "Not Found",
        405 => "Method Not Allowed",
        409 => "Conflict",
        413 => "Payload Too Large",
        _ => "Internal Server Error",
    };
    let resp = format!(
        "HTTP/1.1 {status} {reason}\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{body}",
        body.len()
    );
    let _ = stream.write_all(resp.as_bytes());
    let _ = stream.flush();
}

// --- small json/http helpers ----------------------------------------------

fn err_json(msg: &str) -> Json {
    Json::Obj(vec![
        ("ok".into(), Json::Bool(false)),
        ("error".into(), Json::Str(msg.into())),
    ])
}

fn jsend(status: u16, j: Json) -> (u16, String) {
    (status, j.to_string())
}

fn jsend_pair((status, j): (u16, Json)) -> (u16, String) {
    (status, j.to_string())
}

/// Request body as a JSON object; empty body counts as `{}`.
fn body_obj(body: &[u8]) -> Result<Json, (u16, Json)> {
    if body.is_empty() {
        return Ok(Json::Obj(vec![]));
    }
    let text = std::str::from_utf8(body).map_err(|_| (400, err_json("body is not utf-8")))?;
    let j = Json::parse(text).map_err(|e| (400, err_json(&e.to_string())))?;
    match j {
        Json::Obj(_) => Ok(j),
        _ => Err((400, err_json("body must be a JSON object"))),
    }
}

fn arg_str<'a>(args: &'a Json, key: &str) -> Result<&'a str, (u16, String)> {
    match args.get(key) {
        Some(Json::Str(s)) => Ok(s),
        Some(_) => Err(bad(format!("{key} must be a string"))),
        None => Err(bad(format!("missing field: {key}"))),
    }
}

fn arg_ref(args: &Json, key: &str) -> Result<usize, (u16, String)> {
    match args.get(key) {
        Some(Json::Num(n)) if *n >= 0.0 && n.fract() == 0.0 => Ok(*n as usize),
        Some(_) => Err(bad(format!("{key} must be an integer"))),
        None => Err(bad(format!("missing field: {key}"))),
    }
}
