//! vigia-js: own JavaScript interpreter core (lexer, parser, tree-walk eval).
//! Pragmatic ES5-ish subset with DOM bindings (bindings.rs), prototype-based
//! property lookup, promises + a virtual-clock event loop.
//!
//! Values live in flat arenas (Heap::strs, Heap::objs, Interp::envs) so
//! the mark-sweep GC (gc.rs) can find roots without walking pointer
//! graphs. Rc appears only to share immutable AST bodies into Obj::Func.
//!
//! v1 semantic choices (deliberate deviations from full JS):
//! - `;` optional before `}`, EOF, or a newline-separated token (ASI-lite).
//! - `var` hoists to function scope (undefined until assigned);
//!   `let`/`const` stay block-scoped; sloppy block-level `function`
//!   declarations mirror into function scope (Annex B).
//! - Function declarations hoist within their block.
//! - `this` bound for `o.m()` and `o[i]()` calls, else undefined.
//! - Assignment to an undeclared name creates a global (sloppy mode).
//! - Prototypes: Ordinary/Arr/Func carry `proto`; Promise carries none
//!   (Promise.prototype via a virtual fallback, same as Native ->
//!   Function.prototype). `Func`/`Native` carry `pairs` (own props) so
//!   functions can expose `.prototype` and constructor globals (Object,
//!   Date, ...) their statics; every Obj::Func gets a fresh own "prototype"
//!   object at creation.
//! - `new F()`: proto = F.prototype when it's an object else Object's proto;
//!   `new` on a Native just calls it (ctors allocate their own result).
//!   `new` callee is primary + member chain: `new a.b()` is New(Member a.b).
//! - Supported beyond ES5: ?. ?? => arrow fns, for-of/in over
//!   arrays/strings/keys, regex literals + RegExp
//!   (test/exec/match/replace/split/search), template literals (untagged),
//!   ... spread in calls/arrays/objects, rest params, comma operator,
//!   default params, destructuring in var/let/const, switch, do-while,
//!   void, method/get/set shorthand in literals, Symbol, Map/Set/WeakMap,
//!   Object.freeze/defineProperty.
//! - No classes, logical assignment, **, delete, computed keys, labels,
//!   generators, BigInt, dynamic import, __proto__ accessor.
//! - Events: addEventListener + inline `on*` attrs, bubble phase only
//!   (no capture). Dispatch is synchronous.
//! - Async (synchronous engine, real semantics where the model allows):
//!   `new Promise(executor)` runs the executor inline; then/catch/finally
//!   handlers and queueMicrotask callbacks run as microtasks at drain
//!   points: the end of each top-level run() and after each fire() event
//!   dispatch (the latter flushes early when the event was dispatched
//!   mid-script - browsers would wait for the stack to unwind).
//!   Timers (setTimeout/setInterval) run on a virtual clock: drain fires
//!   the earliest deadline next, advancing now_ms to it without sleeping,
//!   so every queued timer completes before run() returns. Caps: 4096
//!   timer fires per drain, microtask throughput bounded by max_steps.
//!   resolve(promise) adopts its state; non-Promise thenables are not
//!   adopted. Promise rejection reasons are plain values; a handler's
//!   `throw` rejects with the thrown value verbatim, an internal error
//!   with its message text.
//! - async/await: `async function` bodies run synchronously and wrap the
//!   result into a promise (returned promise values are adopted). `await`
//!   on a Fulfilled promise unwraps; Rejected throws the reason value;
//!   Pending is an error - no suspension exists because everything
//!   resolvable is settled eagerly. `await` outside an async fn is an
//!   eval error (the parser accepts it for grammar simplicity).
//! - Errors: throw/try/catch/finally, plus an `Error` builtin (name,
//!   message, toString - no `stack`). A catch param binds thrown values
//!   verbatim; internal errors materialize as Error objects so
//!   `e instanceof Error` and `e.message` work. `finally` runs on every
//!   exit (normal, throw, return, break) and its own abrupt completion
//!   wins. Runaway guards (steps, call depth, heap/env caps) are Fatal:
//!   catch never sees them, finally still runs before they propagate.
//! - fetch() performs the HTTP request eagerly at call time and returns a
//!   resolved Promise holding the response object; network failures give
//!   a rejected Promise (real fetch semantics). Response text()/json()
//!   also return resolved Promises, so both `await r.json()` and
//!   `r.json().then(f)` work. A rejected promise never then'd/caught
//!   reports "unhandled rejection" into the drain error list.
//! - el.click() on <a href> sets pending_nav + location.href instead of
//!   navigating; following it is the host's call.

use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;

use vigia_dom::NodeId;

mod ast;
mod bindings;
mod eval;
mod gc;
mod lex;
mod parse;
pub mod regex;

pub use ast::{Expr, FnDef, Stmt};
pub use bindings::ScriptsOutcome;
pub use gc::GcStats;
pub use parse::parse_program as parse;

/// Interpreter error. `Msg` is an internal (catchable) error; `Throw`
/// carries a script `throw`'s value verbatim; `Fatal` is a runaway-guard
/// stop (steps/call-depth/heap/env caps) that catch clauses never see -
/// it still passes through finally blocks.
#[derive(Debug)]
pub enum JsError {
    Msg(String),
    Throw(Value),
    Fatal(String),
}

impl JsError {
    /// try/catch intercepts only Msg and Throw.
    pub(crate) fn catchable(&self) -> bool {
        !matches!(self, JsError::Fatal(_))
    }
}

impl std::fmt::Display for JsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            JsError::Msg(m) | JsError::Fatal(m) => write!(f, "{m}"),
            // a Throw reaching Display skipped boundary normalization
            JsError::Throw(v) => write!(f, "uncaught throw: {v:?}"),
        }
    }
}
impl std::error::Error for JsError {}

pub(crate) fn err(msg: impl Into<String>) -> JsError {
    JsError::Msg(msg.into())
}

/// Runaway-guard stop: never intercepted by catch clauses.
pub(crate) fn fatal(msg: impl Into<String>) -> JsError {
    JsError::Fatal(msg.into())
}

/// JS value. Str/Obj are arena indices into Heap, not pointers.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Value {
    Undef,
    Null,
    Bool(bool),
    Num(f64),
    Str(u32),
    Obj(u32),
}

/// Element kind of a Typed view (everything but Uint8Array, which has
/// its own byte-packed variant).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypedKind {
    I8,
    U8C,
    U16,
    I16,
    U32,
    I32,
    F32,
    F64,
}

/// Builtin function signature: interpreter access, the receiver (`this`),
/// and already-evaled args.
pub type NativeFn = fn(&mut Interp, this: Value, &[Value]) -> Result<Value, JsError>;

/// One page-JS fetch() call, as Puppeteer's page.on('request'/'response')
/// pair collapses into here: method + resolved url going out, status +
/// bodies coming back. Bodies are truncated - the trace is for endpoint
/// discovery and payload shape, not bulk capture.
#[derive(Debug, Clone)]
pub struct NetEvent {
    pub method: String,
    pub url: String,
    /// HTTP status; 0 when the request never got a response.
    pub status: u16,
    pub req_body: Option<String>,
    pub resp_body: Option<String>,
    pub error: Option<String>,
}

/// Page network context for a script run: the URL the DOM came from
/// (resolves relative fetch()/click() targets) plus the cookie jar. The
/// jar is moved in for the run and handed back through ScriptsOutcome -
/// no pointers, no lifetimes. `trace`, when installed, records every
/// fetch() the page's JS makes so the host can list them.
pub struct NetCtx {
    pub base: vigia_url::Url,
    pub jar: vigia_session::CookieJar,
    pub trace: Option<std::rc::Rc<std::cell::RefCell<Vec<NetEvent>>>>,
}

#[derive(Debug)]
pub enum Obj {
    /// property map, insertion order; proto = heap obj id, None = null proto
    Ordinary {
        pairs: Vec<(String, Value)>,
        proto: Option<u32>,
    },
    Arr {
        items: Vec<Value>,
        proto: Option<u32>,
        /// Expando props (`arr.foo = 1`, webpack's `arr.push = ...`).
        /// Indices and `length` live in items, never here.
        pairs: Vec<(String, Value)>,
    },
    /// def carries params+body shared via Rc; env is the captured EnvId.
    /// pairs holds own props ("prototype" is populated at creation).
    Func {
        def: Rc<FnDef>,
        env: u32,
        proto: Option<u32>,
        pairs: Vec<(String, Value)>,
    },
    /// name+f; pairs holds own props (ctor statics, "prototype"). No proto
    /// field: get_prop falls back to Function.prototype for Natives.
    Native {
        name: &'static str,
        f: NativeFn,
        pairs: Vec<(String, Value)>,
    },
    /// JS handle over a DOM node; valid only while Interp.dom is installed.
    /// `proto` is the virtual prototype by node kind (Element nodes answer
    /// HTMLElement.prototype, the document answers Document.prototype),
    /// so instanceof/getPrototypeOf work without a proto slot in the DOM.
    Dom {
        node: NodeId,
        proto: Option<u32>,
    },
    /// Live CSS declaration block for an element: reads/writes go to the
    /// element's `style` attribute on every access (no cached copy).
    Style { node: NodeId },
    /// Accessor property value (`get x()`/`set x(v)` in literals, and
    /// later class prototypes): invoked on read/write, never exposed.
    Accessor {
        get: Option<u32>,
        set: Option<u32>,
        proto: Option<u32>,
    },
    /// Symbol primitive (boxed): `desc` is an optional Str id. Identity
    /// is the obj id; `Symbol.for` keeps a registry for stability.
    Symbol {
        desc: Option<u32>,
        proto: Option<u32>,
    },
    /// Map entries in insertion order (SameValueZero keys).
    Map {
        entries: Vec<(Value, Value)>,
        proto: Option<u32>,
    },
    /// Set items in insertion order.
    Set {
        items: Vec<Value>,
        proto: Option<u32>,
    },
    /// WeakMap without weakness: entries live forever, no iteration.
    WeakMap {
        entries: Vec<(Value, Value)>,
        proto: Option<u32>,
    },
    /// Compiled regex: `pat`/`flags` are Str ids (GC roots), `last_index`
    /// counts chars (not bytes). The compiled AST is immutable Rust data.
    RegExp {
        pat: u32,
        flags: u32,
        last_index: f64,
        compiled: Rc<regex::Compiled>,
        proto: Option<u32>,
    },
    /// Promise cell; Promise.prototype is a virtual proto (proto_of).
    /// `pairs` holds expandos (deferred resolve/reject helpers) - V8
    /// promises are extensible.
    Promise {
        st: PromiseState,
        pairs: Vec<(String, Value)>,
    },
    /// Uint8Array bytes (+ expando pairs); no shared memory - views over
    /// buffers and subarray()/slice() copy (documented gap).
    Bytes {
        bytes: Vec<u8>,
        pairs: Vec<(String, Value)>,
        proto: Option<u32>,
    },
    /// Other numeric views (elements pre-coerced to f64, so reads are
    /// exact; f32 coerces through `as f32` on write). Copies like Bytes.
    Typed {
        kind: TypedKind,
        elems: Vec<f64>,
        pairs: Vec<(String, Value)>,
        proto: Option<u32>,
    },
    /// DataView over a buffer copy (+ base byteOffset for the offset
    /// form); multi-byte accessors honor the littleEndian flag.
    DView {
        bytes: Vec<u8>,
        off: usize,
        proto: Option<u32>,
    },
    /// ArrayBuffer backing store (non-extensible: writes to named props
    /// are sloppy no-ops).
    Buf { bytes: Vec<u8>, proto: Option<u32> },
    /// Forwarding proxy: reads/writes go to `target` unless `handler`
    /// defines the matching trap (`get`/`set`/`has`/`deleteProperty`,
    /// run at the recv_ level). Free-fn paths (proto chains, keys,
    /// JSON, descriptors) forward transparently; `ownKeys` /
    /// `getOwnPropertyDescriptor` / `getPrototypeOf` / `apply` /
    /// `construct` traps are documented gaps (forwarded, not run).
    Proxy { target: u32, handler: u32 },
    /// GC tombstone: a swept slot awaiting freelist reuse. Reads on a
    /// dangling id see an empty, proto-less object instead of stale data.
    Freed,
}

/// Promise lifecycle. Handlers registered while Pending flush into the
/// microtask queue on settle; a settled promise's `then` enqueues directly.
#[derive(Debug)]
pub enum PromiseState {
    Pending { handlers: Vec<ThenHandler> },
    Fulfilled(Value),
    Rejected(Value),
}

/// One `.then` registration. A missing handler passes the settlement
/// through untouched (so `then(None, onR)` and promise adoption both
/// work). `next` is the promise obj id the handler's result resolves;
/// u32::MAX = no downstream promise (internal subscriptions like all()).
#[derive(Debug, Clone, Copy)]
pub struct ThenHandler {
    pub on_fulfill: Option<Value>,
    pub on_reject: Option<Value>,
    pub next: u32,
}

/// A queued callback: cb runs with `arg`; its result resolves `next`
/// (u32::MAX = fire-and-forget, errors go to the drain error list).
/// cb = None is a settlement pass-through: settle `next` with `arg`
/// keeping the `rejecting` direction.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Microtask {
    pub cb: Option<Value>,
    pub arg: Value,
    pub next: u32,
    pub rejecting: bool,
}

/// setTimeout/setInterval entry on the virtual clock. `interval` Some =
/// repeating; `cancelled` is set by clearTimeout/clearInterval; `parked`
/// marks the timer currently mid-callback so a nested drain (event
/// dispatch inside the cb) can't re-fire it.
#[derive(Debug)]
pub(crate) struct Timer {
    pub id: u32,
    pub deadline_ms: u64,
    pub cb: Value,
    pub args: Vec<Value>,
    pub interval: Option<u64>,
    pub cancelled: bool,
    pub parked: bool,
}

/// Well-known prototype objects (heap ids), allocated once per Interp.
/// u32::MAX = not installed (heap-cap edge during Interp::new).
/// `number`/`date` go beyond the minimal four so Number.prototype.toFixed
/// and Date.prototype methods have somewhere to live.
#[derive(Clone, Copy)]
pub struct Protos {
    pub object: u32,
    pub array: u32,
    pub function_: u32,
    pub string: u32,
    pub number: u32,
    pub date: u32,
    pub promise: u32,
    pub error: u32,
    pub regexp: u32,
    pub symbol: u32,
    pub map: u32,
    pub set: u32,
    pub weakmap: u32,
    pub url: u32,
    pub uint8array: u32,
    pub buffer: u32,
    pub dataview: u32,
    pub int8array: u32,
    pub uint8clampedarray: u32,
    pub uint16array: u32,
    pub int16array: u32,
    pub uint32array: u32,
    pub int32array: u32,
    pub float32array: u32,
    pub float64array: u32,
    pub textencoder: u32,
    pub textdecoder: u32,
    pub dom_node: u32,
    pub dom_element: u32,
    pub dom_htmlelement: u32,
    pub dom_document: u32,
    pub dom_shadowroot: u32,
    pub dom_documentfragment: u32,
    pub dom_input: u32,
    pub dom_form: u32,
    pub dom_select: u32,
    pub dom_textarea: u32,
    pub dom_button: u32,
    pub dom_anchor: u32,
    pub dom_image: u32,
    pub dom_iframe: u32,
    pub dom_svg: u32,
}

impl Protos {
    fn none() -> Self {
        Protos {
            object: u32::MAX,
            array: u32::MAX,
            function_: u32::MAX,
            string: u32::MAX,
            number: u32::MAX,
            date: u32::MAX,
            promise: u32::MAX,
            error: u32::MAX,
            regexp: u32::MAX,
            symbol: u32::MAX,
            map: u32::MAX,
            set: u32::MAX,
            weakmap: u32::MAX,
            url: u32::MAX,
            uint8array: u32::MAX,
            buffer: u32::MAX,
            dataview: u32::MAX,
            int8array: u32::MAX,
            uint8clampedarray: u32::MAX,
            uint16array: u32::MAX,
            int16array: u32::MAX,
            uint32array: u32::MAX,
            int32array: u32::MAX,
            float32array: u32::MAX,
            float64array: u32::MAX,
            textencoder: u32::MAX,
            textdecoder: u32::MAX,
            dom_node: u32::MAX,
            dom_element: u32::MAX,
            dom_htmlelement: u32::MAX,
            dom_document: u32::MAX,
            dom_shadowroot: u32::MAX,
            dom_documentfragment: u32::MAX,
            dom_input: u32::MAX,
            dom_form: u32::MAX,
            dom_select: u32::MAX,
            dom_textarea: u32::MAX,
            dom_button: u32::MAX,
            dom_anchor: u32::MAX,
            dom_image: u32::MAX,
            dom_iframe: u32::MAX,
            dom_svg: u32::MAX,
        }
    }
}

/// u32::MAX sentinel -> None (proto not installed).
pub(crate) fn po(p: u32) -> Option<u32> {
    if p == u32::MAX {
        None
    } else {
        Some(p)
    }
}

/// Value arena. `cap` is a hard limit on live slots (objs + strs). The
/// Vecs never shrink (ids are indices); GC-freed slots tombstone in place
/// and wait on the freelists for reuse.
pub struct Heap {
    /// None = swept tombstone. Interned entries are marked every GC, so a
    /// live intern id always maps to a live slot.
    pub(crate) strs: Vec<Option<String>>,
    pub(crate) objs: Vec<Obj>,
    /// literal -> str arena id; ids here are GC roots.
    pub(crate) intern: HashMap<String, u32>,
    pub(crate) free_objs: Vec<u32>,
    pub(crate) free_strs: Vec<u32>,
    pub(crate) cap: usize,
}

impl Heap {
    pub fn new() -> Self {
        Self::with_cap(1_000_000)
    }

    pub fn with_cap(cap: usize) -> Self {
        Heap {
            strs: Vec::new(),
            objs: Vec::new(),
            intern: HashMap::new(),
            free_objs: Vec::new(),
            free_strs: Vec::new(),
            cap,
        }
    }

    /// Live slots = allocated slots minus freelist entries.
    pub(crate) fn live(&self) -> usize {
        self.objs.len() - self.free_objs.len() + self.strs.len() - self.free_strs.len()
    }

    fn room(&self) -> Result<(), JsError> {
        if self.live() >= self.cap {
            Err(fatal("heap cap"))
        } else {
            Ok(())
        }
    }

    /// Runtime (non-literal) string. No dedup.
    pub fn alloc_str(&mut self, s: String) -> Result<u32, JsError> {
        if let Some(id) = self.free_strs.pop() {
            self.strs[id as usize] = Some(s);
            return Ok(id);
        }
        self.room()?;
        self.strs.push(Some(s));
        Ok(self.strs.len() as u32 - 1)
    }

    /// Source-literal strings dedupe so loops re-evaluating the same
    /// literal don't burn a slot per iteration.
    pub fn intern_str(&mut self, s: &str) -> Result<u32, JsError> {
        if let Some(&id) = self.intern.get(s) {
            debug_assert!(self.strs[id as usize].is_some(), "interned str swept");
            return Ok(id);
        }
        let id = self.alloc_str(s.to_string())?;
        self.intern.insert(s.to_string(), id);
        Ok(id)
    }

    pub fn alloc_obj(&mut self, o: Obj) -> Result<u32, JsError> {
        if let Some(id) = self.free_objs.pop() {
            self.objs[id as usize] = o;
            return Ok(id);
        }
        self.room()?;
        self.objs.push(o);
        Ok(self.objs.len() as u32 - 1)
    }

    pub fn get_str(&self, id: u32) -> &str {
        debug_assert!(self.strs[id as usize].is_some(), "freed str {id}");
        self.strs[id as usize].as_deref().unwrap_or("")
    }

    pub fn obj(&self, id: u32) -> &Obj {
        &self.objs[id as usize]
    }

    pub fn obj_mut(&mut self, id: u32) -> &mut Obj {
        &mut self.objs[id as usize]
    }

    /// (objects, strings) live slots.
    pub fn stats(&self) -> (usize, usize) {
        (
            self.objs.len() - self.free_objs.len(),
            self.strs.len() - self.free_strs.len(),
        )
    }
}

impl Default for Heap {
    fn default() -> Self {
        Self::new()
    }
}

/// Lexical environment, flat-arena style. parent = enclosing EnvId.
/// `free` marks a GC-tombstoned slot waiting on free_envs for reuse.
pub(crate) struct Env {
    pub vars: HashMap<String, Value>,
    pub parent: Option<u32>,
    pub free: bool,
}

/// A form submit captured at submit() time (fields as they were then).
/// The host performs the HTTP, following the same method semantics as a
/// plain form submit.
#[derive(Debug, Clone)]
pub struct PendingSubmit {
    pub method: String,
    pub url: String,
    pub fields: Vec<(String, String)>,
}

pub struct Interp {
    pub heap: Heap,
    /// env 0 is global
    pub(crate) envs: Vec<Env>,
    /// Page DOM installed by set_dom; Obj::Dom indices point into it.
    pub dom: Option<vigia_dom::Dom>,
    /// node -> wrapper obj cache so `a === b` identity holds per node
    pub(crate) dom_objs: HashMap<NodeId, u32>,
    /// node -> (event type, handler) listeners. JS values, so they live
    /// here rather than on DOM nodes. Cleared by set_dom.
    pub(crate) listeners: HashMap<NodeId, Vec<(String, Value)>>,
    /// Net context for fetch()/click resolution; moved in per script run.
    pub net: Option<NetCtx>,
    /// Set by click() on <a href> when default isn't prevented. The host
    /// decides whether to follow it (v1 navigation bridge).
    pub pending_nav: Option<String>,
    /// A form submission requested by page JS (`form.submit()` or the
    /// WebForms `__doPostBack` helper): captured fields plus the resolved
    /// target. Following it (the actual HTTP) is the host's call, like
    /// pending_nav.
    pub pending_submit: Option<PendingSubmit>,
    /// Well-known prototypes, allocated by install_protos in with_cap.
    pub protos: Protos,
    /// Math.random state (xorshift64*; not crypto).
    pub(crate) rng: u64,
    pub(crate) out: String,
    pub(crate) last: Value,
    pub(crate) steps: u64,
    pub(crate) call_depth: u32,
    pub(crate) builtins: bool,
    /// Queued promise handlers / queueMicrotask callbacks, FIFO.
    pub(crate) microtasks: VecDeque<Microtask>,
    /// Live timers ordered implicitly by deadline_ms (earliest fires first).
    pub(crate) timers: Vec<Timer>,
    /// Virtual clock in ms; only advances (to the fired timer's deadline).
    pub(crate) now_ms: u64,
    pub(crate) next_timer_id: u32,
    /// Promise obj ids that were then'd or adopted - the unhandled-
    /// rejection sweep at drain end skips these (and remembers reports).
    pub(crate) handled_promises: HashSet<u32>,
    /// Native fn object currently executing, so natives that stand in for
    /// per-promise callbacks (resolve/reject, all() counters, finally
    /// wrappers) can find their bound state in their own `pairs`.
    pub(crate) cur_native: Value,
    /// true while an `async function` body is on the stack (gate for await).
    pub(crate) fn_async: bool,
    /// Scope env of the innermost in-flight function (its call env).
    /// Annex-B hoisting mirrors block-level `function` declarations here.
    /// Always an ancestor-or-self of open envs, so GC-safe without rooting.
    pub(crate) func_env: u32,
    /// Parent ctors of in-flight derived-class methods (innermost last):
    /// `super()` / `super.m` resolve against the top. Pushed by
    /// call_value for Funcs carrying `__super`, popped on return.
    pub(crate) super_stack: Vec<Value>,
    /// In-flight call chain (func obj ids, innermost last) for error
    /// context ("x is not defined (in S > ?)"). Pushed next to the
    /// super_stack push so `?`s cannot leak it.
    pub(crate) js_stack: Vec<u32>,
    /// Chain snapshot at the innermost unwinding frame of the current
    /// in-flight throw (None when no throw is unwinding). Cleared on
    /// catch and at run() entry; bound_err appends it to the report.
    pub(crate) throw_chain: Option<String>,
    /// Blob URL counter for createObjectURL (opaque handles only).
    pub(crate) blob_next: u32,
    /// Label of the directly-enclosing `name:` when it wraps the loop
    /// about to run (taken by it at start). Lets `continue name` resume
    /// the right loop instead of an inner one restarting itself.
    pub(crate) label_direct: Option<String>,
    /// GC freelist for the env arena (envs never shrink either).
    pub(crate) free_envs: Vec<u32>,
    /// `Symbol.for` registry: key -> symbol obj id (roots, live forever).
    pub(crate) symbol_registry: HashMap<String, u32>,
    /// Every env currently open on the eval stack (innermost last):
    /// exec_block pushes its env, `for` pushes its decl env. GC roots -
    /// together with parent links they cover every live frame.
    pub(crate) env_stack: Vec<u32>,
    /// Values held by in-flight calls (callee, `this`, args). Rust locals
    /// are invisible to GC, so call_value roots them here for the call's
    /// duration (and natives keep their arg slice alive through nested
    /// calls, e.g. arr.map's callback).
    pub(crate) call_vals: Vec<Value>,
    /// FnDefs already materialized by a hoist pass (exec_block_run's
    /// block entry or hoist_vars' function entry), as raw identities -
    /// never dereferenced, only compared. Stmt::FnDecl skips those so a
    /// declaration creates exactly one object per entry (V8 parity: the
    /// old re-declare-on-execution broke prototype identity, e.g.
    /// Babel _inherits' `n.prototype`). Stack discipline with truncate.
    pub(crate) hoisted: Vec<*const FnDef>,
    /// GC collections so far (metrics).
    pub gc_runs: u64,
    /// The `window`/`self`/`globalThis` object id (one object, three
    /// names): reads/writes go live to env 0, so `window.x = 1` and bare
    /// `x` are the same binding like real browsers.
    pub(crate) wind: Option<u32>,
    /// runaway guards, all user-tunable
    pub max_steps: u64,
    pub max_call_depth: u32,
    pub max_envs: usize,
}

impl Interp {
    pub fn new() -> Self {
        Self::with_cap(1_000_000)
    }

    pub fn with_cap(cap: usize) -> Self {
        // non-crypto rng seed from wall clock
        let rng = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos() as u64)
            .unwrap_or(0)
            ^ 0x9E3779B97F4A7C15;
        let mut it = Interp {
            heap: Heap::with_cap(cap),
            envs: vec![Env {
                vars: HashMap::new(),
                parent: None,
                free: false,
            }],
            dom: None,
            dom_objs: HashMap::new(),
            listeners: HashMap::new(),
            net: None,
            pending_nav: None,
            pending_submit: None,
            protos: Protos::none(),
            rng,
            out: String::new(),
            last: Value::Undef,
            steps: 0,
            call_depth: 0,
            builtins: false,
            microtasks: VecDeque::new(),
            timers: Vec::new(),
            now_ms: 0,
            next_timer_id: 1,
            handled_promises: HashSet::new(),
            cur_native: Value::Undef,
            fn_async: false,
            func_env: 0,
            super_stack: Vec::new(),
            js_stack: Vec::new(),
            throw_chain: None,
            blob_next: 0,
            label_direct: None,
            free_envs: Vec::new(),
            symbol_registry: HashMap::new(),
            env_stack: Vec::new(),
            call_vals: Vec::new(),
            hoisted: Vec::new(),
            gc_runs: 0,
            wind: None,
            max_steps: 5_000_000,
            max_call_depth: 1_000,
            max_envs: 200_000,
        };
        it.install_protos();
        it
    }

    /// console.log output accumulated so far.
    pub fn output(&self) -> &str {
        &self.out
    }

    /// Parse + run a program, then drain the microtask queue and pending
    /// timers (script boundary, like browsers). Returns the completion
    /// value (the last expression statement's value), Undef if none.
    /// A script error wins over drain errors; on a clean script the first
    /// drain error (failed callback, unhandled rejection, cap hit)
    /// surfaces as the Err.
    pub fn run(&mut self, src: &str) -> Result<Value, JsError> {
        self.install_builtins();
        let stmts = parse::parse_program(src)?;
        // Top-level `var`s hoist to the global scope (func_env is 0).
        self.func_env = 0;
        self.throw_chain = None;
        let hbase = self.hoisted.len();
        self.hoist_vars(&stmts, 0)?;
        let r = self.exec_block(&stmts, 0);
        self.hoisted.truncate(hbase);
        let mut errs = Vec::new();
        self.drain(&mut errs);
        match r {
            Err(e) => Err(self.bound_err(e)),
            // unreachable: parser rejects top-level return/break/continue
            Ok(eval::Flow::Normal) => match errs.into_iter().next() {
                Some(e) => Err(self.bound_err(e)),
                None => Ok(self.last),
            },
            Ok(_) => Err(fatal("control flow escaped program")),
        }
    }
}

impl Default for Interp {
    fn default() -> Self {
        Self::new()
    }
}
