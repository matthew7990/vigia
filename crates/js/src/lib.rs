//! vigia-js: own JavaScript interpreter core (lexer, parser, tree-walk eval).
//! Pragmatic ES5-ish subset with DOM bindings (bindings.rs), prototype-based
//! property lookup, no async.
//!
//! Values live in flat arenas (Heap::strs, Heap::objs, Interp::envs) so a
//! later mark-sweep GC can find roots without walking pointer graphs. Rc
//! appears only to share immutable AST bodies into Obj::Func.
//!
//! v1 semantic choices (deliberate deviations from full JS):
//! - `;` optional before `}`, EOF, or a newline-separated token (ASI-lite).
//! - var/let/const all declare in the current (block) env; no var-hoisting.
//! - Function declarations hoist within their block.
//! - `this` bound for `o.m()` and `o[i]()` calls, else undefined.
//! - Assignment to an undeclared name creates a global (sloppy mode).
//! - Prototypes: Ordinary/Arr/Func carry `proto`; Native/Dom carry none
//!   (Native objects reach Function.prototype through a virtual fallback).
//!   `Func`/`Native` carry `pairs` (own props) so functions can expose
//!   `.prototype` and constructor globals (Object, Date, ...) their statics;
//!   every Obj::Func gets a fresh own "prototype" object at creation.
//! - `new F()`: proto = F.prototype when it's an object else Object's proto;
//!   `new` on a Native just calls it (ctors allocate their own result).
//!   `new` callee is primary + member chain: `new a.b()` is New(Member a.b).
//! - No regex literals: String.replace takes a string/number needle only.
//! - No for-in/of, switch, try, do-while, getters, delete, void, ?., ??,
//!   =>, spread, classes, labels, __proto__ accessor.
//! - Events: addEventListener + inline `on*` attrs, bubble phase only
//!   (no capture). Dispatch is synchronous.
//! - fetch() is synchronous: returns a plain response object whose
//!   text()/json() methods read its `__body` prop (no hidden state).
//! - el.click() on <a href> sets pending_nav + location.href instead of
//!   navigating; following it is the host's call.

use std::collections::HashMap;
use std::rc::Rc;

use vigia_dom::NodeId;

mod ast;
mod bindings;
mod eval;
mod lex;
mod parse;

pub use ast::{Expr, FnDef, Stmt};
pub use bindings::ScriptsOutcome;
pub use parse::parse_program as parse;

/// Interpreter error. Message carries a byte offset where one is known.
#[derive(Debug)]
pub struct JsError(pub String);

impl std::fmt::Display for JsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl std::error::Error for JsError {}

pub(crate) fn err(msg: impl Into<String>) -> JsError {
    JsError(msg.into())
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

/// Builtin function signature: interpreter access, the receiver (`this`),
/// and already-evaled args.
pub type NativeFn = fn(&mut Interp, this: Value, &[Value]) -> Result<Value, JsError>;

/// Page network context for a script run: the URL the DOM came from
/// (resolves relative fetch()/click() targets) plus the cookie jar. The
/// jar is moved in for the run and handed back through ScriptsOutcome -
/// no pointers, no lifetimes.
pub struct NetCtx {
    pub base: vigia_url::Url,
    pub jar: vigia_session::CookieJar,
}

#[derive(Debug)]
pub enum Obj {
    /// property map, insertion order; proto = heap obj id, None = null proto
    Ordinary { pairs: Vec<(String, Value)>, proto: Option<u32> },
    Arr { items: Vec<Value>, proto: Option<u32> },
    /// def carries params+body shared via Rc; env is the captured EnvId.
    /// pairs holds own props ("prototype" is populated at creation).
    Func { def: Rc<FnDef>, env: u32, proto: Option<u32>, pairs: Vec<(String, Value)> },
    /// name+f; pairs holds own props (ctor statics, "prototype"). No proto
    /// field: get_prop falls back to Function.prototype for Natives.
    Native { name: &'static str, f: NativeFn, pairs: Vec<(String, Value)> },
    /// JS handle over a DOM node; valid only while Interp.dom is installed.
    Dom(NodeId),
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
        }
    }
}

/// u32::MAX sentinel -> None (proto not installed).
pub(crate) fn po(p: u32) -> Option<u32> {
    if p == u32::MAX { None } else { Some(p) }
}

/// Value arena. `cap` is a hard limit on live slots (objs + strs).
pub struct Heap {
    strs: Vec<String>,
    objs: Vec<Obj>,
    intern: HashMap<String, u32>,
    cap: usize,
}

impl Heap {
    pub fn new() -> Self {
        Self::with_cap(1_000_000)
    }

    pub fn with_cap(cap: usize) -> Self {
        Heap { strs: Vec::new(), objs: Vec::new(), intern: HashMap::new(), cap }
    }

    fn room(&self) -> Result<(), JsError> {
        if self.strs.len() + self.objs.len() >= self.cap {
            Err(err("heap cap"))
        } else {
            Ok(())
        }
    }

    /// Runtime (non-literal) string. No dedup.
    pub fn alloc_str(&mut self, s: String) -> Result<u32, JsError> {
        self.room()?;
        self.strs.push(s);
        Ok(self.strs.len() as u32 - 1)
    }

    /// Source-literal strings dedupe so loops re-evaluating the same
    /// literal don't burn a slot per iteration.
    pub fn intern_str(&mut self, s: &str) -> Result<u32, JsError> {
        if let Some(&id) = self.intern.get(s) {
            return Ok(id);
        }
        let id = self.alloc_str(s.to_string())?;
        self.intern.insert(s.to_string(), id);
        Ok(id)
    }

    pub fn alloc_obj(&mut self, o: Obj) -> Result<u32, JsError> {
        self.room()?;
        self.objs.push(o);
        Ok(self.objs.len() as u32 - 1)
    }

    pub fn get_str(&self, id: u32) -> &str {
        &self.strs[id as usize]
    }

    pub fn obj(&self, id: u32) -> &Obj {
        &self.objs[id as usize]
    }

    pub fn obj_mut(&mut self, id: u32) -> &mut Obj {
        &mut self.objs[id as usize]
    }

    /// (objects, strings) live slots.
    pub fn stats(&self) -> (usize, usize) {
        (self.objs.len(), self.strs.len())
    }
}

impl Default for Heap {
    fn default() -> Self {
        Self::new()
    }
}

/// Lexical environment, flat-arena style. parent = enclosing EnvId.
pub(crate) struct Env {
    pub vars: HashMap<String, Value>,
    pub parent: Option<u32>,
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
    /// Well-known prototypes, allocated by install_protos in with_cap.
    pub protos: Protos,
    /// Math.random state (xorshift64*; not crypto).
    pub(crate) rng: u64,
    pub(crate) out: String,
    pub(crate) last: Value,
    pub(crate) steps: u64,
    pub(crate) call_depth: u32,
    pub(crate) builtins: bool,
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
            envs: vec![Env { vars: HashMap::new(), parent: None }],
            dom: None,
            dom_objs: HashMap::new(),
            listeners: HashMap::new(),
            net: None,
            pending_nav: None,
            protos: Protos::none(),
            rng,
            out: String::new(),
            last: Value::Undef,
            steps: 0,
            call_depth: 0,
            builtins: false,
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

    /// Parse + run a program. Returns the completion value (the last
    /// expression statement's value), Undef if there was none.
    pub fn run(&mut self, src: &str) -> Result<Value, JsError> {
        self.install_builtins();
        let stmts = parse::parse_program(src)?;
        match self.exec_block(&stmts, 0)? {
            eval::Flow::Normal => Ok(self.last),
            // unreachable: parser rejects top-level return/break/continue
            _ => Err(err("control flow escaped program")),
        }
    }
}

impl Default for Interp {
    fn default() -> Self {
        Self::new()
    }
}
