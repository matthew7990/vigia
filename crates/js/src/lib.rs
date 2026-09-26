//! vigia-js: own JavaScript interpreter core (lexer, parser, tree-walk eval).
//! Pragmatic ES5-ish subset with DOM bindings (bindings.rs), no prototypes,
//! no async.
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
//! - `new F()` gives a fresh Ordinary as `this`; no prototype wiring.
//! - No regex literals, for-in/of, switch, try, do-while, getters,
//!   instanceof, delete, void, ?., ??, =>, spread, classes, labels.
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
    /// property map, insertion order
    Ordinary(Vec<(String, Value)>),
    Arr(Vec<Value>),
    /// def carries params+body shared via Rc; env is the captured EnvId
    Func { def: Rc<FnDef>, env: u32 },
    Native(&'static str, NativeFn),
    /// JS handle over a DOM node; valid only while Interp.dom is installed.
    Dom(NodeId),
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
        Interp {
            heap: Heap::with_cap(cap),
            envs: vec![Env { vars: HashMap::new(), parent: None }],
            dom: None,
            dom_objs: HashMap::new(),
            listeners: HashMap::new(),
            net: None,
            pending_nav: None,
            out: String::new(),
            last: Value::Undef,
            steps: 0,
            call_depth: 0,
            builtins: false,
            max_steps: 5_000_000,
            max_call_depth: 1_000,
            max_envs: 200_000,
        }
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
