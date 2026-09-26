//! Tree-walking evaluator. `Flow` threads break/continue/return through
//! statement execution. Closures capture their defining EnvId; `this` is
//! an ordinary env binding set per call.

use std::collections::HashMap;
use std::rc::Rc;

use vigia_json::Json;

use crate::ast::{Expr, FnDef, Stmt};
use crate::{err, Env, Heap, Interp, JsError, Obj, Value};

pub(crate) enum Flow {
    Normal,
    Break,
    Continue,
    Return(Value),
}

// ---- coercions ---------------------------------------------------------

pub(crate) fn truthy(h: &Heap, v: Value) -> bool {
    match v {
        Value::Undef | Value::Null => false,
        Value::Bool(b) => b,
        Value::Num(n) => n != 0.0 && !n.is_nan(),
        Value::Str(id) => !h.get_str(id).is_empty(),
        Value::Obj(_) => true,
    }
}

pub(crate) fn to_num(h: &Heap, v: Value) -> f64 {
    match v {
        Value::Undef => f64::NAN,
        Value::Null => 0.0,
        Value::Bool(b) => b as u8 as f64,
        Value::Num(n) => n,
        Value::Str(id) => {
            let s = h.get_str(id).trim();
            if s.is_empty() {
                return 0.0;
            }
            if let Some(x) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
                return u64::from_str_radix(x, 16).map(|n| n as f64).unwrap_or(f64::NAN);
            }
            s.parse().unwrap_or(f64::NAN)
        }
        Value::Obj(_) => f64::NAN,
    }
}

/// JS number formatting: integers without `.0`, NaN/Infinity named.
pub(crate) fn fmt_num(n: f64) -> String {
    if n.is_nan() {
        return "NaN".into();
    }
    if n.is_infinite() {
        return if n > 0.0 { "Infinity".into() } else { "-Infinity".into() };
    }
    if n.fract() == 0.0 && n.abs() < 9e15 {
        (n as i64).to_string()
    } else {
        n.to_string()
    }
}

pub(crate) fn to_str(h: &Heap, v: Value) -> String {
    match v {
        Value::Undef => "undefined".into(),
        Value::Null => "null".into(),
        Value::Bool(b) => if b { "true".into() } else { "false".into() },
        Value::Num(n) => fmt_num(n),
        Value::Str(id) => h.get_str(id).into(),
        Value::Obj(id) => match h.obj(id) {
            Obj::Arr(items) => items
                .iter()
                .map(|x| match x {
                    Value::Undef | Value::Null => String::new(),
                    _ => to_str(h, *x),
                })
                .collect::<Vec<_>>()
                .join(","),
            Obj::Ordinary(_) => "[object Object]".into(),
            Obj::Func { def, .. } => {
                format!("function {}() {{ [code] }}", def.name.as_deref().unwrap_or(""))
            }
            Obj::Native(n, _) => format!("function {n}() {{ [native code] }}"),
            Obj::Dom(_) => "[object Node]".into(),
        },
    }
}

/// Proper JS ToInt32: truncate, wrap mod 2^32.
fn to_i32(h: &Heap, v: Value) -> i32 {
    let n = to_num(h, v);
    if !n.is_finite() || n == 0.0 {
        return 0;
    }
    let m = n.trunc() % 4294967296.0;
    let u = if m < 0.0 { m + 4294967296.0 } else { m };
    if u >= 2147483648.0 {
        (u - 4294967296.0) as i32
    } else {
        u as i32
    }
}

fn to_u32(h: &Heap, v: Value) -> u32 {
    to_i32(h, v) as u32
}

fn strict_eq(h: &Heap, l: Value, r: Value) -> bool {
    match (l, r) {
        (Value::Undef, Value::Undef) | (Value::Null, Value::Null) => true,
        (Value::Bool(a), Value::Bool(b)) => a == b,
        (Value::Num(a), Value::Num(b)) => a == b,
        (Value::Str(a), Value::Str(b)) => h.get_str(a) == h.get_str(b),
        (Value::Obj(a), Value::Obj(b)) => a == b,
        _ => false,
    }
}

fn loose_eq(h: &Heap, l: Value, r: Value) -> bool {
    if strict_eq(h, l, r) {
        return true;
    }
    match (l, r) {
        (Value::Null, Value::Undef) | (Value::Undef, Value::Null) => true,
        (Value::Num(_), Value::Str(_))
        | (Value::Str(_), Value::Num(_))
        | (Value::Bool(_), _)
        | (_, Value::Bool(_)) => to_num(h, l) == to_num(h, r),
        _ => false,
    }
}

pub(crate) fn type_str(h: &Heap, v: Value) -> &'static str {
    match v {
        Value::Undef => "undefined",
        Value::Null => "object",
        Value::Bool(_) => "boolean",
        Value::Num(_) => "number",
        Value::Str(_) => "string",
        Value::Obj(id) => match h.obj(id) {
            Obj::Func { .. } | Obj::Native(..) => "function",
            _ => "object",
        },
    }
}

/// `<`-family: two strings compare lexically, anything else numerically.
fn rel(h: &Heap, l: Value, r: Value, nf: fn(f64, f64) -> bool, sf: fn(&str, &str) -> bool) -> bool {
    if let (Value::Str(a), Value::Str(b)) = (l, r) {
        sf(h.get_str(a), h.get_str(b))
    } else {
        nf(to_num(h, l), to_num(h, r))
    }
}

// ---- property access ---------------------------------------------------

fn get_prop(h: &Heap, v: Value, key: &str) -> Result<Value, JsError> {
    match v {
        Value::Obj(id) => Ok(match h.obj(id) {
            Obj::Ordinary(pairs) => pairs
                .iter()
                .find(|(k, _)| k == key)
                .map(|(_, v)| *v)
                .unwrap_or(Value::Undef),
            Obj::Arr(items) if key == "length" => Value::Num(items.len() as f64),
            _ => Value::Undef,
        }),
        Value::Str(id) if key == "length" => {
            Ok(Value::Num(h.get_str(id).chars().count() as f64))
        }
        Value::Undef | Value::Null => Err(err(format!(
            "cannot read '{key}' of {}",
            if matches!(v, Value::Null) { "null" } else { "undefined" }
        ))),
        _ => Ok(Value::Undef),
    }
}

fn set_prop(h: &mut Heap, v: Value, key: &str, val: Value) -> Result<(), JsError> {
    match v {
        Value::Obj(id) => match h.obj_mut(id) {
            Obj::Ordinary(pairs) => {
                match pairs.iter_mut().find(|(k, _)| k == key) {
                    Some(slot) => slot.1 = val,
                    None => pairs.push((key.to_string(), val)),
                }
                Ok(())
            }
            _ => Err(err("cannot set property on this object")),
        },
        Value::Undef | Value::Null => Err(err("cannot set property of null/undefined")),
        _ => Ok(()), // primitives: sloppy no-op like real JS
    }
}

fn get_index(h: &mut Heap, v: Value, k: Value) -> Result<Value, JsError> {
    match v {
        Value::Obj(id) => {
            let n = to_num(h, k);
            match h.obj(id) {
                Obj::Arr(items) => Ok(if n >= 0.0 && n.fract() == 0.0 {
                    items.get(n as usize).copied().unwrap_or(Value::Undef)
                } else {
                    Value::Undef
                }),
                Obj::Ordinary(_) => {
                    let key = to_str(h, k);
                    get_prop(h, v, &key)
                }
                _ => Ok(Value::Undef),
            }
        }
        Value::Str(id) => {
            let n = to_num(h, k);
            let c = if n >= 0.0 && n.fract() == 0.0 {
                h.get_str(id).chars().nth(n as usize)
            } else {
                None
            };
            match c {
                Some(c) => Ok(Value::Str(h.alloc_str(c.to_string())?)),
                None => Ok(Value::Undef),
            }
        }
        Value::Undef | Value::Null => Err(err("cannot index into null/undefined")),
        _ => Ok(Value::Undef),
    }
}

fn set_index(h: &mut Heap, v: Value, k: Value, val: Value) -> Result<(), JsError> {
    match v {
        Value::Obj(id) => {
            if matches!(h.obj(id), Obj::Arr(_)) {
                let n = to_num(h, k);
                if !(n >= 0.0 && n.fract() == 0.0 && n <= 10_000_000.0) {
                    return Err(err("bad array index"));
                }
                let i = n as usize;
                if let Obj::Arr(items) = h.obj_mut(id) {
                    if i >= items.len() {
                        items.resize(i + 1, Value::Undef);
                    }
                    items[i] = val;
                }
                return Ok(());
            }
            let key = to_str(h, k);
            set_prop(h, v, &key, val)
        }
        Value::Undef | Value::Null => Err(err("cannot set property of null/undefined")),
        _ => Ok(()),
    }
}

// ---- evaluator -----------------------------------------------------------

impl Interp {
    pub(crate) fn install_builtins(&mut self) {
        if self.builtins {
            return;
        }
        self.builtins = true;
        // cap edge: installs silently skip when there's no room
        if let Ok(log) = self.heap.alloc_obj(Obj::Native("log", n_console_log)) {
            if let Ok(c) = self.heap.alloc_obj(Obj::Ordinary(vec![("log".into(), Value::Obj(log))]))
            {
                self.env_declare(0, "console", Value::Obj(c));
            }
        }
        if let Ok(p) = self.heap.alloc_obj(Obj::Native("parse", n_json_parse)) {
            if let Ok(s) = self.heap.alloc_obj(Obj::Native("stringify", n_json_stringify)) {
                let pairs =
                    vec![("parse".into(), Value::Obj(p)), ("stringify".into(), Value::Obj(s))];
                if let Ok(j) = self.heap.alloc_obj(Obj::Ordinary(pairs)) {
                    self.env_declare(0, "JSON", Value::Obj(j));
                }
            }
        }
        self.env_declare(0, "this", Value::Undef);
    }

    fn tick(&mut self) -> Result<(), JsError> {
        self.steps += 1;
        if self.steps > self.max_steps {
            return Err(err("step limit exceeded"));
        }
        Ok(())
    }

    pub(crate) fn new_env(&mut self, parent: u32) -> Result<u32, JsError> {
        if self.envs.len() >= self.max_envs {
            return Err(err("env cap"));
        }
        self.envs.push(Env { vars: HashMap::new(), parent: Some(parent) });
        Ok(self.envs.len() as u32 - 1)
    }

    pub(crate) fn env_declare(&mut self, env: u32, name: &str, v: Value) {
        self.envs[env as usize].vars.insert(name.to_string(), v);
    }

    fn env_get(&self, env: u32, name: &str) -> Option<Value> {
        let mut cur = env;
        loop {
            let e = &self.envs[cur as usize];
            if let Some(v) = e.vars.get(name) {
                return Some(*v);
            }
            cur = e.parent?;
        }
    }

    fn env_set(&mut self, env: u32, name: &str, v: Value) -> bool {
        let mut cur = env;
        loop {
            let e = &mut self.envs[cur as usize];
            if e.vars.contains_key(name) {
                e.vars.insert(name.to_string(), v);
                return true;
            }
            match e.parent {
                Some(p) => cur = p,
                None => return false,
            }
        }
    }

    /// Execute a statement list in `env`: hoist fn decls first, then run.
    pub(crate) fn exec_block(&mut self, stmts: &[Stmt], env: u32) -> Result<Flow, JsError> {
        for s in stmts {
            if let Stmt::FnDecl(def) = s {
                let f = self.heap.alloc_obj(Obj::Func { def: def.clone(), env })?;
                if let Some(n) = &def.name {
                    self.env_declare(env, n, Value::Obj(f));
                }
            }
        }
        for s in stmts {
            self.tick()?;
            match self.stmt(env, s)? {
                Flow::Normal => {}
                f => return Ok(f),
            }
        }
        Ok(Flow::Normal)
    }

    fn stmt(&mut self, env: u32, s: &Stmt) -> Result<Flow, JsError> {
        match s {
            Stmt::Expr(e) => {
                self.last = self.expr(env, e)?;
                Ok(Flow::Normal)
            }
            Stmt::VarDecl(ds) => {
                for (n, init) in ds {
                    let v = match init {
                        Some(e) => self.expr(env, e)?,
                        None => Value::Undef,
                    };
                    self.env_declare(env, n, v);
                }
                Ok(Flow::Normal)
            }
            Stmt::FnDecl(_) => Ok(Flow::Normal), // hoisted
            Stmt::Return(e) => {
                let v = match e {
                    Some(e) => self.expr(env, e)?,
                    None => Value::Undef,
                };
                Ok(Flow::Return(v))
            }
            Stmt::If(c, t, f) => {
                let c = self.expr(env, c)?;
                if truthy(&self.heap, c) {
                    self.stmt(env, t)
                } else if let Some(f) = f {
                    self.stmt(env, f)
                } else {
                    Ok(Flow::Normal)
                }
            }
            Stmt::While(c, body) => {
                loop {
                    let c = self.expr(env, c)?;
                    if !truthy(&self.heap, c) {
                        break;
                    }
                    self.tick()?;
                    match self.stmt(env, body)? {
                        Flow::Normal | Flow::Continue => {}
                        Flow::Break => break,
                        f => return Ok(f),
                    }
                }
                Ok(Flow::Normal)
            }
            Stmt::For(init, test, upd, body) => {
                let fenv = self.new_env(env)?;
                if let Some(init) = init {
                    match self.stmt(fenv, init)? {
                        Flow::Normal => {}
                        f => return Ok(f),
                    }
                }
                loop {
                    self.tick()?;
                    if let Some(t) = test {
                        let c = self.expr(fenv, t)?;
                        if !truthy(&self.heap, c) {
                            break;
                        }
                    }
                    match self.stmt(fenv, body)? {
                        Flow::Normal | Flow::Continue => {}
                        Flow::Break => break,
                        f => return Ok(f),
                    }
                    if let Some(u) = upd {
                        self.expr(fenv, u)?;
                    }
                }
                Ok(Flow::Normal)
            }
            Stmt::Block(ss) => {
                // new env only when the block declares something
                if ss.iter().any(|s| matches!(s, Stmt::VarDecl(_) | Stmt::FnDecl(_))) {
                    let e2 = self.new_env(env)?;
                    self.exec_block(ss, e2)
                } else {
                    self.exec_block(ss, env)
                }
            }
            Stmt::Break => Ok(Flow::Break),
            Stmt::Continue => Ok(Flow::Continue),
        }
    }

    fn expr(&mut self, env: u32, e: &Expr) -> Result<Value, JsError> {
        match e {
            Expr::Num(n) => Ok(Value::Num(*n)),
            Expr::Str(s) => Ok(Value::Str(self.heap.intern_str(s)?)),
            Expr::Bool(b) => Ok(Value::Bool(*b)),
            Expr::Null => Ok(Value::Null),
            Expr::Undef => Ok(Value::Undef),
            Expr::Ident(n) => self
                .env_get(env, n)
                .ok_or_else(|| err(format!("{n} is not defined"))),
            Expr::Arr(items) => {
                let mut v = Vec::with_capacity(items.len());
                for it in items {
                    v.push(self.expr(env, it)?);
                }
                Ok(Value::Obj(self.heap.alloc_obj(Obj::Arr(v))?))
            }
            Expr::ObjLit(ps) => {
                let mut pairs: Vec<(String, Value)> = Vec::new();
                for (k, ex) in ps {
                    let v = self.expr(env, ex)?;
                    match pairs.iter_mut().find(|(pk, _)| pk == k) {
                        Some(slot) => slot.1 = v,
                        None => pairs.push((k.clone(), v)),
                    }
                }
                Ok(Value::Obj(self.heap.alloc_obj(Obj::Ordinary(pairs))?))
            }
            Expr::Unary(op, e) => self.unary(env, op, e),
            Expr::Postfix(op, e) => self.bump(env, e, if *op == "++" { 1.0 } else { -1.0 }, true),
            Expr::Bin(op, l, r) => self.bin(env, op, l, r),
            Expr::Ternary(c, t, f) => {
                let c = self.expr(env, c)?;
                if truthy(&self.heap, c) {
                    self.expr(env, t)
                } else {
                    self.expr(env, f)
                }
            }
            Expr::Assign(op, l, r) => self.assign(env, op, l, r),
            Expr::Call(c, args) => self.call(env, c, args),
            Expr::Member(o, name) => {
                let v = self.expr(env, o)?;
                match self.as_node(v) {
                    Some(n) => self.dom_get(n, name),
                    None => get_prop(&self.heap, v, name),
                }
            }
            Expr::Index(o, ix) => {
                let v = self.expr(env, o)?;
                let k = self.expr(env, ix)?;
                match self.as_node(v) {
                    Some(n) => {
                        let key = to_str(&self.heap, k);
                        self.dom_get(n, &key)
                    }
                    None => get_index(&mut self.heap, v, k),
                }
            }
            Expr::Func(def) => {
                Ok(Value::Obj(self.heap.alloc_obj(Obj::Func { def: def.clone(), env })?))
            }
            Expr::New(c, args) => {
                let f = self.expr(env, c)?;
                let args = self.eval_args(env, args)?;
                let obj = self.heap.alloc_obj(Obj::Ordinary(vec![]))?;
                let r = self.call_value(f, Value::Obj(obj), &args, None)?;
                Ok(match r {
                    Value::Obj(_) => r,
                    _ => Value::Obj(obj),
                })
            }
        }
    }

    fn unary(&mut self, env: u32, op: &str, e: &Expr) -> Result<Value, JsError> {
        match op {
            "typeof" => {
                // typeof on an unbound name must not throw (real JS agrees)
                let v = match e {
                    Expr::Ident(n) => self.env_get(env, n).unwrap_or(Value::Undef),
                    _ => self.expr(env, e)?,
                };
                Ok(Value::Str(self.heap.intern_str(type_str(&self.heap, v))?))
            }
            "++" | "--" => self.bump(env, e, if op == "++" { 1.0 } else { -1.0 }, false),
            _ => {
                let v = self.expr(env, e)?;
                Ok(match op {
                    "-" => Value::Num(-to_num(&self.heap, v)),
                    "+" => Value::Num(to_num(&self.heap, v)),
                    "!" => Value::Bool(!truthy(&self.heap, v)),
                    "~" => Value::Num(!to_i32(&self.heap, v) as f64),
                    _ => return Err(err(format!("bad unary op {op}"))),
                })
            }
        }
    }

    /// ++/-- on a resolved reference; `old` picks postfix semantics.
    fn bump(&mut self, env: u32, e: &Expr, delta: f64, old: bool) -> Result<Value, JsError> {
        let cur = self.get_ref(env, e)?;
        let prev = to_num(&self.heap, cur);
        let next = prev + delta;
        self.set_ref(env, e, Value::Num(next))?;
        Ok(Value::Num(if old { prev } else { next }))
    }

    fn bin(&mut self, env: u32, op: &str, l: &Expr, r: &Expr) -> Result<Value, JsError> {
        match op {
            "&&" => {
                let lv = self.expr(env, l)?;
                if !truthy(&self.heap, lv) {
                    return Ok(lv);
                }
                self.expr(env, r)
            }
            "||" => {
                let lv = self.expr(env, l)?;
                if truthy(&self.heap, lv) {
                    return Ok(lv);
                }
                self.expr(env, r)
            }
            _ => {
                let lv = self.expr(env, l)?;
                let rv = self.expr(env, r)?;
                self.apply_bin(op, lv, rv)
            }
        }
    }

    fn apply_bin(&mut self, op: &str, l: Value, r: Value) -> Result<Value, JsError> {
        let h = &mut self.heap;
        Ok(match op {
            // JS +: string concat when either side is string/object
            "+" => {
                if matches!(l, Value::Str(_) | Value::Obj(_))
                    || matches!(r, Value::Str(_) | Value::Obj(_))
                {
                    let s = to_str(h, l) + &to_str(h, r);
                    Value::Str(h.alloc_str(s)?)
                } else {
                    Value::Num(to_num(h, l) + to_num(h, r))
                }
            }
            "-" => Value::Num(to_num(h, l) - to_num(h, r)),
            "*" => Value::Num(to_num(h, l) * to_num(h, r)),
            "/" => Value::Num(to_num(h, l) / to_num(h, r)),
            "%" => Value::Num(to_num(h, l) % to_num(h, r)),
            "==" => Value::Bool(loose_eq(h, l, r)),
            "!=" => Value::Bool(!loose_eq(h, l, r)),
            "===" => Value::Bool(strict_eq(h, l, r)),
            "!==" => Value::Bool(!strict_eq(h, l, r)),
            "<" => Value::Bool(rel(h, l, r, |a, b| a < b, |a, b| a < b)),
            "<=" => Value::Bool(rel(h, l, r, |a, b| a <= b, |a, b| a <= b)),
            ">" => Value::Bool(rel(h, l, r, |a, b| a > b, |a, b| a > b)),
            ">=" => Value::Bool(rel(h, l, r, |a, b| a >= b, |a, b| a >= b)),
            "&" => Value::Num((to_i32(h, l) & to_i32(h, r)) as f64),
            "|" => Value::Num((to_i32(h, l) | to_i32(h, r)) as f64),
            "^" => Value::Num((to_i32(h, l) ^ to_i32(h, r)) as f64),
            "<<" => Value::Num((to_i32(h, l) << (to_i32(h, r) & 31)) as f64),
            ">>" => Value::Num((to_i32(h, l) >> (to_i32(h, r) & 31)) as f64),
            ">>>" => Value::Num((to_u32(h, l) >> (to_u32(h, r) & 31)) as f64),
            "in" => {
                let key = to_str(h, l);
                match r {
                    Value::Obj(id) => Value::Bool(match h.obj(id) {
                        Obj::Ordinary(ps) => ps.iter().any(|(k, _)| *k == key),
                        Obj::Arr(v) => {
                            key.parse::<usize>().map(|i| i < v.len()).unwrap_or(false)
                        }
                        _ => false,
                    }),
                    _ => return Err(err("'in' needs an object on the right")),
                }
            }
            _ => return Err(err(format!("bad op {op}"))),
        })
    }

    fn assign(&mut self, env: u32, op: &str, l: &Expr, r: &Expr) -> Result<Value, JsError> {
        let rv = self.expr(env, r)?;
        let v = if op == "=" {
            rv
        } else {
            let cur = self.get_ref(env, l)?;
            self.apply_bin(op.trim_end_matches('='), cur, rv)?
        };
        self.set_ref(env, l, v)?;
        Ok(v)
    }

    fn get_ref(&mut self, env: u32, e: &Expr) -> Result<Value, JsError> {
        match e {
            Expr::Ident(n) => self
                .env_get(env, n)
                .ok_or_else(|| err(format!("{n} is not defined"))),
            Expr::Member(o, k) => {
                let v = self.expr(env, o)?;
                match self.as_node(v) {
                    Some(n) => self.dom_get(n, k),
                    None => get_prop(&self.heap, v, k),
                }
            }
            Expr::Index(o, ix) => {
                let v = self.expr(env, o)?;
                let k = self.expr(env, ix)?;
                match self.as_node(v) {
                    Some(n) => {
                        let key = to_str(&self.heap, k);
                        self.dom_get(n, &key)
                    }
                    None => get_index(&mut self.heap, v, k),
                }
            }
            _ => Err(err("bad assignment target")),
        }
    }

    fn set_ref(&mut self, env: u32, e: &Expr, v: Value) -> Result<(), JsError> {
        match e {
            Expr::Ident(n) => {
                if !self.env_set(env, n, v) {
                    self.env_declare(0, n, v); // sloppy mode: implicit global
                }
                Ok(())
            }
            Expr::Member(o, k) => {
                let t = self.expr(env, o)?;
                match self.as_node(t) {
                    Some(n) => self.dom_set(n, k, v),
                    None => set_prop(&mut self.heap, t, k, v),
                }
            }
            Expr::Index(o, ix) => {
                let t = self.expr(env, o)?;
                let k = self.expr(env, ix)?;
                match self.as_node(t) {
                    Some(n) => {
                        let key = to_str(&self.heap, k);
                        self.dom_set(n, &key, v)
                    }
                    None => set_index(&mut self.heap, t, k, v),
                }
            }
            _ => Err(err("bad assignment target")),
        }
    }

    pub(crate) fn eval_args(&mut self, env: u32, es: &[Expr]) -> Result<Vec<Value>, JsError> {
        let mut v = Vec::with_capacity(es.len());
        for e in es {
            v.push(self.expr(env, e)?);
        }
        Ok(v)
    }

    fn call(&mut self, env: u32, callee: &Expr, arg_es: &[Expr]) -> Result<Value, JsError> {
        let (f, this, hint) = match callee {
            Expr::Member(o, name) => {
                let recv = self.expr(env, o)?;
                // string/array builtin methods live outside the property map
                match recv {
                    Value::Str(id) => return self.call_str(id, name, env, arg_es),
                    Value::Obj(id) if matches!(self.heap.obj(id), Obj::Arr(_)) => {
                        return self.call_arr(id, name, env, arg_es)
                    }
                    _ => {}
                }
                // DOM node methods dispatch like the string/array builtins
                if let Some(n) = self.as_node(recv) {
                    return self.call_dom(n, name, env, arg_es);
                }
                (get_prop(&self.heap, recv, name)?, recv, Some(name.as_str()))
            }
            Expr::Index(o, ix) => {
                let recv = self.expr(env, o)?;
                let k = self.expr(env, ix)?;
                if let (Value::Obj(id), Value::Str(s)) = (recv, k) {
                    if matches!(self.heap.obj(id), Obj::Arr(_)) {
                        let n = self.heap.get_str(s).to_string();
                        return self.call_arr(id, &n, env, arg_es);
                    }
                    if let Obj::Dom(n) = self.heap.obj(id) {
                        let (n, m) = (*n, self.heap.get_str(s).to_string());
                        return self.call_dom(n, &m, env, arg_es);
                    }
                }
                if let (Value::Str(id), Value::Str(s)) = (recv, k) {
                    let n = self.heap.get_str(s).to_string();
                    return self.call_str(id, &n, env, arg_es);
                }
                (get_index(&mut self.heap, recv, k)?, recv, None)
            }
            Expr::Ident(n) => (self.expr(env, callee)?, Value::Undef, Some(n.as_str())),
            _ => (self.expr(env, callee)?, Value::Undef, None),
        };
        let args = self.eval_args(env, arg_es)?;
        self.call_value(f, this, &args, hint)
    }

    fn call_value(
        &mut self,
        f: Value,
        this: Value,
        args: &[Value],
        hint: Option<&str>,
    ) -> Result<Value, JsError> {
        enum C {
            Fn(Rc<FnDef>, u32),
            Nat(crate::NativeFn),
        }
        let id = match f {
            Value::Obj(id) => id,
            _ => {
                return Err(err(format!(
                    "{} is not a function",
                    hint.unwrap_or(type_str(&self.heap, f))
                )))
            }
        };
        let c = match self.heap.obj(id) {
            Obj::Func { def, env } => C::Fn(def.clone(), *env),
            Obj::Native(_, nf) => C::Nat(*nf),
            _ => return Err(err(format!("{} is not a function", hint.unwrap_or("object")))),
        };
        self.tick()?;
        self.call_depth += 1;
        if self.call_depth > self.max_call_depth {
            self.call_depth -= 1;
            return Err(err("max call depth"));
        }
        let r = match c {
            C::Fn(def, fenv) => {
                let cenv = self.new_env(fenv)?;
                for (i, p) in def.params.iter().enumerate() {
                    self.env_declare(cenv, p, args.get(i).copied().unwrap_or(Value::Undef));
                }
                if let Some(n) = &def.name {
                    // named fn exprs can self-recurse via their own name
                    self.env_declare(cenv, n, f);
                }
                self.env_declare(cenv, "this", this);
                match self.exec_block(&def.body, cenv) {
                    Ok(Flow::Return(v)) => Ok(v),
                    Ok(_) => Ok(Value::Undef),
                    Err(e) => Err(e),
                }
            }
            C::Nat(nf) => nf(self, args),
        };
        self.call_depth -= 1;
        r
    }

    /// String builtin methods (`.charAt` etc). `.length` is a prop.
    fn call_str(&mut self, id: u32, name: &str, env: u32, arg_es: &[Expr]) -> Result<Value, JsError> {
        let args = self.eval_args(env, arg_es)?;
        let s = self.heap.get_str(id).to_string();
        let chars: Vec<char> = s.chars().collect();
        let len = chars.len() as i64;
        let arg = |i: usize| args.get(i).copied().unwrap_or(Value::Undef);
        match name {
            "charAt" => {
                let i = to_num(&self.heap, arg(0));
                let t = if i >= 0.0 {
                    chars.get(i as usize).map(|c| c.to_string()).unwrap_or_default()
                } else {
                    String::new()
                };
                Ok(Value::Str(self.heap.alloc_str(t)?))
            }
            "charCodeAt" => {
                let i = to_num(&self.heap, arg(0));
                Ok(Value::Num(if i >= 0.0 {
                    chars.get(i as usize).map(|c| *c as u32 as f64).unwrap_or(f64::NAN)
                } else {
                    f64::NAN
                }))
            }
            "indexOf" => {
                let needle = to_str(&self.heap, arg(0));
                Ok(Value::Num(
                    s.find(&needle).map(|p| s[..p].chars().count() as f64).unwrap_or(-1.0),
                ))
            }
            "slice" => {
                let a = to_num(&self.heap, arg(0)) as i64;
                let b = match args.get(1) {
                    Some(v) => to_num(&self.heap, *v) as i64,
                    None => len,
                };
                let lo = (if a < 0 { len + a } else { a }).clamp(0, len) as usize;
                let hi = (if b < 0 { len + b } else { b }).clamp(0, len) as usize;
                let t: String = if hi > lo { chars[lo..hi].iter().collect() } else { String::new() };
                Ok(Value::Str(self.heap.alloc_str(t)?))
            }
            "substring" => {
                let mut a = (to_num(&self.heap, arg(0)) as i64).clamp(0, len);
                let mut b = match args.get(1) {
                    Some(v) => (to_num(&self.heap, *v) as i64).clamp(0, len),
                    None => len,
                };
                if a > b {
                    std::mem::swap(&mut a, &mut b);
                }
                let t: String = chars[a as usize..b as usize].iter().collect();
                Ok(Value::Str(self.heap.alloc_str(t)?))
            }
            "split" => {
                let sep = to_str(&self.heap, arg(0));
                let parts: Vec<String> = if sep.is_empty() {
                    s.chars().map(|c| c.to_string()).collect()
                } else {
                    s.split(&sep).map(|p| p.to_string()).collect()
                };
                let mut vals = Vec::with_capacity(parts.len());
                for p in parts {
                    vals.push(Value::Str(self.heap.alloc_str(p)?));
                }
                Ok(Value::Obj(self.heap.alloc_obj(Obj::Arr(vals))?))
            }
            "toUpperCase" => Ok(Value::Str(self.heap.alloc_str(s.to_uppercase())?)),
            "toLowerCase" => Ok(Value::Str(self.heap.alloc_str(s.to_lowercase())?)),
            "trim" => Ok(Value::Str(self.heap.alloc_str(s.trim().to_string())?)),
            _ => Err(err(format!("{name} is not a function"))),
        }
    }

    /// Array builtin methods. `.length` is a prop; index ops are Index.
    fn call_arr(&mut self, id: u32, name: &str, env: u32, arg_es: &[Expr]) -> Result<Value, JsError> {
        let args = self.eval_args(env, arg_es)?;
        match name {
            "push" => {
                if let Obj::Arr(v) = self.heap.obj_mut(id) {
                    v.extend_from_slice(&args);
                    return Ok(Value::Num(v.len() as f64));
                }
                Err(err("internal: not an array"))
            }
            "pop" => {
                if let Obj::Arr(v) = self.heap.obj_mut(id) {
                    return Ok(v.pop().unwrap_or(Value::Undef));
                }
                Err(err("internal: not an array"))
            }
            "join" => {
                let sep = match args.first() {
                    None | Some(Value::Undef) => ",".to_string(),
                    Some(v) => to_str(&self.heap, *v),
                };
                let items = match self.heap.obj(id) {
                    Obj::Arr(v) => v.clone(),
                    _ => Vec::new(),
                };
                let s = items
                    .iter()
                    .map(|v| to_str(&self.heap, *v))
                    .collect::<Vec<_>>()
                    .join(&sep);
                Ok(Value::Str(self.heap.alloc_str(s)?))
            }
            "indexOf" => {
                let needle = args.first().copied().unwrap_or(Value::Undef);
                if let Obj::Arr(v) = self.heap.obj(id) {
                    let pos = v
                        .iter()
                        .position(|x| strict_eq(&self.heap, *x, needle))
                        .map(|i| i as f64)
                        .unwrap_or(-1.0);
                    return Ok(Value::Num(pos));
                }
                Err(err("internal: not an array"))
            }
            "slice" => {
                let items = match self.heap.obj(id) {
                    Obj::Arr(v) => v.clone(),
                    _ => Vec::new(),
                };
                let len = items.len() as i64;
                let a = to_num(&self.heap, args.first().copied().unwrap_or(Value::Undef)) as i64;
                let b = match args.get(1) {
                    Some(v) => to_num(&self.heap, *v) as i64,
                    None => len,
                };
                let lo = (if a < 0 { len + a } else { a }).clamp(0, len) as usize;
                let hi = (if b < 0 { len + b } else { b }).clamp(0, len) as usize;
                let sub = if hi > lo { items[lo..hi].to_vec() } else { Vec::new() };
                Ok(Value::Obj(self.heap.alloc_obj(Obj::Arr(sub))?))
            }
            _ => Err(err(format!("{name} is not a function"))),
        }
    }

    /// REPL-style display: objects as JSON, scalars via ToString.
    pub fn inspect(&self, v: Value) -> String {
        match v {
            Value::Obj(_) => val_to_json(&self.heap, v, 0)
                .map(|j| j.to_string())
                .unwrap_or_else(|_| "[object Object]".into()),
            _ => to_str(&self.heap, v),
        }
    }
}

// ---- builtins ------------------------------------------------------------

fn n_console_log(it: &mut Interp, args: &[Value]) -> Result<Value, JsError> {
    let mut line = String::new();
    for (i, a) in args.iter().enumerate() {
        if i > 0 {
            line.push(' ');
        }
        line.push_str(&it.inspect(*a));
    }
    it.out.push_str(&line);
    it.out.push('\n');
    Ok(Value::Undef)
}

fn n_json_parse(it: &mut Interp, args: &[Value]) -> Result<Value, JsError> {
    let src = to_str(&it.heap, args.first().copied().unwrap_or(Value::Undef));
    let j = Json::parse(&src).map_err(|e| err(e.to_string()))?;
    json_to_val(&mut it.heap, &j)
}

fn n_json_stringify(it: &mut Interp, args: &[Value]) -> Result<Value, JsError> {
    let j = val_to_json(&it.heap, args.first().copied().unwrap_or(Value::Undef), 0)?;
    Ok(Value::Str(it.heap.alloc_str(j.to_string())?))
}

fn json_to_val(h: &mut Heap, j: &Json) -> Result<Value, JsError> {
    Ok(match j {
        Json::Null => Value::Null,
        Json::Bool(b) => Value::Bool(*b),
        Json::Num(n) => Value::Num(*n),
        Json::Str(s) => Value::Str(h.alloc_str(s.clone())?),
        Json::Arr(items) => {
            let mut v = Vec::with_capacity(items.len());
            for it in items {
                v.push(json_to_val(h, it)?);
            }
            Value::Obj(h.alloc_obj(Obj::Arr(v))?)
        }
        Json::Obj(pairs) => {
            let mut v = Vec::new();
            for (k, jv) in pairs {
                v.push((k.clone(), json_to_val(h, jv)?));
            }
            Value::Obj(h.alloc_obj(Obj::Ordinary(v))?)
        }
    })
}

/// Value -> Json. Functions and non-finite numbers become null; deep or
/// cyclic graphs error out instead of recursing forever.
fn val_to_json(h: &Heap, v: Value, depth: u32) -> Result<Json, JsError> {
    if depth > 100 {
        return Err(err("object graph too deep or cyclic"));
    }
    Ok(match v {
        Value::Undef | Value::Null => Json::Null,
        Value::Bool(b) => Json::Bool(b),
        Value::Num(n) => {
            if n.is_finite() {
                Json::Num(n)
            } else {
                Json::Null
            }
        }
        Value::Str(id) => Json::Str(h.get_str(id).to_string()),
        Value::Obj(id) => match h.obj(id) {
            Obj::Ordinary(pairs) => Json::Obj(
                pairs
                    .iter()
                    .map(|(k, v)| Ok((k.clone(), val_to_json(h, *v, depth + 1)?)))
                    .collect::<Result<_, JsError>>()?,
            ),
            Obj::Arr(items) => Json::Arr(
                items
                    .iter()
                    .map(|v| val_to_json(h, *v, depth + 1))
                    .collect::<Result<_, JsError>>()?,
            ),
            Obj::Func { .. } | Obj::Native(..) | Obj::Dom(_) => Json::Null,
        },
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ev(src: &str) -> Result<Value, JsError> {
        Interp::new().run(src)
    }

    fn num(src: &str) -> f64 {
        match ev(src).unwrap() {
            Value::Num(n) => n,
            v => panic!("{src} -> {v:?}"),
        }
    }

    fn boolean(src: &str) -> bool {
        match ev(src).unwrap() {
            Value::Bool(b) => b,
            v => panic!("{src} -> {v:?}"),
        }
    }

    /// inspect() the completion value: strings bare, objects JSON.
    fn disp(src: &str) -> String {
        let mut it = Interp::new();
        let v = it.run(src).unwrap();
        it.inspect(v)
    }

    fn out(src: &str) -> String {
        let mut it = Interp::new();
        it.run(src).unwrap();
        it.output().to_string()
    }

    fn errmsg(src: &str) -> String {
        ev(src).unwrap_err().0
    }

    #[test]
    fn arithmetic() {
        assert_eq!(num("1+2*3"), 7.0);
        assert_eq!(num("(1+2)*3"), 9.0);
        assert_eq!(num("10%4"), 2.0);
        assert_eq!(num("7/2"), 3.5);
        assert_eq!(num("2*'3'"), 6.0);
        assert_eq!(num("-5"), -5.0);
        assert_eq!(num("+'3'"), 3.0);
        assert_eq!(num("~5"), -6.0);
        assert_eq!(num("5&3"), 1.0);
        assert_eq!(num("5|3"), 7.0);
        assert_eq!(num("1<<4"), 16.0);
        assert_eq!(num("16>>2"), 4.0);
        assert_eq!(num("-1>>>0"), 4294967295.0);
    }

    #[test]
    fn strings() {
        assert_eq!(disp("'a'+1"), "a1");
        assert_eq!(disp("1+'a'"), "1a");
        assert_eq!(disp("'abc'.toUpperCase()"), "ABC");
        assert_eq!(disp("'AbC'.toLowerCase()"), "abc");
        assert_eq!(disp("'abc'.charAt(1)"), "b");
        assert_eq!(num("'abc'.length"), 3.0);
        assert_eq!(num("'abcabc'.indexOf('c')"), 2.0);
        assert_eq!(num("'nope'.indexOf('z')"), -1.0);
        assert_eq!(disp("'abcdef'.slice(2,4)"), "cd");
        assert_eq!(disp("'abcdef'.slice(-2)"), "ef");
        assert_eq!(disp("'a,b,c'.split(',')[1]"), "b");
        assert_eq!(disp("'  x '.trim()"), "x");
        assert_eq!(num("'abc'.charCodeAt(0)"), 97.0);
        assert_eq!(disp("'abc'[1]"), "b");
    }

    #[test]
    fn compare_and_logic() {
        assert!(boolean("1<2"));
        assert!(boolean("'b'>'a'"));
        assert!(boolean("3=='3'"));
        assert!(!boolean("3==='3'"));
        assert!(boolean("null==undefined"));
        assert!(!boolean("null===undefined"));
        assert!(boolean("'x'!='y'"));
        assert!(boolean("2>=2"));
        assert_eq!(num("1&&2"), 2.0);
        assert_eq!(num("0&&2"), 0.0);
        assert_eq!(disp("''||'d'"), "d");
        assert_eq!(num("3||4"), 3.0);
        assert!(boolean("!0"));
        assert!(!boolean("!'a'"));
        assert_eq!(num("1?2:3"), 2.0);
        assert_eq!(num("0?2:3"), 3.0);
    }

    #[test]
    fn assignment() {
        assert_eq!(num("var a=1;a+=5"), 6.0);
        assert_eq!(num("var a=1,b=2;a*b"), 2.0);
        assert_eq!(num("var o={x:1};o.x+=4;o.x"), 5.0);
        assert_eq!(num("var a=[1];a[0]+=9;a[0]"), 10.0);
        assert_eq!(num("var a=b=7;a+b"), 14.0);
        assert_eq!(num("var i=5;i++"), 5.0);
        assert_eq!(num("var i=5;i++;i"), 6.0);
        assert_eq!(num("var i=5;++i"), 6.0);
        assert_eq!(num("var i=5;--i"), 4.0);
        assert_eq!(num("var o={n:1};o.n++"), 1.0);
        assert_eq!(disp("var s='a';s+='b';s"), "ab");
    }

    #[test]
    fn control_flow() {
        assert_eq!(num("var s=0;var i=0;while(i<10){s+=i;i++}s"), 45.0);
        assert_eq!(num("var s=0;for(var i=0;i<4;i++){s+=i}s"), 6.0);
        assert_eq!(num("var i=0;while(1){i++;if(i>3){break}}i"), 4.0);
        assert_eq!(num("var s=0;for(var i=0;i<6;i++){if(i%2==0){continue}s+=i}s"), 9.0);
        assert_eq!(num("var x=1;if(x){2}else{3}"), 2.0);
        assert_eq!(num("var x=0;if(x){2}else{3}"), 3.0);
    }

    #[test]
    fn functions() {
        assert_eq!(num("function d(x){return x*2}d(21)"), 42.0);
        assert_eq!(
            num("function fib(n){return n<2?n:fib(n-1)+fib(n-2)}fib(15)"),
            610.0
        );
        // closures capture env
        assert_eq!(
            num("function mk(){var c=0;return function(){c+=1;return c}}var f=mk();f();f();f()"),
            3.0
        );
        // fn decl hoists within its block
        assert_eq!(num("f();function f(){return 7}"), 7.0);
        assert_eq!(num("function o(){return i();function i(){return 9}}o()"), 9.0);
        // missing arg -> undefined
        assert_eq!(disp("function f(a,b){return b}f(1)"), "undefined");
        // named fn expr can self-recurse
        assert_eq!(num("var f=function g(n){return n<2?1:n*g(n-1)};f(5)"), 120.0);
        // this binding on member call
        assert_eq!(num("var o={n:7,f:function(){return this.n}};o.f()"), 7.0);
        // unbound call -> this is undefined
        assert!(errmsg("var o={n:1,g:function(){return this.n}};var h=o.g;h()")
            .contains("cannot read"));
    }

    #[test]
    fn scope() {
        assert_eq!(num("var x=1;function f(){var x=2;return x}f()"), 2.0);
        assert_eq!(num("var x=1;function f(){var x=2}f();x"), 1.0);
        // all declarations are block-scoped in v1
        assert_eq!(num("let x=1;{let x=2}x"), 1.0);
        // inner assign reaches outer var through the chain
        assert_eq!(num("var x=1;{x=5}x"), 5.0);
    }

    #[test]
    fn arrays() {
        assert_eq!(num("[1,2,3][1]"), 2.0);
        assert_eq!(num("var a=[1,2];a.push(3);a.length"), 3.0);
        assert_eq!(num("var a=[];a.push('x','y');a.length"), 2.0);
        assert_eq!(num("var a=[1,2,3];a.pop()"), 3.0);
        assert_eq!(disp("[1,2,3].join('-')"), "1-2-3");
        assert_eq!(num("[5,6].indexOf(6)"), 1.0);
        assert_eq!(num("var a=[1,2];a[5]=9;a.length"), 6.0);
        assert_eq!(disp("var a=[1];a[9]"), "undefined");
        assert_eq!(disp("[1,[2,3]]"), "[1,[2,3]]");
        assert_eq!(disp("[9,8,7].slice(1)"), "[8,7]");
        assert_eq!(disp("var a=[];a[9]"), "undefined");
    }

    #[test]
    fn objects() {
        assert_eq!(num("({a:1,b:2}).b"), 2.0);
        assert_eq!(num("var o={};o.x=3;o.x"), 3.0);
        assert_eq!(num("var o={a:1};o['a']"), 1.0);
        assert!(boolean("var o={a:1};'a' in o"));
        assert!(!boolean("var o={a:1};'z' in o"));
        assert!(boolean("1 in [9,9]"));
        assert_eq!(num("var x=4;var o={x};o.x"), 4.0);
        // new: fresh object as this
        assert_eq!(num("function P(){this.x=3}var p=new P();p.x"), 3.0);
        assert_eq!(num("function P(){this.x=1;return {x:2}}new P().x"), 2.0);
    }

    #[test]
    fn json() {
        assert_eq!(disp("JSON.stringify({a:1,b:[2,'x']})"), "{\"a\":1,\"b\":[2,\"x\"]}");
        assert_eq!(num("JSON.parse('{\"a\":[10,20]}').a[1]"), 20.0);
        let src = "var x='{\"k\":[1,2,{\"z\":null}]}';JSON.stringify(JSON.parse(x))";
        assert_eq!(disp(src), "{\"k\":[1,2,{\"z\":null}]}");
        assert!(errmsg("JSON.parse('{')").contains("json"));
    }

    #[test]
    fn typeof_and_coercion() {
        assert_eq!(disp("typeof 1"), "number");
        assert_eq!(disp("typeof 'x'"), "string");
        assert_eq!(disp("typeof null"), "object");
        assert_eq!(disp("typeof undefined"), "undefined");
        assert_eq!(disp("typeof function(){}"), "function");
        assert_eq!(disp("typeof missing_name"), "undefined");
        assert_eq!(disp("var t=typeof{};t"), "object");
        assert_eq!(disp("1+2+'3'"), "33");
        assert_eq!(num("'5'*'2'"), 10.0);
        assert_eq!(num("true+1"), 2.0);
        assert_eq!(disp("''+[]"), "");
    }

    #[test]
    fn console_and_completion() {
        assert_eq!(out("console.log('hi',1+2)"), "hi 3\n");
        assert_eq!(out("console.log([1,2],{a:1})"), "[1,2] {\"a\":1}\n");
        assert_eq!(ev("var a=1").unwrap(), Value::Undef);
        assert_eq!(num("42"), 42.0);
        // `return\n5` is return; then 5 (real ASI)
        assert_eq!(disp("function f(){return\n5}f()"), "undefined");
    }

    #[test]
    fn errors() {
        assert!(errmsg("nope").contains("not defined"));
        assert!(errmsg("var a=1;a()").contains("not a function"));
        assert!(errmsg("null.x").contains("cannot read"));
        assert!(errmsg("undefined.f()").contains("cannot read"));
        assert!(errmsg("1+").contains("byte"));
        // test threads have ~2MB stacks: cap depth low, check the guard
        let mut it = Interp::new();
        it.max_call_depth = 200;
        assert!(it.run("function f(){f()}f()").unwrap_err().0.contains("call depth"));
    }

    #[test]
    fn limits() {
        // heap cap: concat allocates a fresh slot per iteration
        let mut it = Interp::with_cap(20);
        let e = it.run("var s='a';while(1){s=s+s}").unwrap_err();
        assert!(e.0.contains("heap cap"), "{}", e.0);
        // step limit
        let mut it = Interp::new();
        it.max_steps = 100;
        assert!(it.run("while(1){}").unwrap_err().0.contains("step"));
    }
}
