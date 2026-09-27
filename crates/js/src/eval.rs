//! Tree-walking evaluator. `Flow` threads break/continue/return through
//! statement execution. Closures capture their defining EnvId; `this` is
//! an ordinary env binding set per call.

use std::collections::HashMap;
use std::rc::Rc;

use vigia_json::Json;

use crate::ast::{Expr, FnDef, OptOp, Stmt};
use crate::{
    err, fatal, po, Env, Heap, Interp, JsError, Microtask, NativeFn, NetEvent, Obj, PromiseState,
    Protos, ThenHandler, Timer, Value,
};

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
                return u64::from_str_radix(x, 16)
                    .map(|n| n as f64)
                    .unwrap_or(f64::NAN);
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
        return if n > 0.0 {
            "Infinity".into()
        } else {
            "-Infinity".into()
        };
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
        Value::Bool(b) => {
            if b {
                "true".into()
            } else {
                "false".into()
            }
        }
        Value::Num(n) => fmt_num(n),
        Value::Str(id) => h.get_str(id).into(),
        Value::Obj(id) => match h.obj(id) {
            Obj::Arr { items, .. } => items
                .iter()
                .map(|x| match x {
                    Value::Undef | Value::Null => String::new(),
                    _ => to_str(h, *x),
                })
                .collect::<Vec<_>>()
                .join(","),
            Obj::Ordinary { .. } => "[object Object]".into(),
            Obj::Func { def, .. } => {
                format!(
                    "function {}() {{ [code] }}",
                    def.name.as_deref().unwrap_or("")
                )
            }
            Obj::Native { name, .. } => format!("function {name}() {{ [native code] }}"),
            Obj::Dom(_) => "[object Node]".into(),
            Obj::Promise(_) => "[object Promise]".into(),
            Obj::RegExp { pat, flags, .. } => {
                format!("/{}/{}", h.get_str(*pat), h.get_str(*flags))
            }
            Obj::Freed => "[object Object]".into(),
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
            Obj::Func { .. } | Obj::Native { .. } => "function",
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

/// Max prototype-chain hops per lookup (cycles are impossible since proto
/// is set at allocation; the cap also bounds absurdly deep chains).
const MAX_PROTO_HOPS: u32 = 64;

/// An object's own (non-inherited) prop. Arr owns "length" + indices.
fn own_prop(h: &Heap, id: u32, key: &str) -> Option<Value> {
    match h.obj(id) {
        Obj::Ordinary { pairs, .. } | Obj::Func { pairs, .. } | Obj::Native { pairs, .. } => {
            pairs.iter().find(|(k, _)| k == key).map(|(_, v)| *v)
        }
        Obj::Arr { items, .. } => {
            if key == "length" {
                return Some(Value::Num(items.len() as f64));
            }
            key.parse::<usize>()
                .ok()
                .and_then(|i| items.get(i))
                .copied()
        }
        Obj::RegExp {
            pat,
            flags,
            last_index,
            compiled,
            ..
        } => match key {
            "source" => Some(Value::Str(*pat)),
            "flags" => Some(Value::Str(*flags)),
            "lastIndex" => Some(Value::Num(*last_index)),
            "global" => Some(Value::Bool(compiled.flags.global)),
            "ignoreCase" => Some(Value::Bool(compiled.flags.ignore_case)),
            "multiline" => Some(Value::Bool(compiled.flags.multiline)),
            "dotAll" => Some(Value::Bool(compiled.flags.dot_all)),
            _ => None,
        },
        Obj::Dom(_) | Obj::Promise(_) | Obj::Freed => None,
    }
}

/// Heap id of `id`'s prototype. Natives get the Function proto virtually;
/// Dom has none.
fn proto_of(h: &Heap, protos: &Protos, id: u32) -> Option<u32> {
    match h.obj(id) {
        Obj::Ordinary { proto, .. } | Obj::Arr { proto, .. } | Obj::Func { proto, .. } => *proto,
        Obj::Native { .. } => po(protos.function_),
        Obj::Promise(_) => po(protos.promise),
        Obj::RegExp { proto, .. } => *proto,
        Obj::Dom(_) | Obj::Freed => None,
    }
}

/// Walk `start` then its proto chain; first own prop wins. Cap hops.
fn walk_props(h: &Heap, protos: &Protos, start: Option<u32>, key: &str) -> Result<Value, JsError> {
    let mut cur = start;
    for _ in 0..MAX_PROTO_HOPS {
        let Some(id) = cur else {
            return Ok(Value::Undef);
        };
        if let Some(v) = own_prop(h, id, key) {
            return Ok(v);
        }
        cur = proto_of(h, protos, id);
    }
    Ok(Value::Undef)
}

/// `key in v` over the proto chain (rhs must already be an object).
fn has_prop(h: &Heap, protos: &Protos, v: Value, key: &str) -> bool {
    let mut cur = match v {
        Value::Obj(id) => Some(id),
        _ => return false,
    };
    for _ in 0..MAX_PROTO_HOPS {
        let Some(id) = cur else { return false };
        if own_prop(h, id, key).is_some() {
            return true;
        }
        cur = proto_of(h, protos, id);
    }
    false
}

/// `v[key]`: own props, then proto chain, then Undef. Primitives map to
/// their protos (Str keeps `length` first).
pub(crate) fn get_prop(h: &Heap, protos: &Protos, v: Value, key: &str) -> Result<Value, JsError> {
    match v {
        Value::Obj(id) => walk_props(h, protos, Some(id), key),
        Value::Str(id) => {
            if key == "length" {
                return Ok(Value::Num(h.get_str(id).chars().count() as f64));
            }
            walk_props(h, protos, po(protos.string), key)
        }
        Value::Num(_) => walk_props(h, protos, po(protos.number), key),
        Value::Undef | Value::Null => Err(err(format!(
            "cannot read '{key}' of {}",
            if matches!(v, Value::Null) {
                "null"
            } else {
                "undefined"
            }
        ))),
        _ => Ok(Value::Undef),
    }
}

/// Writes to own pairs only (Ordinary/Func/Native), like standard JS.
pub(crate) fn set_prop(h: &mut Heap, v: Value, key: &str, val: Value) -> Result<(), JsError> {
    // Computed before the mutable borrow below.
    let last_num = to_num(&*h, val);
    match v {
        Value::Obj(id) => match h.obj_mut(id) {
            Obj::Ordinary { pairs, .. } | Obj::Func { pairs, .. } | Obj::Native { pairs, .. } => {
                match pairs.iter_mut().find(|(k, _)| k == key) {
                    Some(slot) => slot.1 = val,
                    None => pairs.push((key.to_string(), val)),
                }
                Ok(())
            }
            Obj::RegExp { last_index, .. } if key == "lastIndex" => {
                *last_index = last_num;
                Ok(())
            }
            _ => Err(err("cannot set property on this object")),
        },
        Value::Undef | Value::Null => Err(err("cannot set property of null/undefined")),
        _ => Ok(()), // primitives: sloppy no-op like real JS
    }
}

fn get_index(h: &mut Heap, protos: &Protos, v: Value, k: Value) -> Result<Value, JsError> {
    match v {
        Value::Obj(id) => {
            let n = to_num(h, k);
            match h.obj(id) {
                Obj::Arr { items, .. } if n >= 0.0 && n.fract() == 0.0 => {
                    Ok(items.get(n as usize).copied().unwrap_or(Value::Undef))
                }
                Obj::Dom(_) => Ok(Value::Undef),
                _ => {
                    let key = to_str(h, k);
                    get_prop(h, protos, v, &key)
                }
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
                None => {
                    let key = to_str(h, k);
                    get_prop(h, protos, v, &key)
                }
            }
        }
        Value::Undef | Value::Null => Err(err("cannot index into null/undefined")),
        _ => {
            let key = to_str(h, k);
            get_prop(h, protos, v, &key)
        }
    }
}

fn set_index(h: &mut Heap, v: Value, k: Value, val: Value) -> Result<(), JsError> {
    match v {
        Value::Obj(id) => {
            if matches!(h.obj(id), Obj::Arr { .. }) {
                let n = to_num(h, k);
                if !(n >= 0.0 && n.fract() == 0.0 && n <= 10_000_000.0) {
                    return Err(err("bad array index"));
                }
                let i = n as usize;
                if let Obj::Arr { items, .. } = h.obj_mut(id) {
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
    // ---- object allocation helpers (proto wiring lives here) ----------

    /// Fresh Ordinary under Object.prototype.
    pub(crate) fn obj_plain(&mut self) -> Result<u32, JsError> {
        let proto = po(self.protos.object);
        self.heap.alloc_obj(Obj::Ordinary {
            pairs: Vec::new(),
            proto,
        })
    }

    /// Fresh Ordinary with props, under Object.prototype.
    pub(crate) fn obj_pairs(&mut self, pairs: Vec<(String, Value)>) -> Result<u32, JsError> {
        let proto = po(self.protos.object);
        self.heap.alloc_obj(Obj::Ordinary { pairs, proto })
    }

    /// Fresh Arr under Array.prototype.
    pub(crate) fn arr_obj(&mut self, items: Vec<Value>) -> Result<u32, JsError> {
        let proto = po(self.protos.array);
        self.heap.alloc_obj(Obj::Arr { items, proto })
    }

    /// Fresh Func under Function.prototype, with an own "prototype" object
    /// (fresh Ordinary under Object's proto) like real JS.
    pub(crate) fn func_obj(&mut self, def: Rc<FnDef>, env: u32) -> Result<u32, JsError> {
        let pt = self.obj_plain()?;
        let proto = po(self.protos.function_);
        self.heap.alloc_obj(Obj::Func {
            def,
            env,
            proto,
            pairs: vec![("prototype".into(), Value::Obj(pt))],
        })
    }

    /// push a Native method onto a pairs-holding obj (proto bag or ctor).
    /// Heap-cap edge: skips silently when there's no room.
    fn put(&mut self, on: u32, name: &'static str, f: NativeFn) {
        let Ok(n) = self.heap.alloc_obj(nat(name, f)) else {
            return;
        };
        match self.heap.obj_mut(on) {
            Obj::Ordinary { pairs, .. } | Obj::Func { pairs, .. } | Obj::Native { pairs, .. } => {
                pairs.push((name.into(), Value::Obj(n)))
            }
            _ => {}
        }
    }

    /// A constructor global: Native with own statics + "prototype" pair.
    fn ctor(
        &mut self,
        name: &'static str,
        f: NativeFn,
        proto: u32,
        statics: &[(&'static str, NativeFn)],
    ) {
        let mut pairs = Vec::with_capacity(statics.len() + 1);
        for (n, m) in statics {
            let Ok(id) = self.heap.alloc_obj(nat(n, *m)) else {
                return;
            };
            pairs.push((n.to_string(), Value::Obj(id)));
        }
        if let Some(pt) = po(proto) {
            pairs.push(("prototype".into(), Value::Obj(pt)));
        }
        if let Ok(id) = self.heap.alloc_obj(Obj::Native { name, f, pairs }) {
            self.env_declare(0, name, Value::Obj(id));
        }
    }

    /// Alloc a proto bag under Object's proto, filled with `methods`.
    /// u32::MAX on heap-cap failure.
    fn proto_bag(&mut self, methods: &[(&'static str, NativeFn)]) -> u32 {
        let proto = po(self.protos.object);
        let Ok(id) = self.heap.alloc_obj(Obj::Ordinary {
            pairs: vec![],
            proto,
        }) else {
            return u32::MAX;
        };
        for (n, f) in methods {
            self.put(id, n, *f);
        }
        id
    }

    /// Allocate the shared prototype objects once (called from with_cap).
    /// Cap edge: protos left as u32::MAX when there's no room - property
    /// lookup then degrades to own props only.
    pub(crate) fn install_protos(&mut self) {
        let Ok(object) = self.heap.alloc_obj(Obj::Ordinary {
            pairs: vec![],
            proto: None,
        }) else {
            return;
        };
        self.protos.object = object;
        self.put(object, "hasOwnProperty", n_has_own);
        self.put(object, "toString", n_obj_to_string);

        self.protos.function_ = self.proto_bag(&[("call", n_fn_call), ("apply", n_fn_apply)]);
        self.protos.array = self.proto_bag(&[
            ("push", n_arr_push),
            ("pop", n_arr_pop),
            ("shift", n_arr_shift),
            ("unshift", n_arr_unshift),
            ("map", n_arr_map),
            ("filter", n_arr_filter),
            ("forEach", n_arr_for_each),
            ("reduce", n_arr_reduce),
            ("join", n_arr_join),
            ("indexOf", n_arr_index_of),
            ("lastIndexOf", n_arr_last_index_of),
            ("includes", n_arr_includes),
            ("slice", n_arr_slice),
            ("concat", n_arr_concat),
            ("find", n_arr_find),
            ("findIndex", n_arr_find_index),
            ("some", n_arr_some),
            ("every", n_arr_every),
            ("reverse", n_arr_reverse),
            ("sort", n_arr_sort),
            ("splice", n_arr_splice),
            ("flat", n_arr_flat),
        ]);
        self.protos.string = self.proto_bag(&[
            ("split", n_str_split),
            ("indexOf", n_str_index_of),
            ("lastIndexOf", n_str_last_index_of),
            ("slice", n_str_slice),
            ("substring", n_str_substring),
            ("trim", n_str_trim),
            ("trimStart", n_str_trim_start),
            ("trimEnd", n_str_trim_end),
            ("toUpperCase", n_str_to_upper),
            ("toLowerCase", n_str_to_lower),
            ("includes", n_str_includes),
            ("startsWith", n_str_starts_with),
            ("endsWith", n_str_ends_with),
            ("charAt", n_str_char_at),
            ("charCodeAt", n_str_char_code_at),
            ("replace", n_str_replace),
            ("match", n_str_match),
            ("search", n_str_search),
            ("concat", n_str_concat),
            ("repeat", n_str_repeat),
            ("padStart", n_str_pad_start),
            ("padEnd", n_str_pad_end),
        ]);
        self.protos.number = self.proto_bag(&[("toFixed", n_num_to_fixed)]);
        self.protos.promise = self.proto_bag(&[
            ("then", n_promise_then),
            ("catch", n_promise_catch),
            ("finally", n_promise_finally),
        ]);
        self.protos.date = self.proto_bag(&[
            ("getTime", n_date_get_time),
            ("toISOString", n_date_iso),
            ("valueOf", n_date_get_time),
        ]);
        self.protos.regexp = self.proto_bag(&[("test", n_regexp_test), ("exec", n_regexp_exec)]);
        // Error.prototype: `name` as a data prop + a real toString method
        let mut eps: Vec<(String, Value)> = Vec::new();
        if let Ok(nm) = self.heap.intern_str("Error") {
            eps.push(("name".into(), Value::Str(nm)));
        }
        let proto = po(self.protos.object);
        if let Ok(ep) = self.heap.alloc_obj(Obj::Ordinary { pairs: eps, proto }) {
            self.protos.error = ep;
            self.put(ep, "toString", n_err_to_string);
        }
    }

    pub(crate) fn install_builtins(&mut self) {
        if self.builtins {
            return;
        }
        self.builtins = true;
        let pr = self.protos;
        // cap edge: installs silently skip when there's no room
        self.ctor(
            "Object",
            n_object,
            pr.object,
            &[
                ("keys", n_obj_keys),
                ("values", n_obj_values),
                ("entries", n_obj_entries),
                ("assign", n_obj_assign),
                ("create", n_obj_create),
            ],
        );
        self.ctor(
            "Array",
            n_array,
            pr.array,
            &[("isArray", n_is_array), ("of", n_array_of)],
        );
        self.ctor("String", n_string_cast, pr.string, &[]);
        self.ctor("Number", n_number_cast, pr.number, &[]);
        self.ctor("Boolean", n_boolean_cast, u32::MAX, &[]);
        self.ctor("Date", n_date, pr.date, &[("now", n_date_now)]);
        self.ctor("RegExp", n_regexp_ctor, pr.regexp, &[]);
        self.ctor("Error", n_error, pr.error, &[]);
        self.ctor(
            "Promise",
            n_promise_ctor,
            pr.promise,
            &[
                ("resolve", n_promise_static_resolve),
                ("reject", n_promise_static_reject),
                ("all", n_promise_all),
                ("race", n_promise_race),
                ("allSettled", n_promise_all_settled),
            ],
        );
        for (n, f) in [
            ("parseInt", n_parse_int as NativeFn),
            ("parseFloat", n_parse_float),
            ("isNaN", n_is_nan),
            ("isFinite", n_is_finite),
            ("setTimeout", n_set_timeout),
            ("setInterval", n_set_interval),
            ("clearTimeout", n_clear_timeout),
            ("clearInterval", n_clear_interval),
            ("queueMicrotask", n_queue_microtask),
        ] {
            if let Ok(id) = self.heap.alloc_obj(nat(n, f)) {
                self.env_declare(0, n, Value::Obj(id));
            }
        }
        // Math: plain object of fns + constants
        let mut mp: Vec<(String, Value)> = Vec::new();
        for (n, f) in [
            ("floor", n_math_floor as NativeFn),
            ("ceil", n_math_ceil),
            ("round", n_math_round),
            ("random", n_math_random),
            ("max", n_math_max),
            ("min", n_math_min),
            ("abs", n_math_abs),
            ("pow", n_math_pow),
            ("sqrt", n_math_sqrt),
        ] {
            match self.heap.alloc_obj(nat(n, f)) {
                Ok(id) => mp.push((n.into(), Value::Obj(id))),
                Err(_) => break,
            }
        }
        mp.push(("PI".into(), Value::Num(std::f64::consts::PI)));
        mp.push(("E".into(), Value::Num(std::f64::consts::E)));
        if let Ok(m) = self.obj_pairs(mp) {
            self.env_declare(0, "Math", Value::Obj(m));
        }
        if let Ok(log) = self.heap.alloc_obj(nat("log", n_console_log)) {
            if let Ok(c) = self.obj_pairs(vec![("log".into(), Value::Obj(log))]) {
                self.env_declare(0, "console", Value::Obj(c));
            }
        }
        if let Ok(p) = self.heap.alloc_obj(nat("parse", n_json_parse)) {
            if let Ok(s) = self.heap.alloc_obj(nat("stringify", n_json_stringify)) {
                if let Ok(j) = self.obj_pairs(vec![
                    ("parse".into(), Value::Obj(p)),
                    ("stringify".into(), Value::Obj(s)),
                ]) {
                    self.env_declare(0, "JSON", Value::Obj(j));
                }
            }
        }
        if let Ok(f) = self.heap.alloc_obj(nat("fetch", n_fetch)) {
            self.env_declare(0, "fetch", Value::Obj(f));
        }
        self.env_declare(0, "this", Value::Undef);
    }

    fn tick(&mut self) -> Result<(), JsError> {
        self.steps += 1;
        if self.steps > self.max_steps {
            return Err(fatal("step limit exceeded"));
        }
        Ok(())
    }

    pub(crate) fn new_env(&mut self, parent: u32) -> Result<u32, JsError> {
        if let Some(id) = self.free_envs.pop() {
            let e = &mut self.envs[id as usize];
            e.vars.clear();
            e.parent = Some(parent);
            e.free = false;
            return Ok(id);
        }
        if self.envs.len() >= self.max_envs {
            return Err(fatal("env cap"));
        }
        self.envs.push(Env {
            vars: HashMap::new(),
            parent: Some(parent),
            free: false,
        });
        Ok(self.envs.len() as u32 - 1)
    }

    pub(crate) fn env_declare(&mut self, env: u32, name: &str, v: Value) {
        self.envs[env as usize].vars.insert(name.to_string(), v);
    }

    pub(crate) fn env_get(&self, env: u32, name: &str) -> Option<Value> {
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
    /// `env` rides env_stack for the block's duration so GC marking sees
    /// every open frame (a caller's env is only reachable through it).
    pub(crate) fn exec_block(&mut self, stmts: &[Stmt], env: u32) -> Result<Flow, JsError> {
        self.env_stack.push(env);
        let r = self.exec_block_run(stmts, env);
        self.env_stack.pop();
        r
    }

    fn exec_block_run(&mut self, stmts: &[Stmt], env: u32) -> Result<Flow, JsError> {
        for s in stmts {
            if let Stmt::FnDecl(def) = s {
                let f = self.func_obj(def.clone(), env)?;
                if let Some(n) = &def.name {
                    self.env_declare(env, n, Value::Obj(f));
                }
            }
        }
        for s in stmts {
            self.tick()?;
            // safepoint: the previous statement's temporaries are consumed
            self.maybe_gc();
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
                    self.maybe_gc();
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
            Stmt::For(init, test, upd, body) => self.stmt_for(env, init, test, upd, body),
            Stmt::ForOf {
                name,
                is_decl,
                iter,
                body,
            } => self.stmt_for_of(env, name, *is_decl, iter, body),
            Stmt::Block(ss) => self.exec_scoped(env, ss),
            Stmt::Break => Ok(Flow::Break),
            Stmt::Continue => Ok(Flow::Continue),
            Stmt::Throw(e) => {
                let v = self.expr(env, e)?;
                Err(JsError::Throw(v))
            }
            Stmt::Try {
                body,
                catch,
                finally,
            } => self.stmt_try(env, body, catch, finally),
        }
    }

    /// Braced body in a fresh env only when it declares names - the
    /// scoping rule Stmt::Block and the try clauses share.
    fn exec_scoped(&mut self, env: u32, ss: &[Stmt]) -> Result<Flow, JsError> {
        if ss
            .iter()
            .any(|s| matches!(s, Stmt::VarDecl(_) | Stmt::FnDecl(_)))
        {
            let e2 = self.new_env(env)?;
            self.exec_block(ss, e2)
        } else {
            self.exec_block(ss, env)
        }
    }

    /// try/catch/finally. catch sees only catchable errors (thrown values
    /// and internal Msgs - Fatal blows straight through). finally runs on
    /// every exit incl. return/break/continue, and its own abrupt
    /// completion (a throw or a control-flow Flow) overrides whatever was
    /// in flight.
    fn stmt_try(
        &mut self,
        env: u32,
        body: &[Stmt],
        catch: &Option<(Option<String>, Vec<Stmt>)>,
        finally: &Option<Vec<Stmt>>,
    ) -> Result<Flow, JsError> {
        let r = self.exec_scoped(env, body);
        let r = match (r, catch) {
            (Err(e), Some((param, cbody))) if e.catchable() => {
                match self.catch_env(env, param.as_deref(), e) {
                    Ok(cenv) => self.exec_block(cbody, cenv),
                    Err(e2) => Err(e2),
                }
            }
            (r, _) => r,
        };
        let Some(fbody) = finally else { return r };
        match self.exec_scoped(env, fbody) {
            Ok(Flow::Normal) => r,
            abrupt => abrupt,
        }
    }

    /// Fresh env for a catch block, holding the param binding when one
    /// exists: thrown values bind verbatim; an internal Msg materializes
    /// as an Error object so `e.message`/`e instanceof Error` work.
    fn catch_env(&mut self, env: u32, param: Option<&str>, e: JsError) -> Result<u32, JsError> {
        let v = match e {
            JsError::Throw(v) => v,
            JsError::Msg(m) => self.error_obj(&m)?,
            JsError::Fatal(_) => unreachable!("fatal errors aren't catchable"),
        };
        let cenv = self.new_env(env)?;
        if let Some(p) = param {
            self.env_declare(cenv, p, v);
        }
        Ok(cenv)
    }

    /// for(init; test; upd) body: the decl env rides env_stack so GC
    /// keeps the loop var's env alive even when the body opens no block.
    fn stmt_for(
        &mut self,
        env: u32,
        init: &Option<Box<Stmt>>,
        test: &Option<Expr>,
        upd: &Option<Expr>,
        body: &Stmt,
    ) -> Result<Flow, JsError> {
        let fenv = self.new_env(env)?;
        self.env_stack.push(fenv);
        let r = self.stmt_for_loop(fenv, init, test, upd, body);
        self.env_stack.pop();
        r
    }

    fn stmt_for_loop(
        &mut self,
        fenv: u32,
        init: &Option<Box<Stmt>>,
        test: &Option<Expr>,
        upd: &Option<Expr>,
        body: &Stmt,
    ) -> Result<Flow, JsError> {
        if let Some(init) = init {
            match self.stmt(fenv, init)? {
                Flow::Normal => {}
                f => return Ok(f),
            }
        }
        loop {
            self.tick()?;
            self.maybe_gc();
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

    /// Strict for-of over arrays and strings. Objects and other iterables
    /// report `not iterable` instead of silently producing nothing.
    fn stmt_for_of(
        &mut self,
        env: u32,
        name: &str,
        is_decl: bool,
        iter: &Expr,
        body: &Stmt,
    ) -> Result<Flow, JsError> {
        let v = self.expr(env, iter)?;
        let items: Vec<Value> = match v {
            Value::Obj(id) => match self.heap.obj(id) {
                Obj::Arr { items, .. } => items.clone(),
                _ => return Err(err("for-of only over arrays and strings")),
            },
            Value::Str(id) => {
                let s = self.heap.get_str(id).to_string();
                let mut out = Vec::new();
                for ch in s.chars() {
                    out.push(Value::Str(self.heap.alloc_str(ch.to_string())?));
                }
                out
            }
            _ => return Err(err("for-of only over arrays and strings")),
        };
        let fenv = self.new_env(env)?;
        self.env_stack.push(fenv);
        let r = self.stmt_for_of_loop(fenv, name, is_decl, &items, body);
        self.env_stack.pop();
        r
    }

    fn stmt_for_of_loop(
        &mut self,
        fenv: u32,
        name: &str,
        is_decl: bool,
        items: &[Value],
        body: &Stmt,
    ) -> Result<Flow, JsError> {
        for &item in items {
            self.tick()?;
            self.maybe_gc();
            if is_decl {
                self.env_declare(fenv, name, item);
            } else if !self.env_set(fenv, name, item) {
                self.env_declare(0, name, item);
            }
            match self.stmt(fenv, body)? {
                Flow::Normal | Flow::Continue => {}
                Flow::Break => break,
                f => return Ok(f),
            }
        }
        Ok(Flow::Normal)
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
                Ok(Value::Obj(self.arr_obj(v)?))
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
                Ok(Value::Obj(self.obj_pairs(pairs)?))
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
                    None => get_prop(&self.heap, &self.protos, v, name),
                }
            }
            Expr::Regex { pat, flags } => make_regexp(self, pat, flags),
            Expr::Tpl(parts, tail) => {
                let mut s = String::new();
                for (cooked, e) in parts {
                    s.push_str(cooked);
                    let v = self.expr(env, e)?;
                    s.push_str(&to_str(&self.heap, v));
                }
                s.push_str(tail);
                Ok(Value::Str(self.heap.intern_str(&s)?))
            }
            Expr::OptChain(b, ops) => self.opt_chain(env, b, ops),
            Expr::Index(o, ix) => {
                let v = self.expr(env, o)?;
                let k = self.expr(env, ix)?;
                match self.as_node(v) {
                    Some(n) => {
                        let key = to_str(&self.heap, k);
                        self.dom_get(n, &key)
                    }
                    None => get_index(&mut self.heap, &self.protos, v, k),
                }
            }
            Expr::Func(def) => Ok(Value::Obj(self.func_obj(def.clone(), env)?)),
            Expr::New(c, args) => {
                let f = self.expr(env, c)?;
                if let Value::Obj(id) = f {
                    if let Obj::Func { def, .. } = self.heap.obj(id) {
                        if def.is_arrow {
                            return Err(err("arrow is not a constructor"));
                        }
                    }
                }
                let args = self.eval_args(env, args)?;
                // proto = callee.prototype when it's an object (JS); natives
                // may ignore `this` and return their own object anyway.
                let proto = match get_prop(&self.heap, &self.protos, f, "prototype")? {
                    Value::Obj(p) => Some(p),
                    _ => po(self.protos.object),
                };
                let obj = self.heap.alloc_obj(Obj::Ordinary {
                    pairs: vec![],
                    proto,
                })?;
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
            "await" => {
                if !self.fn_async {
                    return Err(err("await outside async"));
                }
                let v = self.expr(env, e)?;
                match as_promise(self, v) {
                    None => Ok(v), // non-promise awaits pass through
                    Some(pid) => {
                        // await counts as handling: its rejection becomes the
                        // async fn's own rejection, not an unhandled one
                        self.handled_promises.insert(pid);
                        match self.heap.obj(pid) {
                            Obj::Promise(PromiseState::Fulfilled(u)) => Ok(*u),
                            // the reason value itself is thrown, so a
                            // try/catch around the await sees it verbatim
                            Obj::Promise(PromiseState::Rejected(r)) => Err(JsError::Throw(*r)),
                            Obj::Promise(PromiseState::Pending { .. }) => {
                                Err(err("await on pending promise (vigia settles fetch/timer \
                                 eagerly; pending awaits unsupported)"))
                            }
                            _ => Ok(v),
                        }
                    }
                }
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
            "??" => {
                let lv = self.expr(env, l)?;
                if matches!(lv, Value::Null | Value::Undef) {
                    return self.expr(env, r);
                }
                Ok(lv)
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
                    Value::Obj(_) => Value::Bool(has_prop(h, &self.protos, r, &key)),
                    _ => return Err(err("'in' needs an object on the right")),
                }
            }
            "instanceof" => {
                // target = rhs.prototype (rhs must be callable); lhs chain
                // walk answers whether target sits on it.
                let target = match r {
                    Value::Obj(id)
                        if matches!(h.obj(id), Obj::Func { .. } | Obj::Native { .. }) =>
                    {
                        get_prop(h, &self.protos, r, "prototype")?
                    }
                    _ => return Err(err("instanceof: right side is not a function")),
                };
                let Value::Obj(tid) = target else {
                    return Ok(Value::Bool(false));
                };
                let mut cur = match l {
                    Value::Obj(id) => proto_of(h, &self.protos, id),
                    _ => None,
                };
                let mut hit = false;
                for _ in 0..MAX_PROTO_HOPS {
                    match cur {
                        Some(c) if c == tid => {
                            hit = true;
                            break;
                        }
                        Some(c) => cur = proto_of(h, &self.protos, c),
                        None => break,
                    }
                }
                Value::Bool(hit)
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
                    None => get_prop(&self.heap, &self.protos, v, k),
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
                    None => get_index(&mut self.heap, &self.protos, v, k),
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
                // DOM node methods dispatch on the node, not the property map
                if let Some(n) = self.as_node(recv) {
                    return self.call_dom(n, name, env, arg_es);
                }
                // proto chains resolve string/array/etc methods to Natives;
                // `this` = the receiver
                (
                    get_prop(&self.heap, &self.protos, recv, name)?,
                    recv,
                    Some(name.as_str()),
                )
            }
            Expr::Index(o, ix) => {
                let recv = self.expr(env, o)?;
                let k = self.expr(env, ix)?;
                if let (Value::Obj(id), Value::Str(s)) = (recv, k) {
                    if let Obj::Dom(n) = self.heap.obj(id) {
                        let (n, m) = (*n, self.heap.get_str(s).to_string());
                        return self.call_dom(n, &m, env, arg_es);
                    }
                }
                (
                    get_index(&mut self.heap, &self.protos, recv, k)?,
                    recv,
                    None,
                )
            }
            Expr::Ident(n) => (self.expr(env, callee)?, Value::Undef, Some(n.as_str())),
            _ => (self.expr(env, callee)?, Value::Undef, None),
        };
        let args = self.eval_args(env, arg_es)?;
        self.call_value(f, this, &args, hint)
    }

    fn opt_chain(&mut self, env: u32, base: &Expr, ops: &[OptOp]) -> Result<Value, JsError> {
        let mut cur = self.expr(env, base)?;
        let mut parent = Value::Undef;
        let mut method: Option<String> = None;
        let mut short = false;
        for op in ops {
            if short {
                return Ok(Value::Undef);
            }
            match op {
                OptOp::Member(name, opt) => {
                    if matches!(cur, Value::Null | Value::Undef) {
                        if *opt {
                            short = true;
                            cur = Value::Undef;
                            parent = Value::Undef;
                            method = None;
                            continue;
                        }
                        return Err(err(format!(
                            "cannot read '{}' of {}",
                            name,
                            if matches!(cur, Value::Null) {
                                "null"
                            } else {
                                "undefined"
                            }
                        )));
                    }
                    parent = cur;
                    method = Some(name.clone());
                    cur = match self.as_node(cur) {
                        Some(n) => self.dom_get(n, name)?,
                        None => get_prop(&self.heap, &self.protos, cur, name)?,
                    };
                }
                OptOp::Index(key, opt) => {
                    if matches!(cur, Value::Null | Value::Undef) {
                        if *opt {
                            short = true;
                            cur = Value::Undef;
                            parent = Value::Undef;
                            method = None;
                            continue;
                        }
                        return Err(err("cannot index into null/undefined"));
                    }
                    let k = self.expr(env, key)?;
                    let recv = cur;
                    parent = recv;
                    method = match k {
                        Value::Str(s) => Some(self.heap.get_str(s).to_string()),
                        _ => None,
                    };
                    cur = match self.as_node(recv) {
                        Some(n) => {
                            let kk = to_str(&self.heap, k);
                            self.dom_get(n, &kk)?
                        }
                        None => get_index(&mut self.heap, &self.protos, recv, k)?,
                    };
                }
                OptOp::Call(arg_es, opt) => {
                    if matches!(cur, Value::Null | Value::Undef) {
                        if *opt {
                            return Ok(Value::Undef);
                        }
                        return Err(err("is not a function"));
                    }
                    if let Some(n) = self.as_node(parent) {
                        if let Some(m) = method.take() {
                            cur = self.call_dom(n, &m, env, arg_es)?;
                            parent = Value::Undef;
                            continue;
                        }
                    }
                    let args = self.eval_args(env, arg_es)?;
                    let this = parent;
                    parent = Value::Undef;
                    method = None;
                    cur = self.call_value(cur, this, &args, None)?;
                }
            }
        }
        if short {
            Ok(Value::Undef)
        } else {
            Ok(cur)
        }
    }

    pub(crate) fn call_value(
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
            Obj::Func { def, env, .. } => C::Fn(def.clone(), *env),
            Obj::Native { f, .. } => C::Nat(*f),
            _ => {
                return Err(err(format!(
                    "{} is not a function",
                    hint.unwrap_or("object")
                )))
            }
        };
        self.tick()?;
        self.call_depth += 1;
        if self.call_depth > self.max_call_depth {
            self.call_depth -= 1;
            return Err(fatal("max call depth"));
        }
        // Root callee/this/args for the call's duration: GC can't see Rust
        // locals, so a callback a native holds (arr.map's f) or an IIFE
        // temp would otherwise be swept mid-execution.
        let vbase = self.call_vals.len();
        self.call_vals.push(f);
        self.call_vals.push(this);
        self.call_vals.extend_from_slice(args);
        let (is_async, r) = match c {
            C::Fn(def, fenv) => {
                let cenv = match self.new_env(fenv) {
                    Ok(cenv) => cenv,
                    Err(e) => {
                        self.call_vals.truncate(vbase);
                        self.call_depth -= 1;
                        return Err(e);
                    }
                };
                for (i, p) in def.params.iter().enumerate() {
                    self.env_declare(cenv, p, args.get(i).copied().unwrap_or(Value::Undef));
                }
                if let Some(n) = &def.name {
                    // named fn exprs can self-recurse via their own name
                    self.env_declare(cenv, n, f);
                }
                // Arrows capture `this` lexically from the defining env.
                let this_val = if def.is_arrow {
                    self.env_get(fenv, "this").unwrap_or(Value::Undef)
                } else {
                    this
                };
                self.env_declare(cenv, "this", this_val);
                // `await` binds to the nearest enclosing fn, so the flag
                // is shadowed per call rather than accumulated.
                let prev_async = self.fn_async;
                self.fn_async = def.is_async;
                let r = match self.exec_block(&def.body, cenv) {
                    Ok(Flow::Return(v)) => Ok(v),
                    Ok(_) => Ok(Value::Undef),
                    Err(e) => Err(e),
                };
                self.fn_async = prev_async;
                (def.is_async, r)
            }
            C::Nat(nf) => {
                // cur_native exposes the callee object to natives that
                // carry bound state in their own props ("__p", "__f", ...).
                let prev = self.cur_native;
                self.cur_native = f;
                let r = nf(self, this, args);
                self.cur_native = prev;
                (false, r)
            }
        };
        self.call_vals.truncate(vbase);
        self.call_depth -= 1;
        if is_async {
            // async fn: a return fulfills (promises adopt); a `throw`
            // rejects with the thrown value verbatim, an internal error
            // with its message text. Fatal propagates instead - the
            // promise just stays pending (and unreported).
            match r {
                Ok(v) => {
                    let p = promise_new(self)?;
                    self.promise_resolve(p, v);
                    Ok(Value::Obj(p))
                }
                Err(e @ JsError::Fatal(_)) => Err(e),
                Err(e) => {
                    let p = promise_new(self)?;
                    let v = err_value(self, e);
                    self.promise_settle(p, true, v);
                    Ok(Value::Obj(p))
                }
            }
        } else {
            r
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

    /// Fresh Error object under Error.prototype carrying `msg`.
    pub(crate) fn error_obj(&mut self, msg: &str) -> Result<Value, JsError> {
        let proto = po(self.protos.error);
        let m = Value::Str(self.heap.alloc_str(msg.to_string())?);
        Ok(Value::Obj(self.heap.alloc_obj(Obj::Ordinary {
            pairs: vec![("message".into(), m)],
            proto,
        })?))
    }

    /// Text of a thrown value for an error report: objects with a
    /// `message` prop (Error-shaped) render "Name: message".
    fn thrown_text(&self, v: Value) -> String {
        if let Value::Obj(_) = v {
            if let Ok(m) = get_prop(&self.heap, &self.protos, v, "message") {
                if !matches!(m, Value::Undef) {
                    let mut name = get_prop(&self.heap, &self.protos, v, "name")
                        .map(|n| to_str(&self.heap, n))
                        .unwrap_or_default();
                    if name.is_empty() {
                        name = "Error".into();
                    }
                    let ms = to_str(&self.heap, m);
                    return if ms.is_empty() {
                        name
                    } else {
                        format!("{name}: {ms}")
                    };
                }
            }
        }
        to_str(&self.heap, v)
    }

    /// Boundary render: a thrown value becomes its text (the heap id
    /// inside Throw isn't rooted once the error leaves eval); Msg and
    /// Fatal pass through unchanged.
    pub(crate) fn bound_err(&self, e: JsError) -> JsError {
        match e {
            JsError::Throw(v) => err(self.thrown_text(v)),
            _ => e,
        }
    }
}

// ---- builtins ------------------------------------------------------------

fn n_console_log(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
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

fn n_json_parse(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let src = to_str(&it.heap, args.first().copied().unwrap_or(Value::Undef));
    let j = Json::parse(&src).map_err(|e| err(e.to_string()))?;
    json_to_val(it, &j)
}

fn n_json_stringify(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let j = val_to_json(&it.heap, args.first().copied().unwrap_or(Value::Undef), 0)?;
    Ok(Value::Str(it.heap.alloc_str(j.to_string())?))
}

/// fetch(url) - the HTTP request still executes eagerly at call time
/// (synchronous engine), but the result is a resolved Promise holding the
/// response object; a network failure rejects the Promise instead of
/// throwing (real fetch semantics). The response carries status/ok/
/// redirected/url plus the body under `__body`; text()/json() read it off
/// `this` and return resolved Promises like real Response methods.
/// Truncate a body for the net trace - discovery needs the payload's
/// shape, not megabytes of it.
fn trunc_body(s: &str) -> String {
    s.chars().take(4096).collect()
}

/// Read {method, headers, body} off a fetch() init object.
fn fetch_init(it: &Interp, v: Value) -> (String, Vec<(String, String)>, Option<String>) {
    let mut method = "GET".to_string();
    let mut headers = Vec::new();
    let mut body = None;
    if let Value::Obj(_) = v {
        if let Ok(Value::Str(s)) = get_prop(&it.heap, &it.protos, v, "method") {
            method = it.heap.get_str(s).to_uppercase();
        }
        if let Ok(Value::Obj(o)) = get_prop(&it.heap, &it.protos, v, "headers") {
            if let Obj::Ordinary { pairs, .. } = &it.heap.objs[o as usize] {
                for (k, val) in pairs {
                    if let Value::Str(s) = val {
                        headers.push((k.clone(), it.heap.get_str(*s).to_string()));
                    }
                }
            }
        }
        if let Ok(Value::Str(s)) = get_prop(&it.heap, &it.protos, v, "body") {
            body = Some(it.heap.get_str(s).to_string());
        }
    }
    (method, headers, body)
}

fn n_fetch(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let raw = to_str(&it.heap, args.first().copied().unwrap_or(Value::Undef));
    if it.net.is_none() {
        return Err(err("fetch needs a page context"));
    }
    let (method, headers, body) = fetch_init(it, args.get(1).copied().unwrap_or(Value::Undef));
    // ctx borrow ends before heap allocs below
    let res = {
        let ctx = it.net.as_mut().unwrap();
        let url = ctx
            .base
            .join(&raw)
            .map_err(|e| err(format!("fetch: {e}")))?;
        let res = vigia_net::req(
            &url.to_string(),
            &method,
            &headers,
            body.as_deref().map(str::as_bytes),
            &mut ctx.jar,
        )
        .map_err(|e| format!("fetch: {e}"));
        if let Some(trace) = &ctx.trace {
            let mut ev = NetEvent {
                method: method.clone(),
                url: url.to_string(),
                status: 0,
                req_body: body.as_deref().map(trunc_body),
                resp_body: None,
                error: None,
            };
            match &res {
                Ok(r) => {
                    ev.status = r.status;
                    ev.resp_body = Some(trunc_body(&r.text()));
                }
                Err(e) => ev.error = Some(e.clone()),
            }
            trace.borrow_mut().push(ev);
        }
        res
    };
    let p = promise_new(it)?;
    match res {
        Ok(res) => {
            let pairs = vec![
                ("status".into(), Value::Num(res.status as f64)),
                ("ok".into(), Value::Bool((200..=299).contains(&res.status))),
                ("redirected".into(), Value::Bool(res.redirects > 0)),
                (
                    "url".into(),
                    Value::Str(it.heap.alloc_str(res.final_url.to_string())?),
                ),
                ("__body".into(), Value::Str(it.heap.alloc_str(res.text())?)),
                (
                    "text".into(),
                    Value::Obj(it.heap.alloc_obj(nat("text", n_res_text))?),
                ),
                (
                    "json".into(),
                    Value::Obj(it.heap.alloc_obj(nat("json", n_res_json))?),
                ),
            ];
            let resp = Value::Obj(it.obj_pairs(pairs)?);
            it.promise_settle(p, false, resp);
        }
        Err(msg) => {
            let s = it
                .heap
                .alloc_str(msg)
                .map(Value::Str)
                .unwrap_or(Value::Undef);
            it.promise_settle(p, true, s);
        }
    }
    Ok(Value::Obj(p))
}

fn res_body(it: &Interp, this: Value) -> Result<String, JsError> {
    match get_prop(&it.heap, &it.protos, this, "__body")? {
        Value::Str(s) => Ok(it.heap.get_str(s).to_string()),
        _ => Err(err("response method called on a non-response object")),
    }
}

/// Wrap `v` in a resolved promise (Response.text/json style).
fn resolved(it: &mut Interp, v: Value) -> Result<Value, JsError> {
    let p = promise_new(it)?;
    it.promise_settle(p, false, v);
    Ok(Value::Obj(p))
}

fn n_res_text(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let b = res_body(it, this)?;
    let v = Value::Str(it.heap.alloc_str(b)?);
    resolved(it, v)
}

fn n_res_json(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let b = res_body(it, this)?;
    let p = promise_new(it)?;
    match Json::parse(&b)
        .map_err(|e| err(e.to_string()))
        .and_then(|j| json_to_val(it, &j))
    {
        Ok(v) => it.promise_settle(p, false, v),
        // real .json() rejects on a parse error, it doesn't throw
        Err(e) => {
            let v = err_value(it, e);
            it.promise_settle(p, true, v);
        }
    }
    Ok(Value::Obj(p))
}

fn json_to_val(it: &mut Interp, j: &Json) -> Result<Value, JsError> {
    Ok(match j {
        Json::Null => Value::Null,
        Json::Bool(b) => Value::Bool(*b),
        Json::Num(n) => Value::Num(*n),
        Json::Str(s) => Value::Str(it.heap.alloc_str(s.clone())?),
        Json::Arr(items) => {
            let mut v = Vec::with_capacity(items.len());
            for i in items {
                v.push(json_to_val(it, i)?);
            }
            Value::Obj(it.arr_obj(v)?)
        }
        Json::Obj(pairs) => {
            let mut v = Vec::new();
            for (k, jv) in pairs {
                v.push((k.clone(), json_to_val(it, jv)?));
            }
            Value::Obj(it.obj_pairs(v)?)
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
            Obj::Ordinary { pairs, .. } => Json::Obj(
                pairs
                    .iter()
                    .map(|(k, v)| Ok((k.clone(), val_to_json(h, *v, depth + 1)?)))
                    .collect::<Result<_, JsError>>()?,
            ),
            Obj::Arr { items, .. } => Json::Arr(
                items
                    .iter()
                    .map(|v| val_to_json(h, *v, depth + 1))
                    .collect::<Result<_, JsError>>()?,
            ),
            Obj::Func { .. } | Obj::Native { .. } | Obj::Dom(_) | Obj::Promise(_) | Obj::Freed => {
                Json::Null
            }
            Obj::RegExp { .. } => Json::Obj(vec![]),
        },
    })
}

// ---- prototype natives -------------------------------------------------------

/// Native fn object with an empty own-props bag.
pub(crate) fn nat(name: &'static str, f: NativeFn) -> Obj {
    Obj::Native {
        name,
        f,
        pairs: Vec::new(),
    }
}

fn arg(args: &[Value], i: usize) -> Value {
    args.get(i).copied().unwrap_or(Value::Undef)
}

/// `this` as an Arr heap id; natives below error out on other receivers.
fn this_arr(it: &Interp, this: Value) -> Result<u32, JsError> {
    match this {
        Value::Obj(id) if matches!(it.heap.obj(id), Obj::Arr { .. }) => Ok(id),
        _ => Err(err("array method needs an array receiver")),
    }
}

fn arr_items(it: &Interp, id: u32) -> Vec<Value> {
    match it.heap.obj(id) {
        Obj::Arr { items, .. } => items.clone(),
        _ => Vec::new(),
    }
}

/// callback args per spec: (item, idx, arr); thisArg = the method's arg1.
fn cb_args(item: Value, idx: usize, arr: Value) -> [Value; 3] {
    [item, Value::Num(idx as f64), arr]
}

// -- Object.prototype + statics ------------------------------------------------

fn n_has_own(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let key = to_str(&it.heap, arg(args, 0));
    let hit = match this {
        Value::Obj(id) => own_prop(&it.heap, id, &key).is_some(),
        _ => false,
    };
    Ok(Value::Bool(hit))
}

fn n_obj_to_string(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let tag = match this {
        Value::Undef => "[object Undefined]",
        Value::Null => "[object Null]",
        Value::Bool(_) => "[object Boolean]",
        Value::Num(_) => "[object Number]",
        Value::Str(_) => "[object String]",
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::Arr { .. } => "[object Array]",
            Obj::Func { .. } | Obj::Native { .. } => "[object Function]",
            Obj::Dom(_) => "[object Node]",
            Obj::Promise(_) => "[object Promise]",
            Obj::RegExp { .. } => "[object RegExp]",
            Obj::Ordinary { .. } | Obj::Freed => "[object Object]",
        },
    };
    Ok(Value::Str(it.heap.alloc_str(tag.into())?))
}

/// Object(x): pass objects through; else (and under `new`) a fresh Ordinary.
fn n_object(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    if let Some(v @ Value::Obj(_)) = args.first().copied() {
        return Ok(v);
    }
    if let Value::Obj(_) = this {
        return Ok(this);
    }
    Ok(Value::Obj(it.obj_plain()?))
}

/// Own enumerable (key, value) pairs; arrays enumerate as index strings.
fn own_pairs(h: &Heap, v: Value) -> Vec<(String, Value)> {
    match v {
        Value::Obj(id) => match h.obj(id) {
            Obj::Ordinary { pairs, .. } | Obj::Func { pairs, .. } | Obj::Native { pairs, .. } => {
                pairs.clone()
            }
            Obj::Arr { items, .. } => items
                .iter()
                .enumerate()
                .map(|(i, x)| (i.to_string(), *x))
                .collect(),
            Obj::Dom(_) | Obj::Promise(_) | Obj::RegExp { .. } | Obj::Freed => Vec::new(),
        },
        _ => Vec::new(),
    }
}

fn n_obj_keys(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let pairs = own_pairs(&it.heap, arg(args, 0));
    let mut out = Vec::with_capacity(pairs.len());
    for (k, _) in pairs {
        out.push(Value::Str(it.heap.alloc_str(k)?));
    }
    Ok(Value::Obj(it.arr_obj(out)?))
}

fn n_obj_values(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let pairs = own_pairs(&it.heap, arg(args, 0));
    let out: Vec<Value> = pairs.into_iter().map(|(_, v)| v).collect();
    Ok(Value::Obj(it.arr_obj(out)?))
}

fn n_obj_entries(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let pairs = own_pairs(&it.heap, arg(args, 0));
    let mut out = Vec::with_capacity(pairs.len());
    for (k, v) in pairs {
        let k = Value::Str(it.heap.alloc_str(k)?);
        out.push(Value::Obj(it.arr_obj(vec![k, v])?));
    }
    Ok(Value::Obj(it.arr_obj(out)?))
}

fn n_obj_assign(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let target = arg(args, 0);
    if !matches!(target, Value::Obj(_)) {
        return Err(err("assign: target must be an object"));
    }
    for src in &args[1.min(args.len())..] {
        for (k, v) in own_pairs(&it.heap, *src) {
            set_prop(&mut it.heap, target, &k, v)?;
        }
    }
    Ok(target)
}

fn n_obj_create(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let proto = match arg(args, 0) {
        Value::Obj(id) => Some(id),
        Value::Null => None,
        _ => return Err(err("create: proto must be an object or null")),
    };
    Ok(Value::Obj(it.heap.alloc_obj(Obj::Ordinary {
        pairs: vec![],
        proto,
    })?))
}

// -- Array ctor + statics --------------------------------------------------------

/// Array(...): one numeric arg = length; anything else = the items.
/// `new` ignores the Ordinary `this` and returns a real Arr.
fn n_array(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let items = if args.len() == 1 {
        match args[0] {
            Value::Num(n) if n >= 0.0 && n.fract() == 0.0 && n <= 10_000_000.0 => {
                vec![Value::Undef; n as usize]
            }
            v => vec![v],
        }
    } else {
        args.to_vec()
    };
    Ok(Value::Obj(it.arr_obj(items)?))
}

fn n_is_array(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let b = match arg(args, 0) {
        Value::Obj(id) => matches!(it.heap.obj(id), Obj::Arr { .. }),
        _ => false,
    };
    Ok(Value::Bool(b))
}

fn n_array_of(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    Ok(Value::Obj(it.arr_obj(args.to_vec())?))
}

// -- primitive casts + number globals -------------------------------------------

fn n_string_cast(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let s = match args.first() {
        Some(v) => to_str(&it.heap, *v),
        None => String::new(),
    };
    Ok(Value::Str(it.heap.alloc_str(s)?))
}

fn n_number_cast(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    Ok(Value::Num(to_num(&it.heap, arg(args, 0))))
}

fn n_boolean_cast(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    Ok(Value::Bool(truthy(&it.heap, arg(args, 0))))
}

fn n_parse_int(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let s = to_str(&it.heap, arg(args, 0));
    let t = s.trim_start();
    let (neg, t) = match t.strip_prefix('-') {
        Some(r) => (true, r),
        None => (false, t.strip_prefix('+').unwrap_or(t)),
    };
    let mut radix = match args.get(1) {
        Some(v) => to_num(&it.heap, *v) as u32,
        None => 0,
    };
    let mut t = t;
    if radix == 0 {
        if let Some(r) = t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
            radix = 16;
            t = r;
        } else {
            radix = 10;
        }
    } else if radix == 16 {
        t = t
            .strip_prefix("0x")
            .or_else(|| t.strip_prefix("0X"))
            .unwrap_or(t);
    }
    let mut n: f64 = 0.0;
    let mut any = false;
    for c in t.chars() {
        match c.to_digit(radix) {
            Some(d) => {
                any = true;
                n = n * radix as f64 + d as f64;
            }
            None => break,
        }
    }
    Ok(Value::Num(if any {
        if neg {
            -n
        } else {
            n
        }
    } else {
        f64::NAN
    }))
}

fn n_parse_float(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let s = to_str(&it.heap, arg(args, 0));
    let t = s.trim_start();
    // longest valid float prefix: [+-] digits [. digits] [(e|E)[+-]digits]
    let b = t.as_bytes();
    let mut i = 0;
    if matches!(b.get(i), Some(b'+') | Some(b'-')) {
        i += 1;
    }
    let d0 = i;
    while matches!(b.get(i), Some(c) if c.is_ascii_digit()) {
        i += 1;
    }
    if b.get(i) == Some(&b'.') {
        i += 1;
        while matches!(b.get(i), Some(c) if c.is_ascii_digit()) {
            i += 1;
        }
    }
    if i == d0 || (i == d0 + 1 && t.as_bytes()[d0] == b'.') {
        return Ok(Value::Num(f64::NAN)); // no mantissa digits
    }
    if matches!(b.get(i), Some(b'e') | Some(b'E')) {
        let save = i;
        i += 1;
        if matches!(b.get(i), Some(b'+') | Some(b'-')) {
            i += 1;
        }
        let e0 = i;
        while matches!(b.get(i), Some(c) if c.is_ascii_digit()) {
            i += 1;
        }
        if i == e0 {
            i = save; // bare 'e' doesn't count
        }
    }
    Ok(Value::Num(t[..i].parse().unwrap_or(f64::NAN)))
}

fn n_is_nan(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    Ok(Value::Bool(to_num(&it.heap, arg(args, 0)).is_nan()))
}

fn n_is_finite(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    Ok(Value::Bool(to_num(&it.heap, arg(args, 0)).is_finite()))
}

// -- Function.prototype ------------------------------------------------------------

fn n_fn_call(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let t = arg(args, 0);
    it.call_value(this, t, &args[1.min(args.len())..], None)
}

fn n_fn_apply(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let t = arg(args, 0);
    let argv = match arg(args, 1) {
        Value::Obj(id) => arr_items(it, id),
        Value::Undef | Value::Null => Vec::new(),
        _ => return Err(err("apply: arg list must be an array")),
    };
    it.call_value(this, t, &argv, None)
}

// -- Array.prototype -------------------------------------------------------------
// `this` is the receiver (an Arr); callbacks get (item, idx, arr) and the
// optional thisArg in arg position 1 where real JS takes one.

fn n_arr_push(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    if let Obj::Arr { items, .. } = it.heap.obj_mut(id) {
        items.extend_from_slice(args);
        return Ok(Value::Num(items.len() as f64));
    }
    Err(err("internal: not an array"))
}

fn n_arr_pop(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    if let Obj::Arr { items, .. } = it.heap.obj_mut(id) {
        return Ok(items.pop().unwrap_or(Value::Undef));
    }
    Err(err("internal: not an array"))
}

fn n_arr_shift(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    if let Obj::Arr { items, .. } = it.heap.obj_mut(id) {
        return Ok(if items.is_empty() {
            Value::Undef
        } else {
            items.remove(0)
        });
    }
    Err(err("internal: not an array"))
}

fn n_arr_unshift(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    if let Obj::Arr { items, .. } = it.heap.obj_mut(id) {
        items.splice(0..0, args.iter().copied());
        return Ok(Value::Num(items.len() as f64));
    }
    Err(err("internal: not an array"))
}

fn n_arr_map(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let f = arg(args, 0);
    let t = arg(args, 1);
    let items = arr_items(it, id);
    let mut out = Vec::with_capacity(items.len());
    for (i, x) in items.iter().enumerate() {
        out.push(it.call_value(f, t, &cb_args(*x, i, this), None)?);
    }
    Ok(Value::Obj(it.arr_obj(out)?))
}

fn n_arr_filter(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let f = arg(args, 0);
    let t = arg(args, 1);
    let items = arr_items(it, id);
    let mut out = Vec::new();
    for (i, x) in items.iter().enumerate() {
        let r = it.call_value(f, t, &cb_args(*x, i, this), None)?;
        if truthy(&it.heap, r) {
            out.push(*x);
        }
    }
    Ok(Value::Obj(it.arr_obj(out)?))
}

fn n_arr_for_each(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let f = arg(args, 0);
    let t = arg(args, 1);
    let items = arr_items(it, id);
    for (i, x) in items.iter().enumerate() {
        it.call_value(f, t, &cb_args(*x, i, this), None)?;
    }
    Ok(Value::Undef)
}

fn n_arr_reduce(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let f = arg(args, 0);
    let items = arr_items(it, id);
    let (mut acc, start) = if args.len() > 1 {
        (args[1], 0)
    } else {
        if items.is_empty() {
            return Err(err("reduce of empty array"));
        }
        (items[0], 1)
    };
    for (i, x) in items.iter().enumerate().skip(start) {
        acc = it.call_value(
            f,
            Value::Undef,
            &[acc, *x, Value::Num(i as f64), this],
            None,
        )?;
    }
    Ok(acc)
}

fn n_arr_join(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let sep = match args.first() {
        None | Some(Value::Undef) => ",".to_string(),
        Some(v) => to_str(&it.heap, *v),
    };
    let s = arr_items(it, id)
        .iter()
        .map(|v| match v {
            Value::Undef | Value::Null => String::new(),
            _ => to_str(&it.heap, *v),
        })
        .collect::<Vec<_>>()
        .join(&sep);
    Ok(Value::Str(it.heap.alloc_str(s)?))
}

/// clamp a JS fromIndex: negative counts from the end.
fn from_idx(n: f64, len: usize) -> usize {
    let l = len as i64;
    (if n < 0.0 { l + n as i64 } else { n as i64 }).clamp(0, l) as usize
}

fn n_arr_index_of(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let needle = arg(args, 0);
    let items = arr_items(it, id);
    let from = from_idx(to_num(&it.heap, arg(args, 1)), items.len());
    Ok(Value::Num(
        items[from..]
            .iter()
            .position(|x| strict_eq(&it.heap, *x, needle))
            .map(|p| (p + from) as f64)
            .unwrap_or(-1.0),
    ))
}

fn n_arr_last_index_of(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let needle = arg(args, 0);
    let items = arr_items(it, id);
    let hi = match args.get(1) {
        Some(v) => from_idx(to_num(&it.heap, *v) + 1.0, items.len()),
        None => items.len(),
    };
    Ok(Value::Num(
        items[..hi]
            .iter()
            .rposition(|x| strict_eq(&it.heap, *x, needle))
            .map(|p| p as f64)
            .unwrap_or(-1.0),
    ))
}

fn n_arr_includes(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let needle = arg(args, 0);
    let items = arr_items(it, id);
    let from = from_idx(to_num(&it.heap, arg(args, 1)), items.len());
    Ok(Value::Bool(
        items[from..]
            .iter()
            .any(|x| strict_eq(&it.heap, *x, needle)),
    ))
}

fn n_arr_slice(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let items = arr_items(it, id);
    let len = items.len() as i64;
    let a = to_num(&it.heap, arg(args, 0)) as i64;
    let b = match args.get(1) {
        Some(v) => to_num(&it.heap, *v) as i64,
        None => len,
    };
    let lo = (if a < 0 { len + a } else { a }).clamp(0, len) as usize;
    let hi = (if b < 0 { len + b } else { b }).clamp(0, len) as usize;
    let sub = if hi > lo {
        items[lo..hi].to_vec()
    } else {
        Vec::new()
    };
    Ok(Value::Obj(it.arr_obj(sub)?))
}

fn n_arr_concat(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let mut out = arr_items(it, id);
    for a in args {
        match a {
            Value::Obj(o) if matches!(it.heap.obj(*o), Obj::Arr { .. }) => {
                out.extend(arr_items(it, *o));
            }
            v => out.push(*v),
        }
    }
    Ok(Value::Obj(it.arr_obj(out)?))
}

fn n_arr_find(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let f = arg(args, 0);
    let t = arg(args, 1);
    let items = arr_items(it, id);
    for (i, x) in items.iter().enumerate() {
        let r = it.call_value(f, t, &cb_args(*x, i, this), None)?;
        if truthy(&it.heap, r) {
            return Ok(*x);
        }
    }
    Ok(Value::Undef)
}

fn n_arr_find_index(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let f = arg(args, 0);
    let t = arg(args, 1);
    let items = arr_items(it, id);
    for (i, x) in items.iter().enumerate() {
        let r = it.call_value(f, t, &cb_args(*x, i, this), None)?;
        if truthy(&it.heap, r) {
            return Ok(Value::Num(i as f64));
        }
    }
    Ok(Value::Num(-1.0))
}

fn n_arr_some(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let f = arg(args, 0);
    let t = arg(args, 1);
    let items = arr_items(it, id);
    for (i, x) in items.iter().enumerate() {
        let r = it.call_value(f, t, &cb_args(*x, i, this), None)?;
        if truthy(&it.heap, r) {
            return Ok(Value::Bool(true));
        }
    }
    Ok(Value::Bool(false))
}

fn n_arr_every(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let f = arg(args, 0);
    let t = arg(args, 1);
    let items = arr_items(it, id);
    for (i, x) in items.iter().enumerate() {
        let r = it.call_value(f, t, &cb_args(*x, i, this), None)?;
        if !truthy(&it.heap, r) {
            return Ok(Value::Bool(false));
        }
    }
    Ok(Value::Bool(true))
}

fn n_arr_reverse(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    if let Obj::Arr { items, .. } = it.heap.obj_mut(id) {
        items.reverse();
    }
    Ok(this)
}

fn n_arr_sort(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let mut items = arr_items(it, id);
    match args.first() {
        Some(f @ Value::Obj(_)) => {
            // insertion sort: the comparator can fail mid-way
            for i in 1..items.len() {
                let mut j = i;
                while j > 0 {
                    let c = it.call_value(*f, Value::Undef, &[items[j - 1], items[j]], None)?;
                    if to_num(&it.heap, c) > 0.0 {
                        items.swap(j - 1, j);
                        j -= 1;
                    } else {
                        break;
                    }
                }
            }
        }
        // default: ascending ToString order
        _ => {
            let mut keyed: Vec<(String, usize)> = items
                .iter()
                .enumerate()
                .map(|(i, v)| (to_str(&it.heap, *v), i))
                .collect();
            keyed.sort_by(|a, b| a.0.cmp(&b.0));
            items = keyed.into_iter().map(|(_, i)| items[i]).collect();
        }
    }
    if let Obj::Arr { items: dst, .. } = it.heap.obj_mut(id) {
        *dst = items;
    }
    Ok(this)
}

fn n_arr_splice(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let len = arr_items(it, id).len() as i64;
    let start = {
        let a = to_num(&it.heap, arg(args, 0)) as i64;
        (if a < 0 { len + a } else { a.min(len) }).clamp(0, len) as usize
    };
    let del = match args.get(1) {
        Some(v) => (to_num(&it.heap, *v) as i64).clamp(0, len - start as i64) as usize,
        None => len as usize - start,
    };
    let ins: Vec<Value> = args[2.min(args.len())..].to_vec();
    let removed = match it.heap.obj_mut(id) {
        Obj::Arr { items, .. } => items.splice(start..start + del, ins).collect(),
        _ => Vec::new(),
    };
    Ok(Value::Obj(it.arr_obj(removed)?))
}

fn flat_into(h: &Heap, out: &mut Vec<Value>, items: &[Value], depth: i64) {
    for v in items {
        match v {
            Value::Obj(id) if depth > 0 && matches!(h.obj(*id), Obj::Arr { .. }) => {
                if let Obj::Arr { items: inner, .. } = h.obj(*id) {
                    let inner = inner.clone();
                    flat_into(h, out, &inner, depth - 1);
                }
            }
            _ => out.push(*v),
        }
    }
}

fn n_arr_flat(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let depth = match args.first() {
        Some(v) => to_num(&it.heap, *v) as i64,
        None => 1,
    };
    let items = arr_items(it, id);
    let mut out = Vec::new();
    flat_into(&it.heap, &mut out, &items, depth);
    Ok(Value::Obj(it.arr_obj(out)?))
}

// -- String.prototype -------------------------------------------------------------
// `this` is usually a Str; anything else goes through ToString first.

fn this_str(it: &Interp, this: Value) -> String {
    to_str(&it.heap, this)
}

/// JS-style slice bounds over a char vec.
fn char_slice(chars: &[char], a: i64, b: i64) -> String {
    let len = chars.len() as i64;
    let lo = (if a < 0 { len + a } else { a }).clamp(0, len) as usize;
    let hi = (if b < 0 { len + b } else { b }).clamp(0, len) as usize;
    if hi > lo {
        chars[lo..hi].iter().collect()
    } else {
        String::new()
    }
}

fn n_str_split(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let s = this_str(it, this);
    let parts: Vec<String> = match arg(args, 0) {
        Value::Undef => vec![s],
        sep if is_regexp(it, sep) => split_regex(it, &s, sep)?,
        sep => {
            let sep = to_str(&it.heap, sep);
            if sep.is_empty() {
                s.chars().map(|c| c.to_string()).collect()
            } else {
                s.split(&sep).map(|p| p.to_string()).collect()
            }
        }
    };
    let parts = match args.get(1) {
        Some(v) => {
            let n = to_num(&it.heap, *v);
            if n >= 0.0 {
                parts.into_iter().take(n as usize).collect()
            } else {
                parts
            }
        }
        None => parts,
    };
    let mut vals = Vec::with_capacity(parts.len());
    for p in parts {
        vals.push(Value::Str(it.heap.alloc_str(p)?));
    }
    Ok(Value::Obj(it.arr_obj(vals)?))
}

fn n_str_index_of(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let s = this_str(it, this);
    let needle = to_str(&it.heap, arg(args, 0));
    let chars: Vec<char> = s.chars().collect();
    let from = from_idx(to_num(&it.heap, arg(args, 1)), chars.len());
    let hay: String = chars[from..].iter().collect();
    Ok(Value::Num(
        hay.find(&needle)
            .map(|p| (hay[..p].chars().count() + from) as f64)
            .unwrap_or(-1.0),
    ))
}

fn n_str_last_index_of(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let s = this_str(it, this);
    let needle = to_str(&it.heap, arg(args, 0));
    Ok(Value::Num(
        s.rfind(&needle)
            .map(|p| s[..p].chars().count() as f64)
            .unwrap_or(-1.0),
    ))
}

fn n_str_slice(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let s = this_str(it, this);
    let chars: Vec<char> = s.chars().collect();
    let a = to_num(&it.heap, arg(args, 0)) as i64;
    let b = match args.get(1) {
        Some(v) => to_num(&it.heap, *v) as i64,
        None => chars.len() as i64,
    };
    Ok(Value::Str(it.heap.alloc_str(char_slice(&chars, a, b))?))
}

fn n_str_substring(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let s = this_str(it, this);
    let chars: Vec<char> = s.chars().collect();
    let len = chars.len() as i64;
    let mut a = (to_num(&it.heap, arg(args, 0)) as i64).clamp(0, len);
    let mut b = match args.get(1) {
        Some(v) => (to_num(&it.heap, *v) as i64).clamp(0, len),
        None => len,
    };
    if a > b {
        std::mem::swap(&mut a, &mut b);
    }
    Ok(Value::Str(it.heap.alloc_str(
        chars[a as usize..b as usize].iter().collect(),
    )?))
}

fn n_str_trim(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let s = this_str(it, this).trim().to_string();
    Ok(Value::Str(it.heap.alloc_str(s)?))
}

fn n_str_trim_start(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let s = this_str(it, this).trim_start().to_string();
    Ok(Value::Str(it.heap.alloc_str(s)?))
}

fn n_str_trim_end(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let s = this_str(it, this).trim_end().to_string();
    Ok(Value::Str(it.heap.alloc_str(s)?))
}

fn n_str_to_upper(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let s = this_str(it, this).to_uppercase();
    Ok(Value::Str(it.heap.alloc_str(s)?))
}

fn n_str_to_lower(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let s = this_str(it, this).to_lowercase();
    Ok(Value::Str(it.heap.alloc_str(s)?))
}

fn n_str_includes(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let s = this_str(it, this);
    let needle = to_str(&it.heap, arg(args, 0));
    Ok(Value::Bool(s.contains(&needle)))
}

fn n_str_starts_with(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let s = this_str(it, this);
    let needle = to_str(&it.heap, arg(args, 0));
    let chars: Vec<char> = s.chars().collect();
    let from = from_idx(to_num(&it.heap, arg(args, 1)), chars.len());
    let t: String = chars[from..].iter().collect();
    Ok(Value::Bool(t.starts_with(&needle)))
}

fn n_str_ends_with(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let s = this_str(it, this);
    let needle = to_str(&it.heap, arg(args, 0));
    Ok(Value::Bool(s.ends_with(&needle)))
}

fn n_str_char_at(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let s = this_str(it, this);
    let i = to_num(&it.heap, arg(args, 0));
    let t = if i >= 0.0 {
        s.chars()
            .nth(i as usize)
            .map(|c| c.to_string())
            .unwrap_or_default()
    } else {
        String::new()
    };
    Ok(Value::Str(it.heap.alloc_str(t)?))
}

fn n_str_char_code_at(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let s = this_str(it, this);
    let i = to_num(&it.heap, arg(args, 0));
    Ok(Value::Num(if i >= 0.0 {
        s.chars()
            .nth(i as usize)
            .map(|c| c as u32 as f64)
            .unwrap_or(f64::NAN)
    } else {
        f64::NAN
    }))
}

/// replace(needle, repl): literal string/number needle, first occurrence,
/// no $-patterns (no regex in this engine).
fn n_str_replace(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let s = this_str(it, this);
    if let Some(src) = regexp_arg(it, arg(args, 0))? {
        return replace_regex(it, &s, &src, arg(args, 1));
    }
    let needle = to_str(&it.heap, arg(args, 0));
    let repl = to_str(&it.heap, arg(args, 1));
    Ok(Value::Str(
        it.heap.alloc_str(s.replacen(&needle, &repl, 1))?,
    ))
}

fn n_str_concat(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let mut s = this_str(it, this);
    for a in args {
        s.push_str(&to_str(&it.heap, *a));
    }
    Ok(Value::Str(it.heap.alloc_str(s)?))
}

fn n_str_repeat(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let s = this_str(it, this);
    let n = to_num(&it.heap, arg(args, 0));
    if n < 0.0 || n.is_nan() || s.len().saturating_mul(n as usize) > 16_000_000 {
        return Err(err("repeat: bad count"));
    }
    Ok(Value::Str(it.heap.alloc_str(s.repeat(n as usize))?))
}

fn pad_to(it: &mut Interp, this: Value, args: &[Value], start: bool) -> Result<Value, JsError> {
    let s = this_str(it, this);
    let len = to_num(&it.heap, arg(args, 0)) as usize;
    let chars: Vec<char> = s.chars().collect();
    if chars.len() >= len || len > 1_000_000 {
        return Ok(Value::Str(it.heap.alloc_str(s)?));
    }
    let pad = match args.get(1) {
        Some(Value::Undef) | None => " ".to_string(),
        Some(v) => to_str(&it.heap, *v),
    };
    let mut fill: Vec<char> = Vec::with_capacity(len - chars.len());
    while fill.len() < len - chars.len() {
        fill.extend(pad.chars());
    }
    fill.truncate(len - chars.len());
    let mut out: String = if start {
        fill.iter().collect::<String>() + &s
    } else {
        s.clone() + &fill.iter().collect::<String>()
    };
    if pad.is_empty() {
        out = s; // real JS returns the string unpadded
    }
    Ok(Value::Str(it.heap.alloc_str(out)?))
}

fn n_str_pad_start(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    pad_to(it, this, args, true)
}

fn n_str_pad_end(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    pad_to(it, this, args, false)
}

// -- Number.prototype --------------------------------------------------------------

fn n_num_to_fixed(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let n = to_num(&it.heap, this);
    let s = if !n.is_finite() {
        fmt_num(n)
    } else {
        let d = (to_num(&it.heap, arg(args, 0)) as i64).clamp(0, 20) as usize;
        format!("{n:.d$}")
    };
    Ok(Value::Str(it.heap.alloc_str(s)?))
}

// -- Date ---------------------------------------------------------------------------

fn now_ms() -> f64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_millis() as f64)
        .unwrap_or(0.0)
}

/// Date(ms?) - `new Date` hands us a fresh Ordinary whose proto is already
/// the Date proto (via Date.prototype); plain Date() allocates one. Epoch
/// ms lives in the `__ms` prop. Date-only subset: no locale parsing.
fn n_date(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let ms = match args.first() {
        Some(v) if !matches!(v, Value::Undef) => to_num(&it.heap, *v),
        _ => now_ms(),
    };
    if let Value::Obj(id) = this {
        if matches!(it.heap.obj(id), Obj::Ordinary { .. }) {
            set_prop(&mut it.heap, this, "__ms", Value::Num(ms))?;
            return Ok(this);
        }
    }
    let proto = po(it.protos.date);
    Ok(Value::Obj(it.heap.alloc_obj(Obj::Ordinary {
        pairs: vec![("__ms".into(), Value::Num(ms))],
        proto,
    })?))
}

fn n_date_now(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let _ = it;
    Ok(Value::Num(now_ms()))
}

fn n_date_get_time(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    Ok(match get_prop(&it.heap, &it.protos, this, "__ms")? {
        Value::Num(n) => Value::Num(n),
        _ => Value::Num(f64::NAN),
    })
}

/// days since epoch -> (year, month, day); civil_from_days (Hinnant).
fn civil(z: i64) -> (i64, u32, u32) {
    let z = z + 719468;
    let era = z.div_euclid(146097);
    let doe = z.rem_euclid(146097);
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    (if m <= 2 { y + 1 } else { y }, m as u32, d as u32)
}

fn n_date_iso(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let ms = match get_prop(&it.heap, &it.protos, this, "__ms")? {
        Value::Num(n) => n as i64,
        _ => return Err(err("toISOString on a non-Date")),
    };
    let days = ms.div_euclid(86_400_000);
    let rem = ms.rem_euclid(86_400_000);
    let (y, mo, d) = civil(days);
    let (h, mi, s, ms3) = (
        rem / 3_600_000,
        rem % 3_600_000 / 60_000,
        rem % 60_000 / 1000,
        rem % 1000,
    );
    let t = format!("{y:04}-{mo:02}-{d:02}T{h:02}:{mi:02}:{s:02}.{ms3:03}Z");
    Ok(Value::Str(it.heap.alloc_str(t)?))
}

// -- RegExp --------------------------------------------------------------------------

/// Fuel per regex exec: bounds catastrophic backtracking into an error.
const REGEX_FUEL: u64 = 500_000;

/// Canonical flag order for the stored `flags` string.
fn canon_flags(fl: &crate::regex::Flags) -> String {
    let mut s = String::new();
    if fl.global {
        s.push('g');
    }
    if fl.ignore_case {
        s.push('i');
    }
    if fl.multiline {
        s.push('m');
    }
    if fl.dot_all {
        s.push('s');
    }
    s
}

fn make_regexp(it: &mut Interp, source: &str, flags: &str) -> Result<Value, JsError> {
    let compiled =
        crate::regex::compile(source, flags).map_err(|m| err(format!("invalid regex: {m}")))?;
    let canon = canon_flags(&compiled.flags);
    let pat = it.heap.intern_str(source)?;
    let fl = it.heap.intern_str(&canon)?;
    let proto = po(it.protos.regexp);
    Ok(Value::Obj(it.heap.alloc_obj(Obj::RegExp {
        pat,
        flags: fl,
        last_index: 0.0,
        compiled: std::rc::Rc::new(compiled),
        proto,
    })?))
}

/// Byte offset of char index `ci` in `s` (clamped).
fn char_to_byte(s: &str, ci: usize) -> usize {
    s.char_indices().nth(ci).map(|(i, _)| i).unwrap_or(s.len())
}

fn set_last_index(it: &mut Interp, id: u32, v: f64) {
    if let Obj::RegExp { last_index, .. } = it.heap.obj_mut(id) {
        *last_index = v;
    }
}

/// Core exec: honors global/lastIndex, updates it, maps fuel-out to error.
fn regexp_exec_inner(
    it: &mut Interp,
    id: u32,
    text: &str,
) -> Result<Option<crate::regex::Match>, JsError> {
    let (compiled, global, last) = match it.heap.obj(id) {
        Obj::RegExp {
            compiled,
            last_index,
            ..
        } => (compiled.clone(), compiled.flags.global, *last_index),
        _ => return Err(err("not a regexp")),
    };
    let chars = text.chars().count();
    let mut from_char = if global {
        (last as usize).min(chars)
    } else {
        0
    };
    if last.is_nan() || last < 0.0 {
        from_char = 0;
    }
    let from_byte = char_to_byte(text, from_char);
    match crate::regex::exec_from(&compiled, text, from_byte, REGEX_FUEL) {
        Err(_) => Err(err("regex fuel exhausted")),
        Ok(None) => {
            if global {
                set_last_index(it, id, 0.0);
            }
            Ok(None)
        }
        Ok(Some(m)) => {
            if global {
                let end_chars = text[..m.end].chars().count();
                // Empty match must still advance (spec AdvanceStringIndex).
                let next = if m.end == from_byte {
                    (end_chars + 1).min(chars)
                } else {
                    end_chars
                };
                set_last_index(it, id, next as f64);
            }
            Ok(Some(m))
        }
    }
}

/// [full, g1, ...] with Undef for unmatched groups.
fn match_to_array(it: &mut Interp, text: &str, m: &crate::regex::Match) -> Result<Value, JsError> {
    let mut vals = Vec::with_capacity(m.groups.len() + 1);
    vals.push(Value::Str(
        it.heap.alloc_str(text[m.start..m.end].to_string())?,
    ));
    for g in &m.groups {
        match g {
            Some((a, b)) => vals.push(Value::Str(it.heap.alloc_str(text[*a..*b].to_string())?)),
            None => vals.push(Value::Undef),
        }
    }
    Ok(Value::Obj(it.arr_obj(vals)?))
}

/// RegExp(pat, flags): called or `new`ed alike (ctors allocate their own).
fn n_regexp_ctor(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let has_flags = !matches!(arg(args, 1), Value::Undef);
    if let Value::Obj(id) = arg(args, 0) {
        if let Obj::RegExp { pat, flags, .. } = it.heap.obj(id) {
            if has_flags {
                return Err(err("cannot supply flags when constructing from RegExp"));
            }
            let (source, fl) = (
                it.heap.get_str(*pat).to_string(),
                it.heap.get_str(*flags).to_string(),
            );
            return make_regexp(it, &source, &fl);
        }
    }
    let source = match arg(args, 0) {
        Value::Undef => String::new(),
        v => to_str(&it.heap, v),
    };
    let flags = match arg(args, 1) {
        Value::Undef => String::new(),
        v => to_str(&it.heap, v),
    };
    make_regexp(it, &source, &flags)
}

fn n_regexp_exec(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let Value::Obj(id) = this else {
        return Err(err("exec on a non-RegExp"));
    };
    if !matches!(it.heap.obj(id), Obj::RegExp { .. }) {
        return Err(err("exec on a non-RegExp"));
    }
    let text = to_str(&it.heap, arg(args, 0));
    match regexp_exec_inner(it, id, &text)? {
        None => Ok(Value::Null),
        Some(m) => match_to_array(it, &text, &m),
    }
}

fn n_regexp_test(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let Value::Obj(id) = this else {
        return Err(err("test on a non-RegExp"));
    };
    if !matches!(it.heap.obj(id), Obj::RegExp { .. }) {
        return Err(err("test on a non-RegExp"));
    }
    let text = to_str(&it.heap, arg(args, 0));
    Ok(Value::Bool(regexp_exec_inner(it, id, &text)?.is_some()))
}

fn is_regexp(it: &Interp, v: Value) -> bool {
    matches!(v, Value::Obj(id) if matches!(it.heap.obj(id), Obj::RegExp { .. }))
}

/// Pattern source for a String-method argument: a RegExp object, or a
/// freshly compiled pattern from any other value (Undef means absent).
enum PatSrc {
    Obj(u32),
    Fresh(crate::regex::Compiled),
}

fn regexp_arg(it: &mut Interp, v: Value) -> Result<Option<PatSrc>, JsError> {
    match v {
        Value::Undef => Ok(None),
        Value::Obj(id) if matches!(it.heap.obj(id), Obj::RegExp { .. }) => {
            Ok(Some(PatSrc::Obj(id)))
        }
        other => {
            let pat = to_str(&it.heap, other);
            let c =
                crate::regex::compile(&pat, "").map_err(|m| err(format!("invalid regex: {m}")))?;
            Ok(Some(PatSrc::Fresh(c)))
        }
    }
}

fn compiled_of(it: &Interp, src: &PatSrc) -> std::rc::Rc<crate::regex::Compiled> {
    match src {
        PatSrc::Obj(id) => match it.heap.obj(*id) {
            Obj::RegExp { compiled, .. } => compiled.clone(),
            _ => unreachable!("checked by caller"),
        },
        PatSrc::Fresh(c) => std::rc::Rc::new(c.clone()),
    }
}

/// Byte offset one char past `byte_pos` (clamped to the end).
fn advance_char(text: &str, byte_pos: usize) -> usize {
    let chars = text[..byte_pos.min(text.len())].chars().count();
    char_to_byte(text, chars + 1)
}

/// All matches from `from`, advancing past empty ones. Caps total matches.
fn collect_matches(
    rc: &std::rc::Rc<crate::regex::Compiled>,
    text: &str,
    from: usize,
) -> Result<Vec<crate::regex::Match>, JsError> {
    let mut out = Vec::new();
    let mut p = from.min(text.len());
    loop {
        if p > text.len() {
            break;
        }
        match crate::regex::exec_from(rc, text, p, REGEX_FUEL) {
            Err(_) => return Err(err("regex fuel exhausted")),
            Ok(None) => break,
            Ok(Some(m)) => {
                let empty = m.start == m.end;
                let end = m.end;
                out.push(m);
                if out.len() > text.len() + 2 {
                    return Err(err("too many regex matches"));
                }
                p = if empty { advance_char(text, end) } else { end };
                if empty && p > text.len() {
                    break;
                }
            }
        }
    }
    Ok(out)
}

fn n_str_match(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let s = this_str(it, this);
    let Some(src) = regexp_arg(it, arg(args, 0))? else {
        // match() with no arg matches the empty pattern once.
        let empty = Value::Str(it.heap.alloc_str(String::new())?);
        return Ok(Value::Obj(it.arr_obj(vec![empty])?));
    };
    let rc = compiled_of(it, &src);
    if rc.flags.global {
        let mut vals = Vec::new();
        for m in collect_matches(&rc, &s, 0)? {
            vals.push(Value::Str(
                it.heap.alloc_str(s[m.start..m.end].to_string())?,
            ));
        }
        if vals.is_empty() {
            return Ok(Value::Null);
        }
        return Ok(Value::Obj(it.arr_obj(vals)?));
    }
    match crate::regex::exec_from(&rc, &s, 0, REGEX_FUEL) {
        Err(_) => Err(err("regex fuel exhausted")),
        Ok(None) => Ok(Value::Null),
        Ok(Some(m)) => match_to_array(it, &s, &m),
    }
}

fn n_str_search(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let s = this_str(it, this);
    // search() with no arg searches the empty pattern (index 0).
    let src = match regexp_arg(it, arg(args, 0))? {
        Some(src) => src,
        None => PatSrc::Fresh(crate::regex::compile("", "").unwrap()),
    };
    let rc = compiled_of(it, &src);
    match crate::regex::exec_from(&rc, &s, 0, REGEX_FUEL) {
        Err(_) => Err(err("regex fuel exhausted")),
        Ok(None) => Ok(Value::Num(-1.0)),
        Ok(Some(m)) => Ok(Value::Num(s[..m.start].chars().count() as f64)),
    }
}

/// Split on a RegExp: segments plus captured groups (Undef when a group
/// did not participate). Empty input matches nothing unless the pattern
/// matches empty at 0, in which case the result is empty.
fn split_regex(it: &mut Interp, s: &str, sep: Value) -> Result<Vec<String>, JsError> {
    let Value::Obj(id) = sep else {
        return Err(err("split on a non-RegExp"));
    };
    let rc = match it.heap.obj(id) {
        Obj::RegExp { compiled, .. } => compiled.clone(),
        _ => return Err(err("split on a non-RegExp")),
    };
    if s.is_empty() {
        match crate::regex::exec_from(&rc, s, 0, REGEX_FUEL) {
            Err(_) => return Err(err("regex fuel exhausted")),
            Ok(None) => return Ok(vec![String::new()]),
            Ok(_) => return Ok(vec![]),
        }
    }
    // Markers keep group holes: Some(text) or None (group absent).
    let mut parts: Vec<Option<String>> = Vec::new();
    let mut q = 0usize;
    let mut p = 0usize;
    let mut guard = 0usize;
    while p <= s.len() {
        guard += 1;
        if guard > s.len() * 2 + 4 {
            return Err(err("too many regex matches"));
        }
        let m = match crate::regex::exec_from(&rc, s, p, REGEX_FUEL) {
            Err(_) => return Err(err("regex fuel exhausted")),
            Ok(m) => m,
        };
        let Some(m) = m else {
            break;
        };
        if m.start == m.end {
            // Empty match: advance, no segment.
            p = advance_char(s, p);
            continue;
        }
        parts.push(Some(s[q..m.start].to_string()));
        for g in &m.groups {
            parts.push(g.map(|(a, b)| s[a..b].to_string()));
        }
        q = m.end;
        p = m.end;
    }
    parts.push(Some(s[q..].to_string()));
    // The public split() truncates by limit; group holes become NaN-like
    // Undef there - encode them via a sentinel the caller expands. To
    // keep split()'s Vec<String> shape, join holes as empty here and let
    // match/replace paths (which keep Values) carry Undef instead. Split
    // holes are an accepted deviation: JS puts `undefined` in the array.
    Ok(parts.into_iter().map(|p| p.unwrap_or_default()).collect())
}

/// Expand `$`-patterns in a replacement string: $$, $&, $`, $', $n.
fn expand_repl(
    tpl: &str,
    text: &str,
    full_start: usize,
    full_end: usize,
    groups: &[Option<(usize, usize)>],
) -> String {
    let mut out = String::new();
    let b = tpl.as_bytes();
    let mut i = 0;
    while i < b.len() {
        if b[i] != b'$' || i + 1 >= b.len() {
            out.push(b[i] as char);
            i += 1;
            continue;
        }
        match b[i + 1] {
            b'$' => {
                out.push('$');
                i += 2;
            }
            b'&' => {
                out.push_str(&text[full_start..full_end]);
                i += 2;
            }
            b'`' => {
                out.push_str(&text[..full_start]);
                i += 2;
            }
            b'\'' => {
                out.push_str(&text[full_end..]);
                i += 2;
            }
            d if d.is_ascii_digit() => {
                let mut n = (d - b'0') as usize;
                let mut w = 1;
                if i + 2 < b.len() && b[i + 2].is_ascii_digit() {
                    let n2 = n * 10 + ((b[i + 2] - b'0') as usize);
                    if n2 <= groups.len() && n2 > 0 {
                        n = n2;
                        w = 2;
                    }
                }
                if n >= 1 && n <= groups.len() {
                    if let Some((a, e)) = groups[n - 1] {
                        out.push_str(&text[a..e]);
                    }
                } else {
                    out.push('$');
                    out.push_str(&tpl[i + 1..i + 1 + w]);
                }
                i += 1 + w;
            }
            _ => {
                out.push('$');
                i += 1;
            }
        }
    }
    out
}

fn replace_regex(it: &mut Interp, s: &str, src: &PatSrc, repl: Value) -> Result<Value, JsError> {
    let rc = compiled_of(it, src);
    let matches = if rc.flags.global {
        collect_matches(&rc, s, 0)?
    } else {
        match crate::regex::exec_from(&rc, s, 0, REGEX_FUEL) {
            Err(_) => return Err(err("regex fuel exhausted")),
            Ok(None) => return Ok(Value::Str(it.heap.alloc_str(s.to_string())?)),
            Ok(Some(m)) => vec![m],
        }
    };
    if matches.is_empty() {
        return Ok(Value::Str(it.heap.alloc_str(s.to_string())?));
    }
    let is_fn = matches!(
        repl,
        Value::Obj(id)
            if matches!(it.heap.obj(id), Obj::Func { .. } | Obj::Native { .. })
    );
    let mut out = String::new();
    let mut last = 0usize;
    for m in &matches {
        out.push_str(&s[last..m.start]);
        if is_fn {
            let mut fargs = Vec::with_capacity(m.groups.len() + 3);
            fargs.push(Value::Str(
                it.heap.alloc_str(s[m.start..m.end].to_string())?,
            ));
            for g in &m.groups {
                match g {
                    Some((a, b)) => {
                        fargs.push(Value::Str(it.heap.alloc_str(s[*a..*b].to_string())?))
                    }
                    None => fargs.push(Value::Undef),
                }
            }
            // Offset counts chars (UTF-16 units in real JS).
            fargs.push(Value::Num(s[..m.start].chars().count() as f64));
            fargs.push(Value::Str(it.heap.alloc_str(s.to_string())?));
            let r = it.call_value(repl, Value::Undef, &fargs, None)?;
            out.push_str(&to_str(&it.heap, r));
        } else {
            let tpl = to_str(&it.heap, repl);
            out.push_str(&expand_repl(&tpl, s, m.start, m.end, &m.groups));
        }
        last = m.end;
    }
    out.push_str(&s[last..]);
    Ok(Value::Str(it.heap.alloc_str(out)?))
}

// -- Error ---------------------------------------------------------------------------

/// Error(msg): called or `new`ed alike - an Ordinary under Error.proto-
/// type with an own `message` prop. No `stack` (v1 documents the gap).
fn n_error(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let msg = match args.first() {
        Some(v) if !matches!(v, Value::Undef) => to_str(&it.heap, *v),
        _ => String::new(),
    };
    if let Value::Obj(id) = this {
        // `new Error(m)` hands us the fresh object with the right proto
        if matches!(it.heap.obj(id), Obj::Ordinary { .. }) {
            let m = Value::Str(it.heap.alloc_str(msg)?);
            set_prop(&mut it.heap, this, "message", m)?;
            return Ok(this);
        }
    }
    it.error_obj(&msg)
}

/// Error.prototype.toString: "Name: message" (missing name -> "Error",
/// missing or empty message -> the name alone).
fn n_err_to_string(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let name = match get_prop(&it.heap, &it.protos, this, "name")? {
        Value::Undef => "Error".to_string(),
        v => to_str(&it.heap, v),
    };
    let msg = match get_prop(&it.heap, &it.protos, this, "message")? {
        Value::Undef => String::new(),
        v => to_str(&it.heap, v),
    };
    let s = if msg.is_empty() {
        name
    } else {
        format!("{name}: {msg}")
    };
    Ok(Value::Str(it.heap.alloc_str(s)?))
}

// -- Math ----------------------------------------------------------------------------

fn n_math_floor(it: &mut Interp, _t: Value, args: &[Value]) -> Result<Value, JsError> {
    Ok(Value::Num(to_num(&it.heap, arg(args, 0)).floor()))
}
fn n_math_ceil(it: &mut Interp, _t: Value, args: &[Value]) -> Result<Value, JsError> {
    Ok(Value::Num(to_num(&it.heap, arg(args, 0)).ceil()))
}
fn n_math_round(it: &mut Interp, _t: Value, args: &[Value]) -> Result<Value, JsError> {
    // JS rounds half toward +inf: floor(n + 0.5)
    Ok(Value::Num((to_num(&it.heap, arg(args, 0)) + 0.5).floor()))
}
fn n_math_random(it: &mut Interp, _t: Value, _a: &[Value]) -> Result<Value, JsError> {
    // xorshift64*; seed fixed at Interp::with_cap
    it.rng ^= it.rng >> 12;
    it.rng ^= it.rng << 25;
    it.rng ^= it.rng >> 27;
    let x = it.rng.wrapping_mul(0x2545F4914F6CDD1D);
    Ok(Value::Num((x >> 11) as f64 / 9007199254740992.0))
}
fn n_math_max(it: &mut Interp, _t: Value, args: &[Value]) -> Result<Value, JsError> {
    Ok(Value::Num(args.iter().fold(f64::NEG_INFINITY, |m, v| {
        m.max(to_num(&it.heap, *v))
    })))
}
fn n_math_min(it: &mut Interp, _t: Value, args: &[Value]) -> Result<Value, JsError> {
    Ok(Value::Num(
        args.iter()
            .fold(f64::INFINITY, |m, v| m.min(to_num(&it.heap, *v))),
    ))
}
fn n_math_abs(it: &mut Interp, _t: Value, args: &[Value]) -> Result<Value, JsError> {
    Ok(Value::Num(to_num(&it.heap, arg(args, 0)).abs()))
}
fn n_math_pow(it: &mut Interp, _t: Value, args: &[Value]) -> Result<Value, JsError> {
    Ok(Value::Num(
        to_num(&it.heap, arg(args, 0)).powf(to_num(&it.heap, arg(args, 1))),
    ))
}
fn n_math_sqrt(it: &mut Interp, _t: Value, args: &[Value]) -> Result<Value, JsError> {
    Ok(Value::Num(to_num(&it.heap, arg(args, 0)).sqrt()))
}

// ---- async runtime: promises, microtasks, timers -----------------------------
// Synchronous engine, real ordering: handlers queue as microtasks and run at
// drain() points (end of each run(), after each fire() event dispatch). Timers
// share the drain on a virtual clock - deadlines order firing, now_ms jumps to
// each deadline instead of sleeping. Caps: 4096 timer fires per drain; the
// microtask loop ticks steps so max_steps bounds it.

/// Fresh pending promise.
fn promise_new(it: &mut Interp) -> Result<u32, JsError> {
    it.heap.alloc_obj(Obj::Promise(PromiseState::Pending {
        handlers: Vec::new(),
    }))
}

/// Heap id if `v` is a Promise.
fn as_promise(it: &Interp, v: Value) -> Option<u32> {
    match v {
        Value::Obj(id) if matches!(it.heap.obj(id), Obj::Promise(_)) => Some(id),
        _ => None,
    }
}

/// Rejection reason for a failed callback/executor: a `throw`'s value
/// verbatim, an internal or fatal error's message text.
fn err_value(it: &mut Interp, e: JsError) -> Value {
    match e {
        JsError::Throw(v) => v,
        JsError::Msg(m) | JsError::Fatal(m) => {
            it.heap.alloc_str(m).map(Value::Str).unwrap_or(Value::Undef)
        }
    }
}

/// `v` if callable (Func/Native), else None. JS treats a non-callable
/// .then argument as absent (pass-through).
fn callable(it: &Interp, v: Value) -> Option<Value> {
    match v {
        Value::Obj(id) if matches!(it.heap.obj(id), Obj::Func { .. } | Obj::Native { .. }) => {
            Some(v)
        }
        _ => None,
    }
}

/// One drain sweep: all queued microtasks first, then the earliest-due
/// timer, repeat until both run dry. Errors collect into `errs` and never
/// abort the loop (a failing callback doesn't cancel its siblings), except
/// the runaway guards which stop the drain.
const MAX_TIMER_FIRES: u32 = 4096;

impl Interp {
    /// Settle a pending promise and queue one microtask per registered
    /// handler (a missing handler passes the outcome through). No-op on
    /// an already-settled promise.
    pub(crate) fn promise_settle(&mut self, id: u32, rejecting: bool, v: Value) {
        let st = match self.heap.obj_mut(id) {
            Obj::Promise(st) => st,
            _ => return,
        };
        if !matches!(st, PromiseState::Pending { .. }) {
            return;
        }
        let next_state = if rejecting {
            PromiseState::Rejected(v)
        } else {
            PromiseState::Fulfilled(v)
        };
        let PromiseState::Pending { handlers } = std::mem::replace(st, next_state) else {
            return;
        };
        for h in handlers {
            self.microtasks.push_back(Microtask {
                cb: if rejecting { h.on_reject } else { h.on_fulfill },
                arg: v,
                next: h.next,
                rejecting,
            });
        }
    }

    /// `resolve(v)` semantics: a Promise argument is adopted (pending
    /// subscribes a pass-through, settled copies the state); anything else
    /// fulfills. No-op if `id` already settled. Non-Promise thenables are
    /// NOT adopted (v1 limitation).
    pub(crate) fn promise_resolve(&mut self, id: u32, v: Value) {
        if v == Value::Obj(id) {
            let s = self
                .heap
                .alloc_str("promise resolved with itself".into())
                .map(Value::Str)
                .unwrap_or(Value::Undef);
            self.promise_settle(id, true, s);
            return;
        }
        let Some(pid) = as_promise(self, v) else {
            self.promise_settle(id, false, v);
            return;
        };
        // adopting counts as handling the source promise
        self.handled_promises.insert(pid);
        enum Adopt {
            Fulfill(Value),
            Reject(Value),
            Subscribe,
        }
        let act = match self.heap.obj(pid) {
            Obj::Promise(PromiseState::Fulfilled(u)) => Adopt::Fulfill(*u),
            Obj::Promise(PromiseState::Rejected(r)) => Adopt::Reject(*r),
            _ => Adopt::Subscribe,
        };
        match act {
            Adopt::Fulfill(u) => self.promise_settle(id, false, u),
            Adopt::Reject(r) => self.promise_settle(id, true, r),
            Adopt::Subscribe => {
                if let Obj::Promise(PromiseState::Pending { handlers }) = self.heap.obj_mut(pid) {
                    handlers.push(ThenHandler {
                        on_fulfill: None,
                        on_reject: None,
                        next: id,
                    });
                }
            }
        }
    }

    /// `.then(onF, onR)` core: allocate `next`, then register or enqueue
    /// depending on the promise's state. Marks the promise handled for the
    /// unhandled-rejection sweep. Returns `next`'s obj id.
    fn promise_then(
        &mut self,
        id: u32,
        on_fulfill: Option<Value>,
        on_reject: Option<Value>,
    ) -> Result<u32, JsError> {
        let next = promise_new(self)?;
        enum S {
            Pend,
            Ful(Value),
            Rej(Value),
        }
        let s = match self.heap.obj(id) {
            Obj::Promise(PromiseState::Pending { .. }) => S::Pend,
            Obj::Promise(PromiseState::Fulfilled(v)) => S::Ful(*v),
            Obj::Promise(PromiseState::Rejected(r)) => S::Rej(*r),
            _ => S::Pend,
        };
        match s {
            S::Pend => {
                if let Obj::Promise(PromiseState::Pending { handlers }) = self.heap.obj_mut(id) {
                    handlers.push(ThenHandler {
                        on_fulfill,
                        on_reject,
                        next,
                    });
                }
            }
            S::Ful(v) => self.microtasks.push_back(Microtask {
                cb: on_fulfill,
                arg: v,
                next,
                rejecting: false,
            }),
            S::Rej(r) => self.microtasks.push_back(Microtask {
                cb: on_reject,
                arg: r,
                next,
                rejecting: true,
            }),
        }
        self.handled_promises.insert(id);
        Ok(next)
    }

    fn run_microtask(&mut self, m: Microtask, errs: &mut Vec<JsError>) {
        // the in-flight settle target is a bare u32 - root it so GC can't
        // sweep `next` (or let a recycled slot alias it) while cb runs
        if m.next != u32::MAX {
            self.call_vals.push(Value::Obj(m.next));
        }
        match m.cb {
            // no handler: the settlement passes straight through to `next`
            None => {
                if m.next != u32::MAX {
                    self.promise_settle(m.next, m.rejecting, m.arg);
                }
            }
            Some(cb) => match self.call_value(cb, Value::Undef, &[m.arg], None) {
                Ok(v) => {
                    if m.next != u32::MAX {
                        self.promise_resolve(m.next, v);
                    }
                    // fire-and-forget cb returning a rejected promise is
                    // still reported by the unhandled sweep below
                }
                // Fatal isn't a rejection reason - the engine is stopped,
                // report it and leave `next` unsettled
                Err(e @ JsError::Fatal(_)) => errs.push(e),
                Err(e) => {
                    if m.next == u32::MAX {
                        // render now: a heap id inside Throw isn't rooted
                        // across the next drain safepoint
                        let e = self.bound_err(e);
                        errs.push(e);
                    } else {
                        let v = err_value(self, e);
                        self.promise_settle(m.next, true, v);
                    }
                }
            },
        }
        if m.next != u32::MAX {
            self.call_vals.pop();
        }
    }

    /// Drain the work queues: microtasks FIFO until empty, then fire the
    /// earliest-deadline timer (advancing the virtual clock to it - never
    /// sleeps), drain whatever it queued, repeat. Intervals reschedule
    /// themselves unless clearTimeout/clearInterval cancelled them mid-cb.
    /// Ends with the unhandled-rejection sweep (reported once each).
    pub(crate) fn drain(&mut self, errs: &mut Vec<JsError>) {
        let mut fires = 0u32;
        'outer: loop {
            while let Some(m) = self.microtasks.pop_front() {
                if self.tick().is_err() {
                    errs.push(fatal("step limit exceeded"));
                    return;
                }
                self.run_microtask(m, errs);
                self.maybe_gc();
            }
            let pick = self
                .timers
                .iter()
                .enumerate()
                .filter(|(_, t)| !t.cancelled && !t.parked)
                .min_by_key(|(_, t)| t.deadline_ms)
                .map(|(i, _)| i);
            let Some(i) = pick else { break };
            fires += 1;
            if fires > MAX_TIMER_FIRES {
                errs.push(fatal("timer cap exceeded (4096 fires in one drain)"));
                break 'outer;
            }
            self.now_ms = self.now_ms.max(self.timers[i].deadline_ms);
            let (cb, args) = {
                let t = &mut self.timers[i];
                t.parked = true; // a nested drain (event dispatch) can't re-fire it
                (t.cb, t.args.clone())
            };
            if let Err(e) = self.call_value(cb, Value::Undef, &args, None) {
                let e = self.bound_err(e);
                errs.push(e);
            }
            let t = &mut self.timers[i];
            t.parked = false;
            if t.cancelled {
                // cleared inside its own callback: stays dead
            } else if let Some(iv) = t.interval {
                t.deadline_ms = self.now_ms + iv;
            } else {
                t.cancelled = true;
            }
            // keep the vec from growing on churny pages
            if self.timers.len() > 64 {
                self.timers.retain(|t| !t.cancelled);
            }
            self.maybe_gc();
        }
        let mut unhandled = Vec::new();
        for i in 0..self.heap.objs.len() as u32 {
            if let Obj::Promise(PromiseState::Rejected(r)) = self.heap.obj(i) {
                if !self.handled_promises.contains(&i) {
                    unhandled.push((i, *r));
                }
            }
        }
        for (id, r) in unhandled {
            self.handled_promises.insert(id);
            errs.push(err(format!("unhandled rejection: {}", self.thrown_text(r))));
        }
    }
}

// -- Promise ctor + prototype -------------------------------------------------

/// resolve/reject executor args are plain Native objects whose bound
/// promise id lives in a "__p" own prop - natives see their own callee
/// through cur_native.
fn bound_prop(it: &Interp, key: &str) -> Result<Value, JsError> {
    get_prop(&it.heap, &it.protos, it.cur_native, key)
}

fn bound_promise(it: &Interp) -> Result<u32, JsError> {
    match bound_prop(it, "__p")? {
        Value::Obj(id) if matches!(it.heap.obj(id), Obj::Promise(_)) => Ok(id),
        _ => Err(err("promise resolver detached")),
    }
}

fn resolver_fn(it: &mut Interp, pid: u32, reject: bool) -> Result<Value, JsError> {
    // __p is a real Obj ref, not an id-in-a-Num, so a live resolver keeps
    // its promise alive through GC (and the marker can follow it).
    Ok(Value::Obj(it.heap.alloc_obj(Obj::Native {
        name: if reject { "reject" } else { "resolve" },
        f: if reject {
            n_promise_reject
        } else {
            n_promise_resolve
        },
        pairs: vec![("__p".into(), Value::Obj(pid))],
    })?))
}

/// new Promise(executor): executor runs synchronously with fresh
/// resolve/reject natives; a throw rejects the promise with the thrown
/// value (Fatal propagates instead of rejecting).
fn n_promise_ctor(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let exec = arg(args, 0);
    if callable(it, exec).is_none() {
        return Err(err("Promise executor is not a function"));
    }
    let pid = promise_new(it)?;
    let res = resolver_fn(it, pid, false)?;
    let rej = resolver_fn(it, pid, true)?;
    if let Err(e) = it.call_value(exec, Value::Undef, &[res, rej], None) {
        match e {
            JsError::Fatal(_) => return Err(e),
            _ => {
                let v = err_value(it, e);
                it.promise_settle(pid, true, v);
            }
        }
    }
    Ok(Value::Obj(pid))
}

fn n_promise_resolve(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let pid = bound_promise(it)?;
    it.promise_resolve(pid, arg(args, 0));
    Ok(Value::Undef)
}

fn n_promise_reject(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let pid = bound_promise(it)?;
    it.promise_settle(pid, true, arg(args, 0));
    Ok(Value::Undef)
}

fn this_promise(it: &Interp, this: Value) -> Result<u32, JsError> {
    as_promise(it, this).ok_or_else(|| err("promise method needs a promise receiver"))
}

fn n_promise_then(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let pid = this_promise(it, this)?;
    let onf = callable(it, arg(args, 0));
    let onr = callable(it, arg(args, 1));
    Ok(Value::Obj(it.promise_then(pid, onf, onr)?))
}

fn n_promise_catch(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let pid = this_promise(it, this)?;
    let onr = callable(it, arg(args, 0));
    Ok(Value::Obj(it.promise_then(pid, None, onr)?))
}

/// finally(f): f runs on either path and its result is ignored - unless f
/// throws (rejects `next`) or returns a rejected promise (adopted). The
/// wrapper natives carry f in "__f"; a non-callable f is a pass-through.
fn n_promise_finally(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let pid = this_promise(it, this)?;
    let (onf, onr) = match callable(it, arg(args, 0)) {
        Some(fv) => {
            let mut wrap = |nf: NativeFn| -> Result<Value, JsError> {
                Ok(Value::Obj(it.heap.alloc_obj(Obj::Native {
                    name: "finally",
                    f: nf,
                    pairs: vec![("__f".into(), fv)],
                })?))
            };
            (Some(wrap(n_finally_pass)?), Some(wrap(n_finally_throw)?))
        }
        None => (None, None),
    };
    Ok(Value::Obj(it.promise_then(pid, onf, onr)?))
}

/// True when `v` is a rejected promise (finally wrappers check f's return).
fn is_rejected_promise(it: &Interp, v: Value) -> bool {
    matches!(v, Value::Obj(id)
        if matches!(it.heap.obj(id), Obj::Promise(PromiseState::Rejected(_))))
}

/// finally on the fulfill path: run f, keep the original value unless f
/// produced a rejection (a pending f() promise is not awaited - v1).
fn n_finally_pass(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let f = match bound_prop(it, "__f")? {
        v @ Value::Obj(_) => v,
        _ => return Err(err("finally detached")),
    };
    let r = it.call_value(f, Value::Undef, &[], None)?;
    if is_rejected_promise(it, r) {
        return Ok(r); // adoption propagates f's reason
    }
    Ok(arg(args, 0))
}

/// finally on the reject path: run f, then re-throw the original reason
/// (as a rejected promise so adoption preserves the reason value, not an
/// error string) unless f itself failed.
fn n_finally_throw(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let f = match bound_prop(it, "__f")? {
        v @ Value::Obj(_) => v,
        _ => return Err(err("finally detached")),
    };
    let r = it.call_value(f, Value::Undef, &[], None)?;
    if is_rejected_promise(it, r) {
        return Ok(r);
    }
    let p = promise_new(it)?;
    it.promise_settle(p, true, arg(args, 0));
    Ok(Value::Obj(p))
}

// -- Promise statics ------------------------------------------------------------

fn n_promise_static_resolve(
    it: &mut Interp,
    _this: Value,
    args: &[Value],
) -> Result<Value, JsError> {
    let v = arg(args, 0);
    if as_promise(it, v).is_some() {
        return Ok(v); // Promise.resolve(promise) IS the promise
    }
    resolved(it, v)
}

fn n_promise_static_reject(
    it: &mut Interp,
    _this: Value,
    args: &[Value],
) -> Result<Value, JsError> {
    let p = promise_new(it)?;
    it.promise_settle(p, true, arg(args, 0));
    Ok(Value::Obj(p))
}

/// Arg as an Arr's items (no iterable protocol - arrays only).
fn array_items(it: &Interp, v: Value, who: &str) -> Result<Vec<Value>, JsError> {
    match v {
        Value::Obj(id) if matches!(it.heap.obj(id), Obj::Arr { .. }) => Ok(arr_items(it, id)),
        _ => Err(err(format!("{who} needs an array"))),
    }
}

/// A promise's immediate state: Some((rejecting, value)) when settled.
fn settled_state(it: &Interp, pid: u32) -> Option<(bool, Value)> {
    match it.heap.obj(pid) {
        Obj::Promise(PromiseState::Fulfilled(v)) => Some((false, *v)),
        Obj::Promise(PromiseState::Rejected(r)) => Some((true, *r)),
        _ => None,
    }
}

/// Subscribe a pure pass-through (or two bound natives) on a pending
/// member promise; `next` = u32::MAX when no downstream promise is needed.
fn subscribe_pending(
    it: &mut Interp,
    pid: u32,
    on_fulfill: Option<Value>,
    on_reject: Option<Value>,
    next: u32,
) {
    it.handled_promises.insert(pid);
    if let Obj::Promise(PromiseState::Pending { handlers }) = it.heap.obj_mut(pid) {
        handlers.push(ThenHandler {
            on_fulfill,
            on_reject,
            next,
        });
    }
}

/// Native with __st (the all() state object) + optional __i (member index)
/// bound in its own props.
fn member_fn(
    it: &mut Interp,
    name: &'static str,
    f: NativeFn,
    st: u32,
    i: Option<usize>,
) -> Result<Value, JsError> {
    let mut pairs = vec![("__st".into(), Value::Obj(st))];
    if let Some(i) = i {
        pairs.push(("__i".into(), Value::Num(i as f64)));
    }
    Ok(Value::Obj(it.heap.alloc_obj(Obj::Native {
        name,
        f,
        pairs,
    })?))
}

fn bound_state(it: &Interp) -> Result<(u32, usize), JsError> {
    let st = match bound_prop(it, "__st")? {
        Value::Obj(id) => id,
        _ => return Err(err("aggregate callback detached")),
    };
    let i = match bound_prop(it, "__i")? {
        Value::Num(n) => n as usize,
        _ => usize::MAX,
    };
    Ok((st, i))
}

/// all()/allSettled() bookkeeping: {count, n, results, out}. Store
/// results[i]=v; on count==n settle `out` fulfilled with the array.
fn all_record(it: &mut Interp, st: u32, i: usize, v: Value) -> Result<(), JsError> {
    let h = &it.heap;
    let (results, out, n, count) = (
        get_prop(h, &it.protos, Value::Obj(st), "results")?,
        get_prop(h, &it.protos, Value::Obj(st), "out")?,
        to_num(h, get_prop(h, &it.protos, Value::Obj(st), "n")?),
        to_num(h, get_prop(h, &it.protos, Value::Obj(st), "count")?),
    );
    set_index(&mut it.heap, results, Value::Num(i as f64), v)?;
    let count = count + 1.0;
    set_prop(&mut it.heap, Value::Obj(st), "count", Value::Num(count))?;
    if count >= n {
        if let Value::Obj(oid) = out {
            it.promise_settle(oid, false, results);
        }
    }
    Ok(())
}

/// Promise.all(arr): members may be promises or plain values; pending
/// members get counting-callback subscriptions. First rejection wins;
/// empty array resolves to [].
fn n_promise_all(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let items = array_items(it, arg(args, 0), "Promise.all")?;
    promise_aggregate(it, &items, false)
}

/// Promise.allSettled(arr): every member records {status,value|reason};
/// `out` never rejects.
fn n_promise_all_settled(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let items = array_items(it, arg(args, 0), "Promise.allSettled")?;
    promise_aggregate(it, &items, true)
}

fn promise_aggregate(it: &mut Interp, items: &[Value], settled: bool) -> Result<Value, JsError> {
    let out = promise_new(it)?;
    let n = items.len();
    let results = it.arr_obj(vec![Value::Undef; n])?;
    let st = it.obj_pairs(vec![
        ("count".into(), Value::Num(0.0)),
        ("n".into(), Value::Num(n as f64)),
        ("results".into(), Value::Obj(results)),
        ("out".into(), Value::Obj(out)),
    ])?;
    for (i, m) in items.iter().enumerate() {
        let pid = match as_promise(it, *m) {
            Some(p) => p,
            None => {
                // plain value: record inline
                if settled {
                    settled_record(it, st, i, false, *m)?;
                } else {
                    all_record(it, st, i, *m)?;
                }
                continue;
            }
        };
        it.handled_promises.insert(pid); // aggregation handles the member
        match settled_state(it, pid) {
            Some((false, v)) if !settled => all_record(it, st, i, v)?,
            Some((true, r)) if !settled => it.promise_settle(out, true, r),
            Some((rej, v)) => settled_record(it, st, i, rej, v)?,
            None => {
                let (okf, badf): (NativeFn, NativeFn) = if settled {
                    (n_as_ok, n_as_bad)
                } else {
                    (n_all_ok, n_all_bad)
                };
                let ok = member_fn(it, "all.ok", okf, st, Some(i))?;
                let bad = member_fn(it, "all.bad", badf, st, Some(i))?;
                subscribe_pending(it, pid, Some(ok), Some(bad), u32::MAX);
            }
        }
    }
    if n == 0 {
        // empty input resolves to [] immediately (all and allSettled alike)
        it.promise_settle(out, false, Value::Obj(results));
    }
    Ok(Value::Obj(out))
}

fn n_all_ok(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let (st, i) = bound_state(it)?;
    all_record(it, st, i, arg(args, 0))?;
    Ok(Value::Undef)
}

fn n_all_bad(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let (st, _) = bound_state(it)?;
    if let Value::Obj(out) = get_prop(&it.heap, &it.protos, Value::Obj(st), "out")? {
        it.promise_settle(out, true, arg(args, 0));
    }
    Ok(Value::Undef)
}

/// allSettled row: {status:"fulfilled",value} / {status:"rejected",reason}.
fn settled_record(
    it: &mut Interp,
    st: u32,
    i: usize,
    rejected: bool,
    v: Value,
) -> Result<(), JsError> {
    let (status, key) = if rejected {
        ("rejected", "reason")
    } else {
        ("fulfilled", "value")
    };
    let s = it.heap.alloc_str(status.into())?;
    let o = it.obj_pairs(vec![("status".into(), Value::Str(s)), (key.into(), v)])?;
    all_record(it, st, i, Value::Obj(o))
}

fn n_as_ok(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let (st, i) = bound_state(it)?;
    settled_record(it, st, i, false, arg(args, 0))?;
    Ok(Value::Undef)
}

fn n_as_bad(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let (st, i) = bound_state(it)?;
    settled_record(it, st, i, true, arg(args, 0))?;
    Ok(Value::Undef)
}

/// Promise.race(arr): every member subscribes a pass-through to `out`;
/// the first settle wins (later settles are no-ops).
fn n_promise_race(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let items = array_items(it, arg(args, 0), "Promise.race")?;
    let out = promise_new(it)?;
    for m in items {
        match as_promise(it, m) {
            Some(pid) => {
                it.handled_promises.insert(pid);
                match settled_state(it, pid) {
                    Some((rej, v)) => it.promise_settle(out, rej, v),
                    None => subscribe_pending(it, pid, None, None, out),
                }
            }
            None => it.promise_settle(out, false, m),
        }
    }
    Ok(Value::Obj(out))
}

// -- timers + queueMicrotask ---------------------------------------------------

fn timer_add(it: &mut Interp, args: &[Value], interval: bool) -> Result<Value, JsError> {
    let cb = arg(args, 0);
    if callable(it, cb).is_none() {
        return Err(err(if interval {
            "setInterval needs a function"
        } else {
            "setTimeout needs a function"
        }));
    }
    let ms = to_num(&it.heap, arg(args, 1));
    let ms = if ms.is_finite() && ms > 0.0 {
        ms as u64
    } else {
        0
    };
    let id = it.next_timer_id;
    it.next_timer_id = it.next_timer_id.wrapping_add(1).max(1);
    it.timers.push(Timer {
        id,
        deadline_ms: it.now_ms + ms,
        cb,
        args: args[2.min(args.len())..].to_vec(),
        // a 0ms interval would spin against the fire cap; floor it at 1
        interval: interval.then_some(ms.max(1)),
        cancelled: false,
        parked: false,
    });
    Ok(Value::Num(id as f64))
}

fn n_set_timeout(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    timer_add(it, args, false)
}

fn n_set_interval(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    timer_add(it, args, true)
}

/// clearTimeout/clearInterval share the id space, like browsers.
fn timer_clear(it: &mut Interp, args: &[Value]) -> Result<Value, JsError> {
    let id = to_num(&it.heap, arg(args, 0));
    if id.is_finite() && id >= 0.0 {
        if let Some(t) = it.timers.iter_mut().find(|t| t.id == id as u32) {
            t.cancelled = true;
        }
    }
    Ok(Value::Undef)
}

fn n_clear_timeout(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    timer_clear(it, args)
}

fn n_clear_interval(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    timer_clear(it, args)
}

fn n_queue_microtask(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let Some(cb) = callable(it, arg(args, 0)) else {
        return Err(err("queueMicrotask needs a function"));
    };
    it.microtasks.push_back(Microtask {
        cb: Some(cb),
        arg: Value::Undef,
        next: u32::MAX,
        rejecting: false,
    });
    Ok(Value::Undef)
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
        ev(src).unwrap_err().to_string()
    }

    #[test]
    fn templates() {
        assert_eq!(disp("var n='w';`hi ${n}!`"), "hi w!");
        assert_eq!(disp("`sum=${1 + 2}`"), "sum=3");
        assert_eq!(disp("`a${`b${'c'}d`}e`"), "abcde");
        assert_eq!(disp("`esc \\` \\$`"), "esc ` $");
        assert_eq!(disp("`x=${{a: 1}.a}`"), "x=1");
        assert_eq!(out("console.log(`v=${7}`)"), "v=7\n");
        assert!(errmsg("var t=`x`;f`t`").contains("tagged templates"));
        assert!(errmsg("`abc").contains("unterminated template"));
    }

    #[test]
    fn regexps() {
        assert_eq!(disp("var r=/ab+c/gi;r.source"), "ab+c");
        assert_eq!(disp("var r=/ab+c/gi;r.flags"), "gi");
        assert_eq!(boolean("var r=/ab+c/gi;r.global"), true);
        assert_eq!(boolean("/a+/.test('baa')"), true);
        assert_eq!(boolean("/^b/m.test('a\\nb')"), true);
        assert_eq!(disp("'a<b@c>d'.match(/<([^>]+@[^>]+)>/)[1]"), "b@c");
        assert_eq!(
            out("console.log('a;b,c'.split(/[,;]/))"),
            "[\"a\",\"b\",\"c\"]\n"
        );
        assert_eq!(disp("'a-b-c'.replace(/-/g,'+')"), "a+b+c");
        assert_eq!(disp("'abc123'.replace(/(\\d+)/,'[$1]')"), "abc[123]");
        assert_eq!(num("'xx'.search(/x/)"), 0.0);
        assert_eq!(num("'xx'.search(/y/)"), -1.0);
        assert_eq!(num("6/2"), 3.0);
        assert_eq!(disp("var r=/a/g;r.test('a');r.lastIndex"), "1");
        assert!(errmsg("var r=/a{2,1}/").contains("invalid regex"));
        assert!(errmsg("new RegExp('(')").contains("invalid regex"));
    }

    #[test]
    fn for_of_arrays_strings() {
        assert_eq!(num("var t=0;for(var x of [1,2,3])t+=x;t"), 6.0);
        assert_eq!(disp("var s='';for(let c of 'ab')s+=c;s"), "ab");
        assert!(errmsg("for(var x of {})x").contains("only over arrays"));
        assert!(errmsg("for(var x in {})x").contains("for-in"));
    }

    #[test]
    fn arrows() {
        assert_eq!(num("(x=>x*2)(21)"), 42.0);
        assert_eq!(num("((a,b)=>a+b)(2,3)"), 5.0);
        assert_eq!(
            disp("var o={x:9,m:function(){var h=()=>this.x;return h()}};o.m()"),
            "9"
        );
        assert_eq!(out("var f=()=>1;console.log(f())"), "1\n");
        assert!(errmsg("var f=()=>1;new f()").contains("not a constructor"));
    }

    #[test]
    fn optional_chain_nullish() {
        assert_eq!(disp("var a=null;a?.b"), "undefined");
        assert_eq!(disp("var a=null;a?.b.c ?? 'short'"), "short");
        assert_eq!(disp("var o={b:{c:42}};o?.b?.c"), "42");
        assert_eq!(disp("var o={b:{c:42}};o?.missing?.deep ?? 'fb'"), "fb");
        assert_eq!(disp("0 ?? 99"), "0");
        assert_eq!(disp("'' ?? 'fb'"), "");
        assert_eq!(disp("null ?? 'd'"), "d");
        assert_eq!(disp("undefined ?? 'd'"), "d");
        assert_eq!(disp("false ?? 'd'"), "false");
        assert_eq!(
            out("var g={x:7,h:function(){return this.x}};console.log(g.h?.())"),
            "7\n"
        );
        assert_eq!(
            out("var g={x:7,h:function(){return this.x}};console.log(g?.h?.())"),
            "7\n"
        );
        assert!(errmsg("var o={b:null};o.b.c").contains("cannot read"));
        assert!(errmsg("null.x").contains("cannot read"));
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
        assert_eq!(
            num("var s=0;for(var i=0;i<6;i++){if(i%2==0){continue}s+=i}s"),
            9.0
        );
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
        assert_eq!(
            num("function o(){return i();function i(){return 9}}o()"),
            9.0
        );
        // missing arg -> undefined
        assert_eq!(disp("function f(a,b){return b}f(1)"), "undefined");
        // named fn expr can self-recurse
        assert_eq!(
            num("var f=function g(n){return n<2?1:n*g(n-1)};f(5)"),
            120.0
        );
        // this binding on member call
        assert_eq!(num("var o={n:7,f:function(){return this.n}};o.f()"), 7.0);
        // unbound call -> this is undefined
        assert!(
            errmsg("var o={n:1,g:function(){return this.n}};var h=o.g;h()").contains("cannot read")
        );
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
        assert_eq!(
            disp("JSON.stringify({a:1,b:[2,'x']})"),
            "{\"a\":1,\"b\":[2,\"x\"]}"
        );
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
        it.max_call_depth = 100;
        assert!(it
            .run("function f(){f()}f()")
            .unwrap_err()
            .to_string()
            .contains("call depth"));
    }

    #[test]
    fn limits() {
        // heap cap: concat allocates a fresh slot per iteration
        let mut it = Interp::with_cap(20);
        let e = it.run("var s='a';while(1){s=s+s}").unwrap_err();
        assert!(e.to_string().contains("heap cap"), "{e}");
        // step limit
        let mut it = Interp::new();
        it.max_steps = 100;
        assert!(it
            .run("while(1){}")
            .unwrap_err()
            .to_string()
            .contains("step"));
    }

    // ---- prototypes -----------------------------------------------------

    #[test]
    fn proto_lookup() {
        // two levels: c -> b -> a
        assert_eq!(
            num("var a={x:1};var b=Object.create(a);var c=Object.create(b);c.x"),
            1.0
        );
        // own prop shadows proto prop
        assert_eq!(num("var b=Object.create({x:1});b.x=2;b.x"), 2.0);
        // hasOwnProperty is own-only; the method itself comes via the chain
        assert!(boolean(
            "var b=Object.create({x:1});b.hasOwnProperty('x') === false"
        ));
        assert!(boolean("({a:1}).hasOwnProperty('a')"));
        assert!(!boolean("({a:1}).hasOwnProperty('toString')"));
        // 'in' walks the chain
        assert!(boolean("'x' in Object.create({x:1})"));
        assert!(boolean("'hasOwnProperty' in {}"));
        assert!(!boolean("'zzz' in {}"));
        // literals get Object.prototype
        assert_eq!(disp("var o={a:1};o.toString()"), "[object Object]");
        assert_eq!(disp("[1].toString()"), "[object Array]");
        // null-proto object has nothing
        assert_eq!(
            disp("typeof Object.create(null).hasOwnProperty"),
            "undefined"
        );
    }

    #[test]
    fn array_methods() {
        assert_eq!(disp("[1,2,3].map(function(x){return x*2})"), "[2,4,6]");
        // callback args: (item, idx, arr)
        assert_eq!(
            disp("[7,8].map(function(x,i,a){return i+':'+a.length}).join(',')"),
            "0:2,1:2"
        );
        assert_eq!(
            disp("[1,2,3,4].filter(function(x){return x%2==0})"),
            "[2,4]"
        );
        assert_eq!(num("[1,2,3,4].reduce(function(a,b){return a+b})"), 10.0);
        assert_eq!(num("[1,2,3,4].reduce(function(a,b){return a+b},10)"), 20.0);
        assert!(errmsg("[].reduce(function(a,b){return a+b})").contains("empty"));
        assert_eq!(disp("[1,2,3].join('-')"), "1-2-3");
        assert_eq!(disp("[1,null,3].join('-')"), "1--3");
        assert_eq!(num("var n=0;[1,2].forEach(function(x){n+=x});n"), 3.0);
        assert_eq!(num("[5,6,5].indexOf(5)"), 0.0);
        assert_eq!(num("[5,6,5].lastIndexOf(5)"), 2.0);
        assert_eq!(num("[5,6,5].indexOf(5,1)"), 2.0);
        assert!(boolean("[1,2].includes(2)"));
        assert!(!boolean("[1,2].includes(9)"));
        assert_eq!(disp("[9,8,7].slice(1)"), "[8,7]");
        assert_eq!(disp("[1].concat([2,3],4)"), "[1,2,3,4]");
        assert_eq!(num("[3,7,9].find(function(x){return x>4})"), 7.0);
        assert_eq!(num("[3,7,9].findIndex(function(x){return x>4})"), 1.0);
        assert!(boolean("[1,3].some(function(x){return x>2})"));
        assert!(!boolean("[1,3].every(function(x){return x>2})"));
        assert_eq!(disp("var a=[1,2,3];a.reverse();a"), "[3,2,1]");
        // sort: default string order, or a comparator
        assert_eq!(disp("[3,1,2].sort()"), "[1,2,3]");
        assert_eq!(disp("[10,9,1].sort()"), "[1,10,9]");
        assert_eq!(disp("[10,9,1].sort(function(a,b){return a-b})"), "[1,9,10]");
        // splice: remove + insert, returns removed
        assert_eq!(disp("var a=[1,2,3,4];var r=a.splice(1,2);r"), "[2,3]");
        assert_eq!(disp("var a=[1,2,3,4];a.splice(1,2,'x');a"), "[1,\"x\",4]");
        assert_eq!(
            disp("var a=[1,2];a.splice(1,0,'x','y');a"),
            "[1,\"x\",\"y\",2]"
        );
        assert_eq!(disp("[[1,2],[3]].flat()"), "[1,2,3]");
        assert_eq!(disp("[[1,[2]]].flat()"), "[1,[2]]");
        assert_eq!(disp("[[1,[2]]].flat(2)"), "[1,2]");
        // mutating basics still mutate the same vec
        assert_eq!(num("var a=[1];a.push(2,3);a.length"), 3.0);
        assert_eq!(num("var a=[1,2];a.shift()"), 1.0);
        assert_eq!(num("var a=[3];a.unshift(1,2);a[0]"), 1.0);
        // index-syntax method call resolves through the proto too
        assert_eq!(disp("var a=[1];a['push'](9);a"), "[1,9]");
        assert!(boolean("Array.isArray([1])"));
        assert!(!boolean("Array.isArray({})"));
        assert_eq!(disp("Array.of(1,2,3)"), "[1,2,3]");
        assert_eq!(num("new Array(3).length"), 3.0);
        assert_eq!(disp("Array(1,2)"), "[1,2]");
    }

    #[test]
    fn string_methods() {
        assert_eq!(disp("' a,b '.trim().split(',')[1]"), "b");
        assert_eq!(disp("'a,b,c'.split(',',2).join('|')"), "a|b");
        assert_eq!(disp("'abc'.split('').length"), "3");
        assert_eq!(disp("'x'.repeat(3)"), "xxx");
        assert_eq!(disp("'5'.padStart(3,'0')"), "005");
        assert_eq!(disp("'5'.padEnd(3,'0')"), "500");
        assert_eq!(disp("'abc'.replace('b','X')"), "aXc");
        assert_eq!(disp("'abab'.replace('b','X')"), "aXab");
        assert_eq!(num("'abcabc'.lastIndexOf('b')"), 4.0);
        assert_eq!(disp("'abcdef'.substring(4,2)"), "cd");
        assert_eq!(disp("'  x'.trimStart()"), "x");
        assert_eq!(disp("'x  '.trimEnd()"), "x");
        assert!(boolean("'abc'.startsWith('ab')"));
        assert!(boolean("'abc'.endsWith('bc')"));
        assert!(boolean("'abc'.includes('b')"));
        assert_eq!(disp("'a'.concat('b','c')"), "abc");
        // via proto on a variable too
        assert_eq!(disp("var s='hi';s.toUpperCase()"), "HI");
    }

    #[test]
    fn object_statics() {
        // insertion order kept
        assert_eq!(disp("Object.keys({b:1,a:2}).join(',')"), "b,a");
        assert_eq!(disp("Object.values({b:1,a:2}).join(',')"), "1,2");
        assert_eq!(disp("Object.entries({a:1})[0].join('=')"), "a=1");
        assert_eq!(disp("Object.keys([7,8])"), "[\"0\",\"1\"]");
        // assign merges left to right
        assert_eq!(
            disp("Object.assign({a:1},{b:2},{a:3})"),
            "{\"a\":3,\"b\":2}"
        );
        // create sets proto
        assert_eq!(num("var o=Object.create({m:5});o.m"), 5.0);
        // Number.prototype + globals
        assert_eq!(disp("(3.14159).toFixed(2)"), "3.14");
        assert_eq!(disp("var n=2;n.toFixed(3)"), "2.000");
        assert_eq!(num("parseInt('42px')"), 42.0);
        assert_eq!(num("parseInt('0x10')"), 16.0);
        assert_eq!(num("parseInt('11',2)"), 3.0);
        assert_eq!(num("parseFloat('1.5x')"), 1.5);
        assert!(boolean("isNaN(parseFloat('x'))"));
        assert_eq!(num("Number('12')+Number('3')"), 15.0);
        assert_eq!(disp("String(9)+String(1)"), "91");
        assert!(boolean("Boolean('x')"));
        assert!(!boolean("Boolean(0)"));
        assert!(boolean("isNaN(0/0)"));
        assert!(boolean("isFinite(1/2)"));
        assert!(!boolean("isFinite(1/0)"));
    }

    #[test]
    fn new_and_instanceof() {
        // proto wiring: instance sees F.prototype methods
        assert_eq!(
            num("function P(){this.x=3}P.prototype.m=function(){return this.x*2};var p=new P();p.m()"),
            6.0
        );
        // no-paren form parses
        assert_eq!(num("function P(){this.x=4}var p=new P;p.x"), 4.0);
        // instanceof on both sides of true
        assert!(boolean("function P(){}var p=new P();p instanceof P"));
        assert!(boolean("function P(){}new P() instanceof Object"));
        assert!(boolean("[1] instanceof Array"));
        assert!(boolean("[] instanceof Object"));
        assert!(!boolean("var q={};q instanceof Array"));
        assert!(!boolean("5 instanceof Number"));
        // functions chain through Function.prototype to Object.prototype
        assert!(boolean("function f(){}f instanceof Object"));
        // error on non-callable rhs
        assert!(errmsg("1 instanceof {}").contains("not a function"));
        // native ctor under new works and instanceof resolves
        assert!(boolean("new Object() instanceof Object"));
        assert!(boolean("new Date() instanceof Date"));
        // explicit object return still wins
        assert_eq!(num("function P(){return {y:8}}new P().y"), 8.0);
        // replaced prototype is honored
        assert!(boolean(
            "function P(){}P.prototype={tag:9};var p=new P();p.tag===9 && p instanceof P"
        ));
    }

    #[test]
    fn fn_call_apply() {
        assert_eq!(
            num("function f(a,b){return this.k+a+b}f.call({k:1},2,3)"),
            6.0
        );
        assert_eq!(
            num("function f(a,b){return this.k+a+b}f.apply({k:1},[2,3])"),
            6.0
        );
        assert_eq!(
            num("var o={k:10};function g(){return this.k}g.call(o)"),
            10.0
        );
        // call/apply reach Native fns too (String cast via call)
        assert_eq!(disp("String.call(null,5)"), "5");
    }

    #[test]
    fn math_and_date() {
        assert_eq!(num("Math.floor(1.9)+Math.ceil(1.1)"), 3.0);
        assert_eq!(num("Math.round(1.5)+Math.round(-1.5)"), 1.0); // 2 + -1
        assert_eq!(num("Math.max(3,7,2)+Math.min(3,7,2)+Math.abs(-4)"), 13.0);
        assert_eq!(num("Math.pow(2,10)+Math.sqrt(9)"), 1027.0);
        assert!(boolean("Math.random()>=0 && Math.random()<1"));
        assert!(boolean("Math.PI>3.14 && Math.E>2.7"));
        assert_eq!(disp("typeof Date.now()"), "number");
        assert_eq!(
            disp("new Date(0).toISOString()"),
            "1970-01-01T00:00:00.000Z"
        );
        assert_eq!(num("new Date(0).getTime()"), 0.0);
        assert_eq!(num("new Date(1234).valueOf()"), 1234.0);
        assert_eq!(disp("Date(0).toISOString()"), "1970-01-01T00:00:00.000Z");
        // day math sanity: 86400000ms = next day
        assert_eq!(
            disp("new Date(86400000).toISOString()"),
            "1970-01-02T00:00:00.000Z"
        );
    }

    #[test]
    fn proto_chain_guard() {
        // deep chain: lookups cap at 64 hops, no hang
        assert_eq!(
            disp("var p={x:1};for(var i=0;i<200;i++){p=Object.create(p)}typeof p.zzz"),
            "undefined"
        );
        assert_eq!(
            num(
                "var p={x:1};for(var i=0;i<200;i++){p=Object.create(p)}p.x === undefined ? 7 : p.x"
            ),
            7.0 // x sits deeper than the 64-hop cap
        );
        assert_eq!(
            num("var p={x:1};for(var i=0;i<10;i++){p=Object.create(p)}p.x"),
            1.0
        );
        // tight heap: proto/builtin installs hit the cap and skip; plain
        // own-prop objects still work
        let mut it = Interp::with_cap(128);
        assert_eq!(it.run("var o={a:1};o.a").unwrap(), Value::Num(1.0));
    }

    // ---- promises, microtasks, timers -----------------------------------

    #[test]
    fn then_handlers_run_at_drain() {
        // .then callbacks run after the remaining sync code, FIFO
        assert_eq!(
            out("Promise.resolve(1).then(function(){console.log('then')});console.log('sync')"),
            "sync\nthen\n"
        );
        // values thread through chains
        assert_eq!(
            out("Promise.resolve(1).then(function(v){return v+1}).then(function(v){console.log(v)})"),
            "2\n"
        );
        // executor resolves synchronously; still delivered post-sync
        assert_eq!(
            out("new Promise(function(res){res(7);console.log('exec')}).then(function(v){console.log(v)})"),
            "exec\n7\n"
        );
        // resolve() called later (stored resolver) flushes the handlers
        assert_eq!(
            out("var r;var p=new Promise(function(res){r=res});\
                p.then(function(v){console.log('late:'+v)});r(9)"),
            "late:9\n"
        );
        // resolve(promise) adopts its state
        assert_eq!(
            out("var r;var p=new Promise(function(res){r=res});\
                p.then(function(v){console.log('adopt:'+v)});r(Promise.resolve(5))"),
            "adopt:5\n"
        );
        // resolve(self) rejects
        assert_eq!(
            out("var r;var p=new Promise(function(res){r=res});\
                p.catch(function(){console.log('self')});r(p)"),
            "self\n"
        );
        // a second then on the same settled promise queues independently
        assert_eq!(
            out(
                "var p=Promise.resolve(1);p.then(function(){console.log('a')});\
                p.then(function(){console.log('b')})"
            ),
            "a\nb\n"
        );
        // instanceof + tag
        assert!(boolean("Promise.resolve(1) instanceof Promise"));
        assert_eq!(disp("Promise.resolve(1)+''"), "[object Promise]");
        // non-function args are pass-through, not errors
        assert_eq!(
            out("Promise.resolve(4).then(undefined).then(function(v){console.log(v)})"),
            "4\n"
        );
    }

    #[test]
    fn rejection_flows_through_chains() {
        // skips fulfill handlers, reaches the reject handler
        assert_eq!(
            out("Promise.reject('x').then(function(){console.log('no')})\
                .then(function(){console.log('no2')},function(r){console.log('got:'+r)})"),
            "got:x\n"
        );
        // catch = then(undefined, onR)
        assert_eq!(
            out("Promise.reject('x').catch(function(r){console.log('caught:'+r)})"),
            "caught:x\n"
        );
        // a throwing handler rejects downstream
        assert_eq!(
            out("Promise.resolve(1).then(function(){nope()})\
                .catch(function(e){console.log('err:'+e)})"),
            "err:nope is not defined\n"
        );
        // catch's return value recovers the chain
        assert_eq!(
            out("Promise.reject('x').catch(function(){return 3})\
                .then(function(v){console.log('rec:'+v)})"),
            "rec:3\n"
        );
        // executor throwing rejects the promise
        assert_eq!(
            out("new Promise(function(){nope()}).catch(function(e){console.log(e)})"),
            "nope is not defined\n"
        );
        // Promise.reject with no handler -> drain error surfaces from run()
        assert!(errmsg("Promise.reject('boom')").contains("unhandled rejection"));
        assert!(errmsg("Promise.reject('boom')").contains("boom"));
        // a .then without onR forwards the rejection to the next promise,
        // which itself is the unhandled one
        assert!(errmsg("Promise.reject('x').then(function(){})").contains("unhandled rejection"));
        // handled in the same script: no error
        assert_eq!(
            out("var p=Promise.reject('x');p.catch(function(r){console.log('ok:'+r)})"),
            "ok:x\n"
        );
        // handler returning a settled promise adopts: fulfilled propagates
        assert_eq!(
            out(
                "Promise.resolve(1).then(function(){return Promise.resolve(9)})\
                .then(function(v){console.log('rv'+v)})"
            ),
            "rv9\n"
        );
        // ...and a returned rejected promise rejects the chain
        assert_eq!(
            out(
                "Promise.resolve(1).then(function(){return Promise.reject('z')})\
                .catch(function(e){console.log('rz'+e)})"
            ),
            "rzz\n"
        );
        // handler returning a PENDING promise: the chain follows it; the
        // timer resolves q after the handler already adopted it
        assert_eq!(
            out("var r;var q=new Promise(function(res){r=res});\
                Promise.resolve(0).then(function(){return q})\
                .then(function(v){console.log('pend'+v)});\
                setTimeout(function(){r(7)},0)"),
            "pend7\n"
        );
    }

    #[test]
    fn promise_finally_both_paths() {
        // fulfill path: f runs, value preserved
        assert_eq!(
            out("Promise.resolve(9).finally(function(){console.log('fin')})\
                .then(function(v){console.log('v'+v)})"),
            "fin\nv9\n"
        );
        // reject path: f runs, original reason preserved
        assert_eq!(
            out(
                "Promise.reject('r').finally(function(){console.log('fin')})\
                .catch(function(e){console.log('c'+e)})"
            ),
            "fin\ncr\n"
        );
        // throwing f overrides the outcome
        assert_eq!(
            out("Promise.resolve(9).finally(function(){nope()})\
                .then(function(){console.log('no')})\
                .catch(function(){console.log('threw')})"),
            "threw\n"
        );
        // f returning a rejected promise overrides too
        assert_eq!(
            out(
                "Promise.resolve(9).finally(function(){return Promise.reject('fx')})\
                .catch(function(e){console.log('rf'+e)})"
            ),
            "rffx\n"
        );
        // non-callable f is a pass-through
        assert_eq!(
            out("Promise.resolve(2).finally(5).then(function(v){console.log(v)})"),
            "2\n"
        );
    }

    #[test]
    fn promise_all_static() {
        assert_eq!(
            out("Promise.all([Promise.resolve(1),2,'x'])\
                .then(function(a){console.log(a.join('|'))})"),
            "1|2|x\n"
        );
        assert_eq!(
            out("Promise.all([]).then(function(a){console.log('n'+a.length)})"),
            "n0\n"
        );
        // order is positional even when members settle out of order
        assert_eq!(
            out("var r1,r2;\
                Promise.all([new Promise(function(a){r1=a}),new Promise(function(b){r2=b})])\
                .then(function(a){console.log(a.join(','))});r2('B');r1('A')"),
            "A,B\n"
        );
        // first rejection rejects the aggregate
        assert_eq!(
            out("Promise.all([Promise.resolve(1),Promise.reject('no'),3])\
                .then(function(){console.log('bad')})\
                .catch(function(e){console.log('rej:'+e)})"),
            "rej:no\n"
        );
        // mixed pending: a late rejection still wins over pending members
        assert_eq!(
            out("var r1,r2;\
                Promise.all([new Promise(function(a){r1=a}),new Promise(function(_,b){r2=b})])\
                .then(function(){console.log('bad')})\
                .catch(function(e){console.log('late:'+e)});r2('x');r1('y')"),
            "late:x\n"
        );
        assert!(errmsg("Promise.all(5)").contains("array"));
    }

    #[test]
    fn promise_race_and_allsettled() {
        // race: first settle wins (here the already-resolved member)
        assert_eq!(
            out(
                "var r1;Promise.race([new Promise(function(a){r1=a}),Promise.resolve('fast')])\
                .then(function(v){console.log('w'+v)});r1('slow')"
            ),
            "wfast\n"
        );
        assert_eq!(
            out("Promise.race([1,Promise.resolve(2)]).then(function(v){console.log(v)})"),
            "1\n"
        );
        // race can reject
        assert_eq!(
            out("Promise.race([Promise.reject('r')]).catch(function(e){console.log(e)})"),
            "r\n"
        );
        // allSettled never rejects; statuses in order
        assert_eq!(
            out("Promise.allSettled([Promise.resolve(1),Promise.reject('e'),3])\
                .then(function(a){\
                    console.log(a[0].status+':'+a[0].value+'|'+a[1].status+':'+a[1].reason+'|'+a[2].status)\
                })"),
            "fulfilled:1|rejected:e|fulfilled\n"
        );
        assert_eq!(
            out("Promise.allSettled([]).then(function(a){console.log(a.length)})"),
            "0\n"
        );
        // Promise.resolve on a promise is identity
        assert!(boolean("var p=Promise.resolve(1);Promise.resolve(p)===p"));
        // unhandled rejection inside all() doesn't double-report members
        assert_eq!(
            errmsg("Promise.all([Promise.reject('m')])")
                .split('\n')
                .count(),
            1
        );
    }

    #[test]
    fn timers_virtual_clock() {
        // deadlines order firing, not registration order; sync code first
        assert_eq!(
            out("setTimeout(function(){console.log('b')},50);\
                setTimeout(function(){console.log('a')},10);console.log('sync')"),
            "sync\na\nb\n"
        );
        // cb args pass through; clearTimeout kills a pending timer
        assert_eq!(
            out("setTimeout(function(x,y){console.log(x+y)},0,3,4)"),
            "7\n"
        );
        assert_eq!(
            out("var t=setTimeout(function(){console.log('dead')},0);\
                clearTimeout(t);console.log('ok')"),
            "ok\n"
        );
        // same deadline = registration order; a timer can schedule a timer
        assert_eq!(
            out("setTimeout(function(){console.log('a');setTimeout(function(){console.log('c')},0)},0);\
                setTimeout(function(){console.log('b')},0)"),
            "a\nb\nc\n"
        );
        // setInterval repeats until cleared (fires at 5,10,15; reader at 20)
        assert_eq!(
            out(
                "var n=0;var i=setInterval(function(){n++;if(n==3){clearInterval(i)}},5);\
                setTimeout(function(){console.log('n='+n)},20)"
            ),
            "n=3\n"
        );
        // clearInterval inside the cb stops it after one fire
        assert_eq!(
            out(
                "var n=0;var i=setInterval(function(){n++;clearInterval(i)},1);\
                setTimeout(function(){console.log('once:'+n)},10)"
            ),
            "once:1\n"
        );
        // clearTimeout with a bogus id is a no-op
        assert_eq!(out("clearTimeout(999);console.log('ok')"), "ok\n");
        // non-function cb errors
        assert!(errmsg("setTimeout(5)").contains("function"));
    }

    #[test]
    fn queue_microtask_ordering() {
        // microtasks (thens + queueMicrotask) all beat timers
        assert_eq!(
            out("setTimeout(function(){console.log('t')},0);\
                queueMicrotask(function(){console.log('m')});\
                Promise.resolve().then(function(){console.log('p')});\
                console.log('s')"),
            "s\nm\np\nt\n"
        );
        // a microtask queueing a microtask still beats the timer
        assert_eq!(
            out("setTimeout(function(){console.log('t')},0);\
                queueMicrotask(function(){console.log('m1');queueMicrotask(function(){console.log('m2')})})"),
            "m1\nm2\nt\n"
        );
        // queueMicrotask cb throwing is a drain error, not a throw
        assert!(errmsg("queueMicrotask(function(){nope()})").contains("nope"));
        assert!(errmsg("queueMicrotask(3)").contains("function"));
    }

    #[test]
    fn async_await() {
        // async fn returns a promise fulfilled with the return value
        assert_eq!(
            out("async function f(){return 5}f().then(function(v){console.log(v)})"),
            "5\n"
        );
        // expr form too
        assert_eq!(
            out("var f=async function(){return 8};f().then(function(v){console.log(v)})"),
            "8\n"
        );
        // await unwraps fulfilled promises; non-promises pass through
        assert_eq!(
            out(
                "async function f(){var a=await Promise.resolve(2);var b=await 3;\
                return a+b}f().then(function(v){console.log(v)})"
            ),
            "5\n"
        );
        // await on rejected throws the reason value -> the async fn's
        // promise rejects with it verbatim
        assert_eq!(
            out("async function f(){await Promise.reject('bad')}\
                f().catch(function(e){console.log('aw:'+e)})"),
            "aw:bad\n"
        );
        // await on pending is a clear error (no suspension exists)
        assert!(out("async function f(){await new Promise(function(){})}\
                f().catch(function(e){console.log(e)})")
        .contains("await on pending promise"));
        // await outside async is an eval error even though it parses
        assert!(errmsg("await 1").contains("await outside async"));
        // ...and inside a plain nested fn too (nearest-fn rule): the error
        // rejects the async fn's promise
        assert!(errmsg("async function f(){(function(){await 1})()}f()")
            .contains("await outside async"));
        // throw inside async rejects; return adopts a promise
        assert_eq!(
            out("async function f(){return Promise.resolve(6)}\
                f().then(function(v){console.log(v)})"),
            "6\n"
        );
    }

    #[test]
    fn drain_caps() {
        // microtask self-requeue is bounded by the step cap
        let mut it = Interp::new();
        it.max_steps = 500;
        assert!(it
            .run("function q(){queueMicrotask(q)}q()")
            .unwrap_err()
            .to_string()
            .contains("step"));
        // an uncleared interval hits the timer cap, not a hang
        let mut it = Interp::new();
        let e = it.run("setInterval(function(){},1)").unwrap_err();
        assert!(e.to_string().contains("timer cap"), "{e}");
    }

    // ---- throw / try / catch / finally --------------------------------

    #[test]
    fn try_catch_basics() {
        // catch binds the thrown value verbatim - numbers, objects alike
        assert_eq!(num("var r=0;try{throw 7}catch(e){r=e}r"), 7.0);
        assert_eq!(num("var r;try{throw {a:5}}catch(e){r=e.a}r"), 5.0);
        // a throw inside a fn reaches the caller's try
        assert_eq!(
            num("function f(){throw 3}var r;try{f()}catch(e){r=e}r"),
            3.0
        );
        // no throw: the catch clause is skipped
        assert_eq!(num("var r=1;try{r=2}catch(e){r=3}r"), 2.0);
        // nested try + rethrow reaches the outer catch
        assert_eq!(
            num("var r;try{try{throw 5}catch(e){throw e+1}}catch(f){r=f}r"),
            6.0
        );
        // catch param is block-scoped: no leak, no clobber of outer `e`
        assert_eq!(disp("var e=9;try{throw 1}catch(e){e=5}e"), "9");
        assert_eq!(disp("try{throw 1}catch(q){}typeof q"), "undefined");
        // bare `catch {}` (no binding) is legal
        assert_eq!(num("var r;try{throw 1}catch{r=4}r"), 4.0);
        // uncaught throw surfaces as the run() error
        assert!(errmsg("throw 'zip'").contains("zip"));
        assert!(errmsg("throw new Error('x')").contains("Error: x"));
        // try/finally without catch still propagates
        assert!(errmsg("try{throw 'up'}finally{1}").contains("up"));
    }

    #[test]
    fn error_builtin() {
        assert_eq!(disp("var e=new Error('x');e.message"), "x");
        assert_eq!(disp("var e=Error('y');e.message"), "y");
        assert!(boolean("var e=new Error('x');e instanceof Error"));
        assert!(boolean("var e=new Error('x');e instanceof Object"));
        assert_eq!(disp("new Error('x').toString()"), "Error: x");
        assert_eq!(disp("Error().toString()"), "Error");
        assert_eq!(disp("new Error('x').name"), "Error");
        // internal errors materialize as Error objects at the binding
        assert_eq!(
            disp("var r;try{nope()}catch(e){r=e.message+'|'+(e instanceof Error)}r"),
            "nope is not defined|true"
        );
        // no `stack` in v1
        assert_eq!(disp("typeof new Error('x').stack"), "undefined");
    }

    #[test]
    fn try_finally() {
        // finally on normal completion and after a handled throw
        assert_eq!(disp("var s='';try{s+='t'}finally{s+='f'}s"), "tf");
        assert_eq!(
            disp("var s='';try{throw 1}catch(e){s+='c'}finally{s+='f'}s"),
            "cf"
        );
        // finally runs while a throw is in flight, then the throw continues
        assert_eq!(
            disp("var s='';try{try{throw 1}finally{s+='f'}}catch(e){s+='c'}s"),
            "fc"
        );
        // ... and on return/break exits too
        assert_eq!(
            num("var s=0;function f(){try{return 9}finally{s=1}}var r=f();r*10+s"),
            91.0
        );
        assert_eq!(
            disp("var s='';for(var i=0;i<3;i++){try{if(i==1){break}s+=i}finally{s+='f'}}s"),
            "0ff"
        );
        // an abrupt finally completion overrides the in-flight outcome
        assert_eq!(num("function f(){try{return 1}finally{return 2}}f()"), 2.0);
        assert_eq!(num("function f(){try{throw 1}finally{return 7}}f()"), 7.0);
        assert!(errmsg("try{throw 1}finally{throw 'fin'}").contains("fin"));
    }

    #[test]
    fn fatal_errors_bypass_catch() {
        // call depth is Fatal: catch never sees it, finally still runs
        let mut it = Interp::new();
        it.max_call_depth = 100;
        let e = it
            .run("var s='';function f(){f()}try{f()}catch(q){s='caught'}finally{s='fin'}")
            .unwrap_err();
        assert!(e.to_string().contains("call depth"), "{e}");
        let v = it.run("s").unwrap();
        assert_eq!(it.inspect(v), "fin");
        // same for the step limit: the catch clause is skipped entirely
        let mut it = Interp::new();
        it.max_steps = 500;
        let e = it
            .run("var s='';try{while(1){}}catch(q){s='caught'}")
            .unwrap_err();
        assert!(e.to_string().contains("step limit"), "{e}");
        it.steps = 0; // the step budget is cumulative across run() calls
        let v = it.run("s").unwrap();
        assert_eq!(it.inspect(v), "");
    }

    #[test]
    fn try_catch_async() {
        // await on a rejection throws the reason into try/catch verbatim
        assert_eq!(
            out("async function f(){try{await Promise.reject('r')}catch(e){console.log('aw:'+e)}}f()"),
            "aw:r\n"
        );
        // an async fn's `throw` rejects with the value verbatim
        assert_eq!(
            out("async function f(){throw {m:'q'}}f().catch(function(e){console.log(e.m)})"),
            "q\n"
        );
        // ... and an Error keeps its shape through .catch
        assert_eq!(
            out("async function f(){throw new Error('z')}f().catch(function(e){console.log(e.message,e instanceof Error)})"),
            "z true\n"
        );
        // a promise executor's throw rejects with the value too
        assert_eq!(
            out("new Promise(function(){throw 42}).catch(function(e){console.log('ex:'+e)})"),
            "ex:42\n"
        );
        // try/finally inside an async body
        assert_eq!(
            out("async function f(){try{return 1}finally{console.log('fin')}}f().then(function(v){console.log(v)})"),
            "fin\n1\n"
        );
        // a then-callback's thrown value rejects the chain verbatim
        assert_eq!(
            out("Promise.resolve(1).then(function(){throw {m:'w'}}).catch(function(e){console.log(e.m)})"),
            "w\n"
        );
    }
}
