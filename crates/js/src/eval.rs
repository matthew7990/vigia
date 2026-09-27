//! Tree-walking evaluator. `Flow` threads break/continue/return through
//! statement execution. Closures capture their defining EnvId; `this` is
//! an ordinary env binding set per call.

use std::collections::HashMap;
use std::rc::Rc;

use vigia_json::Json;

use crate::ast::{
    ClassCtor, ClassMember, Expr, FnDef, MemberKind, ObjEntry, ObjKey, OptOp, Pat, Stmt, VarDecl,
    VarKind,
};
use crate::{
    bindings::{
        WIN_EVENTS, n_dom_method, n_event_ctor, n_get_computed_style, n_image_ctor,
        n_win_add_event_listener, n_win_dispatch_event, n_win_remove_event_listener, zero_rect,
    },
    err, fatal, po, Env, Heap, Interp, JsError, Microtask, NativeFn, NetEvent, Obj, PromiseState,
    Protos, ThenHandler, Timer, TypedKind, Value,
};

pub(crate) enum Flow {
    Normal,
    /// break, optionally to a named label (`None` = innermost loop/switch).
    Break(Option<String>),
    /// continue, optionally to a label wrapping a loop.
    Continue(Option<String>),
    Return(Value),
}

/// Pending class constructor parts: params, rest name, body.
type CtorParts = (Vec<(Pat, Option<Expr>)>, Option<String>, Vec<Stmt>);

// ---- coercions ---------------------------------------------------------

pub(crate) fn truthy(h: &Heap, v: Value) -> bool {
    match v {
        Value::Undef | Value::Null => false,
        Value::Bool(b) => b,
        Value::Num(n) => n != 0.0 && !n.is_nan(),
        Value::Str(id) => !h.get_str(id).is_empty(),
        // 0n is falsy like 0 (boxed BigInts need the value check).
        Value::Obj(id) => match h.obj(id) {
            Obj::BigInt { mag, .. } => mag.iter().any(|&w| w != 0),
            _ => true,
        },
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
        // BigInt -> Number is allowed explicitly (Number(x)); precision past
        // 2^53 is inherently lost, like V8.
        Value::Obj(id) => match h.obj(id) {
            Obj::BigInt { neg, mag, .. } => bi_to_f64(*neg, mag),
            _ => f64::NAN,
        },
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
            Obj::Map { .. } => "[object Map]".into(),
            Obj::Set { .. } => "[object Set]".into(),
            Obj::WeakMap { .. } => "[object WeakMap]".into(),
            Obj::Bytes { bytes, .. } => bytes
                .iter()
                .map(|b| b.to_string())
                .collect::<Vec<_>>()
                .join(","),
            Obj::Typed { elems, .. } => elems
                .iter()
                .map(|e| to_str(h, Value::Num(*e)))
                .collect::<Vec<_>>()
                .join(","),
            // 64-bit views join raw decimal elements (no boxing: to_str
            // lacks &mut; matches Array join semantics via ToString).
            Obj::Big64 { signed, elems, .. } => elems
                .iter()
                .map(|e| {
                    if *signed {
                        (*e as i64).to_string()
                    } else {
                        e.to_string()
                    }
                })
                .collect::<Vec<_>>()
                .join(","),
            Obj::BufView { buf, off, len, kind, .. } => match kind {
                TypedKind::I64 => {
                    let n = view_count(*kind, *len);
                    let mut parts = Vec::with_capacity(n);
                    for i in 0..n {
                        match view_read_u64(h, *buf, off + i * 8) {
                            Some(b) => parts.push((b as i64).to_string()),
                            None => parts.push("0".into()),
                        }
                    }
                    parts.join(",")
                }
                TypedKind::U64 => {
                    let n = view_count(*kind, *len);
                    let mut parts = Vec::with_capacity(n);
                    for i in 0..n {
                        match view_read_u64(h, *buf, off + i * 8) {
                            Some(b) => parts.push(b.to_string()),
                            None => parts.push("0".into()),
                        }
                    }
                    parts.join(",")
                }
                k => {
                    let n = view_count(*k, *len);
                    let mut parts = Vec::with_capacity(n);
                    for i in 0..n {
                        match view_read_num(h, *buf, off + i * t_bpe(*k), *k) {
                            Some(e) => parts.push(to_str(h, Value::Num(e))),
                            None => parts.push("0".into()),
                        }
                    }
                    parts.join(",")
                }
            },
            Obj::DView { .. } => "[object DataView]".into(),
            Obj::Buf { .. } => "[object ArrayBuffer]".into(),
            Obj::Proxy { target, .. } => to_str(h, Value::Obj(*target)),
            Obj::Symbol { desc, .. } => match desc {
                Some(s) => format!("Symbol({})", h.get_str(*s)),
                None => "Symbol()".into(),
            },
            Obj::Dom { .. } => "[object Node]".into(),
            Obj::Promise { .. } => "[object Promise]".into(),
            Obj::Accessor { .. } => "[object Accessor]".into(),
            // Explicit String(x) on a BigInt renders decimal (only implicit
            // `+`/template paths throw - enforced at those sites, not here).
            Obj::BigInt { neg, mag, .. } => bi_fmt(*neg, mag, 10),
            // No Dom access here: String(style) gives the tag, use cssText.
            Obj::Style { .. } => "[object CSSStyleDeclaration]".into(),
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

/// JS ToUint8: truncate, wrap mod 256 (NaN/Infinity -> 0 via the cast).
fn to_u8(h: &Heap, v: Value) -> u8 {
    to_u8_num(to_num(h, v))
}

fn strict_eq(h: &Heap, l: Value, r: Value) -> bool {
    match (l, r) {
        (Value::Undef, Value::Undef) | (Value::Null, Value::Null) => true,
        (Value::Bool(a), Value::Bool(b)) => a == b,
        (Value::Num(a), Value::Num(b)) => a == b,
        (Value::Str(a), Value::Str(b)) => h.get_str(a) == h.get_str(b),
        // Boxed BigInts compare by value (canonical form makes field
        // equality exact); every other object by identity.
        (Value::Obj(a), Value::Obj(b)) => {
            a == b
                || matches!(
                    (h.obj(a), h.obj(b)),
                    (
                        Obj::BigInt { neg: an, mag: am, .. },
                        Obj::BigInt { neg: bn, mag: bm, .. }
                    ) if an == bn && am == bm
                )
        }
        _ => false,
    }
}

fn loose_eq(h: &Heap, l: Value, r: Value) -> bool {
    if strict_eq(h, l, r) {
        return true;
    }
    // BigInt-involved loose equality compares mathematical values (spec);
    // handled in one place so the Num/Str/Bool arms below never see one.
    if is_big(h, l) || is_big(h, r) {
        return loose_big(h, l, r);
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
            Obj::Symbol { .. } => "symbol",
            Obj::BigInt { .. } => "bigint",
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

/// Follow Proxy.target links (proxy-of-proxy is legal JS); caps at 8
/// hops, then returns whatever id that lands on.
fn proxy_resolve(h: &Heap, mut id: u32) -> u32 {
    for _ in 0..8 {
        match h.obj(id) {
            Obj::Proxy { target, .. } => id = *target,
            _ => return id,
        }
    }
    id
}

/// An object's own (non-inherited) prop. Arr owns "length" + indices.
/// Proxies forward transparently (traps run only at the recv_ level).
fn own_prop(h: &Heap, id: u32, key: &str) -> Option<Value> {
    let id = proxy_resolve(h, id);
    match h.obj(id) {
        Obj::Ordinary { pairs, .. } | Obj::Native { pairs, .. } => {
            pairs.iter().find(|(k, _)| k == key).map(|(_, v)| *v)
        }
        // `length` (arity before the first default/rest) lives on the
        // def, like V8 computes it - not stored. `name` is materialized
        // as a pair at creation (see func_obj).
        Obj::Func { pairs, def, .. } => {
            if key == "length" {
                let n = def.params.iter().take_while(|(_, d)| d.is_none()).count();
                return Some(Value::Num(n as f64));
            }
            pairs.iter().find(|(k, _)| k == key).map(|(_, v)| *v)
        }
        Obj::Arr { items, pairs, .. } => {
            if key == "length" {
                return Some(Value::Num(items.len() as f64));
            }
            if let Ok(i) = key.parse::<usize>() {
                if let Some(v) = items.get(i) {
                    return Some(*v);
                }
            }
            pairs.iter().find(|(k, _)| k == key).map(|(_, v)| *v)
        }
        Obj::Bytes { bytes, pairs, .. } => {
            if key == "length" || key == "byteLength" {
                return Some(Value::Num(bytes.len() as f64));
            }
            if key == "byteOffset" {
                return Some(Value::Num(0.0));
            }
            if let Ok(i) = key.parse::<usize>() {
                if let Some(b) = bytes.get(i) {
                    return Some(Value::Num(*b as f64));
                }
            }
            pairs.iter().find(|(k, _)| k == key).map(|(_, v)| *v)
        }
        Obj::Buf { bytes, .. } => match key {
            "byteLength" => Some(Value::Num(bytes.len() as f64)),
            _ => None,
        },
        Obj::Typed {
            kind,
            elems,
            pairs,
            ..
        } => {
            if key == "length" {
                return Some(Value::Num(elems.len() as f64));
            }
            if key == "byteLength" {
                return Some(Value::Num((elems.len() * t_bpe(*kind)) as f64));
            }
            if key == "byteOffset" {
                return Some(Value::Num(0.0));
            }
            if let Ok(i) = key.parse::<usize>() {
                if let Some(e) = elems.get(i) {
                    return Some(Value::Num(*e));
                }
            }
            pairs.iter().find(|(k, _)| k == key).map(|(_, v)| *v)
        }
        Obj::BufView { buf, off, len, kind, pairs, .. } => {
            let n = view_count(*kind, *len);
            if key == "length" {
                return Some(Value::Num(n as f64));
            }
            if key == "byteLength" {
                return Some(Value::Num(*len as f64));
            }
            if key == "byteOffset" {
                return Some(Value::Num(*off as f64));
            }
            if let Ok(i) = key.parse::<usize>() {
                if i >= n {
                    return pairs.iter().find(|(k, _)| k == key).map(|(_, v)| *v);
                }
                let bpe = t_bpe(*kind);
                match kind {
                    TypedKind::I64 | TypedKind::U64 => {}
                    k => {
                        if let Some(e) = view_read_num(h, *buf, off + i * bpe, *k) {
                            return Some(Value::Num(e));
                        }
                    }
                }
            }
            pairs.iter().find(|(k, _)| k == key).map(|(_, v)| *v)
        }
        Obj::DView { len, off, .. } => match key {
            "byteLength" => Some(Value::Num(*len as f64)),
            "byteOffset" => Some(Value::Num(*off as f64)),
            _ => None,
        },
        // BigInts expose no own props. Big64 indices are NOT served here
        // (boxing needs &mut, which own_prop lacks): indexed reads go
        // through get_index, `in`/hasOwnProperty via the has_prop/n_has_own
        // fast paths below; length/byteLength/expandos live here.
        Obj::BigInt { .. } => None,
        Obj::Big64 {
            elems, pairs, ..
        } => {
            if key == "length" {
                return Some(Value::Num(elems.len() as f64));
            }
            if key == "byteLength" {
                return Some(Value::Num((elems.len() * 8) as f64));
            }
            if key == "byteOffset" {
                return Some(Value::Num(0.0));
            }
            pairs.iter().find(|(k, _)| k == key).map(|(_, v)| *v)
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
        Obj::Promise { pairs, .. } => pairs.iter().find(|(k, _)| k == key).map(|(_, v)| *v),
        Obj::Dom { .. }
        | Obj::Style { .. }
        | Obj::Accessor { .. }
        | Obj::Symbol { .. }
        | Obj::Map { .. }
        | Obj::Set { .. }
        | Obj::WeakMap { .. }
        | Obj::Proxy { .. }
        | Obj::Freed => None,
    }
}

/// Heap id of `id`'s prototype. Natives get the Function proto virtually;
/// Dom has none. Proxies forward live to the target's proto
/// (getPrototypeOf trap is a documented gap).
pub(crate) fn proto_of(h: &Heap, protos: &Protos, id: u32) -> Option<u32> {
    let id = proxy_resolve(h, id);
    match h.obj(id) {
        Obj::Ordinary { proto, .. }
        | Obj::Arr { proto, .. }
        | Obj::Func { proto, .. }
        | Obj::Bytes { proto, .. }
        | Obj::Buf { proto, .. }
        | Obj::Typed { proto, .. }
        | Obj::BufView { proto, .. }
        | Obj::BigInt { proto, .. }
        | Obj::Big64 { proto, .. }
        | Obj::DView { proto, .. } => *proto,
        Obj::Native { .. } => po(protos.function_),
        Obj::Promise { .. } => po(protos.promise),
        Obj::RegExp { proto, .. } => *proto,
        Obj::Accessor { proto, .. } => *proto,
        Obj::Symbol { proto, .. } => *proto,
        Obj::Map { proto, .. } => *proto,
        Obj::Set { proto, .. } => *proto,
        Obj::WeakMap { proto, .. } => *proto,
        Obj::Style { .. } => po(protos.object),
        Obj::Dom { proto, .. } => *proto,
        // Deep chains past the resolve cap read as proto-less (gap).
        Obj::Proxy { .. } => None,
        Obj::Freed => None,
    }
}

/// Walk `start` then its proto chain; first own prop wins. Cap hops.
pub(crate) fn walk_props(h: &Heap, protos: &Protos, start: Option<u32>, key: &str) -> Result<Value, JsError> {
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
    // Big64 canonical indices read true (own_prop can't serve them: boxing
    // an element needs &mut, which it lacks).
    if let Value::Obj(id) = v {
        if let Obj::Big64 { elems, .. } = h.obj(id) {
            if key.parse::<usize>().is_ok_and(|i| i < elems.len()) {
                return true;
            }
        }
        if let Obj::BufView { len, kind, .. } = h.obj(id) {
            if matches!(kind, TypedKind::I64 | TypedKind::U64) {
                if key.parse::<usize>().is_ok_and(|i| i < view_count(*kind, *len)) {
                    return true;
                }
            }
        }
    }
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

/// `v[key]`: DOM node, live style block, proxy trap, or plain lookup.
/// Failures carry the call chain (unless they already do) for debugging.
impl Interp {
    fn recv_get(&mut self, v: Value, key: &str) -> Result<Value, JsError> {
        let r = self.recv_get_raw(v, key);
        r.map_err(|e| self.chain_msg(e))
    }

    fn recv_get_raw(&mut self, v: Value, key: &str) -> Result<Value, JsError> {
        if let Value::Obj(id) = v {
            if matches!(self.heap.obj(id), Obj::Proxy { .. }) {
                return self.proxy_get(id, key, v);
            }
            // `window` is the global scope live: env 0 first, own snapshot
            // pairs (builtin writes like defineProperty land there) after.
            if Some(id) == self.wind {
                if let Some(val) = self.env_get(0, key) {
                    return self.invoke_getter(val, v, key);
                }
            }
        }
        if let Some(n) = self.as_node(v) {
            let r = self.dom_get(n, key)?;
            // Unknown DOM keys fall back to the wrapper's proto chain
            // (constructor, hasOwnProperty, inherited bag methods).
            if !matches!(r, Value::Undef) {
                return self.invoke_getter(r, v, key);
            }
            if let Value::Obj(wid) = v {
                if let Some(p) = proto_of(&self.heap, &self.protos, wid) {
                    let val = walk_props(&self.heap, &self.protos, Some(p), key)?;
                    return self.invoke_getter(val, v, key);
                }
            }
            return Ok(Value::Undef);
        }
        if let Some(n) = self.as_style(v) {
            return self.style_get(n, key);
        }
        // `.buffer` materializes a facade (needs &mut for the alloc +
        // parent rewire); own_prop/get_prop stay allocation-free.
        if key == "buffer" {
            if let Value::Obj(id) = v {
                match self.heap.obj(id) {
                    Obj::Bytes { .. }
                    | Obj::Typed { .. }
                    | Obj::Big64 { .. }
                    | Obj::DView { .. }
                    | Obj::BufView { .. } => {
                        let b = buffer_of(self, id)?;
                        return self.invoke_getter(b, v, key);
                    }
                    _ => {}
                }
            }
        }
        let val = get_prop(&self.heap, &self.protos, v, key)?;
        self.invoke_getter(val, v, key)
    }

    fn recv_get_idx(&mut self, v: Value, k: Value) -> Result<Value, JsError> {
        let r = self.recv_get_idx_raw(v, k);
        r.map_err(|e| self.chain_msg(e))
    }

    fn recv_get_idx_raw(&mut self, v: Value, k: Value) -> Result<Value, JsError> {
        if let Value::Obj(id) = v {
            if matches!(self.heap.obj(id), Obj::Proxy { .. }) {
                let key = to_str(&self.heap, k);
                return self.proxy_get(id, &key, v);
            }
            if Some(id) == self.wind {
                let key = to_str(&self.heap, k);
                if let Some(val) = self.env_get(0, &key) {
                    return self.invoke_getter(val, v, &key);
                }
            }
        }
        if let Some(n) = self.as_node(v) {
            let key = to_str(&self.heap, k);
            return self.dom_get(n, &key);
        }
        if let Some(n) = self.as_style(v) {
            let key = to_str(&self.heap, k);
            return self.style_get(n, &key);
        }
        // `v["buffer"]` serves the same facade as `v.buffer`.
        if let Value::Obj(id) = v {
            let key = to_str(&self.heap, k);
            if key == "buffer" {
                match self.heap.obj(id) {
                    Obj::Bytes { .. }
                    | Obj::Typed { .. }
                    | Obj::Big64 { .. }
                    | Obj::DView { .. }
                    | Obj::BufView { .. } => {
                        let b = buffer_of(self, id)?;
                        return self.invoke_getter(b, v, &key);
                    }
                    _ => {}
                }
            }
        }
        let val = get_index(&mut self.heap, &self.protos, v, k)?;
        let key = to_str(&self.heap, k);
        self.invoke_getter(val, v, &key)
    }

    /// A getter value reads by calling it (this = receiver); getter-less
    /// accessors read undefined. Plain values pass through.
    fn invoke_getter(&mut self, val: Value, recv: Value, key: &str) -> Result<Value, JsError> {
        let gid = match val {
            Value::Obj(id) => match self.heap.obj(id) {
                Obj::Accessor { get: Some(g), .. } => *g,
                Obj::Accessor { .. } => return Ok(Value::Undef),
                _ => return Ok(val),
            },
            _ => return Ok(val),
        };
        self.call_value(Value::Obj(gid), recv, &[], Some(key))
    }

    fn recv_set(&mut self, v: Value, key: &str, val: Value) -> Result<(), JsError> {
        if let Value::Obj(id) = v {
            if matches!(self.heap.obj(id), Obj::Proxy { .. }) {
                return self.proxy_set(id, key, val, v);
            }
            // `window.x = v` declares a real global (V8 parity).
            if Some(id) == self.wind {
                self.env_declare(0, key, val);
                return Ok(());
            }
        }
        if let Some(n) = self.as_node(v) {
            return self.dom_set(n, key, val);
        }
        if let Some(n) = self.as_style(v) {
            return self.style_set(n, key, val);
        }
        let cur = get_prop(&self.heap, &self.protos, v, key)?;
        if self.invoke_setter(cur, v, val, key)? {
            return Ok(());
        }
        set_prop(&mut self.heap, v, key, val)
    }

    fn recv_set_idx(&mut self, v: Value, k: Value, val: Value) -> Result<(), JsError> {
        if let Value::Obj(id) = v {
            if matches!(self.heap.obj(id), Obj::Proxy { .. }) {
                let key = to_str(&self.heap, k);
                return self.proxy_set(id, &key, val, v);
            }
            if Some(id) == self.wind {
                let key = to_str(&self.heap, k);
                self.env_declare(0, &key, val);
                return Ok(());
            }
        }
        if let Some(n) = self.as_node(v) {
            let key = to_str(&self.heap, k);
            return self.dom_set(n, &key, val);
        }
        if let Some(n) = self.as_style(v) {
            let key = to_str(&self.heap, k);
            return self.style_set(n, &key, val);
        }
        let key = to_str(&self.heap, k);
        let cur = get_index(&mut self.heap, &self.protos, v, k)?;
        if self.invoke_setter(cur, v, val, &key)? {
            return Ok(());
        }
        set_index(&mut self.heap, v, k, val)
    }

    /// A setter value writes by calling it; setter-less accessors drop the
    /// write (sloppy no-op). Returns whether it handled the write.
    fn invoke_setter(
        &mut self,
        cur: Value,
        recv: Value,
        val: Value,
        key: &str,
    ) -> Result<bool, JsError> {
        let sid = match cur {
            Value::Obj(id) => match self.heap.obj(id) {
                Obj::Accessor { set: Some(s), .. } => *s,
                Obj::Accessor { .. } => return Ok(true),
                _ => return Ok(false),
            },
            _ => return Ok(false),
        };
        self.call_value(Value::Obj(sid), recv, &[val], Some(key))?;
        Ok(true)
    }

    /// `(target, handler)` pair of a proxy id (caller checked the variant).
    fn proxy_parts(&self, pid: u32) -> (Value, Value) {
        match self.heap.obj(pid) {
            Obj::Proxy { target, handler } => (Value::Obj(*target), Value::Obj(*handler)),
            _ => (Value::Undef, Value::Undef),
        }
    }

    /// A handler trap by name (Func/Native only; proxies-as-traps and
    /// non-callables count as absent - documented gap).
    fn trap(&self, handler: Value, name: &str) -> Option<Value> {
        let t = get_prop(&self.heap, &self.protos, handler, name).ok()?;
        match t {
            Value::Obj(id) => match self.heap.obj(id) {
                Obj::Func { .. } | Obj::Native { .. } => Some(t),
                _ => None,
            },
            _ => None,
        }
    }

    /// Proxy read: `handler.get(target, key, recv)` when present, else
    /// the target's value (with its getters applied, receiver = proxy).
    fn proxy_get(&mut self, pid: u32, key: &str, recv: Value) -> Result<Value, JsError> {
        let (target, handler) = self.proxy_parts(pid);
        if let Some(t) = self.trap(handler, "get") {
            let ks = self.heap.alloc_str(key.to_string())?;
            return self.call_value(t, handler, &[target, Value::Str(ks), recv], None);
        }
        let val = get_prop(&self.heap, &self.protos, target, key)?;
        self.invoke_getter(val, recv, key)
    }

    /// Proxy write: `handler.set(target, key, val, recv)` when present
    /// (return ignored, sloppy), else the target's setter/own slot.
    fn proxy_set(&mut self, pid: u32, key: &str, val: Value, recv: Value) -> Result<(), JsError> {
        let (target, handler) = self.proxy_parts(pid);
        if let Some(t) = self.trap(handler, "set") {
            let ks = self.heap.alloc_str(key.to_string())?;
            self.call_value(t, handler, &[target, Value::Str(ks), val, recv], None)?;
            return Ok(());
        }
        let cur = get_prop(&self.heap, &self.protos, target, key)?;
        if self.invoke_setter(cur, recv, val, key)? {
            return Ok(());
        }
        set_prop(&mut self.heap, target, key, val)
    }

    /// `key in proxy`: `handler.has(target, key)` when present, else the
    /// target's chain.
    fn proxy_has(&mut self, pid: u32, key: &str) -> Result<bool, JsError> {
        let (target, handler) = self.proxy_parts(pid);
        if let Some(t) = self.trap(handler, "has") {
            let ks = self.heap.alloc_str(key.to_string())?;
            let r = self.call_value(t, handler, &[target, Value::Str(ks)], None)?;
            return Ok(truthy(&self.heap, r));
        }
        Ok(has_prop(&self.heap, &self.protos, target, key))
    }

    /// `delete proxy[key]`: `handler.deleteProperty(target, key)` when
    /// present (sloppy return), else delete on the target itself.
    fn proxy_delete(&mut self, pid: u32, key: &str, kval: Option<Value>) -> Result<Value, JsError> {
        let (target, handler) = self.proxy_parts(pid);
        if let Some(t) = self.trap(handler, "deleteProperty") {
            let ks = self.heap.alloc_str(key.to_string())?;
            let r = self.call_value(t, handler, &[target, Value::Str(ks)], None)?;
            return Ok(Value::Bool(truthy(&self.heap, r)));
        }
        self.delete_key(target, key, kval)
    }
}

/// `v[key]`: own props, then proto chain, then Undef. Primitives map to
/// their protos (Str keeps `length` first). Proxies forward to the target
/// here (no traps - the recv_ level runs those before calling this).
pub(crate) fn get_prop(h: &Heap, protos: &Protos, v: Value, key: &str) -> Result<Value, JsError> {
    match v {
        Value::Obj(id) => walk_props(h, protos, Some(proxy_resolve(h, id)), key),
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

/// Typed-array store: canonical indices clamp in range and drop
/// out-of-range writes (sloppy); `length`/`byteLength`/`byteOffset` are
/// read-only no-ops; anything else is an expando pair.
fn bytes_set(h: &mut Heap, id: u32, key: &str, val: Value) -> Result<(), JsError> {
    if key == "length" || key == "byteLength" || key == "byteOffset" {
        return Ok(());
    }
    let nb = to_u8(&*h, val);
    if let Ok(i) = key.parse::<usize>() {
        if let Obj::Bytes { bytes, .. } = h.obj_mut(id) {
            if let Some(slot) = bytes.get_mut(i) {
                *slot = nb;
            }
        }
        return Ok(());
    }
    if let Obj::Bytes { pairs, .. } = h.obj_mut(id) {
        match pairs.iter_mut().find(|(k, _)| k == key) {
            Some(slot) => slot.1 = val,
            None => pairs.push((key.to_string(), val)),
        }
    }
    Ok(())
}

/// Typed-view store (non-u8): canonical indices coerce in range and
/// drop out-of-range writes (sloppy); `length`/`byteLength`/`byteOffset`
/// are read-only no-ops; anything else is an expando pair.
fn typed_set(h: &mut Heap, id: u32, kind: TypedKind, key: &str, val: Value) -> Result<(), JsError> {
    if key == "length" || key == "byteLength" || key == "byteOffset" {
        return Ok(());
    }
    let ne = t_write(kind, to_num(&*h, val));
    if let Ok(i) = key.parse::<usize>() {
        if let Obj::Typed { elems, .. } = h.obj_mut(id) {
            if let Some(slot) = elems.get_mut(i) {
                *slot = ne;
            }
        }
        return Ok(());
    }
    if let Obj::Typed { pairs, .. } = h.obj_mut(id) {
        match pairs.iter_mut().find(|(k, _)| k == key) {
            Some(slot) => slot.1 = val,
            None => pairs.push((key.to_string(), val)),
        }
    }
    Ok(())
}

/// Live-view store: indices translate per access through the backing Buf
/// (writes visible via all aliases); length-likes are no-ops; the rest
/// lands in expando pairs.
fn bufview_set(h: &mut Heap, id: u32, key: &str, val: Value) -> Result<(), JsError> {
    if key == "length" || key == "byteLength" || key == "byteOffset" {
        return Ok(());
    }
    if let Ok(i) = key.parse::<usize>() {
        let num = to_num(&*h, val);
        let w = b64_wrap(&*h, val);
        let (buf, off, len, kind) = match h.obj(id) {
            Obj::BufView { buf, off, len, kind, .. } => (*buf, *off, *len, *kind),
            _ => return Ok(()),
        };
        let bpe = t_bpe(kind);
        if i < view_count(kind, len) {
            let at = off + i * bpe;
            match kind {
                TypedKind::I64 | TypedKind::U64 => view_write_u64(h, buf, at, w),
                k => view_write_num(h, buf, at, k, num),
            }
        }
        return Ok(());
    }
    if let Obj::BufView { pairs, .. } = h.obj_mut(id) {
        match pairs.iter_mut().find(|(k, _)| k == key) {
            Some(slot) => slot.1 = val,
            None => pairs.push((key.to_string(), val)),
        }
    }
    Ok(())
}

/// Writes to own pairs only (Ordinary/Func/Native), like standard JS.
pub(crate) fn set_prop(h: &mut Heap, v: Value, key: &str, val: Value) -> Result<(), JsError> {    // Computed before the mutable borrow below.
    let last_num = to_num(&*h, val);
    let kind = match v {
        Value::Obj(id) => match h.obj(id) {
            Obj::Arr { .. } => "array",
            Obj::RegExp { .. } => "regexp",
            Obj::Promise { .. } => "promise",
            Obj::Dom { .. } => "node",
            Obj::Style { .. } => "style",
            Obj::Accessor { .. } => "accessor",
            Obj::Symbol { .. } => "symbol",
            Obj::Map { .. } => "map",
            Obj::Set { .. } => "set",
            Obj::WeakMap { .. } => "weakmap",
            Obj::Bytes { .. } => "uint8array",
            Obj::Buf { .. } => "arraybuffer",
            Obj::Typed { kind, .. } | Obj::BufView { kind, .. } => match kind {
                TypedKind::U8 => "uint8array",
                TypedKind::I8 => "int8array",
                TypedKind::U8C => "uint8clampedarray",
                TypedKind::U16 => "uint16array",
                TypedKind::I16 => "int16array",
                TypedKind::U32 => "uint32array",
                TypedKind::I32 => "int32array",
                TypedKind::F32 => "float32array",
                TypedKind::F64 => "float64array",
                TypedKind::I64 => "bigint64array",
                TypedKind::U64 => "biguint64array",
            },
            Obj::DView { .. } => "dataview",
            _ => "object",
        },
        _ => "value",
    };
    match v {
        // Proxies land on the target here (no set trap - recv_set runs it).
        Value::Obj(id) => {
            let rid = proxy_resolve(h, id);
            // Typed-array stores clamp in a separate step (the clamp
            // reads while the slot write below borrows mutably).
            if matches!(h.obj(rid), Obj::Bytes { .. }) {
                return bytes_set(h, rid, key, val);
            }
            if let Obj::Typed { kind, .. } = h.obj(rid) {
                let kind = *kind;
                return typed_set(h, rid, kind, key, val);
            }
            // Big64 named/element stores (wrap mod 2^64, like typed_set).
            if matches!(h.obj(rid), Obj::Big64 { .. }) {
                return b64_set(h, rid, key, val);
            }
            if matches!(h.obj(rid), Obj::BufView { .. }) {
                return bufview_set(h, rid, key, val);
            }
            match h.obj_mut(rid) {
            Obj::Ordinary { pairs, .. } | Obj::Func { pairs, .. } | Obj::Native { pairs, .. } => {
                match pairs.iter_mut().find(|(k, _)| k == key) {
                    Some(slot) => slot.1 = val,
                    None => pairs.push((key.to_string(), val)),
                }
                Ok(())
            }
            // Arrays take `length` (truncate/extend-with-undefined, holes
            // read undefined here) and canonical indices (growing the
            // array); anything else lands in expando pairs.
            Obj::Arr { items, pairs, .. } => {
                if key == "length" {
                    let n = last_num;
                    if n.is_nan() || n < 0.0 || n.fract() != 0.0 {
                        return Err(err("bad array length"));
                    }
                    let n = (n as usize).min(1 << 28);
                    items.resize(n, Value::Undef);
                    return Ok(());
                }
                match key.parse::<usize>() {
                    Ok(i) if i < (1 << 28) => {
                        if i >= items.len() {
                            items.resize(i + 1, Value::Undef);
                        }
                        items[i] = val;
                        Ok(())
                    }
                    _ => match pairs.iter_mut().find(|(k, _)| k == key) {
                        Some(slot) => {
                            slot.1 = val;
                            Ok(())
                        }
                        None => {
                            pairs.push((key.to_string(), val));
                            Ok(())
                        }
                    },
                }
            }
            Obj::RegExp { last_index, .. } if key == "lastIndex" => {
                *last_index = last_num;
                Ok(())
            }
            // Promises take expandos (deferred resolve/reject helpers).
            Obj::Promise { pairs, .. } => {
                match pairs.iter_mut().find(|(k, _)| k == key) {
                    Some(slot) => slot.1 = val,
                    None => pairs.push((key.to_string(), val)),
                }
                Ok(())
            }
            // Buffers and views are non-extensible: every write is a
            // sloppy no-op.
            Obj::Buf { .. } | Obj::DView { .. } => Ok(()),
            _ => Err(err(format!("cannot set '{key}' on {kind}"))),
            }
        }
        Value::Undef | Value::Null => Err(err("cannot set property of null/undefined")),
        _ => Ok(()), // primitives: sloppy no-op like real JS
    }
}

fn get_index(h: &mut Heap, protos: &Protos, v: Value, k: Value) -> Result<Value, JsError> {
    match v {
        Value::Obj(id) => {
            let n = to_num(h, k);
            // Big64 read first (immutable borrow ends), box after: indexed
            // reads yield fresh BigInts (value equality keeps
            // `a[0] === a[0]` true across boxes).
            if let Obj::Big64 { signed, elems, .. } = h.obj(id) {
                let signed = *signed;
                if n >= 0.0 && n.fract() == 0.0 {
                    match elems.get(n as usize).copied() {
                        Some(bits) => {
                            let (neg, mag) = if signed {
                                bi_from_i64(bits as i64)
                            } else {
                                bi_from_u64(bits)
                            };
                            return Ok(bi_alloc_hp(h, protos, neg, mag)?);
                        }
                        None => return Ok(Value::Undef),
                    }
                }
            }
            // Live views translate per access through the backing Buf;
            // 64-bit lanes box like Big64 above. Swept backing reads Undef.
            if let Obj::BufView { buf, off, len, kind, .. } = h.obj(id) {
                let (buf, off, len, kind) = (*buf, *off, *len, *kind);
                if n >= 0.0 && n.fract() == 0.0 {
                    let i = n as usize;
                    if i < view_count(kind, len) {
                        let bpe = t_bpe(kind);
                        let at = off + i * bpe;
                        match kind {
                            TypedKind::I64 => {
                                return match view_read_u64(h, buf, at) {
                                    Some(b) => {
                                        let (neg, mag) = bi_from_i64(b as i64);
                                        Ok(bi_alloc_hp(h, protos, neg, mag)?)
                                    }
                                    None => Ok(Value::Undef),
                                };
                            }
                            TypedKind::U64 => {
                                return match view_read_u64(h, buf, at) {
                                    Some(b) => {
                                        let (neg, mag) = bi_from_u64(b);
                                        Ok(bi_alloc_hp(h, protos, neg, mag)?)
                                    }
                                    None => Ok(Value::Undef),
                                };
                            }
                            kk => {
                                return Ok(match view_read_num(h, buf, at, kk) {
                                    Some(e) => Value::Num(e),
                                    None => Value::Undef,
                                });
                            }
                        }
                    }
                    return Ok(Value::Undef);
                }
            }
            match h.obj(id) {
                Obj::Arr { items, .. } if n >= 0.0 && n.fract() == 0.0 => {
                    Ok(items.get(n as usize).copied().unwrap_or(Value::Undef))
                }
                Obj::Bytes { bytes, .. } if n >= 0.0 && n.fract() == 0.0 => {
                    Ok(bytes.get(n as usize).map(|b| Value::Num(*b as f64)).unwrap_or(Value::Undef))
                }
                Obj::Typed { elems, .. } if n >= 0.0 && n.fract() == 0.0 => {
                    Ok(elems.get(n as usize).map(|e| Value::Num(*e)).unwrap_or(Value::Undef))
                }
                Obj::Dom { .. } => Ok(Value::Undef),
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
            if matches!(h.obj(id), Obj::Bytes { .. }) {
                // Sloppy out-of-range writes drop; length is read-only.
                let n = to_num(h, k);
                if n >= 0.0 && n.fract() == 0.0 {
                    let b = to_u8(&*h, val);
                    if let Obj::Bytes { bytes, .. } = h.obj_mut(id) {
                        if let Some(slot) = bytes.get_mut(n as usize) {
                            *slot = b;
                        }
                    }
                    return Ok(());
                }
                let key = to_str(h, k);
                return set_prop(h, v, &key, val);
            }
            let tkind = match h.obj(id) {
                Obj::Typed { kind, .. } => Some(*kind),
                _ => None,
            };
            if let Some(kind) = tkind {
                let n = to_num(h, k);
                if n >= 0.0 && n.fract() == 0.0 {
                    let ne = t_write(kind, to_num(&*h, val));
                    if let Obj::Typed { elems, .. } = h.obj_mut(id) {
                        if let Some(slot) = elems.get_mut(n as usize) {
                            *slot = ne;
                        }
                    }
                    return Ok(());
                }
                let key = to_str(h, k);
                return set_prop(h, v, &key, val);
            }
            // Big64 stores wrap mod 2^64 (sloppy coerce like the Typed
            // neighbors; out-of-range canonical indices drop).
            if matches!(h.obj(id), Obj::Big64 { .. }) {
                let n = to_num(h, k);
                if n >= 0.0 && n.fract() == 0.0 {
                    let w = b64_wrap(h, val);
                    if let Obj::Big64 { elems, .. } = h.obj_mut(id) {
                        if let Some(slot) = elems.get_mut(n as usize) {
                            *slot = w;
                        }
                    }
                    return Ok(());
                }
                let key = to_str(h, k);
                return set_prop(h, v, &key, val);
            }
            // Live views translate per access; OOB drops sloppily.
            if let Obj::BufView { buf, off, len, kind, .. } = *h.obj(id) {
                let n = to_num(h, k);
                if n >= 0.0 && n.fract() == 0.0 {
                    let i = n as usize;
                    if i < view_count(kind, len) {
                        let at = off + i * t_bpe(kind);
                        match kind {
                            TypedKind::I64 | TypedKind::U64 => {
                                let w = b64_wrap(h, val);
                                view_write_u64(h, buf, at, w);
                            }
                            kk => {
                                let num = to_num(h, val);
                                view_write_num(h, buf, at, kk, num);
                            }
                        }
                    }
                    return Ok(());
                }
                let key = to_str(h, k);
                return set_prop(h, v, &key, val);
            }
            if matches!(h.obj(id), Obj::Arr { .. }) {
                let n = to_num(h, k);
                // Canonical indices grow the array (capped: absurdly
                // large indices become named props instead of a sparse
                // giant - documented gap); anything else is an expando,
                // like V8 (a[-1], a["x"] never throw).
                if n >= 0.0 && n.fract() == 0.0 && n <= 10_000_000.0 {
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
                return set_prop(h, v, &key, val);
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
        self.heap.alloc_obj(Obj::Arr {
            items,
            proto,
            pairs: Vec::new(),
        })
    }

    /// Fresh Func under Function.prototype, with an own "prototype" object
    /// (fresh Ordinary under Object's proto) like real JS. Named funcs
    /// also carry their `name` (V8 infers more; named declarations and
    /// methods cover the observed cases).
    pub(crate) fn func_obj(&mut self, def: Rc<FnDef>, env: u32) -> Result<u32, JsError> {
        let pt = self.obj_plain()?;
        let proto = po(self.protos.function_);
        let mut pairs = vec![("prototype".into(), Value::Obj(pt))];
        if let Some(n) = &def.name {
            pairs.push(("name".into(), Value::Str(self.heap.intern_str(n)?)));
        }
        self.heap.alloc_obj(Obj::Func {
            def,
            env,
            proto,
            pairs,
        })
    }

    /// `__super` stashed on a method/accessor func by class eval, or None.
    fn func_super(&self, id: u32) -> Option<Value> {
        match self.heap.obj(id) {
            Obj::Func { pairs, .. } => pairs.iter().find(|(k, _)| k == "__super").map(|(_, v)| *v),
            _ => None,
        }
    }

    /// Evaluate a class value: prototype with methods/accessors, ctor func
    /// with statics, instance fields collected for `new`. `declare` binds
    /// the name (declarations only - expressions stay anonymous).
    fn eval_class(
        &mut self,
        env: u32,
        name: Option<String>,
        parent: &Option<Box<Expr>>,
        members: &[ClassMember],
        declare: bool,
    ) -> Result<Value, JsError> {
        let (sup_val, parent_proto) = match parent {
            None => (None, po(self.protos.object)),
            Some(p) => {
                let v = self.expr(env, p)?;
                match v {
                    Value::Null => (None, None),
                    Value::Obj(_) => {
                        let pp = match get_prop(&self.heap, &self.protos, v, "prototype")? {
                            Value::Obj(q) => Some(q),
                            _ => po(self.protos.object),
                        };
                        (Some(v), pp)
                    }
                    _ => return Err(err("class heritage must be a constructor or null")),
                }
            }
        };
        let mut proto_pairs: Vec<(String, Value)> = Vec::new();
        let mut statics: Vec<(String, Value)> = Vec::new();
        let mut fields: Vec<(String, Option<Expr>)> = Vec::new();
        let mut static_inits: Vec<(String, Option<Expr>)> = Vec::new();
        let mut ctor: Option<CtorParts> = None;
        for m in members {
            match &m.kind {
                MemberKind::Ctor { params, rest, body } => {
                    if ctor.is_some() {
                        return Err(err("duplicate constructor"));
                    }
                    ctor = Some((params.clone(), rest.clone(), body.clone()));
                }
                MemberKind::Method(nm, def) => {
                    let mid = self.func_obj(def.clone(), env)?;
                    if sup_val.is_some() {
                        self.stash_super(mid, sup_val)?;
                    }
                    if m.statik {
                        statics.push((nm.clone(), Value::Obj(mid)));
                    } else {
                        proto_pairs.push((nm.clone(), Value::Obj(mid)));
                    }
                }
                MemberKind::Get(nm, def) => {
                    let d = Some(def.clone());
                    if m.statik {
                        self.obj_accessor(env, &mut statics, nm, &d, &None)?;
                    } else {
                        self.obj_accessor(env, &mut proto_pairs, nm, &d, &None)?;
                    }
                }
                MemberKind::Set(nm, def) => {
                    let d = Some(def.clone());
                    if m.statik {
                        self.obj_accessor(env, &mut statics, nm, &None, &d)?;
                    } else {
                        self.obj_accessor(env, &mut proto_pairs, nm, &None, &d)?;
                    }
                }
                MemberKind::Field(nm, init) => {
                    if m.statik {
                        static_inits.push((nm.clone(), init.clone()));
                    } else {
                        fields.push((nm.clone(), init.clone()));
                    }
                }
                MemberKind::ComputedMethod { key, def } => {
                    let kv = self.expr(env, key)?;
                    let nm = to_str(&self.heap, kv);
                    let mid = self.func_obj(def.clone(), env)?;
                    if sup_val.is_some() {
                        self.stash_super(mid, sup_val)?;
                    }
                    if m.statik {
                        statics.push((nm, Value::Obj(mid)));
                    } else {
                        proto_pairs.push((nm, Value::Obj(mid)));
                    }
                }
                MemberKind::ComputedGet { key, def } => {
                    let kv = self.expr(env, key)?;
                    let nm = to_str(&self.heap, kv);
                    let d = Some(def.clone());
                    if m.statik {
                        self.obj_accessor(env, &mut statics, &nm, &d, &None)?;
                    } else {
                        self.obj_accessor(env, &mut proto_pairs, &nm, &d, &None)?;
                    }
                }
                MemberKind::ComputedSet { key, def } => {
                    let kv = self.expr(env, key)?;
                    let nm = to_str(&self.heap, kv);
                    let d = Some(def.clone());
                    if m.statik {
                        self.obj_accessor(env, &mut statics, &nm, &None, &d)?;
                    } else {
                        self.obj_accessor(env, &mut proto_pairs, &nm, &None, &d)?;
                    }
                }
                MemberKind::ComputedField { key, init } => {
                    let kv = self.expr(env, key)?;
                    let nm = to_str(&self.heap, kv);
                    if m.statik {
                        static_inits.push((nm, init.clone()));
                    } else {
                        fields.push((nm, init.clone()));
                    }
                }
            }
        }
        // Accessor funcs are built inside obj_accessor: stash the parent
        // on them too so getters/setters can use `super`.
        if let Some(s) = sup_val {
            let mut accs = Vec::new();
            for (_, v) in proto_pairs.iter().chain(statics.iter()) {
                if let Value::Obj(aid) = v {
                    accs.push(*aid);
                }
            }
            for aid in accs {
                let (g, st) = match self.heap.obj(aid) {
                    Obj::Accessor { get, set, .. } => (*get, *set),
                    _ => continue,
                };
                for f in [g, st].into_iter().flatten() {
                    if let Obj::Func { pairs, .. } = self.heap.obj_mut(f) {
                        pairs.push(("__super".into(), s));
                    }
                }
            }
        }
        let (params, rest, body) = match ctor {
            Some(t) => t,
            // Derived default: `constructor(...@args) { super(...@args); }`.
            None if sup_val.is_some() => (
                vec![],
                Some("@args".to_string()),
                vec![Stmt::Expr(Expr::SuperCall(vec![Expr::Spread(Box::new(
                    Expr::Ident("@args".into()),
                ))]))],
            ),
            None => (vec![], None, vec![]),
        };
        let cdef = Rc::new(FnDef {
            name: name.clone(),
            params,
            body,
            is_async: false,
            is_gen: false,
            is_arrow: false,
            rest,
            cls: Some(ClassCtor { fields }),
        });
        let proto_id = self.heap.alloc_obj(Obj::Ordinary {
            pairs: proto_pairs,
            proto: parent_proto,
        })?;
        let fproto = po(self.protos.function_);
        let mut cpairs = vec![("prototype".into(), Value::Obj(proto_id))];
        if let Some(n) = &name {
            cpairs.push(("name".into(), Value::Str(self.heap.intern_str(n)?)));
        }
        let cid = self.heap.alloc_obj(Obj::Func {
            def: cdef,
            env,
            proto: fproto,
            pairs: cpairs,
        })?;
        match self.heap.obj_mut(cid) {
            Obj::Func { pairs, .. } => {
                pairs.extend(statics);
                if let Some(s) = sup_val {
                    pairs.push(("__super".into(), s));
                }
            }
            _ => unreachable!(),
        }
        match self.heap.obj_mut(proto_id) {
            Obj::Ordinary { pairs, .. } => pairs.push(("constructor".into(), Value::Obj(cid))),
            _ => unreachable!(),
        };
        // The name is in scope for static initializers (and for methods
        // at call time - same env object, declared before any call).
        if declare {
            if let Some(n) = &name {
                self.env_declare(env, n, Value::Obj(cid));
            }
        }
        for (nm, init) in &static_inits {
            let v = match init {
                Some(e) => self.expr(env, e)?,
                None => Value::Undef,
            };
            set_prop(&mut self.heap, Value::Obj(cid), nm, v)?;
        }
        Ok(Value::Obj(cid))
    }

    /// Push a `__super` pair onto a freshly built method func.
    fn stash_super(&mut self, mid: u32, sup: Option<Value>) -> Result<(), JsError> {
        if let Some(s) = sup {
            match self.heap.obj_mut(mid) {
                Obj::Func { pairs, .. } => pairs.push(("__super".into(), s)),
                _ => return Err(err("method is not a function")),
            }
        }
        Ok(())
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

    /// Collection prototype: methods plus a `size` accessor (absent for
    /// WeakMap, like real JS). u32::MAX on heap-cap failure.
    fn coll_bag(
        &mut self,
        methods: &[(&'static str, NativeFn)],
        size_get: Option<NativeFn>,
    ) -> u32 {
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
        if let Some(size_get) = size_get {
            if let Ok(get) = self.heap.alloc_obj(nat("get size", size_get)) {
                if let Ok(acc) = self.heap.alloc_obj(Obj::Accessor {
                    get: Some(get),
                    set: None,
                    proto,
                }) {
                    if let Obj::Ordinary { pairs, .. } = self.heap.obj_mut(id) {
                        pairs.push(("size".into(), Value::Obj(acc)));
                    }
                }
            }
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
        self.put(object, "isPrototypeOf", n_is_proto);
        self.put(object, "propertyIsEnumerable", n_prop_is_enum);
        self.put(object, "valueOf", n_value_of);

        self.protos.function_ = self.proto_bag(&[
            ("call", n_fn_call),
            ("apply", n_fn_apply),
            ("bind", n_fn_bind),
            ("toString", n_fn_to_string),
        ]);
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
            ("fill", n_arr_fill),
            ("findLast", n_arr_find_last),
            ("flatMap", n_arr_flat_map),
            ("at", n_arr_at),
            ("copyWithin", n_arr_copy_within),
            ("entries", n_arr_entries),
            ("keys", n_arr_keys),
            ("values", n_arr_values),
            ("toReversed", n_arr_to_reversed),
            ("toSorted", n_arr_to_sorted),
            ("toSpliced", n_arr_to_spliced),
            ("with", n_arr_with),
        ]);
        self.protos.string = self.proto_bag(&[
            ("split", n_str_split),
            ("indexOf", n_str_index_of),
            ("lastIndexOf", n_str_last_index_of),
            ("slice", n_str_slice),
            ("substring", n_str_substring),
            ("substr", n_str_substr),
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
        self.protos.number = self.proto_bag(&[
            ("toFixed", n_num_to_fixed),
            ("toString", n_num_to_string),
        ]);
        self.protos.promise = self.proto_bag(&[
            ("then", n_promise_then),
            ("catch", n_promise_catch),
            ("finally", n_promise_finally),
        ]);
        self.protos.date = self.proto_bag(&[
            ("getTime", n_date_get_time),
            ("toISOString", n_date_iso),
            ("valueOf", n_date_get_time),
            ("getTimezoneOffset", n_date_tz),
        ]);
        self.protos.url = self.proto_bag(&[]);
        self.protos.uint8array = self.proto_bag(&[
            ("set", n_u8_set),
            ("slice", n_u8_slice),
            ("subarray", n_u8_subarray),
            ("join", n_u8_join),
            ("fill", n_u8_fill),
            ("indexOf", n_u8_index_of),
        ]);
        self.protos.buffer = self.proto_bag(&[("slice", n_buf_slice)]);
        // One method set shared across view kinds (kind rides the instance).
        let t_methods = &[
            ("set", n_t_set as NativeFn),
            ("slice", n_t_slice),
            ("subarray", n_t_subarray),
            ("join", n_t_join),
            ("fill", n_t_fill),
            ("indexOf", n_t_index_of),
        ];
        self.protos.int8array = self.proto_bag(t_methods);
        self.protos.uint8clampedarray = self.proto_bag(t_methods);
        self.protos.uint16array = self.proto_bag(t_methods);
        self.protos.int16array = self.proto_bag(t_methods);
        self.protos.uint32array = self.proto_bag(t_methods);
        self.protos.int32array = self.proto_bag(t_methods);
        self.protos.float32array = self.proto_bag(t_methods);
        self.protos.float64array = self.proto_bag(t_methods);
        self.protos.dataview = self.proto_bag(&[
            ("getUint8", n_dv_get_u8 as NativeFn),
            ("getUint16", n_dv_get_u16),
            ("getUint32", n_dv_get_u32),
            ("getInt8", n_dv_get_i8),
            ("getInt16", n_dv_get_i16),
            ("getInt32", n_dv_get_i32),
            ("getFloat32", n_dv_get_f32),
            ("getFloat64", n_dv_get_f64),
            ("getBigInt64", n_dv_get_bi64),
            ("getBigUint64", n_dv_get_bu64),
            ("setUint8", n_dv_set_u8),
            ("setUint16", n_dv_set_u16),
            ("setUint32", n_dv_set_u32),
            ("setInt8", n_dv_set_i8),
            ("setInt16", n_dv_set_i16),
            ("setInt32", n_dv_set_i32),
            ("setFloat32", n_dv_set_f32),
            ("setFloat64", n_dv_set_f64),
            ("setBigInt64", n_dv_set_bi64),
            ("setBigUint64", n_dv_set_bu64),
        ]);
        self.protos.bigint = self.proto_bag(&[
            ("toString", n_big_to_string),
            ("valueOf", n_big_value_of),
        ]);
        // One method set shared by both 64-bit views (signedness rides the
        // instance); only fill is implemented, the rest are gaps (see b64).
        self.protos.bigint64array = self.proto_bag(&[("fill", n_b64_fill)]);
        self.protos.biguint64array = self.proto_bag(&[("fill", n_b64_fill)]);
        self.protos.textencoder = self.proto_bag(&[("encode", n_te_encode)]);
        self.protos.textdecoder = self.proto_bag(&[("decode", n_td_decode)]);
        self.protos.resizeobserver = self.proto_bag(&[
            ("observe", n_resize_observe),
            ("unobserve", n_resize_observe),
            ("disconnect", n_resize_observe),
        ]);
        self.protos.intersectionobserver = self.proto_bag(&[
            ("observe", n_io_observe),
            ("unobserve", n_io_unobserve),
            ("disconnect", n_io_disconnect),
            ("takeRecords", n_io_records),
        ]);
        self.protos.storage = self.proto_bag(&[
            ("getItem", n_storage_get),
            ("setItem", n_storage_set),
            ("removeItem", n_storage_remove),
            ("clear", n_storage_clear),
            ("key", n_storage_key),
        ]);
        // DOM hierarchy: Node <- Element <- HTMLElement (+ per-tag
        // interfaces), Node <- DocumentFragment <- ShadowRoot, Node <-
        // Document. Bags chained manually (proto_bag parents to Object);
        // each carries its `constructor`. All ctors throw on `new`
        // ("Illegal constructor") - instanceof/prototype use only.
        let dom_ifaces: &[(&str, &str)] = &[
            ("Node", ""),
            ("Element", "Node"),
            ("HTMLElement", "Element"),
            ("Document", "Node"),
            ("DocumentFragment", "Node"),
            ("ShadowRoot", "DocumentFragment"),
            ("HTMLInputElement", "HTMLElement"),
            ("HTMLFormElement", "HTMLElement"),
            ("HTMLSelectElement", "HTMLElement"),
            ("HTMLTextAreaElement", "HTMLElement"),
            ("HTMLButtonElement", "HTMLElement"),
            ("HTMLAnchorElement", "HTMLElement"),
            ("HTMLImageElement", "HTMLElement"),
            ("HTMLCanvasElement", "HTMLElement"),
            ("HTMLIFrameElement", "HTMLElement"),
            ("SVGElement", "Element"),
        ];
        // Field setter per interface (match keeps this a closed set).
        let set_bag = |it: &mut Interp, name: &str, bag: u32| {
            match name {
                "Node" => it.protos.dom_node = bag,
                "Element" => it.protos.dom_element = bag,
                "HTMLElement" => it.protos.dom_htmlelement = bag,
                "Document" => it.protos.dom_document = bag,
                "ShadowRoot" => it.protos.dom_shadowroot = bag,
                "DocumentFragment" => it.protos.dom_documentfragment = bag,
                "HTMLInputElement" => it.protos.dom_input = bag,
                "HTMLFormElement" => it.protos.dom_form = bag,
                "HTMLSelectElement" => it.protos.dom_select = bag,
                "HTMLTextAreaElement" => it.protos.dom_textarea = bag,
                "HTMLButtonElement" => it.protos.dom_button = bag,
                "HTMLAnchorElement" => it.protos.dom_anchor = bag,
                "HTMLImageElement" => it.protos.dom_image = bag,
                "HTMLCanvasElement" => it.protos.dom_canvas = bag,
                "HTMLIFrameElement" => it.protos.dom_iframe = bag,
                "SVGElement" => it.protos.dom_svg = bag,
                _ => {}
            }
        };
        let get_bag = |it: &Interp, name: &str| match name {
            "Node" => it.protos.dom_node,
            "Element" => it.protos.dom_element,
            "HTMLElement" => it.protos.dom_htmlelement,
            "Document" => it.protos.dom_document,
            "ShadowRoot" => it.protos.dom_shadowroot,
            "DocumentFragment" => it.protos.dom_documentfragment,
            "HTMLInputElement" => it.protos.dom_input,
            "HTMLFormElement" => it.protos.dom_form,
            "HTMLSelectElement" => it.protos.dom_select,
            "HTMLTextAreaElement" => it.protos.dom_textarea,
            "HTMLButtonElement" => it.protos.dom_button,
            "HTMLAnchorElement" => it.protos.dom_anchor,
            "HTMLImageElement" => it.protos.dom_image,
            "HTMLCanvasElement" => it.protos.dom_canvas,
            "HTMLIFrameElement" => it.protos.dom_iframe,
            "SVGElement" => it.protos.dom_svg,
            _ => u32::MAX,
        };
        for (name, _parent) in dom_ifaces {
            let bag = self.proto_bag(&[]);
            set_bag(self, name, bag);
            self.ctor(name, n_dom_illegal, bag, &[]);
        }
        // Re-parent the bags under their DOM parents (cap-safe: bags may
        // be u32::MAX sentinels, in which case there is nothing to link
        // and instanceof degrades to false).
        let link = |it: &mut Interp, bag: u32, parent: u32| {
            if bag == u32::MAX || parent == u32::MAX {
                return;
            }
            if let Obj::Ordinary { proto, .. } = it.heap.obj_mut(bag) {
                *proto = Some(parent);
            }
        };
        for (name, parent) in dom_ifaces {
            if !parent.is_empty() {
                let (b, p) = (get_bag(self, name), get_bag(self, parent));
                link(self, b, p);
            }
        }
        // Constructor backlinks on the bags (V8: El.prototype.constructor).
        for (name, _parent) in dom_ifaces {
            let bag = get_bag(self, name);
            if bag == u32::MAX {
                continue;
            }
            if let Some(c) = self.env_get(0, name) {
                let _ = set_prop(&mut self.heap, Value::Obj(bag), "constructor", c);
            }
        }
        // Constructible Event hierarchy (separate table from the DOM
        // Node one): Event <- CustomEvent/MouseEvent/KeyboardEvent. One
        // native serves all four ctors, dispatching on its own name.
        let event_ifaces: &[(&str, &str)] = &[
            ("Event", ""),
            ("CustomEvent", "Event"),
            ("MouseEvent", "Event"),
            ("KeyboardEvent", "Event"),
        ];
        let set_ebag = |it: &mut Interp, name: &str, bag: u32| match name {
            "Event" => it.protos.event = bag,
            "CustomEvent" => it.protos.custom_event = bag,
            "MouseEvent" => it.protos.mouse_event = bag,
            "KeyboardEvent" => it.protos.keyboard_event = bag,
            _ => {}
        };
        let get_ebag = |it: &Interp, name: &str| match name {
            "Event" => it.protos.event,
            "CustomEvent" => it.protos.custom_event,
            "MouseEvent" => it.protos.mouse_event,
            "KeyboardEvent" => it.protos.keyboard_event,
            _ => u32::MAX,
        };
        for (name, _parent) in event_ifaces {
            let bag = self.proto_bag(&[]);
            set_ebag(self, name, bag);
            self.ctor(name, n_event_ctor, bag, &[]);
        }
        for (name, parent) in event_ifaces {
            if !parent.is_empty() {
                let (b, p) = (get_ebag(self, name), get_ebag(self, parent));
                link(self, b, p);
            }
        }
        for (name, _parent) in event_ifaces {
            let bag = get_ebag(self, name);
            if bag == u32::MAX {
                continue;
            }
            if let Some(c) = self.env_get(0, name) {
                let _ = set_prop(&mut self.heap, Value::Obj(bag), "constructor", c);
            }
        }
        // DOM methods as bag values (resolved reads like V8; calls still
        // hit the direct dispatch first). Inherited down the bag chain,
        // so each name registers once at its lowest level.
        for (bag_name, methods) in [
            (
                "Node",
                &[
                    "appendChild",
                    "insertBefore",
                    "removeChild",
                    "remove",
                    "cloneNode",
                    "contains",
                    "addEventListener",
                    "removeEventListener",
                    "dispatchEvent",
                ][..],
            ),
            (
                "Element",
                &[
                    "getAttribute",
                    "hasAttribute",
                    "setAttribute",
                    "removeAttribute",
                    "querySelector",
                    "querySelectorAll",
                    "getElementsByTagName",
                    "getElementsByClassName",
                    "closest",
                    "matches",
                    "getBoundingClientRect",
                    "getClientRects",
                ][..],
            ),
            (
                "Document",
                &[
                    "getElementById",
                    "getElementsByTagName",
                    "getElementsByClassName",
                    "getElementsByName",
                    "createElement",
                    "createElementNS",
                    "createTextNode",
                    "createComment",
                    "createDocumentFragment",
                    "createEvent",
                    "querySelector",
                    "querySelectorAll",
                    "hasFocus",
                ][..],
            ),
            ("HTMLFormElement", &["submit"][..]),
            ("HTMLCanvasElement", &["getContext", "toDataURL"][..]),
        ] {
            let bag = get_bag(self, bag_name);
            if bag == u32::MAX {
                continue;
            }
            for m in methods {
                self.put(bag, m, n_dom_method);
            }
        }
        // Map/Set/WeakMap prototypes; `size` is an accessor (no data slot).
        // (One block per kind: sharing `self` mutably across a table would
        // need unsafe, which this codebase forbids outside vigia-mem.)
        self.protos.map = self.coll_bag(
            &[
                ("set", n_map_set as NativeFn),
                ("get", n_map_get),
                ("has", n_map_has),
                ("delete", n_map_delete),
                ("clear", n_map_clear),
                ("keys", n_map_keys),
                ("values", n_map_values),
                ("entries", n_map_entries),
                ("forEach", n_map_for_each),
            ],
            Some(n_map_size),
        );
        self.protos.set = self.coll_bag(
            &[
                ("add", n_set_add as NativeFn),
                ("has", n_set_has),
                ("delete", n_set_delete),
                ("clear", n_set_clear),
                ("values", n_set_values),
                ("keys", n_set_values),
                ("entries", n_set_entries),
                ("forEach", n_set_for_each),
            ],
            Some(n_set_size),
        );
        self.protos.weakmap = self.coll_bag(
            &[
                ("set", n_weakmap_set as NativeFn),
                ("get", n_weakmap_get),
                ("has", n_weakmap_has),
                ("delete", n_weakmap_delete),
            ],
            None,
        );
        self.protos.regexp = self.proto_bag(&[("test", n_regexp_test), ("exec", n_regexp_exec)]);
        // Symbol.prototype: toString/valueOf methods plus a `description`
        // accessor (reuses the Accessor machinery).
        {
            let proto = po(self.protos.object);
            if let Ok(id) = self.heap.alloc_obj(Obj::Ordinary {
                pairs: vec![],
                proto,
            }) {
                self.put(id, "toString", n_sym_to_string);
                self.put(id, "valueOf", n_sym_value_of);
                if let Ok(get) = self
                    .heap
                    .alloc_obj(nat("get description", n_sym_description))
                {
                    if let Ok(acc) = self.heap.alloc_obj(Obj::Accessor {
                        get: Some(get),
                        set: None,
                        proto,
                    }) {
                        if let Obj::Ordinary { pairs, .. } = self.heap.obj_mut(id) {
                            pairs.push(("description".into(), Value::Obj(acc)));
                        }
                        self.protos.symbol = id;
                    }
                }
            }
        }
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
                ("freeze", n_obj_freeze),
                ("defineProperty", n_obj_define_property),
                ("defineProperties", n_obj_define_properties),
                ("getOwnPropertyNames", n_obj_own_names),
                ("getOwnPropertySymbols", n_obj_own_symbols),
                ("getOwnPropertyDescriptor", n_obj_get_desc),
                ("getOwnPropertyDescriptors", n_obj_get_descs),
                ("getPrototypeOf", n_obj_get_proto),
                ("setPrototypeOf", n_obj_set_proto),
                ("fromEntries", n_obj_from_entries),
                ("is", n_obj_is),
            ],
        );
        self.ctor(
            "Array",
            n_array,
            pr.array,
            &[
                ("isArray", n_is_array),
                ("of", n_array_of),
                ("from", n_array_from),
            ],
        );
        self.ctor(
            "String",
            n_string_cast,
            pr.string,
            &[
                ("fromCharCode", n_str_from_char_code),
                ("fromCodePoint", n_str_from_code_point),
                ("raw", n_str_raw),
            ],
        );
        self.ctor("Number", n_number_cast, pr.number, &[]);
        self.ctor("Boolean", n_boolean_cast, u32::MAX, &[]);
        self.ctor("Date", n_date, pr.date, &[("now", n_date_now), ("UTC", n_date_utc)]);
        self.ctor(
            "URL",
            n_url_ctor,
            pr.url,
            &[
                ("createObjectURL", n_url_create),
                ("revokeObjectURL", n_url_revoke),
            ],
        );
        self.ctor("RegExp", n_regexp_ctor, pr.regexp, &[]);
        self.ctor(
            "Symbol",
            n_symbol,
            pr.symbol,
            &[("for", n_symbol_for), ("keyFor", n_symbol_key_for)],
        );
        self.ctor("Map", n_map_ctor, pr.map, &[]);
        self.ctor("Set", n_set_ctor, pr.set, &[]);
        self.ctor("WeakMap", n_weakmap_ctor, pr.weakmap, &[]);
        self.ctor("ArrayBuffer", n_buf_ctor, pr.buffer, &[("isView", n_buf_is_view)]);
        self.ctor(
            "Uint8Array",
            n_u8_ctor,
            pr.uint8array,
            &[("of", n_u8_of), ("from", n_u8_from)],
        );
        self.ctor(
            "Int8Array",
            n_i8_ctor,
            pr.int8array,
            &[("of", n_i8_of), ("from", n_i8_from)],
        );
        self.ctor(
            "Uint8ClampedArray",
            n_u8c_ctor,
            pr.uint8clampedarray,
            &[("of", n_u8c_of), ("from", n_u8c_from)],
        );
        self.ctor(
            "Uint16Array",
            n_u16_ctor,
            pr.uint16array,
            &[("of", n_u16_of), ("from", n_u16_from)],
        );
        self.ctor(
            "Int16Array",
            n_i16_ctor,
            pr.int16array,
            &[("of", n_i16_of), ("from", n_i16_from)],
        );
        self.ctor(
            "Uint32Array",
            n_u32_ctor,
            pr.uint32array,
            &[("of", n_u32_of), ("from", n_u32_from)],
        );
        self.ctor(
            "Int32Array",
            n_i32_ctor,
            pr.int32array,
            &[("of", n_i32_of), ("from", n_i32_from)],
        );
        self.ctor(
            "Float32Array",
            n_f32_ctor,
            pr.float32array,
            &[("of", n_f32_of), ("from", n_f32_from)],
        );
        self.ctor(
            "Float64Array",
            n_f64_ctor,
            pr.float64array,
            &[("of", n_f64_of), ("from", n_f64_from)],
        );
        self.ctor(
            "BigInt",
            n_bigint_cast,
            pr.bigint,
            &[("asUintN", n_big_as_uint_n), ("asIntN", n_big_as_int_n)],
        );
        self.ctor("BigInt64Array", n_bi64_ctor, pr.bigint64array, &[]);
        self.ctor("BigUint64Array", n_bu64_ctor, pr.biguint64array, &[]);
        self.ctor("DataView", n_dv_ctor, pr.dataview, &[]);
        self.ctor("TextEncoder", n_te_ctor, pr.textencoder, &[]);
        self.ctor("TextDecoder", n_td_ctor, pr.textdecoder, &[]);
        self.ctor("MessageChannel", n_msg_channel, pr.object, &[]);
        self.ctor("ResizeObserver", n_resize_observer_ctor, pr.resizeobserver, &[]);
        self.ctor(
            "IntersectionObserver",
            n_io_ctor,
            pr.intersectionobserver,
            &[],
        );
        // IndexedDB interface guards (bare references must not throw
        // ReferenceError where V8 has the classes; open() lives on the
        // navigator.indexedDB object above).
        self.ctor("IDBRequest", n_dom_illegal, pr.object, &[]);
        self.ctor("IDBDatabase", n_dom_illegal, pr.object, &[]);
        self.ctor("IDBObjectStore", n_dom_illegal, pr.object, &[]);
        self.ctor("IDBIndex", n_dom_illegal, pr.object, &[]);
        self.ctor("IDBCursor", n_dom_illegal, pr.object, &[]);
        self.ctor("IDBTransaction", n_dom_illegal, pr.object, &[]);
        self.ctor("IDBKeyRange", n_dom_illegal, pr.object, &[]);
        // `new Image()` builds a detached <img> (needs a document).
        self.ctor("Image", n_image_ctor, pr.dom_image, &[]);
        self.ctor("Function", n_function_ctor, pr.function_, &[]);
        // Numeric statics the bundle reads (BYTES_PER_ELEMENT per view).
        for (name, bpe) in [
            ("Uint8Array", 1.0),
            ("Int8Array", 1.0),
            ("Uint8ClampedArray", 1.0),
            ("Uint16Array", 2.0),
            ("Int16Array", 2.0),
            ("Uint32Array", 4.0),
            ("Int32Array", 4.0),
            ("Float32Array", 4.0),
            ("Float64Array", 8.0),
            ("BigInt64Array", 8.0),
            ("BigUint64Array", 8.0),
        ] {
            if let Some(c) = self.env_get(0, name) {
                let _ = set_prop(&mut self.heap, c, "BYTES_PER_ELEMENT", Value::Num(bpe));
            }
        }
        let proxyp = self.proto_bag(&[]);
        self.ctor("Proxy", n_proxy_ctor, proxyp, &[]);
        self.ctor("Error", n_error, pr.error, &[]);
        // Error subtypes: own prototype under Error.prototype (so
        // `instanceof Error` holds) with their `name`, same construct
        // behavior as Error (message on `this`).
        for name in ["TypeError", "RangeError", "SyntaxError", "ReferenceError"] {
            let eproto = po(pr.error);
            let id = match self.heap.alloc_obj(Obj::Ordinary {
                pairs: vec![],
                proto: eproto,
            }) {
                Ok(id) => id,
                Err(_) => continue,
            };
            if let Ok(nm) = self.heap.alloc_str(name.to_string()) {
                if let Obj::Ordinary { pairs, .. } = self.heap.obj_mut(id) {
                    pairs.push(("name".into(), Value::Str(nm)));
                }
            }
            self.ctor(name, n_error, id, &[]);
        }
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
            ("atob", n_atob),
            ("btoa", n_btoa),
            ("addEventListener", n_win_add_event_listener),
            ("removeEventListener", n_win_remove_event_listener),
            ("dispatchEvent", n_win_dispatch_event),
            ("matchMedia", n_match_media),
            ("getComputedStyle", n_get_computed_style),
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
            ("fround", n_math_fround),
            ("trunc", n_math_trunc),
            ("sin", n_math_sin),
            ("cos", n_math_cos),
            ("tan", n_math_tan),
            ("asin", n_math_asin),
            ("acos", n_math_acos),
            ("atan", n_math_atan),
            ("atan2", n_math_atan2),
            ("sinh", n_math_sinh),
            ("cosh", n_math_cosh),
            ("tanh", n_math_tanh),
            ("exp", n_math_exp),
            ("log", n_math_log),
            ("cbrt", n_math_cbrt),
            ("hypot", n_math_hypot),
            ("sign", n_math_sign),
            ("clz32", n_math_clz32),
            ("imul", n_math_imul),
        ] {
            match self.heap.alloc_obj(nat(n, f)) {
                Ok(id) => mp.push((n.into(), Value::Obj(id))),
                Err(_) => break,
            }
        }
        mp.push(("PI".into(), Value::Num(std::f64::consts::PI)));
        mp.push(("E".into(), Value::Num(std::f64::consts::E)));
        mp.push(("SQRT2".into(), Value::Num(std::f64::consts::SQRT_2)));
        mp.push(("SQRT1_2".into(), Value::Num(std::f64::consts::FRAC_1_SQRT_2)));
        mp.push(("LN2".into(), Value::Num(std::f64::consts::LN_2)));
        mp.push(("LN10".into(), Value::Num(std::f64::consts::LN_10)));
        mp.push(("LOG2E".into(), Value::Num(std::f64::consts::LOG2_E)));
        mp.push(("LOG10E".into(), Value::Num(std::f64::consts::LOG10_E)));
        if let Ok(m) = self.obj_pairs(mp) {
            self.env_declare(0, "Math", Value::Obj(m));
        }
        if let Ok(log) = self.heap.alloc_obj(nat("log", n_console_log)) {
            if let Ok(err) = self.heap.alloc_obj(nat("error", n_console_diag)) {
                if let Ok(warn) = self.heap.alloc_obj(nat("warn", n_console_diag)) {
                    if let Ok(info) = self.heap.alloc_obj(nat("info", n_console_diag)) {
                        if let Ok(dbg) = self.heap.alloc_obj(nat("debug", n_console_diag)) {
                            if let Ok(c) = self.obj_pairs(vec![
                                ("log".into(), Value::Obj(log)),
                                ("error".into(), Value::Obj(err)),
                                ("warn".into(), Value::Obj(warn)),
                                ("info".into(), Value::Obj(info)),
                                ("debug".into(), Value::Obj(dbg)),
                            ]) {
                                self.env_declare(0, "console", Value::Obj(c));
                            }
                        }
                    }
                }
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
        // Web Storage: memory-backed locals (no persistence, no events).
        if let Ok(ls) = storage_obj(self) {
            self.env_declare(0, "localStorage", Value::Obj(ls));
        }
        if let Ok(ss) = storage_obj(self) {
            self.env_declare(0, "sessionStorage", Value::Obj(ss));
        }
        // window.history for SPA routers (no traversal).
        {
            let mut hp: Vec<(String, Value)> = Vec::new();
            for (n, f) in [
                ("pushState", n_history_push as NativeFn),
                ("replaceState", n_history_push),
                ("back", n_history_noop),
                ("forward", n_history_noop),
                ("go", n_history_noop),
                ("listen", n_history_listen),
                ("createHref", n_history_href),
                ("block", n_history_listen),
            ] {
                match self.heap.alloc_obj(nat(n, f)) {
                    Ok(id) => hp.push((n.into(), Value::Obj(id))),
                    Err(_) => break,
                }
            }
            hp.push(("length".into(), Value::Num(1.0)));
            hp.push(("state".into(), Value::Null));
            if let Ok(h) = self.obj_pairs(hp) {
                self.env_declare(0, "history", Value::Obj(h));
            }
        }
        // Numeric globals (writable in sloppy reality; plain slots here).
        self.env_declare(0, "NaN", Value::Num(f64::NAN));
        self.env_declare(0, "Infinity", Value::Num(f64::INFINITY));
        // Static viewport persona (no layout engine): 1366x768 desktop,
        // mirrored on window via the env0 seeding in set_dom.
        for (n, v) in [
            ("innerWidth", 1366.0),
            ("innerHeight", 768.0),
            ("outerWidth", 1366.0),
            ("outerHeight", 768.0),
            ("screenX", 0.0),
            ("screenY", 0.0),
            ("scrollX", 0.0),
            ("scrollY", 0.0),
            ("pageXOffset", 0.0),
            ("pageYOffset", 0.0),
            ("devicePixelRatio", 1.0),
        ] {
            self.env_declare(0, n, Value::Num(v));
        }
        // window.screen persona (orientation object nested).
        {
            let land = self.heap.alloc_str("landscape-primary".into());
            if let Ok(land) = land {
                if let Ok(ori) = self.obj_pairs(vec![
                    ("angle".into(), Value::Num(0.0)),
                    ("type".into(), Value::Str(land)),
                ]) {
                    if let Ok(scr) = self.obj_pairs(vec![
                        ("width".into(), Value::Num(1920.0)),
                        ("height".into(), Value::Num(1080.0)),
                        ("availWidth".into(), Value::Num(1920.0)),
                        ("availHeight".into(), Value::Num(1040.0)),
                        ("availLeft".into(), Value::Num(0.0)),
                        ("availTop".into(), Value::Num(0.0)),
                        ("colorDepth".into(), Value::Num(24.0)),
                        ("pixelDepth".into(), Value::Num(24.0)),
                        ("orientation".into(), Value::Obj(ori)),
                    ]) {
                        self.env_declare(0, "screen", Value::Obj(scr));
                    }
                }
            }
        }
        // window.performance (ruxit probes exactly this surface).
        {
            let mut pp: Vec<(String, Value)> = Vec::new();
            for (n, f) in [
                ("now", n_perf_now as NativeFn),
                ("getEntries", n_perf_empty_arr),
                ("getEntriesByType", n_perf_empty_arr),
                ("getEntriesByName", n_perf_empty_arr),
                ("setResourceTimingBufferSize", n_perf_noop),
                ("clearResourceTimings", n_perf_noop),
            ] {
                match self.heap.alloc_obj(nat(n, f)) {
                    Ok(id) => pp.push((n.into(), Value::Obj(id))),
                    Err(_) => break,
                }
            }
            pp.push(("timeOrigin".into(), Value::Num(self.perf_t0 as f64)));
            // Chrome-only memory counters (stable persona values;
            // absence reads Firefox/Safari-like, mismatched under a
            // Chrome UA).
            if let Ok(mem) = self.obj_pairs(vec![
                ("jsHeapSizeLimit".into(), Value::Num(4294967296.0)),
                ("totalJSHeapSize".into(), Value::Num(32000000.0)),
                ("usedJSHeapSize".into(), Value::Num(19000000.0)),
            ]) {
                pp.push(("memory".into(), Value::Obj(mem)));
            }
            if let Ok(p) = self.obj_pairs(pp) {
                self.env_declare(0, "performance", Value::Obj(p));
            }
        }
        // PerformanceResourceTiming ctor guard (ruxit: function or object).
        self.ctor("PerformanceResourceTiming", n_dom_illegal, pr.object, &[]);
        // Reflect: plain object (no constructor). Reads/writes honor
        // proxy traps; the rest forwards to the shared free-fn paths.
        let mut rp: Vec<(String, Value)> = Vec::new();
        for (n, f) in [
            ("get", n_reflect_get as NativeFn),
            ("set", n_reflect_set),
            ("has", n_reflect_has),
            ("deleteProperty", n_reflect_delete),
            ("getOwnPropertyDescriptor", n_reflect_get_desc),
            ("getPrototypeOf", n_reflect_get_proto),
            ("ownKeys", n_reflect_own_keys),
            ("construct", n_reflect_construct),
            ("apply", n_reflect_apply),
        ] {
            match self.heap.alloc_obj(nat(n, f)) {
                Ok(id) => rp.push((n.into(), Value::Obj(id))),
                Err(_) => break,
            }
        }
        if let Ok(r) = self.obj_pairs(rp) {
            self.env_declare(0, "Reflect", Value::Obj(r));
        }
        self.env_declare(0, "this", Value::Undef);
    }

    fn tick(&mut self) -> Result<(), JsError> {
        self.steps += 1;
        // Progress sampler: every 2M steps with VIGIA_JSTICK, print the
        // live chain - a stuck chain means an infinite loop, a moving one
        // means slow-but-alive boot.
        if std::env::var_os("VIGIA_JSTICK").is_some() && self.steps % 2_000_000 == 0 {
            eprintln!("js? steps={} chain={}", self.steps, self.js_chain());
        }
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
            // On demand: loops inside a call (obfuscator decode loops)
            // never reach a depth-0 safepoint, so recycle dead envs here.
            // Safe at any depth (see gc_envs).
            self.gc_envs();
            if let Some(id) = self.free_envs.pop() {
                let e = &mut self.envs[id as usize];
                e.vars.clear();
                e.parent = Some(parent);
                e.free = false;
                return Ok(id);
            }
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

    /// Sloppy-mode receiver: the window object when a DOM is installed,
    /// Undef on bare runs (plain `vigia js` has no global object).
    pub(crate) fn sloppy_this(&self) -> Value {
        self.wind.map(Value::Obj).unwrap_or(Value::Undef)
    }

    /// Elapsed wall ms since creation (performance.now).
    pub(crate) fn perf_elapsed(&self) -> f64 {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_millis() as u64)
            .unwrap_or(self.perf_t0);
        now.saturating_sub(self.perf_t0) as f64
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
        // Hoist + record: Stmt::FnDecl below skips recorded defs so each
        // declaration materializes exactly once per entry.
        let hbase = self.hoisted.len();
        for s in stmts {
            if let Stmt::FnDecl(def) = s {
                self.hoisted.push(Rc::as_ptr(def));
                let f = self.func_obj(def.clone(), env)?;
                if let Some(n) = &def.name {
                    self.env_declare(env, n, Value::Obj(f));
                    // Annex B (sloppy): a block-level `function` also
                    // binds - and assigns on block entry - in the
                    // enclosing function scope (a no-op at function top
                    // level and global scope, where env already is it).
                    if env != self.func_env {
                        self.env_declare(self.func_env, n, Value::Obj(f));
                    }
                }
            }
        }
        let mut r = Ok(Flow::Normal);
        for s in stmts {
            self.tick()?;
            // safepoint: the previous statement's temporaries are consumed
            self.maybe_gc();
            match self.stmt(env, s)? {
                Flow::Normal => {}
                f => {
                    r = Ok(f);
                    break;
                }
            }
        }
        self.hoisted.truncate(hbase);
        r
    }

    fn stmt(&mut self, env: u32, s: &Stmt) -> Result<Flow, JsError> {
        match s {
            Stmt::Expr(e) => {
                self.last = self.expr(env, e)?;
                Ok(Flow::Normal)
            }
            Stmt::VarDecl(kind, ds) => {
                // `var` binds function scope; `let`/`const` the block.
                let benv = if *kind == VarKind::Var {
                    self.func_env
                } else {
                    env
                };
                for d in ds {
                    match d {
                        VarDecl::Plain(n, init) => {
                            match init {
                                Some(e) => {
                                    let v = self.expr(env, e)?;
                                    self.env_declare(benv, n, v);
                                }
                                // Bare `var x;` never overwrites (a hoisted
                                // function or earlier value survives).
                                None => {
                                    if !self.envs[benv as usize].vars.contains_key(n) {
                                        self.env_declare(benv, n, Value::Undef);
                                    }
                                }
                            }
                        }
                        VarDecl::Pat(pat, init) => {
                            let v = self.expr(env, init)?;
                            self.destructure(env, benv, pat, v, false)?;
                        }
                    }
                }
                Ok(Flow::Normal)
            }
            Stmt::FnDecl(def) => {
                // Hoisted above (block entry or function entry): skip, so
                // the declaration materializes exactly once - recreating
                // would orphan the prototype installed between (Babel
                // _inherits' `n.prototype`). Unvisited positions (nested
                // blocks no pass reaches... in practice always visited)
                // still declare on execution, with the Annex-B mirror.
                if self.hoisted.contains(&(Rc::as_ptr(def) as *const FnDef)) {
                    return Ok(Flow::Normal);
                }
                let f = self.func_obj(def.clone(), env)?;
                if let Some(n) = &def.name {
                    self.env_declare(env, n, Value::Obj(f));
                    if env != self.func_env {
                        self.env_declare(self.func_env, n, Value::Obj(f));
                    }
                }
                Ok(Flow::Normal)
            }
            Stmt::ClassDecl(n, c) => {
                // Never hoisted: earlier use is "not defined".
                match c {
                    Expr::Class {
                        name: _,
                        parent,
                        members,
                    } => {
                        self.eval_class(env, Some(n.clone()), parent, members, true)?;
                    }
                    _ => {
                        let v = self.expr(env, c)?;
                        self.env_declare(env, n, v);
                    }
                }
                Ok(Flow::Normal)
            }
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
                // A directly-enclosing `name:` hands its name over; only
                // its own (or no) label resumes/breaks here.
                let mine = self.label_direct.take();
                loop {
                    self.maybe_gc();
                    let c = self.expr(env, c)?;
                    if !truthy(&self.heap, c) {
                        break;
                    }
                    self.tick()?;
                    match self.stmt(env, body)? {
                        Flow::Normal => {}
                        Flow::Continue(t) if t.is_none() || mine.as_deref() == t.as_deref() => {}
                        Flow::Break(t) if t.is_none() || mine.as_deref() == t.as_deref() => break,
                        f => return Ok(f),
                    }
                }
                Ok(Flow::Normal)
            }
            Stmt::DoWhile(body, c) => {
                let mine = self.label_direct.take();
                loop {
                    self.maybe_gc();
                    match self.stmt(env, body)? {
                        Flow::Normal => {}
                        Flow::Continue(t) if t.is_none() || mine.as_deref() == t.as_deref() => {}
                        Flow::Break(t) if t.is_none() || mine.as_deref() == t.as_deref() => break,
                        f => return Ok(f),
                    }
                    self.tick()?;
                    let c = self.expr(env, c)?;
                    if !truthy(&self.heap, c) {
                        break;
                    }
                }
                Ok(Flow::Normal)
            }
            Stmt::For(init, test, upd, body) => self.stmt_for(env, init, test, upd, body),
            Stmt::ForOf {
                pat,
                decl,
                iter,
                body,
            } => {
                let items = self.for_of_items(env, iter)?;
                self.stmt_each(env, pat, decl, &items, body)
            }
            Stmt::ForIn {
                pat,
                decl,
                obj,
                body,
            } => {
                let keys = self.for_in_keys(env, obj)?;
                self.stmt_each(env, pat, decl, &keys, body)
            }
            Stmt::Switch { disc, cases } => {
                let v = self.expr(env, disc)?;
                // First strict match wins (tests eval in order); else the
                // default; fallthrough runs every later clause body.
                let mut start = None;
                let mut default = None;
                for (i, (t, _)) in cases.iter().enumerate() {
                    match t {
                        Some(e) => {
                            if start.is_none() {
                                let cv = self.expr(env, e)?;
                                if strict_eq(&self.heap, v, cv) {
                                    start = Some(i);
                                    break;
                                }
                            }
                        }
                        None => {
                            if default.is_none() {
                                default = Some(i);
                            }
                        }
                    }
                }
                if let Some(s) = start.or(default) {
                    for (_, body) in &cases[s..] {
                        match self.exec_block(body, env)? {
                            Flow::Normal => {}
                            Flow::Break(None) => break,
                            other => return Ok(other),
                        }
                    }
                }
                Ok(Flow::Normal)
            }
            Stmt::Label(name, body) => {
                // Hand a directly-wrapped loop its name so `continue
                // name` resumes it (and not some inner loop); anything
                // else keeps the previous handoff. Restored after.
                let wraps_loop = matches!(
                    **body,
                    Stmt::For(..)
                        | Stmt::ForOf { .. }
                        | Stmt::ForIn { .. }
                        | Stmt::While(..)
                        | Stmt::DoWhile(..)
                );
                let prev = std::mem::replace(
                    &mut self.label_direct,
                    if wraps_loop { Some(name.clone()) } else { None },
                );
                let r = self.stmt(env, body);
                self.label_direct = prev;
                match r? {
                    Flow::Normal => Ok(Flow::Normal),
                    Flow::Break(t) if t.is_none() || t.as_deref() == Some(name.as_str()) => {
                        Ok(Flow::Normal)
                    }
                    Flow::Continue(t) if t.as_deref() == Some(name.as_str()) => {
                        Err(err(format!("continue target '{name}' is not a loop")))
                    }
                    f => Ok(f),
                }
            }
            Stmt::Block(ss) => self.exec_scoped(env, ss),
            Stmt::Break(t) => Ok(Flow::Break(t.clone())),
            Stmt::Continue(t) => Ok(Flow::Continue(t.clone())),
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

    /// Innermost call chain for error context ("a > b > ?"),
    /// truncated to the last 6 frames. Empty at top level.
    fn js_chain(&self) -> String {
        let mut parts = Vec::new();
        for &id in &self.js_stack {
            let nm = match self.heap.obj(id) {
                Obj::Func { def, .. } => def.name.clone().unwrap_or_else(|| "?".into()),
                Obj::Native { name, .. } => name.to_string(),
                _ => "?".into(),
            };
            parts.push(nm);
        }
        if parts.len() > 6 {
            parts = parts[parts.len() - 6..].to_vec();
        }
        parts.join(" > ")
    }

    /// "{msg} (in a > b)" when inside calls - the same chain context
    /// undefined_err adds, for errors raised at call boundaries.
    fn err_chain(&self, msg: String) -> JsError {
        if self.js_stack.is_empty() {
            return err(msg);
        }
        err(format!("{msg} (in {})", self.js_chain()))
    }

    /// Append the call chain to a propagated Msg (member reads, calls)
    /// unless it already carries one - pinpoints bundle failures.
    fn chain_msg(&self, e: JsError) -> JsError {
        match e {
            JsError::Msg(m) if !m.contains("(in ") && !self.js_stack.is_empty() => {
                JsError::Msg(format!("{m} (in {})", self.js_chain()))
            }
            _ => e,
        }
    }

    /// "{n} is not defined", plus the call chain when inside calls.
    fn undefined_err(&self, n: &str) -> JsError {
        let mut m = format!("{n} is not defined");
        if !self.js_stack.is_empty() {
            m.push_str(&format!(" (in {})", self.js_chain()));
        }
        err(m)
    }

    /// Hoist `var` bindings (as undefined) and block-level function
    /// declarations into the function env, once per function entry.
    /// `let`/`const`/classes stay lexical (TDZ preserved). Functions win
    /// over vars regardless of source order; `var` never overwrites.
    pub(crate) fn hoist_vars(&mut self, stmts: &[Stmt], fenv: u32) -> Result<(), JsError> {
        for s in stmts {
            match s {
                Stmt::VarDecl(kind, ds) if *kind == VarKind::Var => {
                    for d in ds {
                        match d {
                            VarDecl::Plain(n, _) => self.hoist_name(fenv, n),
                            VarDecl::Pat(pat, _) => self.hoist_pat(fenv, pat),
                        }
                    }
                }
                Stmt::FnDecl(def) => {
                    if let Some(n) = &def.name {
                        self.hoisted.push(Rc::as_ptr(def));
                        let f = self.func_obj(def.clone(), fenv)?;
                        self.env_declare(fenv, n, Value::Obj(f));
                    }
                }
                Stmt::If(_, t, e) => {
                    self.hoist_vars(std::slice::from_ref(t), fenv)?;
                    if let Some(e) = e {
                        self.hoist_vars(std::slice::from_ref(e), fenv)?;
                    }
                }
                Stmt::While(_, b) | Stmt::DoWhile(b, _) | Stmt::Label(_, b) => {
                    self.hoist_vars(std::slice::from_ref(b), fenv)?;
                }
                Stmt::For(init, _, _, b) => {
                    // `for (var x = ...;;)` declares x function-wide even
                    // when the loop never runs: hoist the init too (the
                    // VarDecl arm only takes `var`; `let`/`const` inits
                    // stay loop-scoped, other inits declare nothing).
                    if let Some(init) = init {
                        self.hoist_vars(std::slice::from_ref(init), fenv)?;
                    }
                    self.hoist_vars(std::slice::from_ref(b), fenv)?;
                }
                Stmt::ForOf {
                    pat, decl, body, ..
                }
                | Stmt::ForIn {
                    pat, decl, body, ..
                } => {
                    // `for (var x in/of ...)` likewise binds function scope.
                    if *decl == Some(VarKind::Var) {
                        self.hoist_pat(fenv, pat);
                    }
                    self.hoist_vars(std::slice::from_ref(body), fenv)?;
                }
                Stmt::Switch { cases, .. } => {
                    for (_, body) in cases {
                        self.hoist_vars(body, fenv)?;
                    }
                }
                Stmt::Try {
                    body, catch, finally,
                } => {
                    self.hoist_vars(body, fenv)?;
                    if let Some((_, cbody)) = catch {
                        self.hoist_vars(cbody, fenv)?;
                    }
                    if let Some(f) = finally {
                        self.hoist_vars(f, fenv)?;
                    }
                }
                Stmt::Block(ss) => self.hoist_vars(ss, fenv)?,
                _ => {}
            }
        }
        Ok(())
    }

    /// Declare one hoisted name as undefined unless present (functions
    /// and earlier vars win over later `var`s).
    fn hoist_name(&mut self, fenv: u32, n: &str) {
        if !self.envs[fenv as usize].vars.contains_key(n) {
            self.env_declare(fenv, n, Value::Undef);
        }
    }

    /// Ident leaves of a pattern, for the hoist pre-pass (defaults are
    /// runtime expressions, never evaluated here).
    fn hoist_pat(&mut self, fenv: u32, pat: &Pat) {
        match pat {
            Pat::Ident(n) => self.hoist_name(fenv, n),
            Pat::Arr(els, rest) => {
                for el in els.iter().flatten() {
                    self.hoist_pat(fenv, &el.0);
                }
                if let Some(r) = rest {
                    self.hoist_name(fenv, r);
                }
            }
            Pat::Obj(fields, rest) => {
                for f in fields {
                    self.hoist_pat(fenv, &f.pat);
                }
                if let Some(r) = rest {
                    self.hoist_name(fenv, r);
                }
            }
        }
    }

    fn exec_scoped(&mut self, env: u32, ss: &[Stmt]) -> Result<Flow, JsError> {
        // Fresh env only for block-scoped bindings (`let`/`const`,
        // functions, classes). Pure-`var` blocks bind function scope.
        if ss.iter().any(|s| match s {
            Stmt::VarDecl(k, _) => *k != VarKind::Var,
            Stmt::FnDecl(_) | Stmt::ClassDecl(..) => true,
            _ => false,
        }) {
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
                // Caught: the in-flight chain belongs to a handled throw.
                self.throw_chain = None;
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
    /// as an Error object so `e.message`/`e instanceof Error` work. The
    /// materialized object gets a `stack` from the in-flight chain.
    fn catch_env(&mut self, env: u32, param: Option<&str>, e: JsError) -> Result<u32, JsError> {
        let v = match e {
            JsError::Throw(v) => v,
            JsError::Msg(m) => {
                let o = self.error_obj(&m)?;
                let chain = self.throw_chain.clone().unwrap_or_default();
                let text = Self::stack_string("Error", &m, &chain);
                if let Ok(sid) = self.heap.alloc_str(text) {
                    let _ = set_prop(&mut self.heap, o, "stack", Value::Str(sid));
                }
                o
            }
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
        let mine = self.label_direct.take();
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
                Flow::Normal => {}
                Flow::Continue(t) if t.is_none() || mine.as_deref() == t.as_deref() => {}
                Flow::Break(t) if t.is_none() || mine.as_deref() == t.as_deref() => break,
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
    fn for_of_items(&mut self, env: u32, iter: &Expr) -> Result<Vec<Value>, JsError> {
        let v = self.expr(env, iter)?;
        match v {
            Value::Obj(id) => match self.heap.obj(id) {
                Obj::Arr { items, .. } => Ok(items.clone()),
                Obj::Bytes { bytes, .. } => {
                    Ok(bytes.iter().map(|b| Value::Num(*b as f64)).collect())
                }
                Obj::Typed { elems, .. } => Ok(elems.iter().map(|e| Value::Num(*e)).collect()),
                Obj::BufView { buf, off, len, kind, .. } => {
                    let (buf, off, len, kind) = (*buf, *off, *len, *kind);
                    let n = view_count(kind, len);
                    let bpe = t_bpe(kind);
                    let mut out = Vec::with_capacity(n);
                    for i in 0..n {
                        let at = off + i * bpe;
                        match kind {
                            TypedKind::I64 => {
                                let b = view_read_u64(&self.heap, buf, at).unwrap_or(0);
                                let (neg, mag) = bi_from_i64(b as i64);
                                out.push(bi_alloc(self, neg, mag)?);
                            }
                            TypedKind::U64 => {
                                let b = view_read_u64(&self.heap, buf, at).unwrap_or(0);
                                let (neg, mag) = bi_from_u64(b);
                                out.push(bi_alloc(self, neg, mag)?);
                            }
                            kk => {
                                out.push(Value::Num(
                                    view_read_num(&self.heap, buf, at, kk).unwrap_or(0.0),
                                ));
                            }
                        }
                    }
                    Ok(out)
                }
                Obj::Big64 { signed, elems, .. } => {
                    let signed = *signed;
                    let mut out = Vec::with_capacity(elems.len());
                    for bits in elems.clone() {
                        let (neg, mag) = if signed {
                            bi_from_i64(bits as i64)
                        } else {
                            bi_from_u64(bits)
                        };
                        out.push(bi_alloc(self, neg, mag)?);
                    }
                    Ok(out)
                }
                Obj::Set { items, .. } => Ok(items.clone()),
                Obj::Map { entries, .. } => {
                    let mut out = Vec::with_capacity(entries.len());
                    for (k, v) in entries.clone() {
                        out.push(Value::Obj(self.arr_obj(vec![k, v])?));
                    }
                    Ok(out)
                }
                _ => Err(err("for-of only over arrays, typed arrays, sets, maps and strings")),
            },
            Value::Str(id) => {
                let s = self.heap.get_str(id).to_string();
                let mut out = Vec::new();
                for ch in s.chars() {
                    out.push(Value::Str(self.heap.alloc_str(ch.to_string())?));
                }
                Ok(out)
            }
            _ => Err(err("for-of only over arrays, typed arrays, sets, maps and strings")),
        }
    }

    /// Strict for-in: own enumerable keys. Arrays and strings yield
    /// indices; anything else yields nothing.
    fn for_in_keys(&mut self, env: u32, obj: &Expr) -> Result<Vec<Value>, JsError> {
        let v = self.expr(env, obj)?;
        let mut keys: Vec<String> = Vec::new();
        // ownKeys trap is a documented gap: proxies enumerate the target.
        let v = match v {
            Value::Obj(id) => Value::Obj(proxy_resolve(&self.heap, id)),
            _ => v,
        };
        match v {
            Value::Obj(id) => match self.heap.obj(id) {
                Obj::Ordinary { pairs, .. }
                | Obj::Func { pairs, .. }
                | Obj::Native { pairs, .. } => {
                    keys.extend(pairs.iter().map(|(k, _)| k.clone()));
                }
                Obj::Arr { items, pairs, .. } => {
                    keys.extend((0..items.len()).map(|i| i.to_string()));
                    keys.extend(pairs.iter().map(|(k, _)| k.clone()));
                }
                Obj::Bytes { bytes, pairs, .. } => {
                    keys.extend((0..bytes.len()).map(|i| i.to_string()));
                    keys.extend(pairs.iter().map(|(k, _)| k.clone()));
                }
                Obj::Typed { elems, pairs, .. } => {
                    keys.extend((0..elems.len()).map(|i| i.to_string()));
                    keys.extend(pairs.iter().map(|(k, _)| k.clone()));
                }
                Obj::Big64 { elems, pairs, .. } => {
                    keys.extend((0..elems.len()).map(|i| i.to_string()));
                    keys.extend(pairs.iter().map(|(k, _)| k.clone()));
                }
                Obj::BufView { len, kind, pairs, .. } => {
                    keys.extend((0..view_count(*kind, *len)).map(|i| i.to_string()));
                    keys.extend(pairs.iter().map(|(k, _)| k.clone()));
                }
                Obj::Promise { pairs, .. } => {
                    keys.extend(pairs.iter().map(|(k, _)| k.clone()));
                }
                Obj::RegExp { .. }
                | Obj::Dom { .. }
                | Obj::Style { .. }
                | Obj::Accessor { .. }
                | Obj::Symbol { .. }
                | Obj::BigInt { .. }
                | Obj::Map { .. }
                | Obj::Set { .. }
                | Obj::WeakMap { .. }
                | Obj::Proxy { .. }
                | Obj::Buf { .. }
                | Obj::DView { .. }
                | Obj::Freed => {}
            },
            Value::Str(id) => {
                keys.extend((0..self.heap.get_str(id).chars().count()).map(|i| i.to_string()));
            }
            _ => {}
        }
        let mut out = Vec::with_capacity(keys.len());
        for k in keys {
            out.push(Value::Str(self.heap.alloc_str(k)?));
        }
        Ok(out)
    }

    fn stmt_each(
        &mut self,
        env: u32,
        pat: &Pat,
        decl: &Option<VarKind>,
        items: &[Value],
        body: &Stmt,
    ) -> Result<Flow, JsError> {
        let fenv = self.new_env(env)?;
        self.env_stack.push(fenv);
        let r = self.stmt_each_loop(fenv, pat, decl, items, body);
        self.env_stack.pop();
        r
    }

    fn stmt_each_loop(
        &mut self,
        fenv: u32,
        pat: &Pat,
        decl: &Option<VarKind>,
        items: &[Value],
        body: &Stmt,
    ) -> Result<Flow, JsError> {
        let mine = self.label_direct.take();
        // `var` targets bind function scope; everything else the loop env.
        let benv = match decl {
            Some(VarKind::Var) => self.func_env,
            _ => fenv,
        };
        for &item in items {
            self.tick()?;
            self.maybe_gc();
            match (pat, decl) {
                // Bare `for (x of ...)` assigns (possibly to a global).
                (Pat::Ident(n), None) => {
                    if !self.env_set(fenv, n, item) {
                        self.env_declare(0, n, item);
                    }
                }
                // Declarations always bind fresh (patterns may assign
                // through nested member leaves - handled inside).
                _ => self.destructure(fenv, benv, pat, item, decl.is_none())?,
            }
            match self.stmt(fenv, body)? {
                Flow::Normal => {}
                Flow::Continue(t) if t.is_none() || mine.as_deref() == t.as_deref() => {}
                Flow::Break(t) if t.is_none() || mine.as_deref() == t.as_deref() => break,
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
            Expr::Ident(n) => self.env_get(env, n).ok_or_else(|| self.undefined_err(n)),
            Expr::Arr(items) => {
                let mut v = Vec::with_capacity(items.len());
                for it in items {
                    if let Expr::Spread(e) = it {
                        v.extend(self.spread_items(env, e)?);
                    } else {
                        v.push(self.expr(env, it)?);
                    }
                }
                Ok(Value::Obj(self.arr_obj(v)?))
            }
            Expr::Spread(_) => Err(err("spread outside a call, array or object")),
            Expr::ObjLit(ps) => {
                let mut pairs: Vec<(String, Value)> = Vec::new();
                let put = |pairs: &mut Vec<(String, Value)>, k: String, v: Value| match pairs
                    .iter_mut()
                    .find(|(pk, _)| *pk == k)
                {
                    Some(slot) => slot.1 = v,
                    None => pairs.push((k, v)),
                };
                for entry in ps {
                    match entry {
                        ObjEntry::Pair(k, ex) => {
                            let v = self.expr(env, ex)?;
                            put(&mut pairs, k.clone(), v);
                        }
                        ObjEntry::Spread(ex) => {
                            for (k, v) in self.spread_pairs(env, ex)? {
                                put(&mut pairs, k, v);
                            }
                        }
                        ObjEntry::Computed(kex, vex) => {
                            let kv = self.expr(env, kex)?;
                            let v = self.expr(env, vex)?;
                            put(&mut pairs, to_str(&self.heap, kv), v);
                        }
                        ObjEntry::Accessor { key, get, set } => {
                            self.obj_accessor(env, &mut pairs, key, get, set)?;
                        }
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
            Expr::Destructure(pat, rhs) => {
                let v = self.expr(env, rhs)?;
                self.destructure(env, env, pat, v, true)?;
                Ok(v)
            }
            Expr::Call(c, args) => self.call(env, c, args),
            Expr::Member(o, name) => {
                let v = self.expr(env, o)?;
                if matches!(v, Value::Null | Value::Undef)
                    && std::env::var_os("VIGIA_JSENVDUMP").is_some()
                {
                    self.dump_envs(env);
                    let dbg = format!("{o:?}");
                    eprintln!(
                        "js? .{name} of nullish from {:.300}",
                        dbg.chars().take(300).collect::<String>()
                    );
                }
                self.recv_get(v, name)
            }
            Expr::Regex { pat, flags } => make_regexp(self, pat, flags),
            Expr::Tpl(parts, tail) => {
                let mut s = String::new();
                for (cooked, e) in parts {
                    s.push_str(cooked);
                    let v = self.expr(env, e)?;
                    // No implicit BigInt -> string (spec): templates throw.
                    if is_big(&self.heap, v) {
                        return Err(err("Cannot convert a BigInt value to a string"));
                    }
                    s.push_str(&to_str(&self.heap, v));
                }
                s.push_str(tail);
                Ok(Value::Str(self.heap.intern_str(&s)?))
            }
            Expr::TaggedTpl {
                tag,
                parts,
                cooked_tail,
                raw_tail,
            } => self.tagged_tpl(env, tag, parts, cooked_tail, raw_tail),
            Expr::OptChain(b, ops) => self.opt_chain(env, b, ops),
            Expr::Index(o, ix) => {
                let v = self.expr(env, o)?;
                let k = self.expr(env, ix)?;
                if matches!(v, Value::Null | Value::Undef)
                    && std::env::var_os("VIGIA_JSENVDUMP").is_some()
                {
                    self.dump_envs(env);
                    let dbg = format!("{o:?}[{:?}]", ix);
                    eprintln!(
                        "js? index of nullish from {:.300}",
                        dbg.chars().take(300).collect::<String>()
                    );
                }
                self.recv_get_idx(v, k)
            }
            Expr::Func(def) => Ok(Value::Obj(self.func_obj(def.clone(), env)?)),
            Expr::Class {
                name,
                parent,
                members,
            } => self.eval_class(env, name.clone(), parent, members, false),
            Expr::SuperCall(args) => {
                let sup = self
                    .super_stack
                    .last()
                    .copied()
                    .ok_or_else(|| err("unexpected super"))?;
                let this = self.env_get(env, "this").unwrap_or(Value::Undef);
                // Base frames see the derived newTarget (spec propagates it
                // down the whole super chain); read it from this frame.
                let nt = self.env_get(env, "new.target").unwrap_or(Value::Undef);
                let a = self.eval_args(env, args)?;
                self.pending_new_target = Some(nt);
                let r = self.call_value(sup, this, &a, Some("super"));
                self.pending_new_target.take();
                r
            }
            Expr::SuperProp(k) => {
                let sup = self
                    .super_stack
                    .last()
                    .copied()
                    .ok_or_else(|| err("unexpected super"))?;
                let key = match &**k {
                    Expr::Ident(n) => n.clone(),
                    _ => {
                        let kv = self.expr(env, k)?;
                        to_str(&self.heap, kv)
                    }
                };
                let proto = match get_prop(&self.heap, &self.protos, sup, "prototype")? {
                    Value::Obj(p) => Some(p),
                    _ => po(self.protos.object),
                };
                walk_props(&self.heap, &self.protos, proto, &key)
            }
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
                self.construct_value(f, &args)
            }
            // Constructor frames declare this binding (see call_value);
            // arrows inherit it via the env chain, like `this`.
            Expr::NewTarget => Ok(self.env_get(env, "new.target").unwrap_or(Value::Undef)),
        }
    }

    /// `new f(...args)`: unwrap bound functions (outermost first,
    /// prepending their bound args), then build `this` from the final
    /// target's `prototype` and call it. Bound arrows and non-functions
    /// throw like V8 ("not a constructor").
    fn construct_value(&mut self, f: Value, args: &[Value]) -> Result<Value, JsError> {
        let mut target = f;
        let mut full = args.to_vec();
        loop {
            let Value::Obj(id) = target else {
                return Err(err("not a constructor"));
            };
            match self.heap.obj(id) {
                Obj::Native { name, .. } if *name == "bound" => {
                    let t = get_prop(&self.heap, &self.protos, target, "__t")?;
                    let mut pre = match get_prop(&self.heap, &self.protos, target, "__a")? {
                        Value::Obj(aid) => arr_items(self, aid),
                        _ => Vec::new(),
                    };
                    pre.append(&mut full);
                    full = pre;
                    target = t;
                }
                Obj::Func { def, .. } => {
                    if def.is_arrow {
                        return Err(err("arrow is not a constructor"));
                    }
                    if def.is_gen {
                        return Err(err("generator is not a constructor"));
                    }
                    break;
                }
                // `new Symbol()` throws like V8 (bare calls never reach
                // here; bound-Symbol unwraps to this arm too).
                Obj::Native { name, .. } if *name == "Symbol" => {
                    return Err(err("Symbol is not a constructor"));
                }
                Obj::Native { .. } => break, // natives take `this` as given
                _ => return Err(err("not a constructor")),
            }
        }
        // proto = target.prototype when it's an object (JS); natives may
        // ignore `this` and return their own object anyway.
        let proto = match get_prop(&self.heap, &self.protos, target, "prototype")? {
            Value::Obj(p) => Some(p),
            _ => po(self.protos.object),
        };
        let obj = self.heap.alloc_obj(Obj::Ordinary {
            pairs: vec![],
            proto,
        })?;
        // newTarget is the pre-unwrap `f` (`new C` sees C, `new` on a
        // bound fn sees the bound fn). Cleared after: natives never take
        // the handoff, and no stale value may leak into a later call.
        self.pending_new_target = Some(f);
        let r = self.call_value(target, Value::Obj(obj), &full, None);
        self.pending_new_target.take();
        let r = r?;
        Ok(match r {
            Value::Obj(_) => r,
            _ => Value::Obj(obj),
        })
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
            "void" => {
                self.expr(env, e)?;
                Ok(Value::Undef)
            }
            // Eager generators (no coroutines): the body runs whole at first
            // next(), so `yield v` evaluates v and reads undefined.
            "yield" => {
                self.expr(env, e)?;
                Ok(Value::Undef)
            }
            "delete" => self.delete_op(env, e),
            "++" | "--" => self.bump(env, e, if op == "++" { 1.0 } else { -1.0 }, false),
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
                            Obj::Promise { st: PromiseState::Fulfilled(u), .. } => Ok(*u),
                            // the reason value itself is thrown, so a
                            // try/catch around the await sees it verbatim
                            Obj::Promise { st: PromiseState::Rejected(r), .. } => Err(JsError::Throw(*r)),
                            Obj::Promise { st: PromiseState::Pending { .. }, .. } => {
                                Err(err("await on pending promise (vigia settles fetch/timer \
                                 eagerly; pending awaits unsupported)"))
                            }
                            _ => Ok(v),
                        }
                    }
                }
            }
            _ => {
                let v = self.expr(env, e)?;
                // BigInt unary (spec): `-` negates, `~` is -x-1 exactly,
                // `+` throws (no implicit BigInt -> Number). Anything else
                // (`!`, …) uses the generic path below (truthy).
                if let Some((neg, mag)) = bi_val(&self.heap, v) {
                    match op {
                        "-" => return bi_alloc(self, !neg && !bi_is_zero(&mag), mag),
                        "+" => return Err(err("Cannot convert a BigInt value to a number")),
                        "~" => {
                            return if neg {
                                let mut m = mag;
                                bi_dec(&mut m);
                                bi_alloc(self, false, m)
                            } else {
                                let mut m = mag;
                                bi_inc(&mut m);
                                bi_alloc(self, true, m)
                            };
                        }
                        _ => {}
                    }
                }
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

    /// `delete ref`: remove an own property, true when gone-or-absent.
    /// Bindings can't delete (false); array slots blank to Undef keeping
    /// length (no holes in this engine); DOM nodes drop the attribute.
    fn delete_op(&mut self, env: u32, e: &Expr) -> Result<Value, JsError> {
        match e {
            Expr::Ident(_) => Ok(Value::Bool(false)),
            Expr::Member(o, k) => {
                let t = self.expr(env, o)?;
                self.delete_key(t, k, None)
            }
            Expr::Index(o, ix) => {
                let t = self.expr(env, o)?;
                let kv = self.expr(env, ix)?;
                let ks = to_str(&self.heap, kv);
                self.delete_key(t, &ks, Some(kv))
            }
            _ => {
                self.expr(env, e)?;
                Ok(Value::Bool(true))
            }
        }
    }

    fn delete_key(&mut self, t: Value, key: &str, kval: Option<Value>) -> Result<Value, JsError> {
        match t {
            // `delete window.x` drops the live global (and any snapshot
            // leftover from the set_dom seeding).
            Value::Obj(id) if Some(id) == self.wind => {
                self.envs[0].vars.remove(key);
                if let Obj::Ordinary { pairs, .. } = self.heap.obj_mut(id) {
                    pairs.retain(|(k, _)| k != key);
                }
                Ok(Value::Bool(true))
            }
            Value::Obj(id) if matches!(self.heap.obj(id), Obj::Proxy { .. }) => {
                self.proxy_delete(id, key, kval)
            }
            Value::Obj(id) => match self.heap.obj(id) {
                Obj::Ordinary { .. } | Obj::Func { .. } | Obj::Native { .. } => {
                    if let Obj::Ordinary { pairs, .. }
                    | Obj::Func { pairs, .. }
                    | Obj::Native { pairs, .. } = self.heap.obj_mut(id)
                    {
                        pairs.retain(|(k, _)| k != key);
                    }
                    Ok(Value::Bool(true))
                }
                Obj::Promise { .. } => {
                    if let Obj::Promise { pairs, .. } = self.heap.obj_mut(id) {
                        pairs.retain(|(k, _)| k != key);
                    }
                    Ok(Value::Bool(true))
                }
                Obj::Arr { .. } => {
                    // Canonical index blanks the slot, length kept.
                    // Named keys drop from expando pairs instead.
                    if let Some(Value::Num(n)) = kval {
                        if n >= 0.0 && n.fract() == 0.0 {
                            if let Obj::Arr { items, .. } = self.heap.obj_mut(id) {
                                if let Some(slot) = items.get_mut(n as usize) {
                                    *slot = Value::Undef;
                                }
                            }
                            return Ok(Value::Bool(true));
                        }
                    }
                    if key.parse::<usize>().is_ok() {
                        let n: usize = key.parse().unwrap_or(usize::MAX);
                        if let Obj::Arr { items, .. } = self.heap.obj_mut(id) {
                            if let Some(slot) = items.get_mut(n) {
                                *slot = Value::Undef;
                            }
                        }
                    } else if let Obj::Arr { pairs, .. } = self.heap.obj_mut(id) {
                        pairs.retain(|(k, _)| k != key);
                    }
                    Ok(Value::Bool(true))
                }
                Obj::Dom { node: n, .. } => {
                    let n = *n;
                    // Attribute-mapped props drop the attribute; expando
                    // keys were never stored, so nothing to do.
                    let attr = match key {
                        "className" => "class",
                        k => k,
                    };
                    self.dom_remove_attr(n, attr)?;
                    Ok(Value::Bool(true))
                }
                // Typed-array indices are non-configurable (false);
                // expandos delete like ordinary props.
                Obj::Bytes { bytes, .. } => {
                    let locked = key
                        .parse::<usize>()
                        .map(|i| i < bytes.len())
                        .unwrap_or(false);
                    if locked {
                        return Ok(Value::Bool(false));
                    }
                    if let Obj::Bytes { pairs, .. } = self.heap.obj_mut(id) {
                        pairs.retain(|(k, _)| k != key);
                    }
                    Ok(Value::Bool(true))
                }
                Obj::Typed { elems, .. } => {
                    let locked = key
                        .parse::<usize>()
                        .map(|i| i < elems.len())
                        .unwrap_or(false);
                    if locked {
                        return Ok(Value::Bool(false));
                    }
                    if let Obj::Typed { pairs, .. } = self.heap.obj_mut(id) {
                        pairs.retain(|(k, _)| k != key);
                    }
                    Ok(Value::Bool(true))
                }
                // Big64 indices are non-configurable (false) like the other
                // views; expandos delete like ordinary props.
                Obj::Big64 { elems, .. } => {
                    let locked = key
                        .parse::<usize>()
                        .map(|i| i < elems.len())
                        .unwrap_or(false);
                    if locked {
                        return Ok(Value::Bool(false));
                    }
                    if let Obj::Big64 { pairs, .. } = self.heap.obj_mut(id) {
                        pairs.retain(|(k, _)| k != key);
                    }
                    Ok(Value::Bool(true))
                }
                Obj::BufView { len, kind, .. } => {
                    let n = view_count(*kind, *len);
                    let locked = key.parse::<usize>().map(|i| i < n).unwrap_or(false);
                    if locked {
                        return Ok(Value::Bool(false));
                    }
                    if let Obj::BufView { pairs, .. } = self.heap.obj_mut(id) {
                        pairs.retain(|(k, _)| k != key);
                    }
                    Ok(Value::Bool(true))
                }
                _ => Ok(Value::Bool(true)),
            },
            Value::Str(_) | Value::Num(_) | Value::Bool(_) => Ok(Value::Bool(true)),
            Value::Undef | Value::Null => Err(err(format!(
                "cannot delete '{key}' of {}",
                if matches!(t, Value::Null) {
                    "null"
                } else {
                    "undefined"
                }
            ))),
        }
    }

    /// ++/-- on a resolved reference; `old` picks postfix semantics.
    fn bump(&mut self, env: u32, e: &Expr, delta: f64, old: bool) -> Result<Value, JsError> {
        let cur = self.get_ref(env, e)?;
        // ++/-- on a BigInt stays a BigInt (spec); the array store below
        // wraps it like any other BigInt write.
        if let Some((neg, mag)) = bi_val(&self.heap, cur) {
            let (nneg, nmag) = bi_step(neg, mag, delta > 0.0);
            let next = bi_alloc(self, nneg, nmag)?;
            self.set_ref(env, e, next)?;
            return Ok(if old { cur } else { next });
        }
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
            "," => {
                self.expr(env, l)?;
                self.expr(env, r)
            }
            _ => {
                let lv = self.expr(env, l)?;
                let rv = self.expr(env, r)?;
                if *op == *"instanceof"
                    && !matches!(rv, Value::Obj(_))
                    && std::env::var_os("VIGIA_JSENVDUMP").is_some()
                {
                    self.dump_envs(env);
                    eprintln!(
                        "js? instanceof rhs from {:.250} (lhs {:.120})",
                        format!("{r:?}").chars().take(250).collect::<String>(),
                        format!("{l:?}").chars().take(120).collect::<String>()
                    );
                }
                self.apply_bin(op, lv, rv)
            }
        }
    }

    fn apply_bin(&mut self, op: &str, l: Value, r: Value) -> Result<Value, JsError> {
        // BigInt-involved operators dispatch separately (spec): mixed
        // arithmetic/bitwise/shifts throw, `==`/relational compare
        // numerically, `+` never coerces strings.
        if is_big(&self.heap, l) || is_big(&self.heap, r) {
            if op == "in" && is_big(&self.heap, r) {
                return Err(err("cannot use 'in' on a BigInt"));
            }
            if op == "instanceof" {
                return Ok(Value::Bool(false));
            }
            if op != "in" {
                return bin_big(self, op, l, r);
            }
        }
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
            "**" => Value::Num(to_num(h, l).powf(to_num(h, r))),
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
                let key = to_str(&*h, l);
                match r {
                    Value::Obj(id)
                        if matches!(h.obj(id), Obj::Proxy { .. }) =>
                    {
                        Value::Bool(self.proxy_has(id, &key)?)
                    }
                    // `in window` sees live globals too (field borrows:
                    // envs/protos are disjoint from the heap borrow h).
                    Value::Obj(id) if Some(id) == self.wind => Value::Bool(
                        self.envs[0].vars.get(&key).is_some()
                            || has_prop(h, &self.protos, r, &key),
                    ),
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
                    _ => {
                        return Err(self.err_chain(format!(
                            "instanceof: {} is not a function",
                            self.inspect(r).chars().take(60).collect::<String>()
                        )));
                    }
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
        // V8 order: the LHS reference (base/key side effects) evaluates
        // before the RHS; for compound ops the current value reads next.
        enum Tgt {
            Ident(String),
            Mem(Value, String),
            Idx(Value, Value),
        }
        let tgt = match l {
            Expr::Ident(n) => Tgt::Ident(n.clone()),
            Expr::Member(o, k) => Tgt::Mem(self.expr(env, o)?, k.clone()),
            Expr::Index(o, ix) => {
                let t = self.expr(env, o)?;
                let k = self.expr(env, ix)?;
                Tgt::Idx(t, k)
            }
            _ => return Err(err("bad assignment target")),
        };
        let rv = self.expr(env, r)?;
        let v = if op == "=" {
            rv
        } else {
            let cur = match &tgt {
                Tgt::Ident(n) => self.env_get(env, n).ok_or_else(|| self.undefined_err(n))?,
                Tgt::Mem(t, k) => self.recv_get(*t, k)?,
                Tgt::Idx(t, k) => self.recv_get_idx(*t, *k)?,
            };
            self.apply_bin(op.trim_end_matches('='), cur, rv)?
        };
        match tgt {
            Tgt::Ident(n) => {
                if !self.env_set(env, &n, v) {
                    self.env_declare(0, &n, v); // sloppy mode: implicit global
                }
            }
            Tgt::Mem(t, k) => self.recv_set(t, &k, v)?,
            Tgt::Idx(t, k) => self.recv_set_idx(t, k, v)?,
        }
        Ok(v)
    }

    fn get_ref(&mut self, env: u32, e: &Expr) -> Result<Value, JsError> {
        match e {
            Expr::Ident(n) => self.env_get(env, n).ok_or_else(|| self.undefined_err(n)),
            Expr::Member(o, k) => {
                let v = self.expr(env, o)?;
                self.recv_get(v, k)
            }
            Expr::Index(o, ix) => {
                let v = self.expr(env, o)?;
                let k = self.expr(env, ix)?;
                self.recv_get_idx(v, k)
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
                self.recv_set(t, k, v)
            }
            Expr::Index(o, ix) => {
                let t = self.expr(env, o)?;
                let k = self.expr(env, ix)?;
                self.recv_set_idx(t, k, v)
            }
            _ => Err(err("bad assignment target")),
        }
    }

    /// Pattern binding for `var [a,b] = e` / `var {x} = e`, for loop
    /// targets, and plain params. Sequential: later defaults see earlier
    /// names. `assign` selects assignment semantics (scope-chain set,
    /// sloppy-global fallback) over declaration - used by plain
    /// destructuring assignment (`[a] = e`) and undeclared for-targets.
    /// Declare `n = v`, or assign through the scope chain (sloppy
    /// global fallback) when `assign` is set.
    fn bind_name(&mut self, env: u32, benv: u32, n: &str, v: Value, assign: bool) {
        if assign {
            if !self.env_set(env, n, v) {
                self.env_declare(0, n, v);
            }
        } else {
            self.env_declare(benv, n, v);
        }
    }

    /// Pattern binding with separate eval env (`env`: defaults evaluate
    /// here, scope chain starts here) and bind env (`benv`: declarations
    /// land here - function scope for `var`, current env otherwise).
    fn destructure(
        &mut self,
        env: u32,
        benv: u32,
        pat: &Pat,
        v: Value,
        assign: bool,
    ) -> Result<(), JsError> {
        match pat {
            Pat::Ident(n) => {
                self.bind_name(env, benv, n, v, assign);
                Ok(())
            }
            Pat::Arr(els, rest) => {
                let items: Vec<Value> = match v {
                    Value::Obj(id) => match self.heap.obj(id) {
                        Obj::Arr { items, .. } => items.clone(),
                        _ => return Err(err("destructuring a non-iterable")),
                    },
                    Value::Str(id) => {
                        let s = self.heap.get_str(id).to_string();
                        let mut out = Vec::new();
                        for c in s.chars() {
                            out.push(Value::Str(self.heap.alloc_str(c.to_string())?));
                        }
                        out
                    }
                    _ => return Err(err("destructuring a non-iterable")),
                };
                for (i, el) in els.iter().enumerate() {
                    let Some((p, d)) = el else { continue }; // hole
                    let mut item = items.get(i).copied().unwrap_or(Value::Undef);
                    if matches!(item, Value::Undef) {
                        if let Some(d) = d {
                            item = self.expr(env, d)?;
                        }
                    }
                    self.destructure(env, benv, p, item, assign)?;
                }
                if let Some(r) = rest {
                    let extra = items.get(els.len()..).unwrap_or(&[]).to_vec();
                    let arr = self.arr_obj(extra)?;
                    self.bind_name(env, benv, r, Value::Obj(arr), assign);
                }
                Ok(())
            }
            Pat::Obj(fields, rest) => {
                let mut taken = Vec::with_capacity(fields.len());
                for f in fields {
                    // Computed keys evaluate then coerce like index access.
                    let key = match &f.key {
                        ObjKey::Lit(s) => s.clone(),
                        ObjKey::Computed(e) => {
                            let kv = self.expr(env, e)?;
                            to_str(&self.heap, kv)
                        }
                    };
                    let fv = match self.as_node(v) {
                        Some(n) => self.dom_get(n, &key)?,
                        None => get_prop(&self.heap, &self.protos, v, &key)?,
                    };
                    taken.push(key);
                    let mut item = fv;
                    if matches!(item, Value::Undef) {
                        if let Some(d) = &f.default {
                            item = self.expr(env, d)?;
                        }
                    }
                    self.destructure(env, benv, &f.pat, item, assign)?;
                }
                if let Some(r) = rest {
                    // Own props minus the consumed keys.
                    let mut pairs = match v {
                        Value::Obj(id) => match self.heap.obj(id) {
                            Obj::Arr { items, .. } => items
                                .clone()
                                .into_iter()
                                .enumerate()
                                .map(|(i, x)| (i.to_string(), x))
                                .collect(),
                            Obj::Ordinary { pairs, .. }
                            | Obj::Func { pairs, .. }
                            | Obj::Native { pairs, .. } => pairs.clone(),
                            _ => vec![],
                        },
                        _ => vec![],
                    };
                    pairs.retain(|(k, _)| !taken.contains(k));
                    let obj = self.obj_pairs(pairs)?;
                    self.bind_name(env, benv, r, Value::Obj(obj), assign);
                }
                Ok(())
            }
        }
    }

    /// Tagged template call: build the strings array (cooked items plus
    /// a `raw` array prop) and call the tag with (strings, ...values).
    /// `this` is always undefined per spec, even for `obj.tag`x``.
    /// Freeze is skipped: Object.freeze is a no-op engine-wide, so the
    /// site stays writable like every other object here.
    fn tagged_tpl(
        &mut self,
        env: u32,
        tag: &Expr,
        parts: &[(Option<String>, String, Expr)],
        cooked_tail: &Option<String>,
        raw_tail: &str,
    ) -> Result<Value, JsError> {
        let f = self.expr(env, tag)?;
        let mut vals = Vec::with_capacity(parts.len());
        for (_, _, e) in parts {
            vals.push(self.expr(env, e)?);
        }
        let mut items = Vec::with_capacity(parts.len() + 1);
        let mut raws = Vec::with_capacity(parts.len() + 1);
        for (cooked, raw, _) in parts {
            items.push(match cooked {
                Some(c) => Value::Str(self.heap.intern_str(c)?),
                None => Value::Undef,
            });
            raws.push(Value::Str(self.heap.intern_str(raw)?));
        }
        items.push(match cooked_tail {
            Some(c) => Value::Str(self.heap.intern_str(c)?),
            None => Value::Undef,
        });
        raws.push(Value::Str(self.heap.intern_str(raw_tail)?));
        let site = self.arr_obj(items)?;
        let raw_arr = self.arr_obj(raws)?;
        set_prop(&mut self.heap, Value::Obj(site), "raw", Value::Obj(raw_arr))?;
        let texpr: &Expr = tag;
        let hint = match texpr {
            Expr::Ident(n) | Expr::Member(_, n) => Some(n.as_str()),
            _ => None,
        };
        let mut args = Vec::with_capacity(vals.len() + 1);
        args.push(Value::Obj(site));
        args.extend(vals);
        self.call_value(f, Value::Undef, &args, hint)
    }

    pub(crate) fn eval_args(&mut self, env: u32, es: &[Expr]) -> Result<Vec<Value>, JsError> {
        let mut v = Vec::with_capacity(es.len());
        for e in es {
            if let Expr::Spread(inner) = e {
                v.extend(self.spread_items(env, inner)?);
            } else {
                v.push(self.expr(env, e)?);
            }
        }
        Ok(v)
    }

    /// `...x` in calls and arrays: arrays, strings, typed views, Sets
    /// (Map spreads as [k,v] pairs). Custom iterables via
    /// Symbol.iterator are a documented gap.
    fn spread_items(&mut self, env: u32, e: &Expr) -> Result<Vec<Value>, JsError> {
        match self.expr(env, e)? {
            Value::Obj(id) => match self.heap.obj(id) {
                Obj::Arr { items, .. } => Ok(items.clone()),
                Obj::Bytes { bytes, .. } => {
                    Ok(bytes.iter().map(|b| Value::Num(*b as f64)).collect())
                }
                Obj::Typed { elems, .. } => Ok(elems.iter().map(|e| Value::Num(*e)).collect()),
                Obj::BufView { buf, off, len, kind, .. } => {
                    let (buf, off, len, kind) = (*buf, *off, *len, *kind);
                    let n = view_count(kind, len);
                    let bpe = t_bpe(kind);
                    let mut out = Vec::with_capacity(n);
                    for i in 0..n {
                        let at = off + i * bpe;
                        match kind {
                            TypedKind::I64 => {
                                let b = view_read_u64(&self.heap, buf, at).unwrap_or(0);
                                let (neg, mag) = bi_from_i64(b as i64);
                                out.push(bi_alloc(self, neg, mag)?);
                            }
                            TypedKind::U64 => {
                                let b = view_read_u64(&self.heap, buf, at).unwrap_or(0);
                                let (neg, mag) = bi_from_u64(b);
                                out.push(bi_alloc(self, neg, mag)?);
                            }
                            kk => {
                                out.push(Value::Num(
                                    view_read_num(&self.heap, buf, at, kk).unwrap_or(0.0),
                                ));
                            }
                        }
                    }
                    Ok(out)
                }
                Obj::Big64 { signed, elems, .. } => {
                    let signed = *signed;
                    let mut out = Vec::with_capacity(elems.len());
                    for bits in elems.clone() {
                        let (neg, mag) = if signed {
                            bi_from_i64(bits as i64)
                        } else {
                            bi_from_u64(bits)
                        };
                        out.push(bi_alloc(self, neg, mag)?);
                    }
                    Ok(out)
                }
                Obj::Set { items, .. } => Ok(items.clone()),
                Obj::Map { entries, .. } => {
                    let mut out = Vec::with_capacity(entries.len());
                    for (k, v) in entries.clone() {
                        out.push(Value::Obj(self.arr_obj(vec![k, v])?));
                    }
                    Ok(out)
                }
                _ => Err(err("spread of a non-iterable")),
            },
            Value::Str(id) => {
                let s = self.heap.get_str(id).to_string();
                let mut out = Vec::with_capacity(s.len());
                for c in s.chars() {
                    out.push(Value::Str(self.heap.alloc_str(c.to_string())?));
                }
                Ok(out)
            }
            _ => Err(err("spread of a non-iterable")),
        }
    }

    /// Merge one `get`/`set` side into the pairs: an existing Accessor
    /// under the same key gains the side, anything else is replaced.
    fn obj_accessor(
        &mut self,
        env: u32,
        pairs: &mut Vec<(String, Value)>,
        key: &str,
        get: &Option<std::rc::Rc<FnDef>>,
        set: &Option<std::rc::Rc<FnDef>>,
    ) -> Result<(), JsError> {
        let g = match get {
            Some(d) => Some(self.func_obj(d.clone(), env)?),
            None => None,
        };
        let s = match set {
            Some(d) => Some(self.func_obj(d.clone(), env)?),
            None => None,
        };
        if let Some((_, v)) = pairs.iter_mut().find(|(k, _)| k == key) {
            if let Value::Obj(id) = *v {
                if let Obj::Accessor {
                    get: og, set: os, ..
                } = self.heap.obj_mut(id)
                {
                    if g.is_some() {
                        *og = g;
                    }
                    if s.is_some() {
                        *os = s;
                    }
                    return Ok(());
                }
            }
            let proto = po(self.protos.object);
            *v = Value::Obj(self.heap.alloc_obj(Obj::Accessor {
                get: g,
                set: s,
                proto,
            })?);
            return Ok(());
        }
        let proto = po(self.protos.object);
        pairs.push((
            key.to_string(),
            Value::Obj(self.heap.alloc_obj(Obj::Accessor {
                get: g,
                set: s,
                proto,
            })?),
        ));
        Ok(())
    }

    /// `{...x}` entries: own string-keyed props; null/undefined/numbers /
    /// booleans contribute nothing; strings and arrays spread by index.
    fn spread_pairs(&mut self, env: u32, e: &Expr) -> Result<Vec<(String, Value)>, JsError> {
        match self.expr(env, e)? {
            Value::Undef | Value::Null | Value::Num(_) | Value::Bool(_) => Ok(vec![]),
            Value::Str(id) => {
                let s = self.heap.get_str(id).to_string();
                let mut out = Vec::with_capacity(s.len());
                for (i, c) in s.chars().enumerate() {
                    out.push((
                        i.to_string(),
                        Value::Str(self.heap.alloc_str(c.to_string())?),
                    ));
                }
                Ok(out)
            }
            // ownKeys trap is a documented gap: proxies spread the target.
            Value::Obj(id) => {
                let rid = proxy_resolve(&self.heap, id);
                match self.heap.obj(rid) {
                Obj::Arr { items, pairs, .. } => {
                    let mut out: Vec<(String, Value)> = items
                        .clone()
                        .into_iter()
                        .enumerate()
                        .map(|(i, v)| (i.to_string(), v))
                        .collect();
                    out.extend(pairs.clone());
                    Ok(out)
                }
                Obj::Bytes { bytes, pairs, .. } => {
                    let mut out: Vec<(String, Value)> = bytes
                        .iter()
                        .enumerate()
                        .map(|(i, b)| (i.to_string(), Value::Num(*b as f64)))
                        .collect();
                    out.extend(pairs.clone());
                    Ok(out)
                }
                Obj::Typed { elems, pairs, .. } => {
                    let mut out: Vec<(String, Value)> = elems
                        .iter()
                        .enumerate()
                        .map(|(i, e)| (i.to_string(), Value::Num(*e)))
                        .collect();
                    out.extend(pairs.clone());
                    Ok(out)
                }
                Obj::Big64 {
                    signed,
                    elems,
                    pairs,
                    ..
                } => {
                    let (signed, elems, pairs) = (*signed, elems.clone(), pairs.clone());
                    let mut out = Vec::with_capacity(elems.len() + pairs.len());
                    for (i, bits) in elems.iter().enumerate() {
                        let (neg, mag) = if signed {
                            bi_from_i64(*bits as i64)
                        } else {
                            bi_from_u64(*bits)
                        };
                        out.push((i.to_string(), bi_alloc(self, neg, mag)?));
                    }
                    out.extend(pairs);
                    Ok(out)
                }
                Obj::BufView { buf, off, len, kind, pairs, .. } => {
                    let (buf, off, len, kind, pairs) = (*buf, *off, *len, *kind, pairs.clone());
                    let n = view_count(kind, len);
                    let bpe = t_bpe(kind);
                    let mut out = Vec::with_capacity(n + pairs.len());
                    for i in 0..n {
                        let at = off + i * bpe;
                        match kind {
                            TypedKind::I64 => {
                                let b = view_read_u64(&self.heap, buf, at).unwrap_or(0);
                                let (neg, mag) = bi_from_i64(b as i64);
                                out.push((i.to_string(), bi_alloc(self, neg, mag)?));
                            }
                            TypedKind::U64 => {
                                let b = view_read_u64(&self.heap, buf, at).unwrap_or(0);
                                let (neg, mag) = bi_from_u64(b);
                                out.push((i.to_string(), bi_alloc(self, neg, mag)?));
                            }
                            kk => {
                                let e = view_read_num(&self.heap, buf, at, kk).unwrap_or(0.0);
                                out.push((i.to_string(), Value::Num(e)));
                            }
                        }
                    }
                    out.extend(pairs);
                    Ok(out)
                }
                Obj::Ordinary { pairs, .. }
                | Obj::Func { pairs, .. }
                | Obj::Native { pairs, .. } => Ok(pairs.clone()),
                Obj::Promise { pairs, .. } => Ok(pairs.clone()),
                Obj::BigInt { .. }
                | Obj::RegExp { .. }
                | Obj::Dom { .. }
                | Obj::Style { .. }
                | Obj::Accessor { .. }
                | Obj::Symbol { .. }
                | Obj::Map { .. }
                | Obj::Set { .. }
                | Obj::WeakMap { .. }
                | Obj::Proxy { .. }
                | Obj::Buf { .. }
                | Obj::DView { .. }
                | Obj::Freed => Ok(vec![]),
                }
            }
        }
    }

    /// Trace aid: one-line value description (setProto logging).
    fn describe(&self, v: Value) -> String {
        match v {
            Value::Obj(id) => match self.heap.obj(id) {
                Obj::Func { def, .. } => {
                    format!("fn:{}#{}", def.name.clone().unwrap_or_else(|| "?".into()), id)
                }
                Obj::Native { name, .. } => format!("nat:{name}#{id}"),
                Obj::Ordinary { .. } => format!("ordinary#{id}"),
                Obj::Arr { .. } => format!("array#{id}"),
                _ => format!("obj#{id}"),
            },
            _ => self.inspect(v),
        }
    }

    /// Trace aid: proto slot description.
    fn describe_any_proto(&self, p: Option<u32>) -> String {
        match p {
            Some(id) => self.describe(Value::Obj(id)),
            None => "null".into(),
        }
    }

    /// Trace aid: dump innermost lexical frames (locals) so anonymous
    /// bundle functions can be told apart. Zero cost unless VIGIA_JSENVDUMP.
    fn dump_envs(&self, env: u32) {
        if std::env::var_os("VIGIA_JSENVDUMP").is_none() {
            return;
        }
        // JS stack signatures: name(params)@defenv for each live frame.
        let mut sigs = Vec::new();
        for &id in &self.js_stack {
            match self.heap.obj(id) {
                Obj::Func { def, env: fenv, .. } => {
                    let ps: Vec<String> = def
                        .params
                        .iter()
                        .map(|(p, d)| {
                            let s = match p {
                                Pat::Ident(n) => n.clone(),
                                _ => "?pat".into(),
                            };
                            if d.is_some() {
                                format!("{s}=d")
                            } else {
                                s
                            }
                        })
                        .collect();
                    sigs.push(format!(
                        "{}({})@{}",
                        def.name.clone().unwrap_or_else(|| "?".into()),
                        ps.join(","),
                        fenv
                    ));
                }
                Obj::Native { name, .. } => sigs.push(format!("[{name}]")),
                _ => sigs.push("[?]".into()),
            }
        }
        eprintln!("js? stack: {}", sigs.join(" > "));
        // Innermost body: shows the failing statement + its guard.
        if let Some(&fid) = self.js_stack.last() {
            if let Obj::Func { def, .. } = self.heap.obj(fid) {
                let bdbg = format!("{:?}", def.body);
                eprintln!(
                    "js? body {:.6000}",
                    bdbg.chars().take(6000).collect::<String>()
                );
            }
        }
        let mut e = Some(env);
        for _ in 0..3 {
            let Some(id) = e else { break };
            let Some(ev) = self.envs.get(id as usize) else {
                break;
            };
            let mut names: Vec<String> = ev
                .vars
                .iter()
                .take(60)
                .map(|(k, v)| {
                    format!(
                        "{k}={}",
                        self.inspect(*v).chars().take(60).collect::<String>()
                    )
                })
                .collect();
            names.sort();
            eprintln!("js? env{id}: {}", names.join(" "));
            e = ev.parent;
        }
    }

    fn call(&mut self, env: u32, callee: &Expr, arg_es: &[Expr]) -> Result<Value, JsError> {
        let (f, this, hint) = match callee {
            Expr::Member(o, name) => {
                let recv = self.expr(env, o)?;
                if matches!(recv, Value::Null | Value::Undef) {
                    self.dump_envs(env);
                    if std::env::var_os("VIGIA_JSENVDUMP").is_some() {
                        let dbg = format!("{o:?}");
                        eprintln!(
                            "js? .{name} of nullish from {:.300}",
                            dbg.chars().take(300).collect::<String>()
                        );
                    }
                }
                // DOM node methods dispatch on the node, not the property map
                if let Some(n) = self.as_node(recv) {
                    return self.call_dom(n, name, env, arg_es);
                }
                // Style declaration methods (setProperty & co live on no
                // property map either): resolve through the live style.
                if let Some(n) = self.as_style(recv) {
                    let args = self.eval_args(env, arg_es)?;
                    let f = self.style_get(n, name)?;
                    return self
                        .call_value(f, recv, &args, Some(name.as_str()))
                        .map_err(|e| self.chain_msg(e));
                }
                // Window event methods (addEventListener & co live on no
                // node): route to the sentinel registry, else fall through
                // to ordinary property lookup below.
                if let Value::Obj(id) = recv {
                    if Some(id) == self.wind {
                        let args = self.eval_args(env, arg_es)?;
                        if let Some(v) = self.event_method(WIN_EVENTS, name, &args)? {
                            return Ok(v);
                        }
                    }
                }
                // proto chains resolve string/array/etc methods to Natives;
                // `this` = the receiver. Getters apply like a plain read.
                // `window` reads the global scope live (env 0 first, own
                // snapshot pairs after) - mirroring recv_get, which reads
                // already honor; calls used to skip env 0 and miss globals.
                (
                    {
                        let live = match recv {
                            Value::Obj(id) if Some(id) == self.wind => {
                                self.env_get(0, name)
                            }
                            _ => None,
                        };
                        let val = match live {
                            Some(v) => v,
                            None => get_prop(&self.heap, &self.protos, recv, name)
                                .map_err(|e| self.chain_msg(e))?,
                        };
                        self.invoke_getter(val, recv, name)?
                    },
                    recv,
                    Some(name.as_str()),
                )
            }
            Expr::Index(o, ix) => {
                let recv = self.expr(env, o)?;
                let k = self.expr(env, ix)?;
                if let (Value::Obj(id), Value::Str(s)) = (recv, k) {
                    if let Obj::Dom { node: n, .. } = self.heap.obj(id) {
                        let (n, m) = (*n, self.heap.get_str(s).to_string());
                        return self.call_dom(n, &m, env, arg_es);
                    }
                }
                (
                    {
                        // Same live-global rule as the member arm (and
                        // recv_get_idx): `window[k]()` finds page globals.
                        let key = to_str(&self.heap, k);
                        let live = match recv {
                            Value::Obj(id) if Some(id) == self.wind => {
                                self.env_get(0, &key)
                            }
                            _ => None,
                        };
                        let val = match live {
                            Some(v) => v,
                            None => get_index(&mut self.heap, &self.protos, recv, k)
                                .map_err(|e| self.chain_msg(e))?,
                        };
                        self.invoke_getter(val, recv, &key)?
                    },
                    recv,
                    None,
                )
            }
            Expr::Ident(n) => (self.expr(env, callee)?, Value::Undef, Some(n.as_str())),            Expr::SuperProp(k) => {
                let sup = self
                    .super_stack
                    .last()
                    .copied()
                    .ok_or_else(|| err("unexpected super"))?;
                let key = match &**k {
                    Expr::Ident(n) => n.clone(),
                    _ => {
                        let kv = self.expr(env, k)?;
                        to_str(&self.heap, kv)
                    }
                };
                let recv = self.env_get(env, "this").unwrap_or(Value::Undef);
                let proto = match get_prop(&self.heap, &self.protos, sup, "prototype")? {
                    Value::Obj(p) => Some(p),
                    _ => po(self.protos.object),
                };
                (
                    {
                        let val = walk_props(&self.heap, &self.protos, proto, &key)?;
                        self.invoke_getter(val, recv, &key)?
                    },
                    recv,
                    None,
                )
            }
            _ => (self.expr(env, callee)?, Value::Undef, None),
        };
        // Trace aid: what non-function value sits in callee position.
        if std::env::var_os("VIGIA_JSTRACE").is_some() && !matches!(f, Value::Obj(_)) {
            let dbg = format!("{callee:?}");
            eprintln!(
                "js? callee {:?} holds {} from {:.200} (this {})",
                hint.unwrap_or("?"),
                self.inspect(f),
                dbg.chars().take(200).collect::<String>(),
                self.inspect(this)
            );
            // Innermost function's body: shows the call site + guard.
            if let Some(&fid) = self.js_stack.last() {
                if let Obj::Func { def, .. } = self.heap.obj(fid) {
                    let bdbg = format!("{:?}", def.body);
                    eprintln!(
                        "js? body {:.1200}",
                        bdbg.chars().take(1200).collect::<String>()
                    );
                }
            }
            self.dump_envs(env);
        }
        if let Value::Obj(id) = f {
            if let Obj::Func { def, .. } = self.heap.obj(id) {
                if def.cls.is_some() {
                    return Err(err("class constructor must be invoked with new"));
                }
            }
        }
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
                    cur = self.recv_get(cur, name)?;
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
                    cur = self.recv_get_idx(recv, k)?;
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
                    if let Value::Obj(id) = cur {
                        if let Obj::Func { def, .. } = self.heap.obj(id) {
                            if def.cls.is_some() {
                                return Err(err("class constructor must be invoked with new"));
                            }
                        }
                    }
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
                return Err(self.err_chain(format!(
                    "{} is not a function",
                    hint.unwrap_or(type_str(&self.heap, f))
                )))
            }
        };
        let c = match self.heap.obj(id) {
            Obj::Func { def, env, .. } => C::Fn(def.clone(), *env),
            Obj::Native { f, .. } => C::Nat(*f),
            _ => {
                return Err(self.err_chain(format!(
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
        // Optional call trace for bundle debugging (VIGIA_JSTRACE=1):
        // callee name per entry, stderr. Zero cost when unset.
        let tracing = std::env::var_os("VIGIA_JSTRACE").is_some();
        if tracing {
            let name = match &c {
                C::Fn(def, _) => def.name.clone().unwrap_or_else(|| "?".into()),
                C::Nat(_) => "[native]".into(),
            };
            eprintln!("{:>width$}js> {name}", "", width = self.call_depth as usize);
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
                // Generator call: fresh generator object per call; the body
                // runs eagerly at first next(), never here.
                if def.is_gen {
                    let r = gen_obj(self, id, fenv, this, args);
                    self.call_vals.truncate(vbase);
                    self.call_depth -= 1;
                    return r;
                }
                let cenv = match self.new_env(fenv) {
                    Ok(cenv) => cenv,
                    Err(e) => {
                        self.call_vals.truncate(vbase);
                        self.call_depth -= 1;
                        return Err(e);
                    }
                };
                // Methods of a derived class carry `__super`. It is pushed
                // next to exec_block (below) so the `?`s above cannot
                // leak it; every exit below restores it.
                let sup = self.func_super(id);
                // Hoist `var`s (as undefined) and nested function
                // declarations before params: defaults may read them.
                // Truncated with the rest below (hoisted-list discipline).
                let hbase = self.hoisted.len();
                let saved_last = self.last;
                self.hoist_vars(&def.body, cenv)?;
                // `new.target` per frame: the construct handoff, else
                // undefined (plain calls shadow any outer value). Arrows
                // declare nothing and inherit lexically. Declared before
                // params so defaults (`(a = new.target)`) see it.
                if !def.is_arrow {
                    let nt = self.pending_new_target.take().unwrap_or(Value::Undef);
                    self.env_declare(cenv, "new.target", nt);
                }
                for (i, (p, d)) in def.params.iter().enumerate() {
                    let mut v = args.get(i).copied().unwrap_or(Value::Undef);
                    if matches!(v, Value::Undef) {
                        if let Some(d) = d {
                            v = self.expr(cenv, d)?;
                        }
                    }
                    match p {
                        Pat::Ident(n) => self.env_declare(cenv, n, v),
                        _ => self.destructure(cenv, cenv, p, v, false)?,
                    }
                }
                if let Some(r) = &def.rest {
                    let extra = args.get(def.params.len()..).unwrap_or(&[]).to_vec();
                    let arr = self.arr_obj(extra)?;
                    self.env_declare(cenv, r, Value::Obj(arr));
                }
                if let Some(n) = &def.name {
                    // Named functions self-recurse via their own name -
                    // unless a param (or rest) shadows it, which wins
                    // (V8 scoping; e.g. minified `function t(t,n)`).
                    let shadowed = def.rest.as_deref() == Some(n.as_str())
                        || def.params.iter().any(|(p, _)| match p {
                            Pat::Ident(pn) => pn == n,
                            _ => false,
                        });
                    if !shadowed {
                        self.env_declare(cenv, n, f);
                    }
                }
                // `arguments`: array-like snapshot of the actual args plus
                // `callee` (sloppy; no param aliasing in this engine).
                // Skipped when shadowed by a param or `var` (real scoping).
                // Arrows still get one (a fresh object, not the outer's).
                let shadowed = self.envs[cenv as usize].vars.contains_key("arguments");
                if !shadowed {
                    let argarr = self.arr_obj(args.to_vec())?;
                    if let Obj::Arr { pairs, .. } = self.heap.obj_mut(argarr) {
                        pairs.push(("callee".into(), f));
                    }
                    self.env_declare(cenv, "arguments", Value::Obj(argarr));
                }
                // Arrows capture `this` lexically from the defining env.
                // Sloppy calls coerce nullish receivers to the global
                // object (bound nulls included - documented deviation;
                // V8 keeps bound thisArgs raw).
                let this_val = if def.is_arrow {
                    self.env_get(fenv, "this").unwrap_or(Value::Undef)
                } else {
                    match this {
                        Value::Undef | Value::Null => self.sloppy_this(),
                        _ => this,
                    }
                };
                self.env_declare(cenv, "this", this_val);
                // `await` binds to the nearest enclosing fn, so the flag
                // is shadowed per call rather than accumulated. Same for
                // the Annex-B hoist scope below.
                let prev_async = self.fn_async;
                self.fn_async = def.is_async;
                let prev_fenv = self.func_env;
                self.func_env = cenv;
                let pushed_super = sup.is_some();
                if let Some(s) = sup {
                    self.super_stack.push(s);
                }
                // JS call chain for error context (ids; names resolve
                // lazily). Popped with the rest below - no `?` between.
                self.js_stack.push(id);
                let mut r = match self.exec_block(&def.body, cenv) {
                    Ok(Flow::Return(v)) => Ok(v),
                    Ok(_) => Ok(Value::Undef),
                    Err(e) => Err(e),
                };
                // Class instance fields install on `this` when the body
                // succeeded. Post-body order is a documented deviation
                // (spec runs them right after super()); crucially this
                // also runs for parent fields via super(), which goes
                // through call_value too. super_stack is still pushed.
                if r.is_ok() {
                    if let Some(cc) = def.cls.as_ref() {
                        for (nm, init) in &cc.fields {
                            let v = match init {
                                Some(e) => self.expr(cenv, e),
                                None => Ok(Value::Undef),
                            };
                            match v {
                                Ok(v) => {
                                    if let Err(e) = set_prop(&mut self.heap, this_val, nm, v) {
                                        r = Err(e);
                                        break;
                                    }
                                }
                                Err(e) => {
                                    r = Err(e);
                                    break;
                                }
                            }
                        }
                    }
                }
                if pushed_super {
                    self.super_stack.pop();
                }
                // Snapshot the chain while the innermost frame is still on
                // it (first/innermost Err wins; outer frames see None set).
                // Popped with the rest below - no `?` between. Thrown
                // Error objects also gain their `stack` here.
                if r.is_err() && self.throw_chain.is_none() {
                    let c = self.js_chain();
                    if !c.is_empty() {
                        self.throw_chain = Some(c);
                    }
                }
                if let Err(JsError::Throw(v)) = &r {
                    self.ensure_stack(*v);
                }
                self.js_stack.pop();
                self.fn_async = prev_async;
                self.func_env = prev_fenv;
                self.hoisted.truncate(hbase);
                // Function-body statements must not leak into the
                // top-level completion value (timer callbacks were
                // overwriting it mid-drain).
                self.last = saved_last;
                (def.is_async, r)
            }
            C::Nat(nf) => {
                // cur_native exposes the callee object to natives that
                // carry bound state in their own props ("__p", "__f", ...).
                // A construct handoff never belongs to a native frame, so
                // drop it: sync JS callbacks the native invokes (Promise
                // executors, Reflect.construct targets) start clean.
                self.pending_new_target.take();
                let prev = self.cur_native;
                self.cur_native = f;
                self.js_stack.push(id);
                let r = nf(self, this, args);
                if r.is_err() && self.throw_chain.is_none() {
                    let c = self.js_chain();
                    if !c.is_empty() {
                        self.throw_chain = Some(c);
                    }
                }
                if let Err(JsError::Throw(v)) = &r {
                    self.ensure_stack(*v);
                }
                self.js_stack.pop();
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
            // BigInts render with the `n` suffix (V8 console shape); 64-bit
            // views render element-wise since JSON cannot hold them.
            Value::Obj(id) => match self.heap.obj(id) {
                Obj::BigInt { neg, mag, .. } => format!("{}n", bi_fmt(*neg, mag, 10)),
                Obj::Big64 { signed, elems, .. } => {
                    let parts: Vec<String> = elems
                        .iter()
                        .map(|b| {
                            let (n, m) = if *signed {
                                bi_from_i64(*b as i64)
                            } else {
                                bi_from_u64(*b)
                            };
                            format!("{}n", bi_fmt(n, &m, 10))
                        })
                        .collect();
                    format!("[{}]", parts.join(", "))
                }
                Obj::BufView { buf, off, len, kind, .. }
                    if matches!(kind, TypedKind::I64 | TypedKind::U64) =>
                {
                    let n = view_count(*kind, *len);
                    let mut parts = Vec::with_capacity(n);
                    for i in 0..n {
                        let b = view_read_u64(&self.heap, *buf, off + i * 8).unwrap_or(0);
                        let (nn, m) = if *kind == TypedKind::I64 {
                            bi_from_i64(b as i64)
                        } else {
                            bi_from_u64(b)
                        };
                        parts.push(format!("{}n", bi_fmt(nn, &m, 10)));
                    }
                    format!("[{}]", parts.join(", "))
                }
                _ => val_to_json(&self.heap, v, 0)
                    .map(|j| j.to_string())
                    .unwrap_or_else(|_| "[object Object]".into()),
            },
            _ => to_str(&self.heap, v),
        }
    }

    /// Fresh Error object under Error.prototype carrying `msg`.
    pub(crate) fn error_obj(&mut self, msg: &str) -> Result<Value, JsError> {
        let proto = po(self.protos.error);
        let m = Value::Str(self.heap.alloc_str(msg.to_string())?);
        let o = Value::Obj(self.heap.alloc_obj(Obj::Ordinary {
            pairs: vec![("message".into(), m)],
            proto,
        })?);
        let s = Value::Str(self.heap.alloc_str(Self::stack_string("Error", msg, ""))?);
        set_prop(&mut self.heap, o, "stack", s)?;
        Ok(o)
    }

    /// Text of a thrown value for an error report: objects with a
    /// `message` prop (Error-shaped) render "Name: message".
    fn thrown_text(&self, v: Value) -> String {
        match self.error_parts(v) {
            Some((name, ms)) => {
                if ms.is_empty() {
                    name
                } else {
                    format!("{name}: {ms}")
                }
            }
            None => to_str(&self.heap, v),
        }
    }

    /// (name, message) of an Error-shaped object, if it has a message.
    fn error_parts(&self, v: Value) -> Option<(String, String)> {
        if let Value::Obj(_) = v {
            if let Ok(m) = get_prop(&self.heap, &self.protos, v, "message") {
                if !matches!(m, Value::Undef) {
                    let mut name = get_prop(&self.heap, &self.protos, v, "name")
                        .map(|n| to_str(&self.heap, n))
                        .unwrap_or_default();
                    if name.is_empty() {
                        name = "Error".into();
                    }
                    return Some((name, to_str(&self.heap, m)));
                }
            }
        }
        None
    }

    /// V8-shaped stack text ("Name: msg" + `at` frames, innermost first
    /// like V8). Empty chain gives the bare head line.
    fn stack_string(name: &str, msg: &str, chain: &str) -> String {
        let head = if msg.is_empty() {
            name.to_string()
        } else {
            format!("{name}: {msg}")
        };
        if chain.is_empty() {
            return head;
        }
        let mut s = head;
        let frames: Vec<&str> = chain.split(" > ").collect();
        for f in frames.into_iter().rev() {
            s.push_str("\n    at ");
            s.push_str(f);
        }
        s
    }

    /// Ensure a thrown Error-shaped object carries a framed `stack`.
    /// Objects constructed by Error()/error_obj carry a frameless
    /// default (so `.stack.split` never crashes); the first unwind
    /// upgrades exactly-that-default with frames. Anything else custom
    /// is never touched.
    fn ensure_stack(&mut self, v: Value) {
        let Value::Obj(id) = v else {
            return;
        };
        let Some((nm, ms)) = self.error_parts(v) else {
            return;
        };
        let chain = self.js_chain();
        if chain.is_empty() {
            return;
        }
        let current = match own_prop(&self.heap, id, "stack") {
            Some(Value::Str(sid)) => self.heap.get_str(sid).to_string(),
            _ => String::new(),
        };
        if !current.is_empty() && current != Self::stack_string(&nm, &ms, "") {
            return;
        }
        let text = Self::stack_string(&nm, &ms, &chain);
        if let Ok(sid) = self.heap.alloc_str(text) {
            let _ = set_prop(&mut self.heap, v, "stack", Value::Str(sid));
        }
    }

    /// Boundary render: a thrown value becomes its text (the heap id
    /// inside Throw isn't rooted once the error leaves eval); Msg and
    /// Fatal pass through unchanged. Handled throws append the snapshot
    /// chain ("TypeError: x (in a > b)") for bundle debugging.
    pub(crate) fn bound_err(&mut self, e: JsError) -> JsError {
        match e {
            JsError::Throw(v) => {
                let mut t = self.thrown_text(v);
                if let Some(c) = self.throw_chain.take() {
                    t.push_str(&format!(" (in {c})"));
                }
                err(t)
            }
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

/// console.error/warn/info/debug: same sink as log (no stderr split -
/// the harness reads `out` for diagnostics).
fn n_console_diag(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    n_console_log(it, Value::Undef, args)
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
            // JSON cannot represent BigInts, boxed or in 64-bit views.
            Obj::BigInt { .. } | Obj::Big64 { .. } => {
                return Err(err("Do not know how to serialize a BigInt"));
            }
            Obj::BufView { kind, .. }
                if matches!(kind, TypedKind::I64 | TypedKind::U64) =>
            {
                return Err(err("Do not know how to serialize a BigInt"));
            }
            Obj::Proxy { target, .. } => return val_to_json(h, Value::Obj(*target), depth),
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
            Obj::Func { .. } | Obj::Native { .. } | Obj::Dom { .. } | Obj::Promise { .. } | Obj::Freed => {
                Json::Null
            }
            Obj::RegExp { .. } => Json::Obj(vec![]),
            Obj::Accessor { .. } => Json::Obj(vec![]),
            Obj::Symbol { .. } => Json::Null,
            Obj::Map { .. } => Json::Obj(vec![]),
            Obj::Set { .. } => Json::Obj(vec![]),
            Obj::WeakMap { .. } => Json::Obj(vec![]),
            Obj::Bytes { bytes, .. } => Json::Obj(
                bytes
                    .iter()
                    .enumerate()
                    .map(|(i, b)| (i.to_string(), Json::Num(*b as f64)))
                    .collect(),
            ),
            Obj::Typed { elems, .. } => Json::Obj(
                elems
                    .iter()
                    .enumerate()
                    .map(|(i, e)| (i.to_string(), Json::Num(*e)))
                    .collect(),
            ),
            Obj::BufView { buf, off, len, kind, .. } => {
                let n = view_count(*kind, *len);
                let bpe = t_bpe(*kind);
                let mut out = Vec::with_capacity(n);
                for i in 0..n {
                    let e = view_read_num(h, *buf, off + i * bpe, *kind).unwrap_or(0.0);
                    out.push((i.to_string(), Json::Num(e)));
                }
                Json::Obj(out)
            },
            Obj::DView { .. } => Json::Obj(vec![]),
            Obj::Buf { .. } => Json::Obj(vec![]),
            Obj::Style { .. } => Json::Obj(vec![]),
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

pub(crate) fn arg(args: &[Value], i: usize) -> Value {
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
        Obj::Bytes { bytes, .. } => bytes.iter().map(|b| Value::Num(*b as f64)).collect(),
        Obj::Typed { elems, .. } => elems.iter().map(|e| Value::Num(*e)).collect(),
        Obj::BufView { buf, off, len, kind, .. } => match kind {
            TypedKind::I64 | TypedKind::U64 => Vec::new(),
            k => {
                let n = view_count(*k, *len);
                let bpe = t_bpe(*k);
                (0..n)
                    .map(|i| {
                        Value::Num(view_read_num(&it.heap, *buf, off + i * bpe, *k).unwrap_or(0.0))
                    })
                    .collect()
            }
        },
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
        // Big64 canonical indices read true (own_prop can't serve them:
        // boxing an element needs &mut, which it lacks).
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::Big64 { elems, .. } if key.parse::<usize>().is_ok_and(|i| i < elems.len()) => {
                true
            }
            Obj::BufView { len, kind, .. }
                if matches!(kind, TypedKind::I64 | TypedKind::U64)
                    && key.parse::<usize>().is_ok_and(|i| i < view_count(*kind, *len)) =>
            {
                true
            }
            _ => own_prop(&it.heap, id, &key).is_some(),
        },
        _ => false,
    };
    Ok(Value::Bool(hit))
}

/// Object.prototype.isPrototypeOf(v): `this` on v's proto chain (Chart.js
/// registry shape). Non-objects on either side read false, like V8.
fn n_is_proto(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let (Value::Obj(tid), Value::Obj(mut cur)) = (this, arg(args, 0)) else {
        return Ok(Value::Bool(false));
    };
    for _ in 0..64 {
        match proto_of(&it.heap, &it.protos, cur) {
            Some(p) if p == tid => return Ok(Value::Bool(true)),
            Some(p) => cur = p,
            None => return Ok(Value::Bool(false)),
        }
    }
    Ok(Value::Bool(false))
}

fn n_prop_is_enum(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let key = to_str(&it.heap, arg(args, 0));
    let hit = match this {
        Value::Obj(id) => own_prop(&it.heap, id, &key).is_some(),
        Value::Str(id) => key.parse::<usize>().is_ok_and(|i| i < it.heap.get_str(id).chars().count()),
        _ => false,
    };
    Ok(Value::Bool(hit))
}

fn n_value_of(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let _ = it;
    Ok(this)
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
            Obj::Dom { .. } => "[object Node]",
            Obj::Promise { .. } => "[object Promise]",
            Obj::RegExp { .. } => "[object RegExp]",
            Obj::Accessor { .. } => "[object Accessor]",
            Obj::Symbol { .. } => "[object Symbol]",
            Obj::Map { .. } => "[object Map]",
            Obj::Set { .. } => "[object Set]",
            Obj::WeakMap { .. } => "[object WeakMap]",
            Obj::Bytes { .. } => "[object Uint8Array]",
            Obj::Typed { kind, .. } => t_tag(*kind),
            Obj::BufView { kind, proto, .. } => {
                // Facades over the buffer read as ArrayBuffers.
                if *proto == po(it.protos.buffer) {
                    "[object ArrayBuffer]"
                } else {
                    t_tag(*kind)
                }
            }
            Obj::BigInt { .. } => "[object BigInt]",
            Obj::Big64 { signed, .. } => {
                if *signed {
                    "[object BigInt64Array]"
                } else {
                    "[object BigUint64Array]"
                }
            }
            Obj::DView { .. } => "[object DataView]",
            Obj::Buf { .. } => "[object ArrayBuffer]",
            Obj::Proxy { .. } => "[object Object]",
            Obj::Style { .. } => "[object CSSStyleDeclaration]",
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
/// Proxies enumerate the target (ownKeys trap is a documented gap).
/// Big64 indices box into fresh BigInts (the only arm needing &mut).
fn own_pairs(it: &mut Interp, v: Value) -> Vec<(String, Value)> {
    if let Value::Obj(id) = v {
        let rid = proxy_resolve(&it.heap, id);
        if matches!(it.heap.obj(rid), Obj::Big64 { .. }) {
            let (signed, elems, pairs) = match it.heap.obj(rid) {
                Obj::Big64 {
                    signed,
                    elems,
                    pairs,
                    ..
                } => (*signed, elems.clone(), pairs.clone()),
                _ => unreachable!(),
            };
            let mut out = Vec::with_capacity(elems.len() + pairs.len());
            for (i, bits) in elems.iter().enumerate() {
                let (neg, mag) = if signed {
                    bi_from_i64(*bits as i64)
                } else {
                    bi_from_u64(*bits)
                };
                let proto = po(it.protos.bigint);
                match it.heap.alloc_obj(Obj::BigInt { neg, mag, proto }) {
                    Ok(bid) => out.push((i.to_string(), Value::Obj(bid))),
                    Err(_) => break, // heap-cap edge: partial list
                }
            }
            out.extend(pairs);
            return out;
        }
        if let Obj::BufView { buf, off, len, kind, pairs, .. } = it.heap.obj(rid) {
            let (buf, off, len, kind, pairs) = (*buf, *off, *len, *kind, pairs.clone());
            let n = view_count(kind, len);
            let bpe = t_bpe(kind);
            let mut out = Vec::with_capacity(n + pairs.len());
            for i in 0..n {
                let at = off + i * bpe;
                match kind {
                    TypedKind::I64 | TypedKind::U64 => {
                        let b = view_read_u64(&it.heap, buf, at).unwrap_or(0);
                        let (neg, mag) = if kind == TypedKind::I64 {
                            bi_from_i64(b as i64)
                        } else {
                            bi_from_u64(b)
                        };
                        let proto = po(it.protos.bigint);
                        match it.heap.alloc_obj(Obj::BigInt { neg, mag, proto }) {
                            Ok(bid) => out.push((i.to_string(), Value::Obj(bid))),
                            Err(_) => break,
                        }
                    }
                    kk => {
                        let e = view_read_num(&it.heap, buf, at, kk).unwrap_or(0.0);
                        out.push((i.to_string(), Value::Num(e)));
                    }
                }
            }
            out.extend(pairs);
            return out;
        }
    }
    let h = &it.heap;
    match v {
        Value::Obj(id) => match h.obj(proxy_resolve(h, id)) {
            Obj::Ordinary { pairs, .. } | Obj::Func { pairs, .. } | Obj::Native { pairs, .. } => {
                pairs.clone()
            }
            Obj::Arr { items, pairs, .. } => {
                let mut out: Vec<(String, Value)> = items
                    .iter()
                    .enumerate()
                    .map(|(i, x)| (i.to_string(), *x))
                    .collect();
                out.extend(pairs.iter().cloned());
                out
            }
            Obj::Bytes { bytes, pairs, .. } => {
                let mut out: Vec<(String, Value)> = bytes
                    .iter()
                    .enumerate()
                    .map(|(i, b)| (i.to_string(), Value::Num(*b as f64)))
                    .collect();
                out.extend(pairs.iter().cloned());
                out
            }
            Obj::Typed { elems, pairs, .. } => {
                let mut out: Vec<(String, Value)> = elems
                    .iter()
                    .enumerate()
                    .map(|(i, e)| (i.to_string(), Value::Num(*e)))
                    .collect();
                out.extend(pairs.iter().cloned());
                out
            }
            Obj::Promise { pairs, .. } => pairs.clone(),
            // Big64/BufView return early above (indices need &mut to box).
            Obj::Big64 { .. } => unreachable!("Big64 pairs box above"),
            Obj::BufView { .. } => unreachable!("BufView pairs box above"),
            Obj::Dom { .. }
            | Obj::RegExp { .. }
            | Obj::Style { .. }
            | Obj::Accessor { .. }
            | Obj::Symbol { .. }
            | Obj::BigInt { .. }
            | Obj::Map { .. }
            | Obj::Set { .. }
            | Obj::WeakMap { .. }
            | Obj::Proxy { .. }
            | Obj::Buf { .. }
            | Obj::DView { .. }
            | Obj::Freed => Vec::new(),
        },
        _ => Vec::new(),
    }
}

fn n_obj_keys(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let pairs = own_pairs(it, arg(args, 0));
    let mut out = Vec::with_capacity(pairs.len());
    for (k, _) in pairs {
        out.push(Value::Str(it.heap.alloc_str(k)?));
    }
    Ok(Value::Obj(it.arr_obj(out)?))
}

fn n_obj_values(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let pairs = own_pairs(it, arg(args, 0));
    let out: Vec<Value> = pairs.into_iter().map(|(_, v)| v).collect();
    Ok(Value::Obj(it.arr_obj(out)?))
}

fn n_obj_entries(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let pairs = own_pairs(it, arg(args, 0));
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
        for (k, v) in own_pairs(it, *src) {
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
    let obj = Value::Obj(it.heap.alloc_obj(Obj::Ordinary {
        pairs: vec![],
        proto,
    })?);
    // Optional descriptors ({key: {value/get/set,...}}) install like
    // defineProperty each (Babel _inherits' constructor backlink).
    if let Value::Obj(_) = arg(args, 1) {
        for (k, d) in own_pairs(it, arg(args, 1)) {
            define_one(it, obj, &k, d)?;
        }
    }
    Ok(obj)
}

/// Object.freeze(o): no-op that returns the object (nothing enforces
/// frozenness; scraping never depends on the throw-on-write).
fn n_obj_freeze(_it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    Ok(arg(args, 0))
}

/// Shared by defineProperty/defineProperties: data (`value`) or accessor
/// (`get`/`set`) descriptor; flags ignored (all props stay mutable).
/// Attribute-only descriptors (`{writable:false}`, no value/get/set)
/// keep the existing value like V8 (only absent keys become undefined).
fn define_one(it: &mut Interp, target: Value, key: &str, desc: Value) -> Result<(), JsError> {
    if !matches!(target, Value::Obj(_)) {
        return Err(err("defineProperty: target must be an object"));
    }
    let g = get_prop(&it.heap, &it.protos, desc, "get")?;
    let s = get_prop(&it.heap, &it.protos, desc, "set")?;
    let has_acc = !matches!(g, Value::Undef) || !matches!(s, Value::Undef);
    if has_acc {
        let go = match g {
            Value::Obj(id) => Some(id),
            _ => None,
        };
        let so = match s {
            Value::Obj(id) => Some(id),
            _ => None,
        };
        let proto = po(it.protos.object);
        let acc = Value::Obj(it.heap.alloc_obj(Obj::Accessor {
            get: go,
            set: so,
            proto,
        })?);
        set_prop(&mut it.heap, target, key, acc)?;
        return Ok(());
    }
    // Own `value` (even explicit undefined) overwrites; a descriptor
    // without one only touches flags - the value survives.
    let has_value = match desc {
        Value::Obj(id) => own_prop(&it.heap, id, "value").is_some(),
        _ => false,
    };
    if has_value || own_val(&it.heap, target, key).is_none() {
        let v = get_prop(&it.heap, &it.protos, desc, "value")?;
        set_prop(&mut it.heap, target, key, v)?;
    }
    Ok(())
}

/// Own (non-inherited) value of `key` on an object, if present.
fn own_val(h: &Heap, target: Value, key: &str) -> Option<Value> {
    let Value::Obj(id) = target else {
        return None;
    };
    own_prop(h, id, key)
}

fn n_obj_define_property(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let target = arg(args, 0);
    let key = to_str(&it.heap, arg(args, 1));
    define_one(it, target, &key, arg(args, 2))?;
    Ok(target)
}

fn n_obj_define_properties(
    it: &mut Interp,
    _this: Value,
    args: &[Value],
) -> Result<Value, JsError> {
    let target = arg(args, 0);
    for (k, d) in own_pairs(it, arg(args, 1)) {
        define_one(it, target, &k, d)?;
    }
    Ok(target)
}

fn n_obj_own_names(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    // String keys only (length excluded: non-enumerable, like for-in).
    let keys: Vec<String> = match arg(args, 0) {
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::Ordinary { pairs, .. } | Obj::Func { pairs, .. } | Obj::Native { pairs, .. } => {
                pairs.iter().map(|(k, _)| k.clone()).collect()
            }
            Obj::Arr { items, pairs, .. } => (0..items.len())
                .map(|i| i.to_string())
                .chain(pairs.iter().map(|(k, _)| k.clone()))
                .collect(),
            Obj::Bytes { bytes, pairs, .. } => (0..bytes.len())
                .map(|i| i.to_string())
                .chain(pairs.iter().map(|(k, _)| k.clone()))
                .collect(),
            Obj::Typed { elems, pairs, .. } => (0..elems.len())
                .map(|i| i.to_string())
                .chain(pairs.iter().map(|(k, _)| k.clone()))
                .collect(),
            Obj::Big64 { elems, pairs, .. } => (0..elems.len())
                .map(|i| i.to_string())
                .chain(pairs.iter().map(|(k, _)| k.clone()))
                .collect(),
            Obj::BufView { len, kind, pairs, .. } => (0..view_count(*kind, *len))
                .map(|i| i.to_string())
                .chain(pairs.iter().map(|(k, _)| k.clone()))
                .collect(),
            _ => Vec::new(),
        },
        _ => Vec::new(),
    };
    let mut out = Vec::with_capacity(keys.len());
    for k in keys {
        out.push(Value::Str(it.heap.alloc_str(k)?));
    }
    Ok(Value::Obj(it.arr_obj(out)?))
}

fn n_obj_own_symbols(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    // Always empty: symbol keys coerce to strings on write here, so no
    // object ever holds one (documented model gap).
    Ok(Value::Obj(it.arr_obj(Vec::new())?))
}

/// `{value,writable,enumerable,configurable}` or the accessor triple.
/// All props report mutable + enumerable, except array `length`.
/// Proxies describe the target (getOwnPropertyDescriptor trap gap).
fn describe_own(it: &mut Interp, target: Value, key: &str) -> Result<Value, JsError> {
    let target = match target {
        Value::Obj(id) => Value::Obj(proxy_resolve(&it.heap, id)),
        _ => target,
    };
    let mut desc: Vec<(String, Value)> = vec![
        ("enumerable".into(), Value::Bool(true)),
        ("configurable".into(), Value::Bool(true)),
    ];
    let found = match target {
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::Ordinary { pairs, .. } | Obj::Func { pairs, .. } | Obj::Native { pairs, .. } => {
                pairs.iter().find(|(k, _)| k == key).map(|(_, v)| *v)
            }
            Obj::Promise { pairs, .. } => {
                pairs.iter().find(|(k, _)| k == key).map(|(_, v)| *v)
            }
            Obj::Arr { items, pairs, .. } => {
                if key == "length" {
                    desc = vec![
                        ("value".into(), Value::Num(items.len() as f64)),
                        ("writable".into(), Value::Bool(true)),
                        ("enumerable".into(), Value::Bool(false)),
                        ("configurable".into(), Value::Bool(false)),
                    ];
                    return Ok(Value::Obj(it.obj_pairs(desc)?));
                }
                if let Ok(i) = key.parse::<usize>() {
                    items.get(i).copied()
                } else {
                    pairs.iter().find(|(k, _)| k == key).map(|(_, v)| *v)
                }
            }
            Obj::Bytes { bytes, pairs, .. } => {
                if key == "length" {
                    desc = vec![
                        ("value".into(), Value::Num(bytes.len() as f64)),
                        ("writable".into(), Value::Bool(false)),
                        ("enumerable".into(), Value::Bool(false)),
                        ("configurable".into(), Value::Bool(false)),
                    ];
                    return Ok(Value::Obj(it.obj_pairs(desc)?));
                }
                if let Ok(i) = key.parse::<usize>() {
                    bytes.get(i).map(|b| Value::Num(*b as f64))
                } else {
                    pairs.iter().find(|(k, _)| k == key).map(|(_, v)| *v)
                }
            }
            Obj::Typed { elems, pairs, .. } => {
                if key == "length" {
                    desc = vec![
                        ("value".into(), Value::Num(elems.len() as f64)),
                        ("writable".into(), Value::Bool(false)),
                        ("enumerable".into(), Value::Bool(false)),
                        ("configurable".into(), Value::Bool(false)),
                    ];
                    return Ok(Value::Obj(it.obj_pairs(desc)?));
                }
                if let Ok(i) = key.parse::<usize>() {
                    elems.get(i).map(|e| Value::Num(*e))
                } else {
                    pairs.iter().find(|(k, _)| k == key).map(|(_, v)| *v)
                }
            }
            Obj::Big64 {
                signed,
                elems,
                pairs,
                ..
            } => {
                if key == "length" {
                    desc = vec![
                        ("value".into(), Value::Num(elems.len() as f64)),
                        ("writable".into(), Value::Bool(false)),
                        ("enumerable".into(), Value::Bool(false)),
                        ("configurable".into(), Value::Bool(false)),
                    ];
                    return Ok(Value::Obj(it.obj_pairs(desc)?));
                }
                if let Ok(i) = key.parse::<usize>() {
                    match elems.get(i).copied() {
                        Some(bits) => {
                            let (neg, mag) = if *signed {
                                bi_from_i64(bits as i64)
                            } else {
                                bi_from_u64(bits)
                            };
                            Some(bi_alloc(it, neg, mag)?)
                        }
                        None => None,
                    }
                } else {
                    pairs.iter().find(|(k, _)| k == key).map(|(_, v)| *v)
                }
            }
            Obj::BufView { buf, off, len, kind, pairs, .. } => {
                let n = view_count(*kind, *len);
                if key == "length" {
                    desc = vec![
                        ("value".into(), Value::Num(n as f64)),
                        ("writable".into(), Value::Bool(false)),
                        ("enumerable".into(), Value::Bool(false)),
                        ("configurable".into(), Value::Bool(false)),
                    ];
                    return Ok(Value::Obj(it.obj_pairs(desc)?));
                }
                if let Ok(i) = key.parse::<usize>() {
                    if i >= n {
                        pairs.iter().find(|(k, _)| k == key).map(|(_, v)| *v)
                    } else {
                        let bpe = t_bpe(*kind);
                        let at = off + i * bpe;
                        match kind {
                            TypedKind::I64 | TypedKind::U64 => {
                                match view_read_u64(&it.heap, *buf, at) {
                                    Some(b) => {
                                        let (neg, mag) = if *kind == TypedKind::I64 {
                                            bi_from_i64(b as i64)
                                        } else {
                                            bi_from_u64(b)
                                        };
                                        Some(bi_alloc(it, neg, mag)?)
                                    }
                                    None => None,
                                }
                            }
                            kk => view_read_num(&it.heap, *buf, at, *kk).map(Value::Num),
                        }
                    }
                } else {
                    pairs.iter().find(|(k, _)| k == key).map(|(_, v)| *v)
                }
            }
            _ => None,
        },
        _ => None,
    };
    let Some(v) = found else {
        return Ok(Value::Undef);
    };
    match v {
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::Accessor { get, set, .. } => {
                let g = get.map(Value::Obj).unwrap_or(Value::Undef);
                let s = set.map(Value::Obj).unwrap_or(Value::Undef);
                desc.push(("get".into(), g));
                desc.push(("set".into(), s));
            }
            _ => {
                desc.push(("value".into(), v));
                desc.push(("writable".into(), Value::Bool(true)));
            }
        },
        _ => {
            desc.push(("value".into(), v));
            desc.push(("writable".into(), Value::Bool(true)));
        }
    }
    Ok(Value::Obj(it.obj_pairs(desc)?))
}

fn n_obj_get_desc(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let key = to_str(&it.heap, arg(args, 1));
    describe_own(it, arg(args, 0), &key)
}

fn n_obj_get_descs(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let mut out = Vec::new();
    if let Value::Obj(id) = arg(args, 0) {
        let id = proxy_resolve(&it.heap, id);
        let keys: Vec<String> = match it.heap.obj(id) {
            Obj::Ordinary { pairs, .. } | Obj::Func { pairs, .. } | Obj::Native { pairs, .. } => {
                pairs.iter().map(|(k, _)| k.clone()).collect()
            }
            Obj::Arr { items, pairs, .. } => (0..items.len())
                .map(|i| i.to_string())
                .chain(pairs.iter().map(|(k, _)| k.clone()))
                .collect(),
            Obj::Bytes { bytes, pairs, .. } => (0..bytes.len())
                .map(|i| i.to_string())
                .chain(pairs.iter().map(|(k, _)| k.clone()))
                .collect(),
            Obj::Typed { elems, pairs, .. } => (0..elems.len())
                .map(|i| i.to_string())
                .chain(pairs.iter().map(|(k, _)| k.clone()))
                .collect(),
            Obj::Big64 { elems, pairs, .. } => (0..elems.len())
                .map(|i| i.to_string())
                .chain(pairs.iter().map(|(k, _)| k.clone()))
                .collect(),
            Obj::BufView { len, kind, pairs, .. } => (0..view_count(*kind, *len))
                .map(|i| i.to_string())
                .chain(pairs.iter().map(|(k, _)| k.clone()))
                .collect(),
            _ => Vec::new(),
        };
        for k in keys {
            out.push((k.clone(), describe_own(it, Value::Obj(id), &k)?));
        }
    }
    Ok(Value::Obj(it.obj_pairs(out)?))
}

fn n_obj_get_proto(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    // Heap-cap edge: an uninstalled proto bag reads as null.
    let bag = |p: u32| {
        if p == u32::MAX {
            Value::Null
        } else {
            Value::Obj(p)
        }
    };
    Ok(match arg(args, 0) {
        Value::Obj(id) => match proto_of(&it.heap, &it.protos, id) {
            Some(p) => Value::Obj(p),
            None => Value::Null,
        },
        Value::Str(_) => bag(it.protos.string),
        Value::Num(_) => bag(it.protos.number),
        // No boolean proto bag exists (booleans expose no methods here).
        Value::Bool(_) => Value::Null,
        Value::Undef | Value::Null => {
            return Err(err("getPrototypeOf of null/undefined"));
        }
    })
}

fn n_obj_set_proto(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let target = arg(args, 0);
    let proto = match arg(args, 1) {
        Value::Obj(id) => Some(id),
        Value::Null => None,
        _ => return Err(err("setPrototypeOf: proto must be an object or null")),
    };
    if std::env::var_os("VIGIA_JSTRACE").is_some() {
        eprintln!("js? setProto {} -> {}", it.describe(target), it.describe_any_proto(proto));
    }
    let Value::Obj(id) = target else {
        return Err(err("setPrototypeOf: target must be an object"));
    };
    match it.heap.obj_mut(id) {
        Obj::Ordinary { proto: slot, .. }
        | Obj::Arr { proto: slot, .. }
        | Obj::Func { proto: slot, .. } => {
            *slot = proto;
        }
        // No proto slot (natives use a virtual one, the rest have none):
        // sloppy no-op, still returns the target.
        _ => {}
    }
    Ok(target)
}

fn n_obj_from_entries(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let pairs = match arg(args, 0) {
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::Arr { items, .. } => items.clone(),
            _ => return Err(err("fromEntries takes an array of pairs")),
        },
        _ => return Err(err("fromEntries takes an array of pairs")),
    };
    let mut out = Vec::with_capacity(pairs.len());
    for p in pairs {
        let (k, v) = match p {
            Value::Obj(id) => match it.heap.obj(id) {
                Obj::Arr { items, .. } => (
                    items.first().copied().unwrap_or(Value::Undef),
                    items.get(1).copied().unwrap_or(Value::Undef),
                ),
                _ => return Err(err("fromEntries takes an array of pairs")),
            },
            _ => return Err(err("fromEntries takes an array of pairs")),
        };
        out.push((to_str(&it.heap, k), v));
    }
    Ok(Value::Obj(it.obj_pairs(out)?))
}

/// SameValue: strict plus NaN-equals-NaN, but +0 and -0 differ.
fn n_obj_is(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let (l, r) = (arg(args, 0), arg(args, 1));
    let eq = match (l, r) {
        (Value::Num(a), Value::Num(b)) => {
            if a == b {
                a != 0.0 || (1.0 / a) == (1.0 / b)
            } else {
                a.is_nan() && b.is_nan()
            }
        }
        _ => strict_eq(&it.heap, l, r),
    };
    Ok(Value::Bool(eq))
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

/// Array.from(arrayLike, mapFn?, thisArg?): strings feed chars, like V8.
fn n_array_from(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let raw = from_raw(it, arg(args, 0))?;
    let mapped: Vec<Value> = match arg(args, 1) {
        Value::Obj(mid)
            if matches!(it.heap.obj(mid), Obj::Func { .. } | Obj::Native { .. }) =>
        {
            let this_arg = arg(args, 2);
            let mut out = Vec::with_capacity(raw.len());
            for (i, v) in raw.into_iter().enumerate() {
                out.push(it.call_value(
                    Value::Obj(mid),
                    this_arg,
                    &[v, Value::Num(i as f64)],
                    None,
                )?);
            }
            out
        }
        _ => raw,
    };
    Ok(Value::Obj(it.arr_obj(mapped)?))
}

// -- primitive casts + number globals -------------------------------------------

fn n_string_cast(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let s = match args.first() {
        Some(v) => to_str(&it.heap, *v),
        None => String::new(),
    };
    Ok(Value::Str(it.heap.alloc_str(s)?))
}

/// String.fromCharCode(...codes): UTF-16 units (lone surrogates pass
/// through like real strings here).
fn n_str_from_char_code(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let mut out = String::new();
    for a in args {
        let u = to_num(&it.heap, *a) as u16;
        out.push(char::from_u32(u as u32).unwrap_or('\u{FFFD}'));
    }
    Ok(Value::Str(it.heap.alloc_str(out)?))
}

/// String.fromCodePoint(...cps): real code points (astral included).
fn n_str_from_code_point(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let mut out = String::new();
    for a in args {
        let n = to_num(&it.heap, *a);
        let cp = n as u32;
        if n.is_nan() || (cp as f64) != n || char::from_u32(cp).is_none() {
            return Err(err(format!("invalid code point {}", to_str(&it.heap, *a))));
        }
        out.push(char::from_u32(cp).unwrap());
    }
    Ok(Value::Str(it.heap.alloc_str(out)?))
}

/// String.raw(site, ...subs): interleaves site.raw with the
/// substitutions (raw text, not cooked, so escapes survive verbatim).
fn n_str_raw(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let raw_v = get_prop(&it.heap, &it.protos, arg(args, 0), "raw")?;
    let len = match get_prop(&it.heap, &it.protos, raw_v, "length") {
        Ok(Value::Num(n)) if n > 0.0 => (n.floor() as usize).min(1 << 28),
        _ => 0,
    };
    let mut out = String::new();
    for i in 0..len {
        let seg = get_prop(&it.heap, &it.protos, raw_v, &i.to_string())?;
        out.push_str(&to_str(&it.heap, seg));
        if let Some(sub) = args.get(i + 1) {
            out.push_str(&to_str(&it.heap, *sub));
        }
    }
    Ok(Value::Str(it.heap.alloc_str(out)?))
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

/// Function.prototype.toString: natives render `function n() {
/// [native code] }`, user functions their shape tag. Bot-agent
/// monkey-patch detectors key on exactly this distinction. Non-callable
/// receivers throw like V8.
fn n_fn_to_string(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    match this {
        Value::Obj(id)
            if matches!(
                it.heap.obj(id),
                Obj::Func { .. } | Obj::Native { .. }
            ) => Ok(Value::Str(it.heap.alloc_str(to_str(&it.heap, this))?)),
        _ => Err(err("Function.prototype.toString needs a function")),
    }
}

/// `f.bind(thisArg, ...bound)`: a Native carrying target/this/args in
/// its own pairs (the bound-state pattern). `new` on it ignores the
/// fresh object, like sloppy reality is not worth modeling.
fn n_fn_bind(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    match this {
        Value::Obj(id) if matches!(it.heap.obj(id), Obj::Func { .. } | Obj::Native { .. }) => {}
        _ => return Err(err("bind on a non-function")),
    }
    let bound_this = arg(args, 0);
    let arr = it.arr_obj(args.get(1.min(args.len())..).unwrap_or(&[]).to_vec())?;
    let b = it.heap.alloc_obj(nat("bound", n_bound_call))?;
    set_prop(&mut it.heap, Value::Obj(b), "__t", this)?;
    set_prop(&mut it.heap, Value::Obj(b), "__this", bound_this)?;
    set_prop(&mut it.heap, Value::Obj(b), "__a", Value::Obj(arr))?;
    Ok(Value::Obj(b))
}

fn n_bound_call(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let me = it.cur_native;
    let t = get_prop(&it.heap, &it.protos, me, "__t")?;
    let bt = get_prop(&it.heap, &it.protos, me, "__this")?;
    let mut full = match get_prop(&it.heap, &it.protos, me, "__a")? {
        Value::Obj(id) => arr_items(it, id),
        _ => Vec::new(),
    };
    full.extend_from_slice(args);
    it.call_value(t, bt, &full, None)
}

// -- Eager generators ---------------------------------------------------------
// No lazy stepwise execution: calling a `function*` returns an Ordinary with
// next/return/throw natives plus hidden `__gen_*` state (plain expandos,
// visible to enumeration like the bound-function `__t` pattern). First next()
// runs the whole body at once via a plain (is_gen-off) clone, so it cannot
// recurse into this path. `yield v` never delivers v (reads undefined);
// `yield*` parses as `yield` and stays equally eager. for-of stays strict
// (arrays/strings/sets/maps), so generators are not for-of-able here.

/// Fresh generator object per call: methods link back via `__g`; the body
/// (func, captured env, args, receiver) waits in `__gen_*` for first next().
fn gen_obj(it: &mut Interp, fid: u32, fenv: u32, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let arr = it.arr_obj(args.to_vec())?;
    let gid = it.obj_plain()?;
    for (name, f) in [
        ("next", n_gen_next as NativeFn),
        ("return", n_gen_return as NativeFn),
        ("throw", n_gen_throw as NativeFn),
    ] {
        let nid = it.heap.alloc_obj(Obj::Native {
            name,
            f,
            pairs: vec![("__g".into(), Value::Obj(gid))],
        })?;
        set_prop(&mut it.heap, Value::Obj(gid), name, Value::Obj(nid))?;
    }
    set_prop(&mut it.heap, Value::Obj(gid), "__gen_f", Value::Obj(fid))?;
    set_prop(
        &mut it.heap,
        Value::Obj(gid),
        "__gen_env",
        Value::Num(fenv as f64),
    )?;
    set_prop(
        &mut it.heap,
        Value::Obj(gid),
        "__gen_args",
        Value::Obj(arr),
    )?;
    set_prop(&mut it.heap, Value::Obj(gid), "__gen_this", this)?;
    set_prop(
        &mut it.heap,
        Value::Obj(gid),
        "__gen_started",
        Value::Bool(false),
    )?;
    set_prop(&mut it.heap, Value::Obj(gid), "__gen_done", Value::Bool(false))?;
    Ok(Value::Obj(gid))
}

/// The generator object behind a next/return/throw native (via its `__g`).
fn gen_self(it: &Interp) -> Result<u32, JsError> {
    match bound_prop(it, "__g")? {
        Value::Obj(g) => Ok(g),
        _ => Err(err("generator method detached")),
    }
}

fn gen_flag(it: &Interp, g: u32, key: &str) -> bool {
    matches!(
        get_prop(&it.heap, &it.protos, Value::Obj(g), key),
        Ok(Value::Bool(true))
    )
}

fn gen_result(it: &mut Interp, value: Value, done: bool) -> Result<Value, JsError> {
    Ok(Value::Obj(it.obj_pairs(vec![
        ("value".into(), value),
        ("done".into(), Value::Bool(done)),
    ])?))
}

fn n_gen_next(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let g = gen_self(it)?;
    if gen_flag(it, g, "__gen_done") {
        return gen_result(it, Value::Undef, true);
    }
    // Sent values are meaningless without suspension; dropped.
    let _ = arg(args, 0);
    let gv = Value::Obj(g);
    let fid = match get_prop(&it.heap, &it.protos, gv, "__gen_f")? {
        Value::Obj(f) => f,
        _ => return Err(err("generator detached")),
    };
    let fenv = match get_prop(&it.heap, &it.protos, gv, "__gen_env")? {
        Value::Num(n) => n as u32,
        _ => return Err(err("generator detached")),
    };
    let thisv = get_prop(&it.heap, &it.protos, gv, "__gen_this")?;
    let argv = match get_prop(&it.heap, &it.protos, gv, "__gen_args")? {
        Value::Obj(a) => arr_items(it, a),
        _ => Vec::new(),
    };
    let def = match it.heap.obj(fid) {
        Obj::Func { def, .. } => def.clone(),
        _ => return Err(err("generator detached")),
    };
    set_prop(&mut it.heap, gv, "__gen_started", Value::Bool(true))?;
    let plain = Rc::new(FnDef {
        is_gen: false,
        ..(*def).clone()
    });
    let tf = it.func_obj(plain, fenv)?;
    let r = it.call_value(Value::Obj(tf), thisv, &argv, None);
    set_prop(&mut it.heap, gv, "__gen_done", Value::Bool(true))?;
    match r {
        Ok(v) => gen_result(it, v, true),
        Err(e) => Err(e),
    }
}

fn n_gen_return(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let g = gen_self(it)?;
    set_prop(&mut it.heap, Value::Obj(g), "__gen_done", Value::Bool(true))?;
    gen_result(it, arg(args, 0), true)
}

fn n_gen_throw(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let g = gen_self(it)?;
    set_prop(&mut it.heap, Value::Obj(g), "__gen_done", Value::Bool(true))?;
    Err(JsError::Throw(arg(args, 0)))
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

/// Shared sort core (sort + toSorted): comparator insertion sort, else
/// ascending ToString order. Runs on a clone; the caller writes back.
fn sort_items(
    it: &mut Interp,
    mut items: Vec<Value>,
    args: &[Value],
) -> Result<Vec<Value>, JsError> {
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
    Ok(items)
}

fn n_arr_sort(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let items = arr_items(it, id);
    let sorted = sort_items(it, items, args)?;
    if let Obj::Arr { items: dst, .. } = it.heap.obj_mut(id) {
        *dst = sorted;
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

/// fill(value, start?, end?): relative-index range overwrite, NaN start
/// reads as 0 via from_idx. No hole concept here, so the whole range
/// fills like V8's hole-filling path. Returns the array.
fn n_arr_fill(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let v = arg(args, 0);
    let len = arr_items(it, id).len();
    let lo = match args.get(1) {
        Some(s) => from_idx(to_num(&it.heap, *s), len),
        None => 0,
    };
    let hi = match args.get(2) {
        Some(e) => from_idx(to_num(&it.heap, *e), len),
        None => len,
    };
    if hi > lo {
        if let Obj::Arr { items, .. } = it.heap.obj_mut(id) {
            for x in items[lo..hi].iter_mut() {
                *x = v;
            }
        }
    }
    Ok(this)
}

fn n_arr_find_last(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let f = arg(args, 0);
    let t = arg(args, 1);
    let items = arr_items(it, id);
    for (i, x) in items.iter().enumerate().rev() {
        let r = it.call_value(f, t, &cb_args(*x, i, this), None)?;
        if truthy(&it.heap, r) {
            return Ok(*x);
        }
    }
    Ok(Value::Undef)
}

fn n_arr_flat_map(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let f = arg(args, 0);
    let t = arg(args, 1);
    let items = arr_items(it, id);
    let mut mapped = Vec::with_capacity(items.len());
    for (i, x) in items.iter().enumerate() {
        mapped.push(it.call_value(f, t, &cb_args(*x, i, this), None)?);
    }
    let mut out = Vec::with_capacity(mapped.len());
    flat_into(&it.heap, &mut out, &mapped, 1);
    Ok(Value::Obj(it.arr_obj(out)?))
}

fn n_arr_at(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let items = arr_items(it, id);
    let len = items.len() as i64;
    let mut i = to_num(&it.heap, arg(args, 0)) as i64;
    if i < 0 {
        i += len;
    }
    if i < 0 || i >= len {
        return Ok(Value::Undef);
    }
    Ok(items[i as usize])
}

fn n_arr_copy_within(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let items = arr_items(it, id);
    let len = items.len();
    let to = from_idx(to_num(&it.heap, arg(args, 0)), len);
    let from = match args.get(1) {
        Some(s) => from_idx(to_num(&it.heap, *s), len),
        None => 0,
    };
    let end = match args.get(2) {
        Some(e) => from_idx(to_num(&it.heap, *e), len),
        None => len,
    };
    let count = end.saturating_sub(from).min(len.saturating_sub(to));
    if let Obj::Arr { items: dst, .. } = it.heap.obj_mut(id) {
        let src = items[from..from + count].to_vec();
        dst[to..to + count].copy_from_slice(&src);
    }
    Ok(this)
}

/// keys/values/entries return arrays, not iterators: the engine has no
/// iterator protocol (Set does the same), so for-of/spread over them
/// throw like any other non-iterable.
fn n_arr_keys(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let n = arr_items(it, id).len();
    Ok(Value::Obj(
        it.arr_obj((0..n).map(|i| Value::Num(i as f64)).collect())?,
    ))
}

fn n_arr_values(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    Ok(Value::Obj(it.arr_obj(arr_items(it, id))?))
}

fn n_arr_entries(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let items = arr_items(it, id);
    let mut vals = Vec::with_capacity(items.len());
    for (i, v) in items.into_iter().enumerate() {
        vals.push(Value::Obj(it.arr_obj(vec![Value::Num(i as f64), v])?));
    }
    Ok(Value::Obj(it.arr_obj(vals)?))
}

fn n_arr_to_reversed(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let mut items = arr_items(it, id);
    items.reverse();
    Ok(Value::Obj(it.arr_obj(items)?))
}

fn n_arr_to_sorted(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let items = arr_items(it, id);
    let sorted = sort_items(it, items, args)?;
    Ok(Value::Obj(it.arr_obj(sorted)?))
}

fn n_arr_to_spliced(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let mut items = arr_items(it, id);
    let len = items.len() as i64;
    let start = {
        let a = to_num(&it.heap, arg(args, 0)) as i64;
        (if a < 0 { len + a } else { a.min(len) }).clamp(0, len) as usize
    };
    let del = match args.get(1) {
        Some(v) => (to_num(&it.heap, *v) as i64).clamp(0, len - start as i64) as usize,
        None => len as usize - start,
    };
    let ins: Vec<Value> = args[2.min(args.len())..].to_vec();
    items.splice(start..start + del, ins);
    Ok(Value::Obj(it.arr_obj(items)?))
}

fn n_arr_with(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = this_arr(it, this)?;
    let mut items = arr_items(it, id);
    let len = items.len() as i64;
    let mut i = to_num(&it.heap, arg(args, 0)) as i64;
    if i < 0 {
        i += len;
    }
    if i < 0 || i >= len {
        return Err(err("Array.prototype.with index out of range"));
    }
    items[i as usize] = arg(args, 1);
    Ok(Value::Obj(it.arr_obj(items)?))
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

/// Legacy substr(start, length): negative start counts from the end.
fn n_str_substr(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let s = this_str(it, this);
    let chars: Vec<char> = s.chars().collect();
    let len = chars.len() as i64;
    let mut a = to_num(&it.heap, arg(args, 0)).trunc() as i64;
    if a < 0 {
        a = (len + a).max(0);
    }
    let b = match args.get(1) {
        Some(v) => {
            let n = to_num(&it.heap, *v).trunc() as i64;
            if n <= 0 {
                return Ok(Value::Str(it.heap.alloc_str(String::new())?));
            }
            (a + n).min(len)
        }
        None => len,
    };
    let a = a.clamp(0, len);
    Ok(Value::Str(it.heap.alloc_str(
        chars[a as usize..b as usize].iter().collect(),
    )?))
}

fn n_str_substring(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {    let s = this_str(it, this);
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
    // No implicit BigInt -> string here either (engine-wide rule: only the
    // explicit String(x) call renders a BigInt).
    if is_big(&it.heap, this) || args.iter().any(|a| is_big(&it.heap, *a)) {
        return Err(err("Cannot convert a BigInt value to a string"));
    }
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

/// Number.prototype.toString(radix): integers in bases 2..36, anything
/// else in base 10 (fractional non-decimal expansion is a gap - falls
/// back to the base-10 rendering).
fn n_num_to_string(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    const DIGITS: &[u8] = b"0123456789abcdefghijklmnopqrstuvwxyz";
    let n = to_num(&it.heap, this);
    let radix = match arg(args, 0) {
        Value::Undef => 10,
        v => to_num(&it.heap, v).trunc() as i64,
    };
    if !(2..=36).contains(&radix) {
        return Err(err("radix out of range"));
    }
    let s = if !n.is_finite() || radix == 10 || n.fract() != 0.0 {
        fmt_num(n)
    } else {
        let u = n.trunc().abs();
        if u >= 9e15 {
            fmt_num(n)
        } else {
            let mut ui = u as u64;
            let mut out = Vec::new();
            if ui == 0 {
                out.push(b'0');
            }
            while ui > 0 {
                out.push(DIGITS[(ui % radix as u64) as usize]);
                ui /= radix as u64;
            }
            if n < 0.0 {
                out.push(b'-');
            }
            out.reverse();
            String::from_utf8(out).unwrap_or_default()
        }
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

/// days since epoch from y/m/d (Hinnant days_from_civil, inverse of civil).
fn days_from_civil(y: i64, m: u32, d: u32) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = y.div_euclid(400);
    let yoe = y.rem_euclid(400);
    let mp = ((m as i64 + 9) % 12) as i64;
    let doy = (153 * mp + 2) / 5 + d as i64 - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146097 + doe - 719468
}

/// Date.UTC(y, m0, d=1, h=0, min=0, s=0, ms=0): month is 0-based,
/// years 0-99 map to 1900+y, out-of-range fields overflow like V8.
fn n_date_utc(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let num = |i: usize, dflt: f64| match arg(args, i) {
        Value::Undef => dflt,
        v => to_num(&it.heap, v),
    };
    if matches!(arg(args, 0), Value::Undef) {
        return Ok(Value::Num(f64::NAN));
    }
    // Non-finite components poison the whole computation (V8 parity).
    for i in 0..7 {
        if !matches!(arg(args, i), Value::Undef) && !to_num(&it.heap, arg(args, i)).is_finite() {
            return Ok(Value::Num(f64::NAN));
        }
    }
    let mut y = num(0, 0.0).trunc() as i64;
    if (0..=99).contains(&y) {
        y += 1900;
    }
    // Month overflow folds into the year before the civil conversion.
    let m = num(1, 0.0).trunc() as i64;
    let y = y + m.div_euclid(12);
    let mo = (m.rem_euclid(12) + 1) as u32;
    let ms = num(6, 0.0)
        + 1000.0 * num(5, 0.0)
        + 60_000.0 * num(4, 0.0)
        + 3_600_000.0 * num(3, 0.0)
        + 86_400_000.0 * (num(2, 1.0) - 1.0)
        + 86_400_000.0 * days_from_civil(y, mo, 1) as f64;
    Ok(Value::Num(ms))
}

// -- URL -----------------------------------------------------------------------------

/// `new URL(input, base?)`: components materialized as own string props
/// (read-only snapshot - setters stay unimplemented).
fn n_url_ctor(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let input = to_str(&it.heap, arg(args, 0));
    let url = match arg(args, 1) {
        Value::Undef => vigia_url::Url::parse(&input),
        b => {
            let bs = to_str(&it.heap, b);
            vigia_url::Url::parse(&bs).and_then(|base| base.join(&input))
        }
    }
    .map_err(|e| err(format!("invalid URL: {e}")))?;
    let mut props = Vec::with_capacity(8);
    let str_prop = |pairs: &mut Vec<(String, Value)>,
                        heap: &mut Heap,
                        k: &str,
                        v: String| {
        let id = heap.alloc_str(v)?;
        pairs.push((k.into(), Value::Str(id)));
        Ok::<(), JsError>(())
    };
    str_prop(&mut props, &mut it.heap, "href", url.to_string())?;
    str_prop(&mut props, &mut it.heap, "protocol", format!("{}:", url.scheme))?;
    str_prop(
        &mut props,
        &mut it.heap,
        "host",
        if url.host.is_empty() {
            String::new()
        } else {
            url.host_header()
        },
    )?;
    str_prop(&mut props, &mut it.heap, "hostname", url.host.clone())?;
    str_prop(
        &mut props,
        &mut it.heap,
        "port",
        url.port.map(|p| p.to_string()).unwrap_or_default(),
    )?;
    str_prop(&mut props, &mut it.heap, "pathname", url.path.clone())?;
    str_prop(
        &mut props,
        &mut it.heap,
        "search",
        url.query.as_deref().map(|q| format!("?{q}")).unwrap_or_default(),
    )?;
    str_prop(
        &mut props,
        &mut it.heap,
        "hash",
        url.fragment
            .as_deref()
            .map(|f| format!("#{f}"))
            .unwrap_or_default(),
    )?;
    str_prop(
        &mut props,
        &mut it.heap,
        "origin",
        if url.host.is_empty() {
            "null".into()
        } else {
            format!("{}://{}", url.scheme, url.host_header())
        },
    )?;
    let proto = po(it.protos.url);
    Ok(Value::Obj(it.heap.alloc_obj(Obj::Ordinary {
        pairs: props,
        proto,
    })?))
}

fn n_url_create(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    // Opaque unique handle; nothing backs it (no Blob URLs resolve here).
    let n = it.blob_next;
    it.blob_next = n.wrapping_add(1);
    Ok(Value::Str(it.heap.alloc_str(format!("blob:vigia-{n}"))?))
}

fn n_url_revoke(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let _ = it;
    Ok(Value::Undef)
}

/// Fixed persona offset (America/Montevideo, no DST): UTC-3. A real
/// browser reports the OS zone; without tz data this stays constant
/// (and deterministic for tests) - documented.
fn n_date_tz(_it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    Ok(Value::Num(-180.0))
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

// -- Symbol --------------------------------------------------------------------------

fn make_symbol(it: &mut Interp, desc: Option<u32>) -> Result<Value, JsError> {
    let proto = po(it.protos.symbol);
    Ok(Value::Obj(it.heap.alloc_obj(Obj::Symbol { desc, proto })?))
}

/// Symbol(desc?): never called with `new` (construct_value rejects
/// it before dispatch); bare calls always produce a symbol.
fn n_symbol(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let desc = match arg(args, 0) {
        Value::Undef => None,
        v => Some(it.heap.alloc_str(to_str(&it.heap, v))?),
    };
    make_symbol(it, desc)
}

fn n_symbol_for(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let key = to_str(&it.heap, arg(args, 0));
    if let Some(&id) = it.symbol_registry.get(&key) {
        return Ok(Value::Obj(id));
    }
    let desc = it.heap.alloc_str(key.clone())?;
    let Value::Obj(id) = make_symbol(it, Some(desc))? else {
        unreachable!()
    };
    it.symbol_registry.insert(key, id);
    Ok(Value::Obj(id))
}

fn n_symbol_key_for(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let Value::Obj(id) = arg(args, 0) else {
        return Err(err("keyFor on a non-Symbol"));
    };
    if !matches!(it.heap.obj(id), Obj::Symbol { .. }) {
        return Err(err("keyFor on a non-Symbol"));
    }
    for (k, &v) in &it.symbol_registry {
        if v == id {
            return Ok(Value::Str(it.heap.alloc_str(k.clone())?));
        }
    }
    Ok(Value::Undef)
}

fn sym_this(it: &Interp, this: Value, op: &str) -> Result<u32, JsError> {
    match this {
        Value::Obj(id) if matches!(it.heap.obj(id), Obj::Symbol { .. }) => Ok(id),
        _ => Err(err(format!("{op} on a non-Symbol"))),
    }
}

fn n_sym_description(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    // Called as an accessor with this = the symbol.
    let id = sym_this(it, this, "description")?;
    match it.heap.obj(id) {
        Obj::Symbol { desc: Some(s), .. } => Ok(Value::Str(*s)),
        _ => Ok(Value::Undef),
    }
}

fn n_sym_to_string(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let id = sym_this(it, this, "toString")?;
    let s = match it.heap.obj(id) {
        Obj::Symbol { desc: Some(s), .. } => format!("Symbol({})", it.heap.get_str(*s)),
        _ => "Symbol()".to_string(),
    };
    Ok(Value::Str(it.heap.alloc_str(s)?))
}

fn n_sym_value_of(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let id = sym_this(it, this, "valueOf")?;
    Ok(Value::Obj(id))
}

// -- Map / Set / WeakMap -------------------------------------------------------------

/// SameValueZero for map keys: strict plus NaN-equals-NaN.
fn same_key(h: &Heap, a: Value, b: Value) -> bool {
    if strict_eq(h, a, b) {
        return true;
    }
    matches!((a, b), (Value::Num(x), Value::Num(y)) if x.is_nan() && y.is_nan())
}

fn map_this(it: &Interp, this: Value, op: &str) -> Result<u32, JsError> {
    match this {
        Value::Obj(id) if matches!(it.heap.obj(id), Obj::Map { .. }) => Ok(id),
        _ => Err(err(format!("{op} on a non-Map"))),
    }
}

fn set_this(it: &Interp, this: Value, op: &str) -> Result<u32, JsError> {
    match this {
        Value::Obj(id) if matches!(it.heap.obj(id), Obj::Set { .. }) => Ok(id),
        _ => Err(err(format!("{op} on a non-Set"))),
    }
}

fn wmap_this(it: &Interp, this: Value, op: &str) -> Result<u32, JsError> {
    match this {
        Value::Obj(id) if matches!(it.heap.obj(id), Obj::WeakMap { .. }) => Ok(id),
        _ => Err(err(format!("{op} on a non-WeakMap"))),
    }
}

fn map_find(h: &Heap, entries: &[(Value, Value)], key: Value) -> Option<usize> {
    entries.iter().position(|(k, _)| same_key(h, *k, key))
}

fn set_find(h: &Heap, items: &[Value], key: Value) -> Option<usize> {
    items.iter().position(|v| same_key(h, *v, key))
}

fn n_map_ctor(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let proto = po(it.protos.map);
    let id = it.heap.alloc_obj(Obj::Map {
        entries: vec![],
        proto,
    })?;
    // `new Map([[k,v], ...])`: strict arrays of pairs.
    if let Some(pairs) = args.first() {
        if !matches!(pairs, Value::Undef) {
            let Value::Obj(pid) = pairs else {
                return Err(err("Map constructor takes pairs"));
            };
            let items = match it.heap.obj(*pid) {
                Obj::Arr { items, .. } => items.clone(),
                _ => return Err(err("Map constructor takes pairs")),
            };
            for p in items {
                let Value::Obj(eid) = p else {
                    return Err(err("Map constructor takes pairs"));
                };
                let (k, v) = match it.heap.obj(eid) {
                    Obj::Arr { items, .. } => (
                        items.first().copied().unwrap_or(Value::Undef),
                        items.get(1).copied().unwrap_or(Value::Undef),
                    ),
                    _ => return Err(err("Map constructor takes pairs")),
                };
                let found = match it.heap.obj(id) {
                    Obj::Map { entries, .. } => map_find(&it.heap, entries, k),
                    _ => unreachable!(),
                };
                match it.heap.obj_mut(id) {
                    Obj::Map { entries, .. } => match found {
                        Some(i) => entries[i].1 = v,
                        None => entries.push((k, v)),
                    },
                    _ => unreachable!(),
                }
            }
        }
    }
    Ok(Value::Obj(id))
}

fn n_map_set(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = map_this(it, this, "set")?;
    let (k, v) = (arg(args, 0), arg(args, 1));
    let found = match it.heap.obj(id) {
        Obj::Map { entries, .. } => map_find(&it.heap, entries, k),
        _ => unreachable!(),
    };
    match it.heap.obj_mut(id) {
        Obj::Map { entries, .. } => match found {
            Some(i) => entries[i].1 = v,
            None => entries.push((k, v)),
        },
        _ => unreachable!(),
    }
    Ok(this)
}

fn n_map_get(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = map_this(it, this, "get")?;
    Ok(match it.heap.obj(id) {
        Obj::Map { entries, .. } => map_find(&it.heap, entries, arg(args, 0))
            .map(|i| entries[i].1)
            .unwrap_or(Value::Undef),
        _ => unreachable!(),
    })
}

fn n_map_has(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = map_this(it, this, "has")?;
    Ok(match it.heap.obj(id) {
        Obj::Map { entries, .. } => {
            Value::Bool(map_find(&it.heap, entries, arg(args, 0)).is_some())
        }
        _ => unreachable!(),
    })
}

fn n_map_delete(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = map_this(it, this, "delete")?;
    let found = match it.heap.obj(id) {
        Obj::Map { entries, .. } => map_find(&it.heap, entries, arg(args, 0)),
        _ => unreachable!(),
    };
    Ok(match it.heap.obj_mut(id) {
        Obj::Map { entries, .. } => match found {
            Some(i) => {
                entries.remove(i);
                Value::Bool(true)
            }
            None => Value::Bool(false),
        },
        _ => unreachable!(),
    })
}

fn n_map_clear(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let id = map_this(it, this, "clear")?;
    if let Obj::Map { entries, .. } = it.heap.obj_mut(id) {
        entries.clear();
    }
    Ok(Value::Undef)
}

fn map_vec(
    it: &mut Interp,
    this: Value,
    op: &str,
    pick: fn(Value, Value) -> Value,
) -> Result<Value, JsError> {
    let id = map_this(it, this, op)?;
    let vals = match it.heap.obj(id) {
        Obj::Map { entries, .. } => entries.iter().map(|&(k, v)| pick(k, v)).collect(),
        _ => unreachable!(),
    };
    Ok(Value::Obj(it.arr_obj(vals)?))
}

fn n_map_keys(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    map_vec(it, this, "keys", |k, _| k)
}

fn n_map_values(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    map_vec(it, this, "values", |_, v| v)
}

fn n_map_entries(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let id = map_this(it, this, "entries")?;
    let pairs = match it.heap.obj(id) {
        Obj::Map { entries, .. } => entries.clone(),
        _ => unreachable!(),
    };
    let mut vals = Vec::with_capacity(pairs.len());
    for (k, v) in pairs {
        vals.push(Value::Obj(it.arr_obj(vec![k, v])?));
    }
    Ok(Value::Obj(it.arr_obj(vals)?))
}

fn n_map_for_each(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = map_this(it, this, "forEach")?;
    let pairs = match it.heap.obj(id) {
        Obj::Map { entries, .. } => entries.clone(),
        _ => unreachable!(),
    };
    let (f, that) = (arg(args, 0), arg(args, 1));
    for (k, v) in pairs {
        it.call_value(f, that, &[v, k, this], None)?;
    }
    Ok(Value::Undef)
}

fn n_map_size(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let id = map_this(it, this, "size")?;
    Ok(match it.heap.obj(id) {
        Obj::Map { entries, .. } => Value::Num(entries.len() as f64),
        _ => unreachable!(),
    })
}

fn n_set_ctor(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let proto = po(it.protos.set);
    let id = it.heap.alloc_obj(Obj::Set {
        items: vec![],
        proto,
    })?;
    if let Some(Value::Obj(pid)) = args.first() {
        let items = match it.heap.obj(*pid) {
            Obj::Arr { items, .. } => items.clone(),
            _ => return Err(err("Set constructor takes an array")),
        };
        for v in items {
            let fresh = match it.heap.obj(id) {
                Obj::Set { items, .. } => set_find(&it.heap, items, v).is_none(),
                _ => unreachable!(),
            };
            if fresh {
                if let Obj::Set { items, .. } = it.heap.obj_mut(id) {
                    items.push(v);
                }
            }
        }
    }
    Ok(Value::Obj(id))
}

fn n_set_add(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = set_this(it, this, "add")?;
    let v = arg(args, 0);
    let fresh = match it.heap.obj(id) {
        Obj::Set { items, .. } => set_find(&it.heap, items, v).is_none(),
        _ => unreachable!(),
    };
    if fresh {
        if let Obj::Set { items, .. } = it.heap.obj_mut(id) {
            items.push(v);
        }
    }
    Ok(this)
}

fn n_set_has(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = set_this(it, this, "has")?;
    Ok(match it.heap.obj(id) {
        Obj::Set { items, .. } => Value::Bool(set_find(&it.heap, items, arg(args, 0)).is_some()),
        _ => unreachable!(),
    })
}

fn n_set_delete(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = set_this(it, this, "delete")?;
    let found = match it.heap.obj(id) {
        Obj::Set { items, .. } => set_find(&it.heap, items, arg(args, 0)),
        _ => unreachable!(),
    };
    Ok(match it.heap.obj_mut(id) {
        Obj::Set { items, .. } => match found {
            Some(i) => {
                items.remove(i);
                Value::Bool(true)
            }
            None => Value::Bool(false),
        },
        _ => unreachable!(),
    })
}

fn n_set_clear(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let id = set_this(it, this, "clear")?;
    if let Obj::Set { items, .. } = it.heap.obj_mut(id) {
        items.clear();
    }
    Ok(Value::Undef)
}

fn set_vec(
    it: &mut Interp,
    this: Value,
    op: &str,
    pick: fn(Value) -> Value,
) -> Result<Value, JsError> {
    let id = set_this(it, this, op)?;
    let vals = match it.heap.obj(id) {
        Obj::Set { items, .. } => items.iter().map(|&v| pick(v)).collect(),
        _ => unreachable!(),
    };
    Ok(Value::Obj(it.arr_obj(vals)?))
}

fn n_set_values(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    set_vec(it, this, "values", |v| v)
}

fn n_set_entries(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let id = set_this(it, this, "entries")?;
    let items = match it.heap.obj(id) {
        Obj::Set { items, .. } => items.clone(),
        _ => unreachable!(),
    };
    let mut vals = Vec::with_capacity(items.len());
    for v in items {
        vals.push(Value::Obj(it.arr_obj(vec![v, v])?));
    }
    Ok(Value::Obj(it.arr_obj(vals)?))
}

fn n_set_for_each(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = set_this(it, this, "forEach")?;
    let items = match it.heap.obj(id) {
        Obj::Set { items, .. } => items.clone(),
        _ => unreachable!(),
    };
    let (f, that) = (arg(args, 0), arg(args, 1));
    for v in items {
        it.call_value(f, that, &[v, v, this], None)?;
    }
    Ok(Value::Undef)
}

fn n_set_size(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let id = set_this(it, this, "size")?;
    Ok(match it.heap.obj(id) {
        Obj::Set { items, .. } => Value::Num(items.len() as f64),
        _ => unreachable!(),
    })
}

fn n_weakmap_ctor(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let proto = po(it.protos.weakmap);
    Ok(Value::Obj(it.heap.alloc_obj(Obj::WeakMap {
        entries: vec![],
        proto,
    })?))
}

fn weak_key(v: Value) -> Result<(), JsError> {
    match v {
        Value::Obj(_) => Ok(()),
        _ => Err(err("WeakMap key must be an object")),
    }
}

fn n_weakmap_set(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = wmap_this(it, this, "set")?;
    let (k, v) = (arg(args, 0), arg(args, 1));
    weak_key(k)?;
    let found = match it.heap.obj(id) {
        Obj::WeakMap { entries, .. } => map_find(&it.heap, entries, k),
        _ => unreachable!(),
    };
    match it.heap.obj_mut(id) {
        Obj::WeakMap { entries, .. } => match found {
            Some(i) => entries[i].1 = v,
            None => entries.push((k, v)),
        },
        _ => unreachable!(),
    }
    Ok(this)
}

fn n_weakmap_get(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = wmap_this(it, this, "get")?;
    Ok(match it.heap.obj(id) {
        Obj::WeakMap { entries, .. } => map_find(&it.heap, entries, arg(args, 0))
            .map(|i| entries[i].1)
            .unwrap_or(Value::Undef),
        _ => unreachable!(),
    })
}

fn n_weakmap_has(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = wmap_this(it, this, "has")?;
    Ok(match it.heap.obj(id) {
        Obj::WeakMap { entries, .. } => {
            Value::Bool(map_find(&it.heap, entries, arg(args, 0)).is_some())
        }
        _ => unreachable!(),
    })
}

fn n_weakmap_delete(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = wmap_this(it, this, "delete")?;
    let found = match it.heap.obj(id) {
        Obj::WeakMap { entries, .. } => map_find(&it.heap, entries, arg(args, 0)),
        _ => unreachable!(),
    };
    Ok(match it.heap.obj_mut(id) {
        Obj::WeakMap { entries, .. } => match found {
            Some(i) => {
                entries.remove(i);
                Value::Bool(true)
            }
            None => Value::Bool(false),
        },
        _ => unreachable!(),
    })
}

fn is_regexp(it: &Interp, v: Value) -> bool {
    matches!(v, Value::Obj(id) if matches!(it.heap.obj(id), Obj::RegExp { .. }))
}

// -- Typed arrays / ArrayBuffer --------------------------------------------------
// Minimal Uint8Array + ArrayBuffer for the base64/crypto/table code in
// real bundles. Views copy (no shared memory with the buffer or
// subarray/slice results - documented gap); only the u8 view exists.

/// ToIndex for lengths: floor, negatives and absurd sizes throw.
fn typed_len(h: &Heap, v: Value) -> Result<usize, JsError> {
    let n = to_num(h, v);
    if n.is_nan() {
        return Ok(0);
    }
    let n = n.floor();
    if n < 0.0 {
        return Err(err("invalid typed array length"));
    }
    Ok((n as usize).min(1 << 28))
}

/// `this` as a Bytes heap id; natives below error out on other receivers.
fn u8_this(it: &Interp, this: Value, name: &str) -> Result<u32, JsError> {
    match this {
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::Bytes { .. } => Ok(id),
            Obj::BufView { kind, .. } if *kind == TypedKind::U8 => Ok(id),
            _ => Err(err(format!("Uint8Array.{name} needs a Uint8Array receiver"))),
        },
        _ => Err(err(format!("Uint8Array.{name} needs a Uint8Array receiver"))),
    }
}

/// Element source for the ctor and set(): arrays map through ToUint8,
/// bytes/buffers clone, anything else copies length-based (like V8's
/// array-like path; strings yield zeros since chars aren't numbers).
fn u8_src_items(it: &Interp, v: Value) -> Vec<u8> {
    match v {
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::Arr { items, .. } => items.iter().map(|x| to_u8(&it.heap, *x)).collect(),
            Obj::Bytes { bytes, .. } => bytes.clone(),
            Obj::Buf { bytes, .. } => bytes.clone(),
            // Big64 elements feed their low byte (wrap mod 256, like u8).
            Obj::Big64 { elems, .. } => elems.iter().map(|e| *e as u8).collect(),
            Obj::BufView { buf, off, len, kind, .. } => {
                let n = view_count(*kind, *len);
                let bpe = t_bpe(*kind);
                (0..n)
                    .map(|i| {
                        let at = off + i * bpe;
                        match kind {
                            TypedKind::I64 | TypedKind::U64 => {
                                view_read_u64(&it.heap, *buf, at).unwrap_or(0) as u8
                            }
                            kk => to_u8_num(view_read_num(&it.heap, *buf, at, *kk).unwrap_or(0.0)),
                        }
                    })
                    .collect()
            }
            _ => u8_len_items(it, Value::Obj(id)),
        },
        _ => u8_len_items(it, v),
    }
}

fn u8_len_items(it: &Interp, v: Value) -> Vec<u8> {
    let len = match get_prop(&it.heap, &it.protos, v, "length") {
        Ok(Value::Num(n)) if n > 0.0 => (n.floor() as usize).min(1 << 28),
        _ => return Vec::new(),
    };
    let mut out = Vec::with_capacity(len);
    for i in 0..len {
        let key = i.to_string();
        let n = match get_prop(&it.heap, &it.protos, v, &key) {
            Ok(x) => to_num(&it.heap, x),
            Err(_) => f64::NAN,
        };
        out.push(to_u8_num(n));
    }
    out
}

/// ToUint8 on a bare number (shared by to_u8 and the length copier).
fn to_u8_num(n: f64) -> u8 {
    let n = n.trunc();
    if !n.is_finite() {
        return 0;
    }
    (((n % 256.0) + 256.0) % 256.0) as u8
}

/// Write coercion per view kind (V8 element semantics; stored as f64 so
/// reads are exact, f32 round-trips through `as f32`).
fn t_write(kind: TypedKind, n: f64) -> f64 {
    match kind {
        TypedKind::F64 => n,
        TypedKind::F32 => (n as f32) as f64,
        TypedKind::U8 => to_u8_num(n) as f64,
        TypedKind::U32 => {
            let n = n.trunc();
            if !n.is_finite() {
                return 0.0;
            }
            ((n % 4294967296.0) + 4294967296.0) % 4294967296.0
        }
        TypedKind::I32 => {
            let n = n.trunc();
            if !n.is_finite() {
                return 0.0;
            }
            let u = ((n % 4294967296.0) + 4294967296.0) % 4294967296.0;
            if u >= 2147483648.0 {
                u - 4294967296.0
            } else {
                u
            }
        }
        TypedKind::U16 => {
            let n = n.trunc();
            if !n.is_finite() {
                return 0.0;
            }
            ((n % 65536.0) + 65536.0) % 65536.0
        }
        TypedKind::I16 => {
            let u = t_write(TypedKind::U16, n);
            if u >= 32768.0 {
                u - 65536.0
            } else {
                u
            }
        }
        TypedKind::I8 => {
            let u = to_u8_num(n) as f64;
            if u >= 128.0 {
                u - 256.0
            } else {
                u
            }
        }
        // ToUint8Clamp: NaN -> 0, saturate, round half to even.
        TypedKind::U8C => {
            if n.is_nan() || n <= 0.0 {
                return 0.0;
            }
            if n >= 255.0 {
                return 255.0;
            }
            let f = n.floor();
            let d = n - f;
            if d < 0.5 || (d == 0.5 && (f as i64) % 2 == 0) {
                f
            } else {
                f + 1.0
            }
        }
        // I64/U64 store u64 bits, never f64: no t_write caller uses
        // them (writes go through b64_wrap); degrade to 0 if hit.
        TypedKind::I64 | TypedKind::U64 => 0.0,
    }
}

/// Bytes per element (BYTES_PER_ELEMENT, buffer sizing).
fn t_bpe(kind: TypedKind) -> usize {
    match kind {
        TypedKind::U8 | TypedKind::I8 | TypedKind::U8C => 1,
        TypedKind::U16 | TypedKind::I16 => 2,
        TypedKind::U32 | TypedKind::I32 | TypedKind::F32 => 4,
        TypedKind::F64 | TypedKind::I64 | TypedKind::U64 => 8,
    }
}

/// Tag for Object.prototype.toString.
fn t_tag(kind: TypedKind) -> &'static str {
    match kind {
        TypedKind::U8 => "[object Uint8Array]",
        TypedKind::I8 => "[object Int8Array]",
        TypedKind::U8C => "[object Uint8ClampedArray]",
        TypedKind::U16 => "[object Uint16Array]",
        TypedKind::I16 => "[object Int16Array]",
        TypedKind::U32 => "[object Uint32Array]",
        TypedKind::I32 => "[object Int32Array]",
        TypedKind::F32 => "[object Float32Array]",
        TypedKind::F64 => "[object Float64Array]",
        TypedKind::I64 => "[object BigInt64Array]",
        TypedKind::U64 => "[object BigUint64Array]",
    }
}

/// Proto bag id for a live-view kind.
fn view_proto(it: &Interp, kind: TypedKind) -> u32 {
    match kind {
        TypedKind::U8 => it.protos.uint8array,
        TypedKind::I8 => it.protos.int8array,
        TypedKind::U8C => it.protos.uint8clampedarray,
        TypedKind::U16 => it.protos.uint16array,
        TypedKind::I16 => it.protos.int16array,
        TypedKind::U32 => it.protos.uint32array,
        TypedKind::I32 => it.protos.int32array,
        TypedKind::F32 => it.protos.float32array,
        TypedKind::F64 => it.protos.float64array,
        TypedKind::I64 => it.protos.bigint64array,
        TypedKind::U64 => it.protos.biguint64array,
    }
}

/// Backing bytes of a Buf id, if still live (swept → None, degrade).
fn buf_live(h: &Heap, buf: u32) -> Option<&[u8]> {
    match h.objs.get(buf as usize)? {
        Obj::Buf { bytes, .. } => Some(bytes),
        _ => None,
    }
}

/// Element count of a view window (stored byte len / bpe).
fn view_count(kind: TypedKind, len: usize) -> usize {
    len / t_bpe(kind).max(1)
}

/// LE-decode one numeric element at absolute byte `at` (None when the
/// backing Buf is swept or the window is short: callers read Undef).
fn view_read_num(h: &Heap, buf: u32, at: usize, kind: TypedKind) -> Option<f64> {
    let bytes = buf_live(h, buf)?;
    let bpe = t_bpe(kind);
    let w = bytes.get(at..at + bpe)?;
    let mut raw = [0u8; 8];
    raw[..bpe].copy_from_slice(w);
    let u = u64::from_le_bytes(raw);
    Some(match kind {
        TypedKind::U8 => w[0] as f64,
        TypedKind::I8 => (w[0] as i8) as f64,
        TypedKind::U8C => t_write(TypedKind::U8C, w[0] as f64),
        TypedKind::U16 => (u as u16) as f64,
        TypedKind::I16 => (u as u16) as i16 as f64,
        TypedKind::U32 => (u as u32) as f64,
        TypedKind::I32 => (u as u32) as i32 as f64,
        TypedKind::F32 => f32::from_le_bytes([w[0], w[1], w[2], w[3]]) as f64,
        TypedKind::F64 => f64::from_le_bytes(w.try_into().unwrap_or([0; 8])),
        TypedKind::I64 | TypedKind::U64 => return None,
    })
}

/// LE-decode one 64-bit element at absolute byte `at`.
fn view_read_u64(h: &Heap, buf: u32, at: usize) -> Option<u64> {
    let bytes = buf_live(h, buf)?;
    let w = bytes.get(at..at + 8)?;
    Some(u64::from_le_bytes([
        w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7],
    ]))
}

/// LE-encode one numeric element into the backing Buf (swept/short → no-op).
fn view_write_num(h: &mut Heap, buf: u32, at: usize, kind: TypedKind, v: f64) {
    let bpe = t_bpe(kind);
    let enc: Vec<u8> = match kind {
        TypedKind::U8 | TypedKind::U8C => vec![to_u8_num(t_write(kind, v))],
        TypedKind::I8 => vec![t_write(kind, v) as i8 as u8],
        TypedKind::U16 | TypedKind::I16 => (t_write(kind, v) as i32 as u16).to_le_bytes().to_vec(),
        TypedKind::U32 | TypedKind::I32 => (t_write(kind, v) as i64 as u32).to_le_bytes().to_vec(),
        TypedKind::F32 => (t_write(kind, v) as f32).to_le_bytes().to_vec(),
        TypedKind::F64 => t_write(kind, v).to_le_bytes().to_vec(),
        TypedKind::I64 | TypedKind::U64 => return,
    };
    if let Some(Obj::Buf { bytes, .. }) = h.objs.get_mut(buf as usize) {
        if at + bpe <= bytes.len() {
            bytes[at..at + bpe].copy_from_slice(&enc);
        }
    }
}

/// LE-encode one 64-bit element into the backing Buf.
fn view_write_u64(h: &mut Heap, buf: u32, at: usize, v: u64) {
    if let Some(Obj::Buf { bytes, .. }) = h.objs.get_mut(buf as usize) {
        if at + 8 <= bytes.len() {
            bytes[at..at + 8].copy_from_slice(&v.to_le_bytes());
        }
    }
}

/// LE-encode owned numeric elems into fresh bytes (for `.buffer` snapshots).
fn encode_owned(kind: TypedKind, elems: &[f64]) -> Vec<u8> {
    let mut out = Vec::with_capacity(elems.len() * t_bpe(kind));
    for e in elems {
        match kind {
            TypedKind::U8 | TypedKind::U8C => out.push(to_u8_num(t_write(kind, *e))),
            TypedKind::I8 => out.push(t_write(kind, *e) as i8 as u8),
            TypedKind::U16 | TypedKind::I16 => {
                out.extend_from_slice(&(t_write(kind, *e) as i32 as u16).to_le_bytes())
            }
            TypedKind::U32 | TypedKind::I32 => {
                out.extend_from_slice(&(t_write(kind, *e) as i64 as u32).to_le_bytes())
            }
            TypedKind::F32 => out.extend_from_slice(&(t_write(kind, *e) as f32).to_le_bytes()),
            TypedKind::F64 => out.extend_from_slice(&t_write(kind, *e).to_le_bytes()),
            TypedKind::I64 | TypedKind::U64 => out.extend_from_slice(&0u64.to_le_bytes()),
        }
    }
    out
}

/// View window (buf, abs off, byte len, kind) for ctors: Buf or BufView
/// source with byteOffset/length forms. byteOffset is relative to the
/// source window; length is an element count defaulting to the rest.
fn view_window(
    it: &Interp,
    src: u32,
    kind: TypedKind,
    args: &[Value],
) -> Result<Option<(u32, usize, usize)>, JsError> {
    let (buf, base, avail) = match it.heap.obj(src) {
        Obj::Buf { bytes, .. } => (src, 0, bytes.len()),
        Obj::BufView { buf, off, len, .. } => (*buf, *off, *len),
        _ => return Ok(None),
    };
    let bpe = t_bpe(kind);
    let off = match arg(args, 1) {
        Value::Undef => 0,
        v => {
            let n = to_num(&it.heap, v).trunc();
            if n < 0.0 || n.fract() != 0.0 || !(n as usize).is_multiple_of(bpe) {
                return Err(err("typed array buffer offset misaligned"));
            }
            n as usize
        }
    };
    if off > avail {
        return Err(err("typed array buffer offset misaligned"));
    }
    let rest = avail - off;
    if rest % bpe != 0 {
        return Err(err("typed array buffer length mismatch"));
    }
    let mut count = rest / bpe;
    if !matches!(arg(args, 2), Value::Undef) {
        let want = typed_len(&it.heap, arg(args, 2))?;
        if want > count {
            return Err(err("typed array length out of range"));
        }
        count = want;
    }
    Ok(Some((buf, base + off, count * bpe)))
}

/// `.buffer` value: a BufView facade over the whole backing Buf. Owned
/// parents snapshot once (LE-encode current elems) then rewire live onto
/// the new Buf, so later writes propagate; V8 aliases from birth, the
/// only gap is the pre-buffer snapshot instant, which is exact.
fn buffer_of(it: &mut Interp, id: u32) -> Result<Value, JsError> {
    let bproto = po(it.protos.buffer);
    match it.heap.obj(id) {
        Obj::Bytes { .. } | Obj::Typed { .. } | Obj::Big64 { .. } => {}
        Obj::DView { buf, .. } => {
            let buf = *buf;
            let blen = buf_live(&it.heap, buf).map(|b| b.len()).unwrap_or(0);
            return Ok(Value::Obj(it.heap.alloc_obj(Obj::BufView {
                buf,
                off: 0,
                len: blen,
                kind: TypedKind::U8,
                pairs: Vec::new(),
                proto: bproto,
            })?));
        }
        Obj::BufView { buf, .. } => {
            let buf = *buf;
            let blen = buf_live(&it.heap, buf).map(|b| b.len()).unwrap_or(0);
            return Ok(Value::Obj(it.heap.alloc_obj(Obj::BufView {
                buf,
                off: 0,
                len: blen,
                kind: TypedKind::U8,
                pairs: Vec::new(),
                proto: bproto,
            })?));
        }
        _ => return Ok(Value::Undef),
    }
    let (bytes, kind, pairs, proto) = match it.heap.obj(id) {
        Obj::Bytes { bytes, pairs, proto, .. } => (bytes.clone(), TypedKind::U8, pairs.clone(), *proto),
        Obj::Typed { kind, elems, pairs, proto, .. } => {
            (encode_owned(*kind, elems), *kind, pairs.clone(), *proto)
        }
        Obj::Big64 { signed, elems, pairs, proto, .. } => {
            let mut out = Vec::with_capacity(elems.len() * 8);
            for e in elems {
                out.extend_from_slice(&e.to_le_bytes());
            }
            let kind = if *signed { TypedKind::I64 } else { TypedKind::U64 };
            (out, kind, pairs.clone(), *proto)
        }
        _ => unreachable!(),
    };
    let blen = bytes.len();
    let buf = it.heap.alloc_obj(Obj::Buf { bytes, proto: bproto })?;
    let fac = Value::Obj(it.heap.alloc_obj(Obj::BufView {
        buf,
        off: 0,
        len: blen,
        kind: TypedKind::U8,
        pairs: Vec::new(),
        proto: bproto,
    })?);
    it.heap.objs[id as usize] = Obj::BufView {
        buf,
        off: 0,
        len: blen,
        kind,
        pairs,
        proto,
    };
    Ok(fac)
}

fn n_u8_ctor(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    if let Value::Obj(src) = arg(args, 0) {
        if let Ok(Some((buf, off, len))) = view_window(it, src, TypedKind::U8, args) {
            let proto = po(view_proto(it, TypedKind::U8));
            return Ok(Value::Obj(it.heap.alloc_obj(Obj::BufView {
                buf,
                off,
                len,
                kind: TypedKind::U8,
                pairs: Vec::new(),
                proto,
            })?));
        }
    }
    let bytes = match arg(args, 0) {
        Value::Undef => Vec::new(),
        v @ (Value::Num(_) | Value::Str(_) | Value::Bool(_) | Value::Null) => {
            vec![0; typed_len(&it.heap, v)?]
        }
        v => u8_src_items(it, v),
    };
    let proto = po(it.protos.uint8array);
    Ok(Value::Obj(it.heap.alloc_obj(Obj::Bytes {
        bytes,
        pairs: Vec::new(),
        proto,
    })?))
}

/// ArrayBuffer.isView(v): typed views and DataViews (not plain
/// arrays, buffers, or objects; buffer facades read as buffers).
fn n_buf_is_view(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let hit = match arg(args, 0) {
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::Bytes { .. } | Obj::Typed { .. } | Obj::DView { .. } | Obj::Big64 { .. } => true,
            Obj::BufView { proto, .. } => *proto != po(it.protos.buffer),
            _ => false,
        },
        _ => false,
    };
    Ok(Value::Bool(hit))
}

fn n_buf_ctor(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {    let n = match arg(args, 0) {
        Value::Undef => 0,
        v => typed_len(&it.heap, v)?,
    };
    let proto = po(it.protos.buffer);
    Ok(Value::Obj(it.heap.alloc_obj(Obj::Buf {
        bytes: vec![0; n],
        proto,
    })?))
}

/// Clamp [start,end) to [0,len]; negatives count from the end.
fn typed_range(len: usize, s: f64, e: f64) -> (usize, usize) {
    let lenf = len as f64;
    let norm = |x: f64| {
        if x.is_nan() {
            return 0;
        }
        let x = x.trunc();
        let x = if x < 0.0 { (lenf + x).max(0.0) } else { x.min(lenf) };
        x as usize
    };
    let (a, b) = (norm(s), norm(e));
    (a, b.max(a))
}

fn n_u8_set(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = u8_this(it, this, "set")?;
    let src = u8_src_items(it, arg(args, 0));
    let off = match arg(args, 1) {
        Value::Undef => 0,
        v => {
            let n = to_num(&it.heap, v).trunc();
            if n < 0.0 {
                return Err(err("Uint8Array.set offset out of bounds"));
            }
            n as usize
        }
    };
    match it.heap.obj(id) {
        Obj::Bytes { bytes, .. } if off + src.len() <= bytes.len() => {}
        Obj::BufView { len, kind, .. }
            if *kind == TypedKind::U8 && off + src.len() <= view_count(*kind, *len) => {}
        _ => return Err(err("Uint8Array.set source out of bounds")),
    }
    match it.heap.obj(id) {
        Obj::Bytes { .. } => {
            if let Obj::Bytes { bytes, .. } = it.heap.obj_mut(id) {
                bytes[off..off + src.len()].copy_from_slice(&src);
            }
        }
        Obj::BufView { buf, off: base, .. } => {
            let (buf, base) = (*buf, *base);
            if let Some(Obj::Buf { bytes, .. }) = it.heap.objs.get_mut(buf as usize) {
                if base + off + src.len() <= bytes.len() {
                    bytes[base + off..base + off + src.len()].copy_from_slice(&src);
                }
            }
        }
        _ => unreachable!(),
    }
    Ok(this)
}

fn n_u8_slice(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = u8_this(it, this, "slice")?;
    let (bytes, proto) = match it.heap.obj(id) {
        Obj::Bytes { bytes, proto, .. } => (bytes.clone(), *proto),
        Obj::BufView { buf, off, len, kind, proto, .. } => {
            let n = view_count(*kind, *len);
            let bpe = t_bpe(*kind);
            let out: Vec<u8> = (0..n)
                .map(|i| {
                    let at = off + i * bpe;
                    match kind {
                        TypedKind::I64 | TypedKind::U64 => {
                            view_read_u64(&it.heap, *buf, at).unwrap_or(0) as u8
                        }
                        kk => to_u8_num(view_read_num(&it.heap, *buf, at, *kk).unwrap_or(0.0)),
                    }
                })
                .collect();
            (out, *proto)
        }
        _ => unreachable!(),
    };
    let (a, b) = match (arg(args, 0), arg(args, 1)) {
        (Value::Undef, Value::Undef) => (0, bytes.len()),
        (s, Value::Undef) => typed_range(bytes.len(), to_num(&it.heap, s), bytes.len() as f64),
        (s, e) => typed_range(bytes.len(), to_num(&it.heap, s), to_num(&it.heap, e)),
    };
    Ok(Value::Obj(it.heap.alloc_obj(Obj::Bytes {
        bytes: bytes[a..b].to_vec(),
        pairs: Vec::new(),
        proto,
    })?))
}

fn n_u8_subarray(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    // Copy, not a live view (documented gap) - same observable bytes.
    n_u8_slice(it, this, args)
}

fn n_u8_join(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = u8_this(it, this, "join")?;
    let sep = match arg(args, 0) {
        Value::Undef => ",".to_string(),
        v => to_str(&it.heap, v),
    };
    let s = match it.heap.obj(id) {
        Obj::Bytes { bytes, .. } => bytes
            .iter()
            .map(|b| b.to_string())
            .collect::<Vec<_>>()
            .join(&sep),
        Obj::BufView { buf, off, len, kind, .. } => {
            let n = view_count(*kind, *len);
            let bpe = t_bpe(*kind);
            (0..n)
                .map(|i| {
                    let at = off + i * bpe;
                    match kind {
                        TypedKind::I64 | TypedKind::U64 => {
                            (view_read_u64(&it.heap, *buf, at).unwrap_or(0) as u8).to_string()
                        }
                        kk => to_u8_num(view_read_num(&it.heap, *buf, at, *kk).unwrap_or(0.0))
                            .to_string(),
                    }
                })
                .collect::<Vec<_>>()
                .join(&sep)
        }
        _ => unreachable!(),
    };
    Ok(Value::Str(it.heap.alloc_str(s)?))
}

fn n_u8_fill(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = u8_this(it, this, "fill")?;
    let b = to_u8(&it.heap, arg(args, 0));
    let len = match it.heap.obj(id) {
        Obj::Bytes { bytes, .. } => bytes.len(),
        Obj::BufView { len, kind, .. } => view_count(*kind, *len),
        _ => unreachable!(),
    };
    let (a, c) = match (arg(args, 1), arg(args, 2)) {
        (Value::Undef, Value::Undef) => (0, len),
        (s, Value::Undef) => typed_range(len, to_num(&it.heap, s), len as f64),
        (s, e) => typed_range(len, to_num(&it.heap, s), to_num(&it.heap, e)),
    };
    match it.heap.obj(id) {
        Obj::Bytes { .. } => {
            if let Obj::Bytes { bytes, .. } = it.heap.obj_mut(id) {
                bytes[a..c].fill(b);
            }
        }
        Obj::BufView { buf, off, len, kind, .. } => {
            let (buf, off, blen, kind) = (*buf, *off, *len, *kind);
            let bpe = t_bpe(kind);
            let n = view_count(kind, blen);
            // U8 live views are byte-packed: element i is byte off+i.
            if kind == TypedKind::U8 {
                if let Some(Obj::Buf { bytes, .. }) = it.heap.objs.get_mut(buf as usize) {
                    for i in a.min(n)..c.min(n) {
                        if off + i < bytes.len() {
                            bytes[off + i] = b;
                        }
                    }
                }
            } else {
                for i in a.min(n)..c.min(n) {
                    view_write_num(&mut it.heap, buf, off + i * bpe, kind, b as f64);
                }
            }
        }
        _ => unreachable!(),
    }
    Ok(this)
}

fn n_u8_index_of(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let id = u8_this(it, this, "indexOf")?;
    let b = to_u8(&it.heap, arg(args, 0));
    let from = match arg(args, 1) {
        Value::Undef => 0,
        v => {
            let n = to_num(&it.heap, v).trunc();
            if n <= 0.0 || n.is_nan() {
                0
            } else {
                n as usize
            }
        }
    };
    Ok(match it.heap.obj(id) {
        Obj::Bytes { bytes, .. } => Value::Num(
            bytes
                .iter()
                .skip(from)
                .position(|x| *x == b)
                .map(|i| (from + i) as f64)
                .unwrap_or(-1.0),
        ),
        Obj::BufView { buf, off, len, kind, .. } => {
            let n = view_count(*kind, *len);
            let bpe = t_bpe(*kind);
            let mut hit: Option<usize> = None;
            for i in from.min(n)..n {
                let at = off + i * bpe;
                let cur = match kind {
                    TypedKind::I64 | TypedKind::U64 => {
                        view_read_u64(&it.heap, *buf, at).unwrap_or(0) as u8
                    }
                    kk => to_u8_num(view_read_num(&it.heap, *buf, at, *kk).unwrap_or(0.0)),
                };
                if cur == b {
                    hit = Some(i);
                    break;
                }
            }
            Value::Num(hit.map(|i| i as f64).unwrap_or(-1.0))
        }
        _ => unreachable!(),
    })
}

// -- Typed statics: of / from -------------------------------------------------------
// `of` takes elements directly; `from` takes an array-like (strings feed
// chars, like V8) plus an optional map fn. Coercion matches the view.

/// Raw (pre-coercion) items of a `from` source.
fn from_raw(it: &mut Interp, v: Value) -> Result<Vec<Value>, JsError> {
    match v {
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::Arr { items, .. } => Ok(items.clone()),
            Obj::Bytes { bytes, .. } => {
                Ok(bytes.iter().map(|b| Value::Num(*b as f64)).collect())
            }
            Obj::Typed { elems, .. } => Ok(elems.iter().map(|e| Value::Num(*e)).collect()),
            Obj::BufView { buf, off, len, kind, .. } => {
                let (buf, off, len, kind) = (*buf, *off, *len, *kind);
                let n = view_count(kind, len);
                let bpe = t_bpe(kind);
                match kind {
                    TypedKind::I64 | TypedKind::U64 => {
                        let bits: Vec<u64> = (0..n)
                            .map(|i| view_read_u64(&it.heap, buf, off + i * bpe).unwrap_or(0))
                            .collect();
                        let mut out = Vec::with_capacity(n);
                        for b in bits {
                            let (neg, mag) = if kind == TypedKind::I64 {
                                bi_from_i64(b as i64)
                            } else {
                                bi_from_u64(b)
                            };
                            out.push(bi_alloc(it, neg, mag)?);
                        }
                        Ok(out)
                    }
                    kk => Ok((0..n)
                        .map(|i| {
                            Value::Num(
                                view_read_num(&it.heap, buf, off + i * bpe, kk).unwrap_or(0.0),
                            )
                        })
                        .collect()),
                }
            }
            Obj::Big64 { signed, elems, .. } => {
                let signed = *signed;
                let mut out = Vec::with_capacity(elems.len());
                for bits in elems.clone() {
                    let (neg, mag) = if signed {
                        bi_from_i64(bits as i64)
                    } else {
                        bi_from_u64(bits)
                    };
                    out.push(bi_alloc(it, neg, mag)?);
                }
                Ok(out)
            },
            Obj::Buf { bytes, .. } => {
                Ok(bytes.iter().map(|b| Value::Num(*b as f64)).collect())
            }
            _ => {
                let len = match get_prop(&it.heap, &it.protos, Value::Obj(id), "length") {
                    Ok(Value::Num(n)) if n > 0.0 => (n.floor() as usize).min(1 << 28),
                    _ => return Ok(Vec::new()),
                };
                let mut out = Vec::with_capacity(len);
                for i in 0..len {
                    out.push(get_prop(&it.heap, &it.protos, Value::Obj(id), &i.to_string())?);
                }
                Ok(out)
            }
        },
        Value::Str(id) => {
            let s = it.heap.get_str(id).to_string();
            let mut out = Vec::with_capacity(s.len());
            for c in s.chars() {
                out.push(Value::Str(it.heap.alloc_str(c.to_string())?));
            }
            Ok(out)
        }
        _ => Ok(Vec::new()),
    }
}

/// Shared `from` body: None = Uint8Array, Some(k) = that view.
fn typed_from(
    it: &mut Interp,
    kind: Option<TypedKind>,
    args: &[Value],
) -> Result<Value, JsError> {
    let raw = from_raw(it, arg(args, 0))?;
    let mapped: Vec<Value> = match arg(args, 1) {
        Value::Obj(mid)
            if matches!(it.heap.obj(mid), Obj::Func { .. } | Obj::Native { .. }) =>
        {
            let this_arg = arg(args, 2);
            let mut out = Vec::with_capacity(raw.len());
            for (i, v) in raw.into_iter().enumerate() {
                out.push(it.call_value(
                    Value::Obj(mid),
                    this_arg,
                    &[v, Value::Num(i as f64)],
                    None,
                )?);
            }
            out
        }
        _ => raw,
    };
    match kind {
        None => {
            let bytes = mapped.iter().map(|x| to_u8(&it.heap, *x)).collect();
            let proto = po(it.protos.uint8array);
            Ok(Value::Obj(it.heap.alloc_obj(Obj::Bytes {
                bytes,
                pairs: Vec::new(),
                proto,
            })?))
        }
        Some(k) => {
            let elems = mapped.iter().map(|x| t_write(k, to_num(&it.heap, *x))).collect();
            let proto = po(match k {
                TypedKind::U8 => it.protos.uint8array,
                TypedKind::I8 => it.protos.int8array,
                TypedKind::U8C => it.protos.uint8clampedarray,
                TypedKind::U16 => it.protos.uint16array,
                TypedKind::I16 => it.protos.int16array,
                TypedKind::U32 => it.protos.uint32array,
                TypedKind::I32 => it.protos.int32array,
                TypedKind::F32 => it.protos.float32array,
                TypedKind::F64 => it.protos.float64array,
                TypedKind::I64 => it.protos.bigint64array,
                TypedKind::U64 => it.protos.biguint64array,
            });
            Ok(Value::Obj(it.heap.alloc_obj(Obj::Typed {
                kind: k,
                elems,
                pairs: Vec::new(),
                proto,
            })?))
        }
    }
}

fn n_u8_of(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let bytes = args.iter().map(|x| to_u8(&it.heap, *x)).collect();
    let proto = po(it.protos.uint8array);
    Ok(Value::Obj(it.heap.alloc_obj(Obj::Bytes {
        bytes,
        pairs: Vec::new(),
        proto,
    })?))
}

fn n_u8_from(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    typed_from(it, None, args)
}

/// Shared `of` body for the non-u8 views.
fn t_of(it: &mut Interp, kind: TypedKind, args: &[Value]) -> Result<Value, JsError> {
    let elems = args.iter().map(|x| t_write(kind, to_num(&it.heap, *x))).collect();
    let proto = po(match kind {
        TypedKind::U8 => it.protos.uint8array,
        TypedKind::I8 => it.protos.int8array,
        TypedKind::U8C => it.protos.uint8clampedarray,
        TypedKind::U16 => it.protos.uint16array,
        TypedKind::I16 => it.protos.int16array,
        TypedKind::U32 => it.protos.uint32array,
        TypedKind::I32 => it.protos.int32array,
        TypedKind::F32 => it.protos.float32array,
        TypedKind::F64 => it.protos.float64array,
        TypedKind::I64 => it.protos.bigint64array,
        TypedKind::U64 => it.protos.biguint64array,
    });
    Ok(Value::Obj(it.heap.alloc_obj(Obj::Typed {
        kind,
        elems,
        pairs: Vec::new(),
        proto,
    })?))
}

fn n_i8_of(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    t_of(it, TypedKind::I8, a)
}
fn n_u8c_of(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    t_of(it, TypedKind::U8C, a)
}
fn n_u16_of(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    t_of(it, TypedKind::U16, a)
}
fn n_i16_of(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    t_of(it, TypedKind::I16, a)
}
fn n_u32_of(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    t_of(it, TypedKind::U32, a)
}
fn n_i32_of(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    t_of(it, TypedKind::I32, a)
}
fn n_f32_of(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    t_of(it, TypedKind::F32, a)
}
fn n_f64_of(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    t_of(it, TypedKind::F64, a)
}
fn n_i8_from(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    typed_from(it, Some(TypedKind::I8), a)
}
fn n_u8c_from(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    typed_from(it, Some(TypedKind::U8C), a)
}
fn n_u16_from(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    typed_from(it, Some(TypedKind::U16), a)
}
fn n_i16_from(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    typed_from(it, Some(TypedKind::I16), a)
}
fn n_u32_from(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    typed_from(it, Some(TypedKind::U32), a)
}
fn n_i32_from(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    typed_from(it, Some(TypedKind::I32), a)
}
fn n_f32_from(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    typed_from(it, Some(TypedKind::F32), a)
}
fn n_f64_from(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    typed_from(it, Some(TypedKind::F64), a)
}

fn n_buf_slice(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {    let (bytes, proto) = match this {
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::Buf { bytes, proto, .. } => (bytes.clone(), *proto),
            // Buffer facades slice their whole backing store.
            Obj::BufView { buf, proto, .. } if *proto == po(it.protos.buffer) => {
                match buf_live(&it.heap, *buf) {
                    Some(b) => (b.to_vec(), *proto),
                    None => (Vec::new(), *proto),
                }
            }
            _ => return Err(err("ArrayBuffer.slice needs an ArrayBuffer receiver")),
        },
        _ => return Err(err("ArrayBuffer.slice needs an ArrayBuffer receiver")),
    };
    let (a, b) = match (arg(args, 0), arg(args, 1)) {
        (Value::Undef, Value::Undef) => (0, bytes.len()),
        (s, Value::Undef) => typed_range(bytes.len(), to_num(&it.heap, s), bytes.len() as f64),
        (s, e) => typed_range(bytes.len(), to_num(&it.heap, s), to_num(&it.heap, e)),
    };
    Ok(Value::Obj(it.heap.alloc_obj(Obj::Buf {
        bytes: bytes[a..b].to_vec(),
        proto,
    })?))
}

// -- Other numeric views (Int8..Float64) -----------------------------------------
// Same copy semantics as Bytes: elements pre-coerced, one method set
// shared across kinds (the kind rides on the instance).

/// `this` as a Typed heap id with its kind (owned or live view).
fn t_this(it: &Interp, this: Value, name: &str) -> Result<(u32, TypedKind), JsError> {
    match this {
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::Typed { kind, .. } => Ok((id, *kind)),
            Obj::BufView { kind, .. }
                if !matches!(kind, TypedKind::U8 | TypedKind::I64 | TypedKind::U64) =>
            {
                Ok((id, *kind))
            }
            _ => Err(err(format!("typed array method {name} needs a typed array"))),
        },
        _ => Err(err(format!("typed array method {name} needs a typed array"))),
    }
}

/// Element source for view ctors: numbers coerce per kind; buffers
/// decode little-endian bytes (like V8 reinterpreting the store).
fn t_src_items(it: &Interp, kind: TypedKind, v: Value) -> Vec<f64> {
    let cv = |n: f64| t_write(kind, n);
    match v {
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::Arr { items, .. } => items.iter().map(|x| cv(to_num(&it.heap, *x))).collect(),
            Obj::Bytes { bytes, .. } => bytes.iter().map(|b| cv(*b as f64)).collect(),
            Obj::Typed { elems, .. } => elems.iter().map(|e| cv(*e)).collect(),
            // f64 can't hold u64 exactly past 2^53 (inherent precision loss,
            // same as Number(big) explicit conversion).
            Obj::Big64 { elems, .. } => elems.iter().map(|e| cv(*e as f64)).collect(),
            Obj::Buf { bytes, .. } => t_decode(kind, bytes),
            Obj::BufView { buf, off, len, kind: sk, .. } => {
                let n = view_count(*sk, *len);
                let bpe = t_bpe(*sk);
                (0..n)
                    .map(|i| {
                        let at = off + i * bpe;
                        match sk {
                            TypedKind::I64 | TypedKind::U64 => cv(
                                view_read_u64(&it.heap, *buf, at).unwrap_or(0) as f64,
                            ),
                            kk => cv(view_read_num(&it.heap, *buf, at, *kk).unwrap_or(0.0)),
                        }
                    })
                    .collect()
            },
            _ => t_len_items(it, kind, Value::Obj(id)),
        },
        _ => t_len_items(it, kind, v),
    }
}

fn t_len_items(it: &Interp, kind: TypedKind, v: Value) -> Vec<f64> {
    let len = match get_prop(&it.heap, &it.protos, v, "length") {
        Ok(Value::Num(n)) if n > 0.0 => (n.floor() as usize).min(1 << 28),
        _ => return Vec::new(),
    };
    let mut out = Vec::with_capacity(len);
    for i in 0..len {
        let key = i.to_string();
        let n = match get_prop(&it.heap, &it.protos, v, &key) {
            Ok(x) => to_num(&it.heap, x),
            Err(_) => f64::NAN,
        };
        out.push(t_write(kind, n));
    }
    out
}

/// Little-endian decode of raw bytes into elements (odd tails throw,
/// like V8's length-mismatch RangeError).
fn t_decode(kind: TypedKind, bytes: &[u8]) -> Vec<f64> {
    let bpe = t_bpe(kind);
    let mut out = Vec::with_capacity(bytes.len() / bpe);
    for w in bytes.chunks_exact(bpe) {
        let mut raw = [0u8; 8];
        raw[..bpe].copy_from_slice(w);
        let u = u64::from_le_bytes(raw);
        out.push(match kind {
            TypedKind::U8 => w[0] as f64,
            TypedKind::I8 => (w[0] as i8) as f64,
            TypedKind::U8C => t_write(TypedKind::U8C, w[0] as f64),
            TypedKind::U16 => (u as u16) as f64,
            TypedKind::I16 => (u as u16) as i16 as f64,
            TypedKind::U32 => (u as u32) as f64,
            TypedKind::I32 => (u as u32) as i32 as f64,
            TypedKind::F32 => f32::from_le_bytes([w[0], w[1], w[2], w[3]]) as f64,
            TypedKind::F64 => f64::from_le_bytes(w.try_into().unwrap_or([0; 8])),
            // I64/U64 never decode to f64 (callers use the u64 path).
            TypedKind::I64 | TypedKind::U64 => 0.0,
        });
    }
    out
}

/// Shared view constructor: length, source view/array, buffer (+ byte
/// offset/length), or empty. Buffer-backed forms (Buf/BufView) are live
/// views sharing the store; every other source copies. Buffer offsets
/// must align to the element size; odd buffer lengths throw (V8 parity).
fn t_ctor(it: &mut Interp, kind: TypedKind, proto: u32, args: &[Value]) -> Result<Value, JsError> {
    if let Value::Obj(src) = arg(args, 0) {
        if let Ok(Some((buf, off, len))) = view_window(it, src, kind, args) {
            return Ok(Value::Obj(it.heap.alloc_obj(Obj::BufView {
                buf,
                off,
                len,
                kind,
                pairs: Vec::new(),
                proto: po(proto),
            })?));
        }
        if matches!(
            it.heap.obj(src),
            Obj::Buf { .. } | Obj::BufView { .. }
        ) {
            // view_window errored (misaligned/OOB/mismatch): propagate.
            view_window(it, src, kind, args)?;
        }
    }
    let elems = match arg(args, 0) {
        Value::Undef => Vec::new(),
        v @ (Value::Num(_) | Value::Str(_) | Value::Bool(_) | Value::Null) => {
            vec![t_write(kind, 0.0); typed_len(&it.heap, v)?]
        }
        Value::Obj(id) if matches!(it.heap.obj(id), Obj::Buf { .. }) => {
            let bytes = match it.heap.obj(id) {
                Obj::Buf { bytes, .. } => bytes.clone(),
                _ => unreachable!(),
            };
            let bpe = t_bpe(kind);
            let off = match arg(args, 1) {
                Value::Undef => 0,
                v => {
                    let n = to_num(&it.heap, v).trunc();
                    if n < 0.0 || n.fract() != 0.0 || !(n as usize).is_multiple_of(bpe) {
                        return Err(err("typed array buffer offset misaligned"));
                    }
                    n as usize
                }
            };
            if off > bytes.len() || bytes.len() % bpe != 0 {
                return Err(err("typed array buffer length mismatch"));
            }
            let mut els = t_decode(kind, &bytes[off..]);
            if !matches!(arg(args, 2), Value::Undef) {
                let want = typed_len(&it.heap, arg(args, 2))?;
                if want > els.len() {
                    return Err(err("typed array length out of range"));
                }
                els.truncate(want);
            }
            els
        }
        v => t_src_items(it, kind, v),
    };
    Ok(Value::Obj(it.heap.alloc_obj(Obj::Typed {
        kind,
        elems,
        pairs: Vec::new(),
        proto: po(proto),
    })?))
}

fn n_i8_ctor(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    t_ctor(it, TypedKind::I8, it.protos.int8array, a)
}
fn n_u8c_ctor(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    t_ctor(it, TypedKind::U8C, it.protos.uint8clampedarray, a)
}
fn n_u16_ctor(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    t_ctor(it, TypedKind::U16, it.protos.uint16array, a)
}
fn n_i16_ctor(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    t_ctor(it, TypedKind::I16, it.protos.int16array, a)
}
fn n_u32_ctor(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    t_ctor(it, TypedKind::U32, it.protos.uint32array, a)
}
fn n_i32_ctor(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    t_ctor(it, TypedKind::I32, it.protos.int32array, a)
}
fn n_f32_ctor(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    t_ctor(it, TypedKind::F32, it.protos.float32array, a)
}
fn n_f64_ctor(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    t_ctor(it, TypedKind::F64, it.protos.float64array, a)
}

fn n_t_set(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let (id, kind) = t_this(it, this, "set")?;
    let src: Vec<f64> = match arg(args, 0) {
        Value::Obj(sid) => match it.heap.obj(sid) {
            Obj::Arr { items, .. } => items.iter().map(|x| t_write(kind, to_num(&it.heap, *x))).collect(),
            Obj::Bytes { bytes, .. } => bytes.iter().map(|b| t_write(kind, *b as f64)).collect(),
            Obj::Typed { elems, .. } => elems.iter().map(|e| t_write(kind, *e)).collect(),
            Obj::Big64 { elems, .. } => elems.iter().map(|e| t_write(kind, *e as f64)).collect(),
            Obj::Buf { bytes, .. } => t_decode(kind, bytes),
            Obj::BufView { buf, off, len, kind: sk, .. } => {
                let n = view_count(*sk, *len);
                let bpe = t_bpe(*sk);
                (0..n)
                    .map(|i| {
                        let at = off + i * bpe;
                        match sk {
                            TypedKind::I64 | TypedKind::U64 => t_write(
                                kind,
                                view_read_u64(&it.heap, *buf, at).unwrap_or(0) as f64,
                            ),
                            kk => t_write(
                                kind,
                                view_read_num(&it.heap, *buf, at, *kk).unwrap_or(0.0),
                            ),
                        }
                    })
                    .collect()
            }
            _ => t_len_items(it, kind, Value::Obj(sid)),
        },
        v => t_len_items(it, kind, v),
    };
    let off = match arg(args, 1) {
        Value::Undef => 0,
        v => {
            let n = to_num(&it.heap, v).trunc();
            if n < 0.0 {
                return Err(err("typed array set offset out of bounds"));
            }
            n as usize
        }
    };
    match it.heap.obj(id) {
        Obj::Typed { elems, .. } if off + src.len() <= elems.len() => {}
        Obj::BufView { len, kind: dk, .. }
            if off + src.len() <= view_count(*dk, *len) => {}
        _ => return Err(err("typed array set source out of bounds")),
    }
    match it.heap.obj(id) {
        Obj::Typed { .. } => {
            if let Obj::Typed { elems, .. } = it.heap.obj_mut(id) {
                elems[off..off + src.len()].copy_from_slice(&src);
            }
        }
        Obj::BufView { buf, off: base, kind: dk, .. } => {
            let (buf, base, dk) = (*buf, *base, *dk);
            let bpe = t_bpe(dk);
            for (i, e) in src.iter().enumerate() {
                view_write_num(&mut it.heap, buf, base + (off + i) * bpe, dk, *e);
            }
        }
        _ => unreachable!(),
    }
    Ok(this)
}

fn t_slice_vec(it: &Interp, id: u32, args: &[Value]) -> Result<Vec<f64>, JsError> {
    let elems: Vec<f64> = match it.heap.obj(id) {
        Obj::Typed { elems, .. } => elems.clone(),
        Obj::BufView { buf, off, len, kind, .. } => {
            let n = view_count(*kind, *len);
            let bpe = t_bpe(*kind);
            (0..n)
                .map(|i| view_read_num(&it.heap, *buf, off + i * bpe, *kind).unwrap_or(0.0))
                .collect()
        }
        _ => unreachable!(),
    };
    let (a, b) = match (arg(args, 0), arg(args, 1)) {
        (Value::Undef, Value::Undef) => (0, elems.len()),
        (s, Value::Undef) => typed_range(elems.len(), to_num(&it.heap, s), elems.len() as f64),
        (s, e) => typed_range(elems.len(), to_num(&it.heap, s), to_num(&it.heap, e)),
    };
    Ok(elems[a..b].to_vec())
}

fn n_t_slice(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let (id, kind) = t_this(it, this, "slice")?;
    let proto = match it.heap.obj(id) {
        Obj::Typed { proto, .. } => *proto,
        Obj::BufView { proto, .. } => *proto,
        _ => unreachable!(),
    };
    let out = t_slice_vec(it, id, args)?;
    Ok(Value::Obj(it.heap.alloc_obj(Obj::Typed {
        kind,
        elems: out,
        pairs: Vec::new(),
        proto,
    })?))
}

fn n_t_subarray(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    // Copy, not a live view (documented gap) - same observable bytes.
    n_t_slice(it, this, args)
}

fn n_t_join(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let (id, _) = t_this(it, this, "join")?;
    let sep = match arg(args, 0) {
        Value::Undef => ",".to_string(),
        v => to_str(&it.heap, v),
    };
    let s = match it.heap.obj(id) {
        Obj::Typed { elems, .. } => elems
            .iter()
            .map(|e| to_str(&it.heap, Value::Num(*e)))
            .collect::<Vec<_>>()
            .join(&sep),
        Obj::BufView { buf, off, len, kind, .. } => {
            let n = view_count(*kind, *len);
            let bpe = t_bpe(*kind);
            (0..n)
                .map(|i| {
                    to_str(
                        &it.heap,
                        Value::Num(
                            view_read_num(&it.heap, *buf, off + i * bpe, *kind).unwrap_or(0.0),
                        ),
                    )
                })
                .collect::<Vec<_>>()
                .join(&sep)
        }
        _ => unreachable!(),
    };
    Ok(Value::Str(it.heap.alloc_str(s)?))
}

fn n_t_fill(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let (id, kind) = t_this(it, this, "fill")?;
    let ne = t_write(kind, to_num(&it.heap, arg(args, 0)));
    let len = match it.heap.obj(id) {
        Obj::Typed { elems, .. } => elems.len(),
        Obj::BufView { len, kind, .. } => view_count(*kind, *len),
        _ => unreachable!(),
    };
    let (a, c) = match (arg(args, 1), arg(args, 2)) {
        (Value::Undef, Value::Undef) => (0, len),
        (s, Value::Undef) => typed_range(len, to_num(&it.heap, s), len as f64),
        (s, e) => typed_range(len, to_num(&it.heap, s), to_num(&it.heap, e)),
    };
    match it.heap.obj(id) {
        Obj::Typed { .. } => {
            if let Obj::Typed { elems, .. } = it.heap.obj_mut(id) {
                elems[a..c].fill(ne);
            }
        }
        Obj::BufView { buf, off, kind, .. } => {
            let (buf, off, kind) = (*buf, *off, *kind);
            let bpe = t_bpe(kind);
            for i in a.min(len)..c.min(len) {
                view_write_num(&mut it.heap, buf, off + i * bpe, kind, ne);
            }
        }
        _ => unreachable!(),
    }
    Ok(this)
}

fn n_t_index_of(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let (id, kind) = t_this(it, this, "indexOf")?;
    let ne = t_write(kind, to_num(&it.heap, arg(args, 0)));
    let from = match arg(args, 1) {
        Value::Undef => 0,
        v => {
            let n = to_num(&it.heap, v).trunc();
            if n <= 0.0 || n.is_nan() {
                0
            } else {
                n as usize
            }
        }
    };
    Ok(match it.heap.obj(id) {
        Obj::Typed { elems, .. } => Value::Num(
            elems
                .iter()
                .skip(from)
                .position(|x| *x == ne)
                .map(|i| (from + i) as f64)
                .unwrap_or(-1.0),
        ),
        Obj::BufView { buf, off, len, kind, .. } => {
            let n = view_count(*kind, *len);
            let bpe = t_bpe(*kind);
            let mut hit: Option<usize> = None;
            for i in from.min(n)..n {
                let e = view_read_num(&it.heap, *buf, off + i * bpe, *kind).unwrap_or(0.0);
                if e == ne {
                    hit = Some(i);
                    break;
                }
            }
            Value::Num(hit.map(|i| i as f64).unwrap_or(-1.0))
        }
        _ => unreachable!(),
    })
}

// -- DataView --------------------------------------------------------------------
// Live window onto a Buf (buf id + byte off/len); accessors translate per
// access through the backing store, so views sharing one Buf see each
// other's writes. From owned sources the Buf is a fresh copy.

fn dv_this(it: &Interp, this: Value, name: &str) -> Result<u32, JsError> {
    match this {
        Value::Obj(id) if matches!(it.heap.obj(id), Obj::DView { .. }) => Ok(id),
        _ => Err(err(format!("DataView.{name} needs a DataView receiver"))),
    }
}

/// (buf, absolute byte, view len, little-endian) for an accessor call.
fn dv_args(it: &Interp, id: u32, args: &[Value]) -> Result<(u32, usize, usize, bool), JsError> {
    let (buf, off, len) = match it.heap.obj(id) {
        Obj::DView { buf, off, len, .. } => (*buf, *off, *len),
        _ => unreachable!(),
    };
    let at = match to_num(&it.heap, arg(args, 0)).trunc() {
        n if n < 0.0 => return Err(err("DataView offset out of bounds")),
        n => n as usize,
    };
    let le = truthy(&it.heap, arg(args, 1));
    Ok((buf, off + at, len, le))
}

fn dv_rel(at_abs: usize, off: usize, len: usize, size: usize) -> Result<(), JsError> {
    let rel = at_abs.saturating_sub(off);
    if rel + size <= len {
        Ok(())
    } else {
        Err(err("DataView offset out of bounds"))
    }
}

fn dv_need(bytes: &[u8], at: usize, size: usize) -> Result<(), JsError> {
    if at + size <= bytes.len() {
        Ok(())
    } else {
        Err(err("DataView offset out of bounds"))
    }
}

fn n_dv_ctor(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    // Shared base when the source is already buffer-backed (live).
    let shared: Option<(u32, usize, usize)> = match arg(args, 0) {
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::Buf { bytes, .. } => Some((id, 0, bytes.len())),
            Obj::BufView { buf, off, len, .. } => Some((*buf, *off, *len)),
            _ => None,
        },
        _ => None,
    };
    let (buf, base, avail) = match shared {
        Some(t) => t,
        None => {
            let bytes = match arg(args, 0) {
                Value::Obj(id) => match it.heap.obj(id) {
                    Obj::Bytes { bytes, .. } => bytes.clone(),
                    Obj::Typed { elems, kind, .. } => {
                        let mut out = Vec::with_capacity(elems.len() * t_bpe(*kind));
                        for e in elems {
                            dv_push(&mut out, *kind, *e);
                        }
                        out
                    }
                    Obj::Big64 { elems, .. } => {
                        let mut out = Vec::with_capacity(elems.len() * 8);
                        for e in elems {
                            out.extend_from_slice(&e.to_le_bytes());
                        }
                        out
                    }
                    Obj::Buf { bytes, .. } => bytes.clone(),
                    Obj::BufView { buf, off, len, .. } => {
                        match buf_live(&it.heap, *buf) {
                            Some(b) => b
                                .get(*off..off + len)
                                .unwrap_or(&[])
                                .to_vec(),
                            None => Vec::new(),
                        }
                    }
                    _ => return Err(err("DataView needs an ArrayBuffer")),
                },
                _ => return Err(err("DataView needs an ArrayBuffer")),
            };
            let proto = po(it.protos.buffer);
            let b = it.heap.alloc_obj(Obj::Buf { bytes, proto })?;
            let blen = match it.heap.obj(b) {
                Obj::Buf { bytes, .. } => bytes.len(),
                _ => unreachable!(),
            };
            (b, 0, blen)
        }
    };
    let off = match arg(args, 1) {
        Value::Undef => 0,
        v => match to_num(&it.heap, v).trunc() {
            n if n < 0.0 => return Err(err("DataView offset out of bounds")),
            n => n as usize,
        },
    };
    if off > avail {
        return Err(err("DataView offset out of bounds"));
    }
    let mut len = avail - off;
    if !matches!(arg(args, 2), Value::Undef) {
        let want = typed_len(&it.heap, arg(args, 2))?;
        if want > len {
            return Err(err("DataView length out of range"));
        }
        len = want;
    }
    let proto = po(it.protos.dataview);
    Ok(Value::Obj(it.heap.alloc_obj(Obj::DView {
        buf,
        off: base + off,
        len,
        proto,
    })?))
}

/// Little-endian encode of one element (for DataView-over-view; the
/// bundle path this serves).
fn dv_push(out: &mut Vec<u8>, kind: TypedKind, e: f64) {
    match kind {
        TypedKind::U8 => out.push(to_u8_num(e)),
        TypedKind::I8 => out.push(e as i8 as u8),
        TypedKind::U8C => out.push(e as u8),
        TypedKind::U16 | TypedKind::I16 => out.extend_from_slice(&(e as i16 as u16).to_le_bytes()),
        TypedKind::U32 | TypedKind::I32 => out.extend_from_slice(&(e as i32 as u32).to_le_bytes()),
        TypedKind::F32 => out.extend_from_slice(&(e as f32).to_le_bytes()),
        TypedKind::F64 => out.extend_from_slice(&e.to_le_bytes()),
        // Big64 views never flow through here (u64 path in the ctor).
        TypedKind::I64 | TypedKind::U64 => out.extend_from_slice(&0u64.to_le_bytes()),
    }
}

fn dv_get(it: &mut Interp, this: Value, args: &[Value], size: usize, name: &str) -> Result<Value, JsError> {
    let id = dv_this(it, this, name)?;
    let (buf, at, vlen, le) = dv_args(it, id, args)?;
    let (voff, _) = match it.heap.obj(id) {
        Obj::DView { off, .. } => (*off, 0),
        _ => unreachable!(),
    };
    dv_rel(at, voff, vlen, size)?;
    let bytes = match buf_live(&it.heap, buf) {
        Some(b) => b,
        None => return Err(err("DataView offset out of bounds")),
    };
    dv_need(bytes, at, size)?;
    let w = &bytes[at..at + size];
    Ok(Value::Num(match (name, size) {
        (_, 1) => w[0] as f64,
        (_, 2) if le => u16::from_le_bytes([w[0], w[1]]) as f64,
        (_, 2) => u16::from_be_bytes([w[0], w[1]]) as f64,
        (_, 4) if name.starts_with("getFloat") => f32::from_le_bytes([w[0], w[1], w[2], w[3]]) as f64,
        (_, 4) if le => u32::from_le_bytes([w[0], w[1], w[2], w[3]]) as f64,
        (_, 4) => {
            if name.starts_with("getFloat") {
                f32::from_be_bytes([w[0], w[1], w[2], w[3]]) as f64
            } else {
                u32::from_be_bytes([w[0], w[1], w[2], w[3]]) as f64
            }
        }
        (_, 8) if le => f64::from_le_bytes(w.try_into().unwrap_or([0; 8])),
        (_, 8) => f64::from_be_bytes(w.try_into().unwrap_or([0; 8])),
        _ => unreachable!(),
    }))
}

fn n_dv_get_u8(it: &mut Interp, t: Value, a: &[Value]) -> Result<Value, JsError> {
    dv_get(it, t, a, 1, "getUint8")
}
fn n_dv_get_u16(it: &mut Interp, t: Value, a: &[Value]) -> Result<Value, JsError> {
    dv_get(it, t, a, 2, "getUint16")
}
fn n_dv_get_u32(it: &mut Interp, t: Value, a: &[Value]) -> Result<Value, JsError> {
    dv_get(it, t, a, 4, "getUint32")
}
fn n_dv_get_i8(it: &mut Interp, t: Value, a: &[Value]) -> Result<Value, JsError> {
    let r = dv_get(it, t, a, 1, "getInt8")?;
    Ok(match r {
        Value::Num(n) if n >= 128.0 => Value::Num(n - 256.0),
        _ => r,
    })
}
fn n_dv_get_i16(it: &mut Interp, t: Value, a: &[Value]) -> Result<Value, JsError> {
    let r = dv_get(it, t, a, 2, "getInt16")?;
    Ok(match r {
        Value::Num(n) if n >= 32768.0 => Value::Num(n - 65536.0),
        _ => r,
    })
}
fn n_dv_get_i32(it: &mut Interp, t: Value, a: &[Value]) -> Result<Value, JsError> {
    let r = dv_get(it, t, a, 4, "getInt32")?;
    Ok(match r {
        Value::Num(n) if n >= 2147483648.0 => Value::Num(n - 4294967296.0),
        _ => r,
    })
}
fn n_dv_get_f32(it: &mut Interp, t: Value, a: &[Value]) -> Result<Value, JsError> {
    dv_get(it, t, a, 4, "getFloat32")
}
fn n_dv_get_f64(it: &mut Interp, t: Value, a: &[Value]) -> Result<Value, JsError> {
    dv_get(it, t, a, 8, "getFloat64")
}

fn dv_set(it: &mut Interp, this: Value, args: &[Value], size: usize, name: &str) -> Result<Value, JsError> {
    let id = dv_this(it, this, name)?;
    let (buf, vlen, off) = match it.heap.obj(id) {
        Obj::DView { buf, len, off, .. } => (*buf, *len, *off),
        _ => unreachable!(),
    };
    let rel = match to_num(&it.heap, arg(args, 0)).trunc() {
        n if n < 0.0 => return Err(err("DataView offset out of bounds")),
        n => n as usize,
    };
    if rel + size > vlen {
        return Err(err("DataView offset out of bounds"));
    }
    let at = off + rel;
    let le = truthy(&it.heap, arg(args, 2));
    let n = to_num(&it.heap, arg(args, 1));
    let enc: Vec<u8> = match (name, size) {
        (_, 1) => vec![to_u8_num(n)],
        (_, 2) if le => ((n as i32 as u16).to_le_bytes()).to_vec(),
        (_, 2) => ((n as i32 as u16).to_be_bytes()).to_vec(),
        (_, 4) if name.starts_with("setFloat") => {
            if le {
                (n as f32).to_le_bytes().to_vec()
            } else {
                (n as f32).to_be_bytes().to_vec()
            }
        }
        (_, 4) if le => (n as i64 as u32).to_le_bytes().to_vec(),
        (_, 4) => (n as i64 as u32).to_be_bytes().to_vec(),
        (_, 8) => {
            if le {
                n.to_le_bytes().to_vec()
            } else {
                n.to_be_bytes().to_vec()
            }
        }
        _ => unreachable!(),
    };
    match it.heap.objs.get_mut(buf as usize) {
        Some(Obj::Buf { bytes, .. }) if at + size <= bytes.len() => {
            bytes[at..at + size].copy_from_slice(&enc);
            Ok(Value::Undef)
        }
        _ => Err(err("DataView offset out of bounds")),
    }
}

fn n_dv_set_u8(it: &mut Interp, t: Value, a: &[Value]) -> Result<Value, JsError> {
    dv_set(it, t, a, 1, "setUint8")
}
fn n_dv_set_u16(it: &mut Interp, t: Value, a: &[Value]) -> Result<Value, JsError> {
    dv_set(it, t, a, 2, "setUint16")
}
fn n_dv_set_u32(it: &mut Interp, t: Value, a: &[Value]) -> Result<Value, JsError> {
    dv_set(it, t, a, 4, "setUint32")
}
fn n_dv_set_i8(it: &mut Interp, t: Value, a: &[Value]) -> Result<Value, JsError> {
    dv_set(it, t, a, 1, "setInt8")
}
fn n_dv_set_i16(it: &mut Interp, t: Value, a: &[Value]) -> Result<Value, JsError> {
    dv_set(it, t, a, 2, "setInt16")
}
fn n_dv_set_i32(it: &mut Interp, t: Value, a: &[Value]) -> Result<Value, JsError> {
    dv_set(it, t, a, 4, "setInt32")
}
fn n_dv_set_f32(it: &mut Interp, t: Value, a: &[Value]) -> Result<Value, JsError> {
    dv_set(it, t, a, 4, "setFloat32")
}
fn n_dv_set_f64(it: &mut Interp, t: Value, a: &[Value]) -> Result<Value, JsError> {
    dv_set(it, t, a, 8, "setFloat64")
}

// -- BigInt ------------------------------------------------------------------------
// Boxed primitive (Obj::BigInt): sign + little-endian base-2^32 magnitude,
// canonical (no leading zero limbs; zero is neg:false + empty mag, so field
// equality is value equality). Out of scope (one line each): `123n` literal
// syntax (lexer-level; BigInt("10n") rejects the `n` like V8), BigInt.prototype
// extras beyond toString/valueOf, `new BigInt()` throwing (all natives here
// are callable), Object(1n) boxing (passes the primitive through).

/// DoS cap on bigint width, in bits: schoolbook mul/div stay tractable and
/// hostile shifts/pows fail fast instead of hanging the page.
const BI_MAX_BITS: usize = 1 << 20;

fn bi_is_zero(mag: &[u32]) -> bool {
    mag.iter().all(|&w| w == 0)
}

/// Strip leading zero limbs; returns the canonical sign (zero is never
/// negative). Cheap belt-and-braces: every op maintains canonical form.
fn bi_norm(neg: bool, mag: &mut Vec<u32>) -> bool {
    while mag.last() == Some(&0) {
        mag.pop();
    }
    neg && !mag.is_empty()
}

fn is_big(h: &Heap, v: Value) -> bool {
    matches!(v, Value::Obj(id) if matches!(h.obj(id), Obj::BigInt { .. }))
}

/// Boxed BigInt payload, cloned (clone-then-writeback like the typed-array
/// neighbors: callers compute on the clone, then alloc the result).
fn bi_val(h: &Heap, v: Value) -> Option<(bool, Vec<u32>)> {
    match v {
        Value::Obj(id) => match h.obj(id) {
            Obj::BigInt { neg, mag, .. } => Some((*neg, mag.clone())),
            _ => None,
        },
        _ => None,
    }
}

/// Alloc a canonical boxed BigInt under BigInt.prototype.
fn bi_alloc_hp(
    h: &mut Heap,
    protos: &Protos,
    neg: bool,
    mut mag: Vec<u32>,
) -> Result<Value, JsError> {
    let neg = bi_norm(neg, &mut mag);
    let proto = po(protos.bigint);
    Ok(Value::Obj(h.alloc_obj(Obj::BigInt { neg, mag, proto })?))
}

fn bi_alloc(it: &mut Interp, neg: bool, mag: Vec<u32>) -> Result<Value, JsError> {
    bi_alloc_hp(&mut it.heap, &it.protos, neg, mag)
}

fn bi_add_small(mag: &mut Vec<u32>, d: u32) {
    let mut c = d as u64;
    for w in mag.iter_mut() {
        if c == 0 {
            break;
        }
        let s = *w as u64 + c;
        *w = s as u32;
        c = s >> 32;
    }
    if c > 0 {
        mag.push(c as u32);
    }
}

fn bi_mul_small(mag: &mut Vec<u32>, d: u32) {
    if d == 0 {
        mag.clear();
        return;
    }
    if d == 1 || mag.is_empty() {
        return;
    }
    let mut c = 0u64;
    for w in mag.iter_mut() {
        let p = *w as u64 * d as u64 + c;
        *w = p as u32;
        c = p >> 32;
    }
    if c > 0 {
        mag.push(c as u32);
    }
}

/// In-place divide by a small radix; returns the remainder.
fn bi_divmod_small(mag: &mut Vec<u32>, d: u32) -> u32 {
    let mut r = 0u64;
    for w in mag.iter_mut().rev() {
        let cur = (r << 32) | *w as u64;
        *w = (cur / d as u64) as u32;
        r = cur % d as u64;
    }
    while mag.last() == Some(&0) {
        mag.pop();
    }
    r as u32
}

fn bi_inc(mag: &mut Vec<u32>) {
    bi_add_small(mag, 1);
}

fn bi_dec(mag: &mut Vec<u32>) {
    // Canonical nonzero input; trims so one step past zero comes back empty.
    for w in mag.iter_mut() {
        if *w != 0 {
            *w -= 1;
            break;
        }
        *w = u32::MAX;
    }
    while mag.last() == Some(&0) {
        mag.pop();
    }
}

/// (neg, mag) +/- 1 for ++/-- (canonical in, canonical out).
fn bi_step(neg: bool, mag: Vec<u32>, up: bool) -> (bool, Vec<u32>) {
    if bi_is_zero(&mag) {
        return if up {
            (false, vec![1])
        } else {
            (true, vec![1])
        };
    }
    let mut m = mag;
    if neg != up {
        bi_inc(&mut m);
        (neg, m)
    } else {
        bi_dec(&mut m);
        (if bi_is_zero(&m) { false } else { neg }, m)
    }
}

fn bi_cmp_mag(a: &[u32], b: &[u32]) -> std::cmp::Ordering {
    // Canonical inputs: length decides, then most-significant limb first.
    if a.len() != b.len() {
        return a.len().cmp(&b.len());
    }
    for (&x, &y) in a.iter().rev().zip(b.iter().rev()) {
        if x != y {
            return x.cmp(&y);
        }
    }
    std::cmp::Ordering::Equal
}

fn bi_cmp(an: bool, a: &[u32], bn: bool, b: &[u32]) -> std::cmp::Ordering {
    use std::cmp::Ordering::*;
    if bi_is_zero(a) && bi_is_zero(b) {
        return Equal;
    }
    if an != bn {
        return if an { Less } else { Greater };
    }
    let o = bi_cmp_mag(a, b);
    if an { o.reverse() } else { o }
}

fn rel_holds(op: &str, o: std::cmp::Ordering) -> bool {
    use std::cmp::Ordering::*;
    matches!(
        (op, o),
        ("<", Less) | ("<=", Less | Equal) | (">", Greater) | (">=", Greater | Equal)
    )
}

fn bi_add_mag(a: &[u32], b: &[u32]) -> Vec<u32> {
    let mut out = Vec::with_capacity(a.len().max(b.len()) + 1);
    let mut c = 0u64;
    for i in 0..a.len().max(b.len()) {
        let s = a.get(i).copied().unwrap_or(0) as u64 + b.get(i).copied().unwrap_or(0) as u64 + c;
        out.push(s as u32);
        c = s >> 32;
    }
    if c > 0 {
        out.push(c as u32);
    }
    out
}

/// `a - b` with `a >= b` (both canonical); result canonical.
fn bi_sub_mag(a: &[u32], b: &[u32]) -> Vec<u32> {
    let mut out = Vec::with_capacity(a.len());
    let mut borrow = 0i64;
    for i in 0..a.len() {
        let d = a[i] as i64 - b.get(i).copied().unwrap_or(0) as i64 - borrow;
        if d < 0 {
            out.push((d + 0x1_0000_0000) as u32);
            borrow = 1;
        } else {
            out.push(d as u32);
            borrow = 0;
        }
    }
    while out.last() == Some(&0) {
        out.pop();
    }
    out
}

fn bi_add(an: bool, a: &[u32], bn: bool, b: &[u32]) -> (bool, Vec<u32>) {
    if bi_is_zero(a) {
        return (bn, b.to_vec());
    }
    if bi_is_zero(b) {
        return (an, a.to_vec());
    }
    if an == bn {
        (an, bi_add_mag(a, b))
    } else {
        match bi_cmp_mag(a, b) {
            std::cmp::Ordering::Equal => (false, Vec::new()),
            std::cmp::Ordering::Greater => (an, bi_sub_mag(a, b)),
            std::cmp::Ordering::Less => (bn, bi_sub_mag(b, a)),
        }
    }
}

fn bi_bit_len(mag: &[u32]) -> usize {
    let mut n = mag.len() * 32;
    if let Some(&top) = mag.last() {
        n -= top.leading_zeros() as usize;
    }
    n
}

/// Magnitude product, width-capped (schoolbook is O(n^2): hostile widths
/// fail fast instead of hanging the page).
fn bi_mul_mag(a: &[u32], b: &[u32]) -> Result<Vec<u32>, JsError> {
    if bi_is_zero(a) || bi_is_zero(b) {
        return Ok(Vec::new());
    }
    if bi_bit_len(a) + bi_bit_len(b) > BI_MAX_BITS + 64 {
        return Err(err("Maximum BigInt size exceeded"));
    }
    let mut out = vec![0u32; a.len() + b.len()];
    for (i, &x) in a.iter().enumerate() {
        if x == 0 {
            continue;
        }
        let mut carry = 0u64;
        for (j, &y) in b.iter().enumerate() {
            let cur = out[i + j] as u64 + x as u64 * y as u64 + carry;
            out[i + j] = cur as u32;
            carry = cur >> 32;
        }
        let mut k = i + b.len();
        while carry > 0 {
            let cur = out[k] as u64 + carry;
            out[k] = cur as u32;
            carry = cur >> 32;
            k += 1;
        }
    }
    while out.last() == Some(&0) {
        out.pop();
    }
    Ok(out)
}

fn bi_shl1(mag: &mut Vec<u32>) {
    let mut c = 0u32;
    for w in mag.iter_mut() {
        let n = (*w << 1) | c;
        c = *w >> 31;
        *w = n;
    }
    if c > 0 {
        mag.push(c);
    }
}

/// Long division on magnitudes (restoring, bit-by-bit): scraper operands
/// are tiny and obvious correctness beats clever here. `b` must be nonzero.
fn bi_divmod_mag(a: &[u32], b: &[u32]) -> (Vec<u32>, Vec<u32>) {
    if bi_cmp_mag(a, b) == std::cmp::Ordering::Less {
        return (Vec::new(), a.to_vec());
    }
    let nbits = bi_bit_len(a);
    let mut quo = vec![0u32; a.len()];
    let mut rem: Vec<u32> = Vec::new();
    for i in (0..nbits).rev() {
        bi_shl1(&mut rem);
        if a[i / 32] >> (i % 32) & 1 == 1 {
            bi_add_small(&mut rem, 1);
        }
        if bi_cmp_mag(&rem, b) != std::cmp::Ordering::Less {
            rem = bi_sub_mag(&rem, b);
            quo[i / 32] |= 1 << (i % 32);
        }
    }
    while quo.last() == Some(&0) {
        quo.pop();
    }
    (quo, rem)
}

fn bi_shl_mag(a: &[u32], k: usize) -> Vec<u32> {
    if bi_is_zero(a) {
        return Vec::new();
    }
    let (word, bit) = (k / 32, k % 32);
    let mut out = vec![0u32; word];
    if bit == 0 {
        out.extend_from_slice(a);
    } else {
        let mut c = 0u32;
        for &w in a {
            out.push((w << bit) | c);
            c = w >> (32 - bit);
        }
        if c > 0 {
            out.push(c);
        }
    }
    out
}

/// Magnitude shift right; the flag reports dropped nonzero bits so the
/// caller can round floor for negative operands (arithmetic `>>`).
fn bi_shr_mag(a: &[u32], k: usize) -> (Vec<u32>, bool) {
    let (word, bit) = (k / 32, k % 32);
    if word >= a.len() {
        return (Vec::new(), !bi_is_zero(a));
    }
    let mut out = Vec::with_capacity(a.len() - word);
    if bit == 0 {
        out.extend_from_slice(&a[word..]);
    } else {
        for i in word..a.len() {
            out.push(a[i] >> bit | a.get(i + 1).copied().unwrap_or(0) << (32 - bit));
        }
    }
    let mut lost = a[..word].iter().any(|&w| w != 0);
    if bit != 0 {
        if let Some(&w) = a.get(word) {
            lost |= w & (u32::MAX >> (32 - bit)) != 0;
        }
    }
    while out.last() == Some(&0) {
        out.pop();
    }
    (out, lost)
}

fn bi_pow_mag(base: &[u32], exp: &[u32]) -> Result<Vec<u32>, JsError> {
    if bi_is_zero(exp) {
        return Ok(vec![1]); // x**0 == 1, including 0n**0n
    }
    if bi_is_zero(base) {
        return Ok(Vec::new());
    }
    if bi_cmp_mag(base, &[1]) == std::cmp::Ordering::Equal {
        return Ok(vec![1]);
    }
    if bi_bit_len(exp) > 64 {
        return Err(err("Maximum BigInt size exceeded"));
    }
    let mut e: u64 = 0;
    for (i, &w) in exp.iter().enumerate() {
        e |= (w as u64) << (i * 32);
    }
    // Width pre-check (each squaring step re-checks via bi_mul_mag).
    if (e as u128).saturating_mul(bi_bit_len(base) as u128) > BI_MAX_BITS as u128 {
        return Err(err("Maximum BigInt size exceeded"));
    }
    let mut acc = vec![1u32];
    let mut b = base.to_vec();
    while e > 0 {
        if e & 1 == 1 {
            acc = bi_mul_mag(&acc, &b)?;
        }
        e >>= 1;
        if e > 0 {
            b = bi_mul_mag(&b, &b)?;
        }
    }
    Ok(acc)
}

/// n-limb two's complement of (neg, mag): negatives sign-extend with 1s so
/// `&`/`|`/`^` get infinite-sign-extension semantics.
fn bi_twos(neg: bool, mag: &[u32], n: usize) -> Vec<u32> {
    let mut t = vec![0u32; n];
    let m = mag.len().min(n);
    t[..m].copy_from_slice(&mag[..m]);
    if neg {
        for w in t.iter_mut() {
            *w = !*w;
        }
        let mut c = 1u64;
        for w in t.iter_mut() {
            if c == 0 {
                break;
            }
            let s = *w as u64 + c;
            *w = s as u32;
            c = s >> 32;
        }
    }
    t
}

/// Two's complement words back to (sign, magnitude). The top bit decides.
fn bi_from_twos(t: &[u32]) -> (bool, Vec<u32>) {
    if t.last().map(|&w| w >> 31 == 0).unwrap_or(true) {
        let mut m = t.to_vec();
        while m.last() == Some(&0) {
            m.pop();
        }
        (false, m)
    } else {
        let mut m: Vec<u32> = t.iter().map(|w| !w).collect();
        bi_add_small(&mut m, 1);
        while m.last() == Some(&0) {
            m.pop();
        }
        (true, m)
    }
}

fn bi_bitwise(an: bool, a: &[u32], bn: bool, b: &[u32], op: u8) -> (bool, Vec<u32>) {
    let n = a.len().max(b.len()) + 1;
    let ta = bi_twos(an, a, n);
    let tb = bi_twos(bn, b, n);
    let out: Vec<u32> = ta
        .into_iter()
        .zip(tb)
        .map(|(x, y)| match op {
            b'&' => x & y,
            b'|' => x | y,
            _ => x ^ y,
        })
        .collect();
    bi_from_twos(&out)
}

/// Exact f64-integer -> BigInt via bit decomposition (every integral f64 is
/// an exact integer, however large). Caller guarantees finite + integral.
fn bi_from_f64_int(n: f64) -> (bool, Vec<u32>) {
    if n == 0.0 {
        return (false, Vec::new()); // also kills -0.0: no negative zero
    }
    let neg = n < 0.0;
    let bits = n.abs().to_bits();
    let raw = ((bits >> 52) & 0x7ff) as i32;
    // Integral nonzero values are always normal (subnormals are < 1).
    debug_assert!(raw != 0);
    let mant = (bits & ((1u64 << 52) - 1)) | (1u64 << 52);
    let e = raw - 1075;
    let mut mag = vec![(mant & 0xFFFF_FFFF) as u32, (mant >> 32) as u32];
    while mag.last() == Some(&0) {
        mag.pop();
    }
    if e >= 0 {
        mag = bi_shl_mag(&mag, e as usize);
    } else {
        mag = bi_shr_mag(&mag, (-e) as usize).0; // lossless: input integral
    }
    (neg, mag)
}

fn bi_to_f64(neg: bool, mag: &[u32]) -> f64 {
    let mut n = 0.0;
    for (i, &w) in mag.iter().enumerate() {
        if w != 0 {
            n += w as f64 * 2f64.powi(i as i32 * 32);
        }
    }
    if neg { -n } else { n }
}

fn bi_parse(s: &str) -> Result<(bool, Vec<u32>), ()> {
    let t = s.trim();
    if t.is_empty() {
        return Ok((false, Vec::new())); // BigInt("") is 0n
    }
    let (neg, t) = match t.strip_prefix('-') {
        Some(r) => (true, r),
        None => (false, t.strip_prefix('+').unwrap_or(t)),
    };
    let (radix, digits) = if let Some(x) = t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
        (16, x)
    } else if let Some(x) = t.strip_prefix("0b").or_else(|| t.strip_prefix("0B")) {
        (2, x)
    } else if let Some(x) = t.strip_prefix("0o").or_else(|| t.strip_prefix("0O")) {
        (8, x)
    } else {
        (10u32, t)
    };
    if digits.is_empty() {
        return Err(());
    }
    let mut mag: Vec<u32> = Vec::new();
    for c in digits.chars() {
        let d = c.to_digit(radix).ok_or(())?;
        bi_mul_small(&mut mag, radix);
        bi_add_small(&mut mag, d);
    }
    Ok((neg && !bi_is_zero(&mag), mag))
}

fn bi_fmt(neg: bool, mag: &[u32], radix: u32) -> String {
    const DIGITS: &[u8] = b"0123456789abcdefghijklmnopqrstuvwxyz";
    if bi_is_zero(mag) {
        return "0".into();
    }
    let mut m = mag.to_vec();
    let mut out: Vec<u8> = Vec::new();
    while !bi_is_zero(&m) {
        out.push(DIGITS[bi_divmod_small(&mut m, radix) as usize]);
    }
    if neg {
        out.push(b'-');
    }
    out.reverse();
    String::from_utf8(out).unwrap_or_default()
}

fn bi_from_u64(u: u64) -> (bool, Vec<u32>) {
    if u == 0 {
        return (false, Vec::new());
    }
    let mut m = vec![u as u32];
    if u > 0xFFFF_FFFF {
        m.push((u >> 32) as u32);
    }
    (false, m)
}

fn bi_from_i64(i: i64) -> (bool, Vec<u32>) {
    if i == 0 {
        return (false, Vec::new());
    }
    let (neg, u) = if i < 0 {
        (true, i.unsigned_abs())
    } else {
        (false, i as u64)
    };
    let (_, m) = bi_from_u64(u);
    (neg, m)
}

fn bi_bit_set(mag: &[u32], i: usize) -> bool {
    mag.get(i / 32)
        .map(|&w| w >> (i % 32) & 1 == 1)
        .unwrap_or(false)
}

/// BigInt vs f64, exactly: integral Numbers convert losslessly (every
/// integral f64 IS an exact integer); fractional ones compare via their
/// truncation plus the leftover fraction. None = unordered (NaN).
fn cmp_big_num(neg: bool, mag: &[u32], n: f64) -> Option<std::cmp::Ordering> {
    use std::cmp::Ordering::*;
    if n.is_nan() {
        return None;
    }
    if n.is_infinite() {
        return Some(if n > 0.0 { Less } else { Greater });
    }
    if n.fract() == 0.0 {
        let (nn, nm) = bi_from_f64_int(n);
        return Some(bi_cmp(neg, mag, nn, &nm));
    }
    let (tn, tm) = bi_from_f64_int(n.trunc());
    match bi_cmp(neg, mag, tn, &tm) {
        Equal => Some(if n > 0.0 { Less } else { Greater }),
        o => Some(o),
    }
}

enum BigOrNum {
    Big(bool, Vec<u32>),
    Num(f64),
    NaN,
}

/// A string as BigInt when it parses, else as Number, else NaN-ish
/// (mirrors the spec's ToNumeric-then-compare for `==` and relational ops).
fn str_to_big_num(s: &str) -> BigOrNum {
    if let Ok((neg, mag)) = bi_parse(s) {
        return BigOrNum::Big(neg, mag);
    }
    match s.trim().parse::<f64>() {
        // Rust rejects the hex/inf casings V8 accepts; exact-bigint strings
        // took the first path, so this fallback only shapes numerics.
        Ok(n) => {
            if n.is_nan() {
                BigOrNum::NaN
            } else {
                BigOrNum::Num(n)
            }
        }
        Err(_) => BigOrNum::NaN,
    }
}

/// Loose `==` with exactly one BigInt side (both-big is value equality).
fn big_loose_rhs(mag: &[u32], neg: bool, h: &Heap, o: Value) -> bool {
    match o {
        Value::Num(n) => cmp_big_num(neg, mag, n) == Some(std::cmp::Ordering::Equal),
        Value::Bool(b) => {
            cmp_big_num(neg, mag, b as u8 as f64) == Some(std::cmp::Ordering::Equal)
        }
        Value::Str(id) => match str_to_big_num(h.get_str(id)) {
            BigOrNum::Big(bn, bm) => neg == bn && mag == bm.as_slice(),
            BigOrNum::Num(n) => cmp_big_num(neg, mag, n) == Some(std::cmp::Ordering::Equal),
            BigOrNum::NaN => false,
        },
        _ => false,
    }
}

fn loose_big(h: &Heap, l: Value, r: Value) -> bool {
    match (bi_val(h, l), bi_val(h, r)) {
        (Some((an, am)), Some((bn, bm))) => an == bn && am == bm,
        (Some((an, am)), _) => big_loose_rhs(&am, an, h, r),
        (_, Some((bn, bm))) => big_loose_rhs(&bm, bn, h, l),
        (None, None) => false,
    }
}

/// Ordering of (big) vs (non-big value): None when unordered.
fn big_ord_rhs(mag: &[u32], neg: bool, h: &Heap, o: Value) -> Option<std::cmp::Ordering> {
    match o {
        Value::Num(n) => cmp_big_num(neg, mag, n),
        Value::Bool(b) => cmp_big_num(neg, mag, b as u8 as f64),
        Value::Str(id) => match str_to_big_num(h.get_str(id)) {
            BigOrNum::Big(bn, bm) => Some(bi_cmp(neg, mag, bn, &bm)),
            BigOrNum::Num(n) => cmp_big_num(neg, mag, n),
            BigOrNum::NaN => None,
        },
        _ => None,
    }
}

fn big_rel_ord(h: &Heap, l: Value, r: Value) -> Option<std::cmp::Ordering> {
    match (bi_val(h, l), bi_val(h, r)) {
        (Some((an, am)), Some((bn, bm))) => Some(bi_cmp(an, &am, bn, &bm)),
        (Some((an, am)), _) => big_ord_rhs(&am, an, h, r),
        (_, Some((bn, bm))) => big_ord_rhs(&bm, bn, h, l).map(std::cmp::Ordering::reverse),
        (None, None) => None,
    }
}

fn rel_big(h: &Heap, op: &str, l: Value, r: Value) -> bool {
    big_rel_ord(h, l, r).is_some_and(|o| rel_holds(op, o))
}

/// BigInt-involved binary operator (spec): both-BigInt computes; `==`/`!=`
/// and relational ops compare numerically across types; everything else
/// mixed throws ("Cannot mix BigInt and other types").
fn bin_big(it: &mut Interp, op: &str, l: Value, r: Value) -> Result<Value, JsError> {
    match (bi_val(&it.heap, l), bi_val(&it.heap, r)) {
        (Some((an, am)), Some((bn, bm))) => bin_big_both(it, op, an, &am, bn, &bm),
        _ => Ok(match op {
            "==" => Value::Bool(loose_big(&it.heap, l, r)),
            "!=" => Value::Bool(!loose_big(&it.heap, l, r)),
            "===" => Value::Bool(strict_eq(&it.heap, l, r)),
            "!==" => Value::Bool(!strict_eq(&it.heap, l, r)),
            "<" | "<=" | ">" | ">=" => Value::Bool(rel_big(&it.heap, op, l, r)),
            _ => {
                return Err(err(
                    "Cannot mix BigInt and other types, use explicit conversions",
                ));
            }
        }),
    }
}

fn bin_big_both(
    it: &mut Interp,
    op: &str,
    an: bool,
    am: &[u32],
    bn: bool,
    bm: &[u32],
) -> Result<Value, JsError> {
    match op {
        "+" => {
            let (n, m) = bi_add(an, am, bn, bm);
            bi_alloc(it, n, m)
        }
        "-" => {
            let (n, m) = bi_add(an, am, !bn, bm);
            bi_alloc(it, n, m)
        }
        "*" => {
            let m = bi_mul_mag(am, bm)?;
            bi_alloc(it, an != bn && !bi_is_zero(&m), m)
        }
        "/" => {
            if bi_is_zero(bm) {
                return Err(err("Division by zero"));
            }
            let (q, _) = bi_divmod_mag(am, bm); // magnitudes: truncation
            bi_alloc(it, an != bn && !bi_is_zero(&q), q)
        }
        "%" => {
            if bi_is_zero(bm) {
                return Err(err("Division by zero"));
            }
            let (_, r) = bi_divmod_mag(am, bm); // sign follows the dividend
            bi_alloc(it, an && !bi_is_zero(&r), r)
        }
        "**" => {
            if bn && !bi_is_zero(bm) {
                return Err(err("Exponent must be non-negative"));
            }
            let m = bi_pow_mag(am, bm)?;
            let neg = an && !bi_is_zero(bm) && bm[0] & 1 == 1 && !bi_is_zero(&m);
            bi_alloc(it, neg, m)
        }
        "&" => {
            let (n, m) = bi_bitwise(an, am, bn, bm, b'&');
            bi_alloc(it, n, m)
        }
        "|" => {
            let (n, m) = bi_bitwise(an, am, bn, bm, b'|');
            bi_alloc(it, n, m)
        }
        "^" => {
            let (n, m) = bi_bitwise(an, am, bn, bm, b'^');
            bi_alloc(it, n, m)
        }
        "<<" | ">>" => {
            if bn && !bi_is_zero(bm) {
                return Err(err("BigInt shift count must be non-negative"));
            }
            if bi_bit_len(bm) > 64 {
                // Counts past the width cap: << overflows (unless the value
                // is zero), >> settles to 0, or -1 for negatives (floor).
                if op == "<<" {
                    if bi_is_zero(am) {
                        return bi_alloc(it, false, Vec::new());
                    }
                    return Err(err("Maximum BigInt size exceeded"));
                }
                return if !an || bi_is_zero(am) {
                    bi_alloc(it, false, Vec::new())
                } else {
                    bi_alloc(it, true, vec![1])
                };
            }
            let mut k: usize = 0;
            for (i, &w) in bm.iter().enumerate() {
                k |= (w as usize) << (i * 32);
            }
            if op == "<<" {
                if bi_bit_len(am) + k > BI_MAX_BITS {
                    return Err(err("Maximum BigInt size exceeded"));
                }
                bi_alloc(it, an, bi_shl_mag(am, k))
            } else {
                let (q, sticky) = bi_shr_mag(am, k);
                // Arithmetic shift floors negatives: round away on residue.
                if an && sticky {
                    let mut m = q;
                    bi_inc(&mut m);
                    bi_alloc(it, true, m)
                } else {
                    bi_alloc(it, an && !bi_is_zero(&q), q)
                }
            }
        }
        ">>>" => Err(err("BigInts have no unsigned right shift, use >> instead")),
        "==" => Ok(Value::Bool(an == bn && am == bm)),
        "!=" => Ok(Value::Bool(an != bn || am != bm)),
        "===" => Ok(Value::Bool(an == bn && am == bm)),
        "!==" => Ok(Value::Bool(an != bn || am != bm)),
        "<" | "<=" | ">" | ">=" => Ok(Value::Bool(rel_holds(op, bi_cmp(an, am, bn, bm)))),
        _ => Err(err(format!("bad op {op}"))),
    }
}

/// ToBigInt for the BigInt() call and asUintN/asIntN: numbers truncate
/// toward zero via exact conversion (NaN/Infinity throw); numeric strings
/// parse; bools and BigInts pass through; null/undefined/symbols/plain
/// objects throw.
fn bi_from_value(it: &Interp, v: Value) -> Result<(bool, Vec<u32>), JsError> {
    match v {
        Value::Num(n) => {
            if n.is_nan() {
                return Err(err("Cannot convert NaN to a BigInt"));
            }
            if n.is_infinite() {
                return Err(err("Cannot convert Infinity to a BigInt"));
            }
            Ok(bi_from_f64_int(n.trunc()))
        }
        Value::Str(id) => {
            let s = it.heap.get_str(id).to_string();
            bi_parse(&s).map_err(|()| err(format!("Cannot convert {s} to a BigInt")))
        }
        Value::Bool(b) => Ok(if b {
            (false, vec![1])
        } else {
            (false, Vec::new())
        }),
        Value::Null => Err(err("Cannot convert null to a BigInt")),
        Value::Undef => Err(err("Cannot convert undefined to a BigInt")),
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::BigInt { neg, mag, .. } => Ok((*neg, mag.clone())),
            Obj::Symbol { .. } => Err(err("Cannot convert a Symbol value to a BigInt")),
            _ => Err(err("Cannot convert object to a BigInt")),
        },
    }
}

/// BigInt(v): no-arg is 0n; BigInt args pass through (immutable values).
fn n_bigint_cast(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    if args.is_empty() {
        return bi_alloc(it, false, Vec::new());
    }
    let v = args[0];
    if let Value::Obj(id) = v {
        if matches!(it.heap.obj(id), Obj::BigInt { .. }) {
            return Ok(v);
        }
    }
    let (neg, mag) = bi_from_value(it, v)?;
    bi_alloc(it, neg, mag)
}

fn bi_bits(h: &Heap, v: Value, op: &str) -> Result<usize, JsError> {
    let n = to_num(h, v);
    if n.is_nan() {
        return Ok(0);
    }
    if n.fract() != 0.0 || n < 0.0 {
        return Err(err(format!("BigInt.{op} needs a non-negative integer bit count")));
    }
    if n > BI_MAX_BITS as f64 {
        return Err(err("Maximum BigInt size exceeded"));
    }
    Ok(n as usize)
}

/// x mod 2^bits in [0, 2^bits): mask the low limbs, complement negatives.
/// Never allocates 2^bits: only the (capped) residue is materialized.
fn bi_mod_pow2(neg: bool, mag: &[u32], bits: usize) -> (bool, Vec<u32>) {
    let k = bits.div_ceil(32);
    let mut low: Vec<u32> = mag.iter().take(k.min(mag.len())).copied().collect();
    if bits % 32 != 0 {
        if let Some(top) = low.last_mut() {
            *top &= u32::MAX >> (32 - bits % 32);
        }
    }
    while low.last() == Some(&0) {
        low.pop();
    }
    if !neg || low.is_empty() {
        return (false, low);
    }
    let two = bi_shl_mag(&[1], bits);
    (false, bi_sub_mag(&two, &low))
}

fn n_big_as_uint_n(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let bits = bi_bits(&it.heap, arg(args, 0), "asUintN")?;
    let (neg, mag) = bi_from_value(it, arg(args, 1))?;
    let (n, m) = bi_mod_pow2(neg, &mag, bits);
    bi_alloc(it, n, m)
}

fn n_big_as_int_n(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let bits = bi_bits(&it.heap, arg(args, 0), "asIntN")?;
    if bits == 0 {
        return bi_alloc(it, false, Vec::new());
    }
    let (neg, mag) = bi_from_value(it, arg(args, 1))?;
    let (_, u) = bi_mod_pow2(neg, &mag, bits);
    // A set sign bit means the unsigned residue reads negative here.
    if bi_bit_set(&u, bits - 1) {
        let two = bi_shl_mag(&[1], bits);
        let m = bi_sub_mag(&two, &u);
        bi_alloc(it, true, m)
    } else {
        bi_alloc(it, false, u)
    }
}

fn bi_this(it: &Interp, this: Value, op: &str) -> Result<(bool, Vec<u32>), JsError> {
    match this {
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::BigInt { neg, mag, .. } => Ok((*neg, mag.clone())),
            _ => Err(err(format!("BigInt.prototype.{op} needs a BigInt receiver"))),
        },
        _ => Err(err(format!("BigInt.prototype.{op} needs a BigInt receiver"))),
    }
}

/// BigInt.prototype.toString(radix): 2..36 like Number's (exact here, since
/// the value is already integral).
fn n_big_to_string(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let (neg, mag) = bi_this(it, this, "toString")?;
    let radix = match arg(args, 0) {
        Value::Undef => 10,
        v => to_num(&it.heap, v).trunc() as i64,
    };
    if !(2..=36).contains(&radix) {
        return Err(err("toString() radix argument must be between 2 and 36"));
    }
    Ok(Value::Str(
        it.heap.alloc_str(bi_fmt(neg, &mag, radix as u32))?,
    ))
}

fn n_big_value_of(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    bi_this(it, this, "valueOf")?;
    Ok(this)
}

// -- BigInt64Array / BigUint64Array -------------------------------------------------
// Raw u64 elements (f64 storage would lose precision past 2^53); reads box
// into BigInts, writes wrap mod 2^64 with sloppy coerce like the Typed
// neighbors (never throws on value shape). Only fill() is implemented:
// of/from/slice/subarray/join/set/indexOf are documented gaps.

fn b64_this(it: &Interp, this: Value, op: &str) -> Result<(u32, bool), JsError> {
    match this {
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::Big64 { signed, .. } => Ok((id, *signed)),
            Obj::BufView { kind, .. } if *kind == TypedKind::I64 => Ok((id, true)),
            Obj::BufView { kind, .. } if *kind == TypedKind::U64 => Ok((id, false)),
            _ => Err(err(format!("{op} needs a BigInt array receiver"))),
        },
        _ => Err(err(format!("{op} needs a BigInt array receiver"))),
    }
}

/// Truncated f64 wrapped into u64 range. Done via the exact bit
/// decomposition (every integral f64 converts losslessly): the naive
/// `((n % 2^64) + 2^64) % 2^64` rounds small values to zero in f64
/// (2^64 + 5 is not representable), and `as u64` saturates past 2^63.
fn b64_wrap_num(n: f64) -> u64 {
    let n = n.trunc();
    if !n.is_finite() || n == 0.0 {
        return 0;
    }
    let (neg, mag) = bi_from_f64_int(n);
    let m = mag.first().copied().unwrap_or(0) as u64
        | ((mag.get(1).copied().unwrap_or(0) as u64) << 32);
    if neg { m.wrapping_neg() } else { m }
}

/// Element write coercion: BigInts wrap exactly off the low limbs,
/// everything else truncates through f64 like the Typed neighbors.
fn b64_wrap(h: &Heap, v: Value) -> u64 {
    if let Some((neg, mag)) = bi_val(h, v) {
        let m = mag.first().copied().unwrap_or(0) as u64
            | ((mag.get(1).copied().unwrap_or(0) as u64) << 32);
        if neg { m.wrapping_neg() } else { m }
    } else {
        b64_wrap_num(to_num(h, v))
    }
}

/// Named/element store: canonical indices wrap in range (out-of-range
/// drops, sloppy); `length`/`byteLength`/`byteOffset` are read-only
/// no-ops; anything else is an expando pair.
fn b64_set(h: &mut Heap, id: u32, key: &str, val: Value) -> Result<(), JsError> {
    if key == "length" || key == "byteLength" || key == "byteOffset" {
        return Ok(());
    }
    let w = b64_wrap(&*h, val);
    if let Ok(i) = key.parse::<usize>() {
        if let Obj::Big64 { elems, .. } = h.obj_mut(id) {
            if let Some(slot) = elems.get_mut(i) {
                *slot = w;
            }
        }
        return Ok(());
    }
    if let Obj::Big64 { pairs, .. } = h.obj_mut(id) {
        match pairs.iter_mut().find(|(k, _)| k == key) {
            Some(slot) => slot.1 = val,
            None => pairs.push((key.to_string(), val)),
        }
    }
    Ok(())
}

/// Length-based element source for the ctor (mirrors t_len_items).
fn b64_len_items(it: &Interp, v: Value) -> Vec<u64> {
    let len = match get_prop(&it.heap, &it.protos, v, "length") {
        Ok(Value::Num(n)) if n > 0.0 => (n.floor() as usize).min(1 << 28),
        _ => return Vec::new(),
    };
    let mut out = Vec::with_capacity(len);
    for i in 0..len {
        let key = i.to_string();
        let n = match get_prop(&it.heap, &it.protos, v, &key) {
            Ok(x) => b64_wrap(&it.heap, x),
            Err(_) => 0,
        };
        out.push(n);
    }
    out
}

/// Shared Big64 constructor: length, source view/array, or buffer (+ byte
/// offset/element length, 8-aligned like the Typed views). Buffer-backed
/// forms (Buf/BufView) are live views sharing the store; the rest copy.
fn b64_ctor(it: &mut Interp, signed: bool, proto: u32, args: &[Value]) -> Result<Value, JsError> {
    let kind = if signed { TypedKind::I64 } else { TypedKind::U64 };
    if let Value::Obj(src) = arg(args, 0) {
        if let Ok(Some((buf, off, len))) = view_window(it, src, kind, args) {
            return Ok(Value::Obj(it.heap.alloc_obj(Obj::BufView {
                buf,
                off,
                len,
                kind,
                pairs: Vec::new(),
                proto: po(proto),
            })?));
        }
        if matches!(
            it.heap.obj(src),
            Obj::Buf { .. } | Obj::BufView { .. }
        ) {
            view_window(it, src, kind, args)?;
        }
    }
    let elems: Vec<u64> = match arg(args, 0) {
        Value::Undef => Vec::new(),
        v @ (Value::Num(_) | Value::Str(_) | Value::Bool(_) | Value::Null) => {
            vec![0; typed_len(&it.heap, v)?]
        }
        Value::Obj(id) if matches!(it.heap.obj(id), Obj::BigInt { .. }) => {
            vec![0; typed_len(&it.heap, Value::Obj(id))?]
        }
        Value::Obj(id) if matches!(it.heap.obj(id), Obj::Buf { .. }) => {
            let bytes = match it.heap.obj(id) {
                Obj::Buf { bytes, .. } => bytes.clone(),
                _ => unreachable!(),
            };
            let off = match arg(args, 1) {
                Value::Undef => 0,
                v => {
                    let n = to_num(&it.heap, v).trunc();
                    if n < 0.0 || n.fract() != 0.0 || !(n as usize).is_multiple_of(8) {
                        return Err(err("typed array buffer offset misaligned"));
                    }
                    n as usize
                }
            };
            if off > bytes.len() || bytes.len() % 8 != 0 {
                return Err(err("typed array buffer length mismatch"));
            }
            let mut els: Vec<u64> = bytes[off..]
                .chunks_exact(8)
                .map(|w| {
                    u64::from_le_bytes([
                        w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7],
                    ])
                })
                .collect();
            if !matches!(arg(args, 2), Value::Undef) {
                let want = typed_len(&it.heap, arg(args, 2))?;
                if want > els.len() {
                    return Err(err("typed array length out of range"));
                }
                els.truncate(want);
            }
            els
        }
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::Big64 { elems, .. } => elems.clone(),
            Obj::Bytes { bytes, .. } => bytes.iter().map(|b| *b as u64).collect(),
            Obj::Typed { elems, .. } => elems.iter().map(|e| b64_wrap_num(*e)).collect(),
            Obj::BufView { buf, off, len, kind, .. } => {
                let n = view_count(*kind, *len);
                let bpe = t_bpe(*kind);
                (0..n)
                    .map(|i| {
                        let at = off + i * bpe;
                        match kind {
                            TypedKind::I64 | TypedKind::U64 => {
                                view_read_u64(&it.heap, *buf, at).unwrap_or(0)
                            }
                            kk => b64_wrap_num(
                                view_read_num(&it.heap, *buf, at, *kk).unwrap_or(0.0),
                            ),
                        }
                    })
                    .collect()
            }
            Obj::Arr { items, .. } => {
                items.iter().map(|x| b64_wrap(&it.heap, *x)).collect()
            }
            _ => b64_len_items(it, Value::Obj(id)),
        },
    };
    Ok(Value::Obj(it.heap.alloc_obj(Obj::Big64 {
        signed,
        elems,
        pairs: Vec::new(),
        proto: po(proto),
    })?))
}

fn n_bi64_ctor(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    b64_ctor(it, true, it.protos.bigint64array, a)
}

fn n_bu64_ctor(it: &mut Interp, _t: Value, a: &[Value]) -> Result<Value, JsError> {
    b64_ctor(it, false, it.protos.biguint64array, a)
}

fn n_b64_fill(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let (id, _) = b64_this(it, this, "fill")?;
    let w = b64_wrap(&it.heap, arg(args, 0));
    let len = match it.heap.obj(id) {
        Obj::Big64 { elems, .. } => elems.len(),
        Obj::BufView { len, kind, .. } => view_count(*kind, *len),
        _ => unreachable!(),
    };
    let (a, c) = match (arg(args, 1), arg(args, 2)) {
        (Value::Undef, Value::Undef) => (0, len),
        (s, Value::Undef) => typed_range(len, to_num(&it.heap, s), len as f64),
        (s, e) => typed_range(len, to_num(&it.heap, s), to_num(&it.heap, e)),
    };
    match it.heap.obj(id) {
        Obj::Big64 { .. } => {
            if let Obj::Big64 { elems, .. } = it.heap.obj_mut(id) {
                elems[a..c].fill(w);
            }
        }
        Obj::BufView { buf, off, .. } => {
            let (buf, off) = (*buf, *off);
            for i in a.min(len)..c.min(len) {
                view_write_u64(&mut it.heap, buf, off + i * 8, w);
            }
        }
        _ => unreachable!(),
    }
    Ok(this)
}

// -- DataView 64-bit accessors -------------------------------------------------------
// Values cross as boxed BigInts (exact); setters coerce like Big64 element
// writes (wrap mod 2^64) and return undefined like the other setters.

fn dv_big_get(
    it: &mut Interp,
    this: Value,
    args: &[Value],
    signed: bool,
    name: &str,
) -> Result<Value, JsError> {
    let id = dv_this(it, this, name)?;
    let (buf, at, vlen, le) = dv_args(it, id, args)?;
    let (voff, _) = match it.heap.obj(id) {
        Obj::DView { off, .. } => (*off, 0),
        _ => unreachable!(),
    };
    dv_rel(at, voff, vlen, 8)?;
    let bytes = match buf_live(&it.heap, buf) {
        Some(b) => b,
        None => return Err(err("DataView offset out of bounds")),
    };
    dv_need(bytes, at, 8)?;
    let w = &bytes[at..at + 8];
    let bits = if le {
        u64::from_le_bytes([w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]])
    } else {
        u64::from_be_bytes([w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]])
    };
    let (neg, mag) = if signed {
        bi_from_i64(bits as i64)
    } else {
        bi_from_u64(bits)
    };
    bi_alloc(it, neg, mag)
}

fn dv_big_set(
    it: &mut Interp,
    this: Value,
    args: &[Value],
    name: &str,
) -> Result<Value, JsError> {
    let id = dv_this(it, this, name)?;
    let (buf, vlen, off) = match it.heap.obj(id) {
        Obj::DView { buf, len, off, .. } => (*buf, *len, *off),
        _ => unreachable!(),
    };
    let rel = match to_num(&it.heap, arg(args, 0)).trunc() {
        n if n < 0.0 => return Err(err("DataView offset out of bounds")),
        n => n as usize,
    };
    if rel + 8 > vlen {
        return Err(err("DataView offset out of bounds"));
    }
    let at = off + rel;
    let le = truthy(&it.heap, arg(args, 2));
    let w = b64_wrap(&it.heap, arg(args, 1));
    let enc = if le { w.to_le_bytes() } else { w.to_be_bytes() };
    match it.heap.objs.get_mut(buf as usize) {
        Some(Obj::Buf { bytes, .. }) if at + 8 <= bytes.len() => {
            bytes[at..at + 8].copy_from_slice(&enc);
            Ok(Value::Undef)
        }
        _ => Err(err("DataView offset out of bounds")),
    }
}

fn n_dv_get_bi64(it: &mut Interp, t: Value, a: &[Value]) -> Result<Value, JsError> {
    dv_big_get(it, t, a, true, "getBigInt64")
}

fn n_dv_get_bu64(it: &mut Interp, t: Value, a: &[Value]) -> Result<Value, JsError> {
    dv_big_get(it, t, a, false, "getBigUint64")
}

fn n_dv_set_bi64(it: &mut Interp, t: Value, a: &[Value]) -> Result<Value, JsError> {
    dv_big_set(it, t, a, "setBigInt64")
}

fn n_dv_set_bu64(it: &mut Interp, t: Value, a: &[Value]) -> Result<Value, JsError> {
    dv_big_set(it, t, a, "setBigUint64")
}

// -- TextEncoder / TextDecoder -----------------------------------------------------
// UTF-8 via Rust's own encoding (engine strings are UTF-8); lossy decode
// substitutes U+FFFD like V8's non-fatal path. Only utf-8 and latin1
// families exist here; other labels throw. `stream` decode state and
// `fatal` are documented gaps (stateless, never throws on bad bytes).

/// Sugar for the one label family V8 reports for latin1 inputs.
fn td_normalize(label: &str) -> Option<&'static str> {
    let l = label.trim().to_ascii_lowercase().replace('_', "-");
    match l.as_str() {
        "utf-8" | "utf8" => Some("utf-8"),
        "latin1" | "iso-8859-1" | "windows-1252" | "ascii" => Some("windows-1252"),
        _ => None,
    }
}

/// Decode input (any byte-ish view or array) to raw bytes.
fn td_bytes(it: &Interp, v: Value) -> Vec<u8> {
    match v {
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::Arr { items, .. } => items.iter().map(|x| to_u8(&it.heap, *x)).collect(),
            Obj::Bytes { bytes, .. } => bytes.clone(),
            Obj::Buf { bytes, .. } => bytes.clone(),
            Obj::Typed { elems, kind, .. } => {
                elems.iter().map(|e| to_u8_num(t_write(*kind, *e))).collect()
            }
            Obj::BufView { buf, off, len, kind, .. } => match kind {
                TypedKind::I64 | TypedKind::U64 => Vec::new(),
                kk => {
                    let n = view_count(*kk, *len);
                    let bpe = t_bpe(*kk);
                    (0..n)
                        .map(|i| {
                            to_u8_num(t_write(
                                *kk,
                                view_read_num(&it.heap, *buf, off + i * bpe, *kk).unwrap_or(0.0),
                            ))
                        })
                        .collect()
                }
            },
            _ => Vec::new(),
        },
        _ => Vec::new(),
    }
}

fn n_te_ctor(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    if let Value::Obj(id) = this {
        if matches!(it.heap.obj(id), Obj::Ordinary { .. }) {
            return Ok(this);
        }
    }
    let proto = po(it.protos.textencoder);
    Ok(Value::Obj(it.heap.alloc_obj(Obj::Ordinary {
        pairs: Vec::new(),
        proto,
    })?))
}

fn n_te_encode(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let s = match arg(args, 0) {
        Value::Undef => String::new(),
        v => to_str(&it.heap, v),
    };
    let proto = po(it.protos.uint8array);
    Ok(Value::Obj(it.heap.alloc_obj(Obj::Bytes {
        bytes: s.into_bytes(),
        pairs: Vec::new(),
        proto,
    })?))
}

fn n_td_ctor(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let enc = match arg(args, 0) {
        Value::Undef => "utf-8",
        v => match td_normalize(&to_str(&it.heap, v)) {
            Some(e) => e,
            None => return Err(err(format!("unknown encoding {}", to_str(&it.heap, v)))),
        },
    };
    let proto = po(it.protos.textdecoder);
    let id = it.heap.alloc_obj(Obj::Ordinary {
        pairs: Vec::new(),
        proto,
    })?;
    let es = Value::Str(it.heap.alloc_str(enc.to_string())?);
    set_prop(&mut it.heap, Value::Obj(id), "encoding", es)?;
    Ok(Value::Obj(id))
}

fn n_td_decode(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let enc = match get_prop(&it.heap, &it.protos, this, "encoding")? {
        Value::Str(id) => it.heap.get_str(id).to_string(),
        _ => "utf-8".into(),
    };
    let bytes = td_bytes(it, arg(args, 0));
    let s = if enc == "windows-1252" {
        bytes.iter().map(|b| *b as char).collect()
    } else {
        String::from_utf8_lossy(&bytes).into_owned()
    };
    Ok(Value::Str(it.heap.alloc_str(s)?))
}

// -- Proxy / Reflect -----------------------------------------------------------

/// `new Proxy(target, handler)`: both must be objects (V8 throws
/// TypeError otherwise - surfaced here as a plain error like the other
/// internal TypeErrors). Callable targets stay non-callable through the
/// proxy (no apply/construct traps - documented gap).
fn n_proxy_ctor(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let (target, handler) = match (arg(args, 0), arg(args, 1)) {
        (Value::Obj(t), Value::Obj(h)) => (t, h),
        _ => return Err(err("Proxy needs an object target and handler")),
    };
    Ok(Value::Obj(it.heap.alloc_obj(Obj::Proxy {
        target,
        handler,
    })?))
}

/// Proxy-aware read shared by Reflect.get: runs the get trap, else the
/// target's value (getters applied, receiver = the proxy/target value).
fn reflect_get(it: &mut Interp, target: Value, key: &str) -> Result<Value, JsError> {
    if let Value::Obj(id) = target {
        if matches!(it.heap.obj(id), Obj::Proxy { .. }) {
            return it.proxy_get(id, key, target);
        }
        // Big64 canonical indices box here (get_prop can't: it lacks &mut).
        if let Obj::Big64 { signed, elems, .. } = it.heap.obj(id) {
            let signed = *signed;
            if let Ok(i) = key.parse::<usize>() {
                if let Some(bits) = elems.get(i).copied() {
                    let (neg, mag) = if signed {
                        bi_from_i64(bits as i64)
                    } else {
                        bi_from_u64(bits)
                    };
                    return bi_alloc(it, neg, mag);
                }
            }
        }
    }
    let val = get_prop(&it.heap, &it.protos, target, key)?;
    it.invoke_getter(val, target, key)
}

fn n_reflect_get(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let key = to_str(&it.heap, arg(args, 1));
    reflect_get(it, arg(args, 0), &key)
}

fn n_reflect_set(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let target = arg(args, 0);
    let key = to_str(&it.heap, arg(args, 1));
    let val = arg(args, 2);
    if let Value::Obj(id) = target {
        if matches!(it.heap.obj(id), Obj::Proxy { .. }) {
            it.proxy_set(id, &key, val, target)?;
            return Ok(Value::Bool(true));
        }
    }
    let cur = get_prop(&it.heap, &it.protos, target, &key)?;
    if it.invoke_setter(cur, target, val, &key)? {
        return Ok(Value::Bool(true));
    }
    set_prop(&mut it.heap, target, &key, val)?;
    Ok(Value::Bool(true))
}

fn n_reflect_has(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let target = arg(args, 0);
    let key = to_str(&it.heap, arg(args, 1));
    if let Value::Obj(id) = target {
        if matches!(it.heap.obj(id), Obj::Proxy { .. }) {
            return Ok(Value::Bool(it.proxy_has(id, &key)?));
        }
    }
    Ok(Value::Bool(has_prop(&it.heap, &it.protos, target, &key)))
}

fn n_reflect_delete(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let target = arg(args, 0);
    let key = to_str(&it.heap, arg(args, 1));
    it.delete_key(target, &key, Some(arg(args, 1)))
}

fn n_reflect_get_desc(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let key = to_str(&it.heap, arg(args, 1));
    let d = describe_own(it, arg(args, 0), &key)?;
    // Absent key reads undefined (describe_own reports it so); real
    // Reflect returns undefined instead of a descriptor.
    if let Value::Obj(id) = d {
        if let Obj::Ordinary { pairs, .. } = it.heap.obj(id) {
            if !pairs.iter().any(|(k, _)| k == "value" || k == "get") {
                return Ok(Value::Undef);
            }
        }
    }
    Ok(d)
}

fn n_reflect_get_proto(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    match arg(args, 0) {
        Value::Obj(id) => Ok(match proto_of(&it.heap, &it.protos, id) {
            Some(p) => Value::Obj(p),
            None => Value::Null,
        }),
        _ => Err(err("Reflect.getPrototypeOf needs an object")),
    }
}

fn n_reflect_own_keys(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    // ownKeys trap is a documented gap: proxies report the target's keys.
    let mut keys = Vec::new();
    for (k, _) in own_pairs(it, arg(args, 0)) {
        keys.push(Value::Str(it.heap.alloc_str(k)?));
    }
    Ok(Value::Obj(it.arr_obj(keys)?))
}

fn n_reflect_construct(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let argv = match arg(args, 1) {
        Value::Obj(id) => arr_items(it, id),
        Value::Undef => Vec::new(),
        _ => return Err(err("Reflect.construct needs an argument list")),
    };
    let target = arg(args, 0);
    // newTarget (Babel _createSuper's native path): `this` gets
    // newTarget.prototype while the target ctor runs on it.
    if matches!(arg(args, 2), Value::Undef) {
        return it.construct_value(target, &argv);
    }
    let nt = arg(args, 2);
    let proto = match get_prop(&it.heap, &it.protos, nt, "prototype")? {
        Value::Obj(p) => Some(p),
        _ => po(it.protos.object),
    };
    let obj = it.heap.alloc_obj(Obj::Ordinary {
        pairs: Vec::new(),
        proto,
    })?;
    it.pending_new_target = Some(nt);
    let r = it.call_value(target, Value::Obj(obj), &argv, None);
    it.pending_new_target.take();
    let r = r?;
    Ok(match r {
        Value::Obj(_) => r,
        _ => Value::Obj(obj),
    })
}

fn n_reflect_apply(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let argv = match arg(args, 2) {
        Value::Obj(id) => arr_items(it, id),
        Value::Undef => Vec::new(),
        _ => return Err(err("Reflect.apply needs an argument list")),
    };
    it.call_value(arg(args, 0), arg(args, 1), &argv, None)
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
/// type with own `message` + frameless `stack` (upgraded with frames on
/// first unwind; custom stacks are never touched).
fn n_error(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let msg = match args.first() {
        Some(v) if !matches!(v, Value::Undef) => to_str(&it.heap, *v),
        _ => String::new(),
    };
    if let Value::Obj(id) = this {
        // `new Error(m)` hands us the fresh object with the right proto
        if matches!(it.heap.obj(id), Obj::Ordinary { .. }) {
            let m = Value::Str(it.heap.alloc_str(msg.clone())?);
            set_prop(&mut it.heap, this, "message", m)?;
            let name = match get_prop(&it.heap, &it.protos, this, "name") {
                Ok(Value::Undef) | Err(_) => "Error".to_string(),
                Ok(v) => to_str(&it.heap, v),
            };
            let s = Value::Str(it.heap.alloc_str(Interp::stack_string(&name, &msg, ""))?);
            set_prop(&mut it.heap, this, "stack", s)?;
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

fn n_math_fround(it: &mut Interp, _t: Value, args: &[Value]) -> Result<Value, JsError> {
    Ok(Value::Num(to_num(&it.heap, arg(args, 0)) as f32 as f64))
}

fn n_math_trunc(it: &mut Interp, _t: Value, args: &[Value]) -> Result<Value, JsError> {
    Ok(Value::Num(to_num(&it.heap, arg(args, 0)).trunc()))
}

/// One-arg float ops straight through Rust (same IEEE results as V8).
macro_rules! math_unary {
    ($name:ident, $meth:ident) => {
        fn $name(it: &mut Interp, _t: Value, args: &[Value]) -> Result<Value, JsError> {
            Ok(Value::Num(to_num(&it.heap, arg(args, 0)).$meth()))
        }
    };
}
math_unary!(n_math_sin, sin);
math_unary!(n_math_cos, cos);
math_unary!(n_math_tan, tan);
math_unary!(n_math_asin, asin);
math_unary!(n_math_acos, acos);
math_unary!(n_math_atan, atan);
math_unary!(n_math_sinh, sinh);
math_unary!(n_math_cosh, cosh);
math_unary!(n_math_tanh, tanh);
math_unary!(n_math_exp, exp);
math_unary!(n_math_log, ln);
math_unary!(n_math_cbrt, cbrt);

fn n_math_atan2(it: &mut Interp, _t: Value, args: &[Value]) -> Result<Value, JsError> {
    Ok(Value::Num(
        to_num(&it.heap, arg(args, 0)).atan2(to_num(&it.heap, arg(args, 1))),
    ))
}

fn n_math_hypot(it: &mut Interp, _t: Value, args: &[Value]) -> Result<Value, JsError> {
    // Naive sum-of-squares (overflowBalanced paths are a gap - V8 avoids
    // intermediate overflow; bundles use modest magnitudes).
    let mut acc = 0.0;
    for a in args {
        let n = to_num(&it.heap, *a);
        acc += n * n;
    }
    Ok(Value::Num(acc.sqrt()))
}

fn n_math_sign(it: &mut Interp, _t: Value, args: &[Value]) -> Result<Value, JsError> {
    let n = to_num(&it.heap, arg(args, 0));
    Ok(Value::Num(if n.is_nan() {
        f64::NAN
    } else if n == 0.0 {
        n // ±0 preserved
    } else if n > 0.0 {
        1.0
    } else {
        -1.0
    }))
}

fn n_math_clz32(it: &mut Interp, _t: Value, args: &[Value]) -> Result<Value, JsError> {
    // ToUint32 then leading zeros (NaN/Infinity -> 32 via the zero word).
    let n = to_num(&it.heap, arg(args, 0)).trunc();
    let u = if !n.is_finite() {
        0u32
    } else {
        (((n % 4294967296.0) + 4294967296.0) % 4294967296.0) as u32
    };
    Ok(Value::Num(u.leading_zeros() as f64))
}

fn n_math_imul(it: &mut Interp, _t: Value, args: &[Value]) -> Result<Value, JsError> {
    let a = to_i32(&it.heap, arg(args, 0));
    let b = to_i32(&it.heap, arg(args, 1));
    Ok(Value::Num(a.wrapping_mul(b) as f64))
}

// -- base64 globals ---------------------------------------------------------------
// atob/btoa over Latin-1 strings (browser parity: whitespace stripped,
// missing padding tolerated, bad chars throw).

fn b64_val(c: u8) -> Option<u8> {
    match c {
        b'A'..=b'Z' => Some(c - b'A'),
        b'a'..=b'z' => Some(c - b'a' + 26),
        b'0'..=b'9' => Some(c - b'0' + 52),
        b'+' => Some(62),
        b'/' => Some(63),
        _ => None,
    }
}

/// DOM interface ctors (Element, Node, ...): V8 throws on `new`
/// ("Illegal constructor") - only instanceof/prototype use them here.
fn n_dom_illegal(_it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    Err(err("Illegal constructor"))
}

/// Web Storage (local/session): Ordinary with string pairs plus a
/// maintained `length` pair. Deviations: `length` enumerates (V8 hides
/// it), and a literal key named "length" collides with the counter.
/// Memory-only (no profile persistence yet); no `storage` events.
fn storage_recount(it: &mut Interp, obj: Value) {
    let n = match obj {
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::Ordinary { pairs, .. } => pairs
                .iter()
                .filter(|(k, _)| k != "length")
                .count() as f64,
            _ => return,
        },
        _ => return,
    };
    let _ = set_prop(&mut it.heap, obj, "length", Value::Num(n));
}

fn n_storage_get(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let key = to_str(&it.heap, arg(args, 0));
    // Own data pairs only (methods live on the prototype, never leak).
    let found = match this {
        Value::Obj(id) => own_prop(&it.heap, id, &key),
        _ => None,
    };
    match found {
        Some(Value::Str(id)) => Ok(Value::Str(id)),
        Some(v) => Ok(Value::Str(it.heap.alloc_str(to_str(&it.heap, v))?)),
        None => Ok(Value::Null),
    }
}

fn n_storage_set(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let key = to_str(&it.heap, arg(args, 0));
    let val = to_str(&it.heap, arg(args, 1));
    if !matches!(this, Value::Obj(_)) {
        return Err(err("Storage.setItem needs a storage receiver"));
    }
    let v = Value::Str(it.heap.alloc_str(val)?);
    set_prop(&mut it.heap, this, &key, v)?;
    storage_recount(it, this);
    Ok(Value::Undef)
}

fn n_storage_remove(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let key = to_str(&it.heap, arg(args, 0));
    if let Value::Obj(id) = this {
        if let Obj::Ordinary { pairs, .. } = it.heap.obj_mut(id) {
            pairs.retain(|(k, _)| k != &key);
        }
        storage_recount(it, this);
    }
    Ok(Value::Undef)
}

fn n_storage_clear(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    if let Value::Obj(id) = this {
        if let Obj::Ordinary { pairs, .. } = it.heap.obj_mut(id) {
            pairs.clear();
        }
        storage_recount(it, this);
    }
    Ok(Value::Undef)
}

fn n_storage_key(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let i = to_num(&it.heap, arg(args, 0));
    if !(i >= 0.0) || i.fract() != 0.0 {
        return Ok(Value::Null);
    }
    let hit = match this {
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::Ordinary { pairs, .. } => pairs
                .iter()
                .filter(|(k, _)| k != "length")
                .nth(i as usize)
                .map(|(k, _)| k.clone()),
            _ => None,
        },
        _ => None,
    };
    match hit {
        Some(k) => Ok(Value::Str(it.heap.alloc_str(k)?)),
        None => Ok(Value::Null),
    }
}

fn storage_obj(it: &mut Interp) -> Result<u32, JsError> {
    let proto = po(it.protos.storage);
    let id = it.heap.alloc_obj(Obj::Ordinary {
        pairs: vec![("length".into(), Value::Num(0.0))],
        proto,
    })?;
    Ok(id)
}

/// window.history: length/state plus pushState/replaceState updating
/// the shared location object; back/forward/go/listen/block are no-ops
/// (single-snapshot model - no traversal or POP events). Enough for
/// React Router's createBrowserHistory({window}).
fn n_history_push(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let url = to_str(&it.heap, arg(args, 2));
    if !url.is_empty() {
        // Resolve against the current href like a real pushState, then
        // refresh the whole location object (pathname/search/...).
        let href = to_str(
            &it.heap,
            match it.env_get(0, "location") {
                Some(loc) => get_prop(&it.heap, &it.protos, loc, "href").unwrap_or(Value::Undef),
                None => Value::Undef,
            },
        );
        // Proper URL join through the engine parser first (handles
        // query/hash replacement); string fallback for odd shapes.
        let joined = vigia_url::Url::parse(&href)
            .and_then(|b| b.join(&url))
            .map(|u| u.to_string())
            .unwrap_or_else(|_| {
                if url.contains("://") || url.starts_with('/') || href.is_empty() {
                    url.clone()
                } else if let Some(i) = href.rfind('/') {
                    format!("{}{}", &href[..i + 1], url)
                } else {
                    url.clone()
                }
            });
        let _ = it.set_location_href(&joined);
    }
    if let Some(st) = it.env_get(0, "history") {
        let _ = set_prop(&mut it.heap, st, "state", arg(args, 0));
    }
    Ok(Value::Undef)
}

fn n_history_noop(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let _ = it;
    Ok(Value::Undef)
}

fn n_history_listen(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    // Unlisten function; POP never fires in a snapshot.
    Ok(Value::Obj(it.heap.alloc_obj(nat("unlisten", n_history_noop))?))
}

fn n_history_href(_it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    Ok(arg(args, 0))
}

/// Constant natives for host predicates (javaEnabled=false…).
pub(crate) fn n_const_false(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let _ = it;
    Ok(Value::Bool(false))
}

/// ResizeObserver: records observations, never fires (no layout engine
/// to observe - poppers just never reposition). Enough for sidebar code
/// that constructs + observes + disconnects at boot.
fn n_resize_observer_ctor(
    it: &mut Interp,
    _this: Value,
    args: &[Value],
) -> Result<Value, JsError> {
    let cb = arg(args, 0);
    if !matches!(cb, Value::Obj(_)) {
        return Err(err("ResizeObserver needs a callback"));
    }
    let proto = po(it.protos.resizeobserver);
    let id = it.heap.alloc_obj(Obj::Ordinary {
        pairs: vec![("__cb".into(), cb)],
        proto,
    })?;
    Ok(Value::Obj(id))
}

fn n_resize_observe(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let _ = it;
    Ok(Value::Undef)
}

/// IntersectionObserver: the scraping viewport has no fold, so every
/// observed target reads as visible (lazy content loads instead of
/// taking the headless fallback). observe() records the target and
/// fires one all-visible entry for it on a zero timer; unobserve /
/// disconnect drop targets so pending entries never fire.
fn n_io_ctor(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let Some(cb) = callable(it, arg(args, 0)) else {
        return Err(err("IntersectionObserver needs a callback"));
    };
    let proto = po(it.protos.intersectionobserver);
    let targets = Value::Obj(it.arr_obj(Vec::new())?);
    let id = it.heap.alloc_obj(Obj::Ordinary {
        pairs: vec![
            ("__cb".into(), cb),
            ("__targets".into(), targets),
            ("__gen".into(), Value::Num(0.0)),
        ],
        proto,
    })?;
    Ok(Value::Obj(id))
}

/// Live (callback, targets array id, targets, generation) on an
/// observer instance; None when `this` is detached or clobbered.
fn io_state(it: &Interp, obs: Value) -> Option<(Value, u32, Vec<Value>, f64)> {
    let cb = get_prop(&it.heap, &it.protos, obs, "__cb").ok()?;
    let arr = match get_prop(&it.heap, &it.protos, obs, "__targets").ok()? {
        Value::Obj(a) => a,
        _ => return None,
    };
    let items = match it.heap.obj(arr) {
        Obj::Arr { items, .. } => items.clone(),
        _ => return None,
    };
    let gen = to_num(&it.heap, get_prop(&it.heap, &it.protos, obs, "__gen").ok()?);
    Some((cb, arr, items, gen))
}

fn n_io_observe(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let target = arg(args, 0);
    if it.as_node(target).is_none() {
        return Err(err("IntersectionObserver.observe needs a node"));
    }
    let Some((_, arr, items, gen)) = io_state(it, this) else {
        return Err(err("IntersectionObserver.observe needs an observer"));
    };
    if items.contains(&target) {
        return Ok(Value::Undef);
    }
    if let Obj::Arr { items, .. } = it.heap.obj_mut(arr) {
        items.push(target);
    }
    // Zero-timer entry for this target; the fire fn carries observer +
    // target + generation so removals win over scheduling.
    let fire = Value::Obj(it.heap.alloc_obj(nat("fireIo", n_io_fire))?);
    let st = Value::Obj(it.heap.alloc_obj(nat("setTimeout", n_set_timeout))?);
    let _ = it.call_value(st, Value::Undef, &[fire, Value::Num(0.0)], None);
    let _ = set_prop(&mut it.heap, fire, "__obs", this);
    let _ = set_prop(&mut it.heap, fire, "__target", target);
    let _ = set_prop(&mut it.heap, fire, "__gen", Value::Num(gen));
    Ok(Value::Undef)
}

fn n_io_unobserve(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let target = arg(args, 0);
    if it.as_node(target).is_none() {
        return Err(err("IntersectionObserver.unobserve needs a node"));
    }
    if let Some((_, arr, _, _)) = io_state(it, this) {
        if let Obj::Arr { items, .. } = it.heap.obj_mut(arr) {
            items.retain(|t| *t != target);
        }
    }
    Ok(Value::Undef)
}

fn n_io_disconnect(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    if let Some((_, arr, _, gen)) = io_state(it, this) {
        if let Obj::Arr { items, .. } = it.heap.obj_mut(arr) {
            items.clear();
        }
        let _ = set_prop(&mut it.heap, this, "__gen", Value::Num(gen + 1.0));
    }
    Ok(Value::Undef)
}

fn n_io_records(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    Ok(Value::Obj(it.arr_obj(Vec::new())?))
}

fn n_io_fire(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let me = it.cur_native;
    let obs = get_prop(&it.heap, &it.protos, me, "__obs")?;
    let target = get_prop(&it.heap, &it.protos, me, "__target")?;
    let gen_at = to_num(&it.heap, get_prop(&it.heap, &it.protos, me, "__gen")?);
    let Some((cb, _, items, gen)) = io_state(it, obs) else {
        return Ok(Value::Undef);
    };
    if gen != gen_at || !items.contains(&target) {
        return Ok(Value::Undef);
    }
    let Some(cb) = callable(it, cb) else {
        return Ok(Value::Undef);
    };
    let brect = Value::Obj(zero_rect(it)?);
    let irect = Value::Obj(zero_rect(it)?);
    let entry = it.obj_pairs(vec![
        ("target".into(), target),
        ("isIntersecting".into(), Value::Bool(true)),
        ("intersectionRatio".into(), Value::Num(1.0)),
        ("boundingClientRect".into(), brect),
        ("intersectionRect".into(), irect),
        ("rootBounds".into(), Value::Null),
        ("time".into(), Value::Num(it.perf_elapsed())),
    ])?;
    let entries = Value::Obj(it.arr_obj(vec![Value::Obj(entry)])?);
    let _ = it.call_value(cb, obs, &[entries, obs], None);
    Ok(Value::Undef)
}

/// window.matchMedia(query): static result (matches false - no layout
/// engine, so everything reads as the desktop default), with the
/// listener surface as no-ops. Bundles use it for responsive branches
/// and reduced-motion checks.
fn n_match_media(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let q = to_str(&it.heap, arg(args, 0));
    let qs = Value::Str(it.heap.alloc_str(q)?);
    let mut ids = Vec::new();
    for (n, f) in [
        ("addListener", n_history_noop as NativeFn),
        ("removeListener", n_history_noop),
        ("addEventListener", n_history_noop),
        ("removeEventListener", n_history_noop),
        ("dispatchEvent", n_history_noop),
    ] {
        ids.push((n.into(), Value::Obj(it.heap.alloc_obj(nat(n, f))?)));
    }
    ids.push(("matches".into(), Value::Bool(false)));
    ids.push(("media".into(), qs));
    ids.push(("onchange".into(), Value::Null));
    Ok(Value::Obj(it.obj_pairs(ids)?))
}

/// window.performance: wall-clock now()/timeOrigin plus empty entry
/// lists and no-op buffer controls (ruxit gates its timing features on
/// exactly this surface). No navigation entries are ever recorded.
fn n_perf_now(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    Ok(Value::Num(it.perf_elapsed()))
}

fn n_perf_empty_arr(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    Ok(Value::Obj(it.arr_obj(Vec::new())?))
}

fn n_perf_noop(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let _ = it;
    Ok(Value::Undef)
}

/// navigator.sendBeacon(url, data?): best-effort sync POST through the
/// page jar (traced like fetch), always true like V8 - failures never
/// surface to the caller.
pub(crate) fn n_send_beacon(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let raw = to_str(&it.heap, arg(args, 0));
    let data = arg(args, 1);
    if it.net.is_none() {
        return Ok(Value::Bool(true));
    }
    let bytes: Vec<u8> = match data {
        Value::Str(id) => it.heap.get_str(id).as_bytes().to_vec(),
        Value::Obj(bid) => match it.heap.obj(bid) {
            Obj::Arr { items, .. } => items
                .iter()
                .map(|x| to_u8(&it.heap, *x))
                .collect(),
            Obj::Bytes { bytes, .. } => bytes.clone(),
            Obj::Typed { elems, kind, .. } => {
                elems.iter().map(|e| to_u8_num(t_write(*kind, *e))).collect()
            }
            _ => to_str(&it.heap, data).into_bytes(),
        },
        Value::Undef | Value::Null => Vec::new(),
        _ => to_str(&it.heap, data).into_bytes(),
    };
    let ctx = it.net.as_mut().unwrap();
    if let Ok(url) = ctx.base.join(&raw) {
        let res = vigia_net::req(
            &url.to_string(),
            "POST",
            &[],
            if bytes.is_empty() { None } else { Some(&bytes) },
            &mut ctx.jar,
        );
        if let Some(trace) = &ctx.trace {
            let mut ev = NetEvent {
                method: "POST".into(),
                url: url.to_string(),
                status: 0,
                req_body: (!bytes.is_empty()).then(|| trunc_body(&String::from_utf8_lossy(&bytes))),
                resp_body: None,
                error: None,
            };
            match &res {
                Ok(r) => {
                    ev.status = r.status;
                }
                Err(e) => ev.error = Some(format!("{e:?}")),
            }
            trace.borrow_mut().push(ev);
        }
    }
    Ok(Value::Bool(true))
}

/// navigator.connection persona: steady desktop wifi (stormcaster
/// reads effectiveType/downlink/rtt when present, else a constant).
pub(crate) fn n_connection(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let et = Value::Str(it.heap.alloc_str("4g".into())?);
    Ok(Value::Obj(it.obj_pairs(vec![
        ("effectiveType".into(), et),
        ("downlink".into(), Value::Num(10.0)),
        ("rtt".into(), Value::Num(50.0)),
        ("saveData".into(), Value::Bool(false)),
    ])?))
}

/// navigator.geolocation: presence + V8-shaped toString. No position
/// fix is ever produced here (getCurrentPosition never fires its
/// callback - documented gap); existence is what the collectors probe.
pub(crate) fn n_geolocation(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let mut ids = Vec::new();
    for (n, f) in [
        ("getCurrentPosition", n_geolocation_noop as NativeFn),
        ("watchPosition", n_geolocation_noop),
        ("clearWatch", n_geolocation_noop),
        ("toString", n_geo_to_string),
    ] {
        ids.push((n.into(), Value::Obj(it.heap.alloc_obj(nat(n, f))?)));
    }
    Ok(Value::Obj(it.obj_pairs(ids)?))
}

fn n_geolocation_noop(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let _ = it;
    Ok(Value::Undef)
}

/// Geolocation.prototype.toString: "[object Geolocation]" (the
/// collector matches /object Geolocation/ against it explicitly).
fn n_geo_to_string(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    Ok(Value::Str(it.heap.alloc_str("[object Geolocation]".into())?))
}

/// navigator.userAgentData (Client Hints): Chrome 126 brand set +
/// getHighEntropyValues resolving the static dict.
pub(crate) fn n_user_agent_data(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let s_chromium = Value::Str(it.heap.alloc_str("Chromium".into())?);
    let s_gc = Value::Str(it.heap.alloc_str("Google Chrome".into())?);
    let s_nab = Value::Str(it.heap.alloc_str("Not-A.Brand".into())?);
    let v126 = Value::Str(it.heap.alloc_str("126".into())?);
    let v99 = Value::Str(it.heap.alloc_str("99".into())?);
    let s_linux = Value::Str(it.heap.alloc_str("Linux".into())?);
    let b1 = Value::Obj(it.obj_pairs(vec![
        ("brand".into(), s_chromium),
        ("version".into(), v126),
    ])?);
    let b2 = Value::Obj(it.obj_pairs(vec![("brand".into(), s_gc), ("version".into(), v126)])?);
    let b3 = Value::Obj(it.obj_pairs(vec![("brand".into(), s_nab), ("version".into(), v99)])?);
    let brands = Value::Obj(it.arr_obj(vec![b1, b2, b3])?);
    let ghe = Value::Obj(it.heap.alloc_obj(nat("getHighEntropyValues", n_ua_entropy))?);
    Ok(Value::Obj(it.obj_pairs(vec![
        ("brands".into(), brands),
        ("mobile".into(), Value::Bool(false)),
        ("platform".into(), s_linux),
        ("getHighEntropyValues".into(), ghe),
    ])?))
}

fn n_ua_entropy(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let dict = [
        ("architecture", "x86"),
        ("bitness", "64"),
        ("model", ""),
        ("platform", "Linux"),
        ("platformVersion", ""),
        ("uaFullVersion", "126.0.0.0"),
    ];
    let mut pairs = Vec::with_capacity(dict.len() + 2);
    for (k, v) in dict {
        pairs.push((k.into(), Value::Str(it.heap.alloc_str(v.to_string())?)));
    }
    let gc_brand = Value::Str(it.heap.alloc_str("Google Chrome".into())?);
    let full_ver = Value::Str(it.heap.alloc_str("126.0.0.0".into())?);
    let bfull = Value::Obj(it.obj_pairs(vec![
        ("brand".into(), gc_brand),
        ("version".into(), full_ver),
    ])?);
    let full = Value::Obj(it.arr_obj(vec![bfull])?);
    pairs.push(("fullVersionList".into(), full));
    pairs.push(("mobile".into(), Value::Bool(false)));
    let p = promise_new(it)?;
    let dict = Value::Obj(it.obj_pairs(pairs)?);
    it.promise_settle(p, false, dict);
    Ok(Value::Obj(p))
}

/// navigator.indexedDB: presence plus an open() that fails the V8 way
/// (async error event, never a sync throw). Offline-first libs degrade
/// through this path instead of crashing on a missing global.
pub(crate) fn n_indexed_db(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let _ = args;
    let open = Value::Obj(it.heap.alloc_obj(nat("open", n_idb_open))?);
    Ok(Value::Obj(it.obj_pairs(vec![("open".into(), open)] )?))
}

/// IDBRequest stub: {result, error, readyState} + onsuccess/onerror
/// expandos; the error event fires on a zero timer (denied backend).
fn n_idb_open(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let pending = Value::Str(it.heap.alloc_str("pending".into())?);
    let req = it.obj_pairs(vec![
        ("result".into(), Value::Undef),
        ("error".into(), Value::Undef),
        ("readyState".into(), pending),
        ("onsuccess".into(), Value::Null),
        ("onerror".into(), Value::Null),
    ])?;
    let req_v = Value::Obj(req);
    // Async denial: setTimeout fires the onerror expando, if any.
    let fire = Value::Obj(it.heap.alloc_obj(nat("fireDeny", n_idb_fire_deny))?);
    let st = Value::Obj(it.heap.alloc_obj(nat("setTimeout", n_set_timeout))?);
    let _ = it.call_value(st, Value::Undef, &[fire, Value::Num(0.0)], None);
    // Stash the request where the denial can find it (own expando).
    let _ = set_prop(&mut it.heap, fire, "__req", req_v);
    let _ = args;
    Ok(req_v)
}

fn n_idb_fire_deny(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let me = it.cur_native;
    let req = get_prop(&it.heap, &it.protos, me, "__req")?;
    let err = it.error_obj("IDB denied")?;
    let done = Value::Str(it.heap.alloc_str("done".into())?);
    let _ = set_prop(&mut it.heap, req, "error", err);
    let _ = set_prop(&mut it.heap, req, "readyState", done);
    if let Ok(Value::Obj(cb)) = get_prop(&it.heap, &it.protos, req, "onerror") {
        if matches!(it.heap.obj(cb), Obj::Func { .. } | Obj::Native { .. }) {
            let _ = it.call_value(Value::Obj(cb), req, &[err], None);
        }
    }
    Ok(Value::Undef)
}

// -- MessageChannel/MessagePort ----------------------------------------------
// React 18's scheduler prefers MessageChannel over setTimeout. Ports are
// ordinary objects with own function props (matchMedia shape); delivery
// is a zero timer like the IDB-denial path. The value passes by
// reference, NOT structuredClone. Listener surface is minimal:
// `onmessage` plus add/removeEventListener for 'message' only (no other
// types, no capture/once/passive options).
fn msg_port_obj(it: &mut Interp) -> Result<u32, JsError> {
    let mut pairs: Vec<(String, Value)> = Vec::new();
    for (n, f) in [
        ("postMessage", n_msg_post as NativeFn),
        ("start", n_msg_start),
        ("close", n_msg_close),
        ("addEventListener", n_msg_add_listener),
        ("removeEventListener", n_msg_remove_listener),
    ] {
        pairs.push((n.into(), Value::Obj(it.heap.alloc_obj(nat(n, f))?)));
    }
    pairs.push(("onmessage".into(), Value::Null));
    pairs.push(("__closed".into(), Value::Bool(false)));
    let cbs = Value::Obj(it.arr_obj(Vec::new())?);
    pairs.push(("__msg_cbs".into(), cbs));
    let proto = po(it.protos.object);
    it.heap.alloc_obj(Obj::Ordinary { pairs, proto })
}

fn n_msg_channel(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let a = msg_port_obj(it)?;
    let b = msg_port_obj(it)?;
    let _ = set_prop(&mut it.heap, Value::Obj(a), "__peer", Value::Obj(b));
    let _ = set_prop(&mut it.heap, Value::Obj(b), "__peer", Value::Obj(a));
    // instanceof MessageChannel: proto rides the ctor's prototype pair.
    let proto = match get_prop(&it.heap, &it.protos, it.cur_native, "prototype") {
        Ok(Value::Obj(p)) => Some(p),
        _ => po(it.protos.object),
    };
    let ch = it.heap.alloc_obj(Obj::Ordinary {
        pairs: vec![
            ("port1".into(), Value::Obj(a)),
            ("port2".into(), Value::Obj(b)),
        ],
        proto,
    })?;
    Ok(Value::Obj(ch))
}

/// Entangled peer for a postMessage, or None when either end closed
/// (close disentangles; late posts drop silently like a dead port).
fn msg_target(it: &Interp, this: Value) -> Option<Value> {
    let Value::Obj(_) = this else { return None };
    if truthy(
        &it.heap,
        get_prop(&it.heap, &it.protos, this, "__closed").unwrap_or(Value::Undef),
    ) {
        return None;
    }
    let peer = get_prop(&it.heap, &it.protos, this, "__peer").ok()?;
    let Value::Obj(_) = peer else { return None };
    if truthy(
        &it.heap,
        get_prop(&it.heap, &it.protos, peer, "__closed").unwrap_or(Value::Undef),
    ) {
        return None;
    }
    Some(peer)
}

fn n_msg_post(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let Value::Obj(_) = this else {
        return Err(err("MessagePort.postMessage needs a port"));
    };
    let Some(peer) = msg_target(it, this) else {
        return Ok(Value::Undef);
    };
    let fire = Value::Obj(it.heap.alloc_obj(nat("fireMsg", n_msg_fire))?);
    let st = Value::Obj(it.heap.alloc_obj(nat("setTimeout", n_set_timeout))?);
    let _ = it.call_value(st, Value::Undef, &[fire, Value::Num(0.0)], None);
    let _ = set_prop(&mut it.heap, fire, "__target", peer);
    let _ = set_prop(&mut it.heap, fire, "__msg", arg(args, 0));
    Ok(Value::Undef)
}

fn n_msg_fire(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let me = it.cur_native;
    let target = get_prop(&it.heap, &it.protos, me, "__target")?;
    let msg = get_prop(&it.heap, &it.protos, me, "__msg")?;
    // close() drops queued messages: a closed target swallows the fire.
    if truthy(
        &it.heap,
        get_prop(&it.heap, &it.protos, target, "__closed").unwrap_or(Value::Undef),
    ) {
        return Ok(Value::Undef);
    }
    let ev = Value::Obj(it.obj_pairs(vec![("data".into(), msg)])?);
    // onmessage is a plain expando like the IDB request's onerror: a
    // non-function value is ignored, never thrown.
    if let Ok(Value::Obj(cb)) = get_prop(&it.heap, &it.protos, target, "onmessage") {
        if matches!(it.heap.obj(cb), Obj::Func { .. } | Obj::Native { .. }) {
            let _ = it.call_value(Value::Obj(cb), target, &[ev], None);
        }
    }
    // addEventListener('message') callbacks, in registration order.
    let cbs = match get_prop(&it.heap, &it.protos, target, "__msg_cbs") {
        Ok(Value::Obj(a)) => match it.heap.obj(a) {
            Obj::Arr { items, .. } => items.clone(),
            _ => Vec::new(),
        },
        _ => Vec::new(),
    };
    for cb in cbs {
        if callable(it, cb).is_some() {
            let _ = it.call_value(cb, target, &[ev], None);
        }
    }
    Ok(Value::Undef)
}

fn n_msg_start(_it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    match this {
        Value::Obj(_) => Ok(Value::Undef),
        _ => Err(err("MessagePort.start needs a port")),
    }
}

fn n_msg_close(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let Value::Obj(_) = this else {
        return Err(err("MessagePort.close needs a port"));
    };
    let _ = set_prop(&mut it.heap, this, "__closed", Value::Bool(true));
    Ok(Value::Undef)
}

fn n_msg_add_listener(
    it: &mut Interp,
    this: Value,
    args: &[Value],
) -> Result<Value, JsError> {
    let Value::Obj(_) = this else {
        return Err(err("MessagePort.addEventListener needs a port"));
    };
    if to_str(&it.heap, arg(args, 0)) != "message" {
        return Ok(Value::Undef);
    }
    let Some(cb) = callable(it, arg(args, 1)) else {
        return Ok(Value::Undef);
    };
    let aid = match get_prop(&it.heap, &it.protos, this, "__msg_cbs") {
        Ok(Value::Obj(a)) if matches!(it.heap.obj(a), Obj::Arr { .. }) => a,
        _ => {
            let a = it.arr_obj(Vec::new())?;
            let _ = set_prop(&mut it.heap, this, "__msg_cbs", Value::Obj(a));
            a
        }
    };
    if let Obj::Arr { items, .. } = it.heap.obj_mut(aid) {
        items.push(cb);
    }
    Ok(Value::Undef)
}

fn n_msg_remove_listener(
    it: &mut Interp,
    this: Value,
    args: &[Value],
) -> Result<Value, JsError> {
    let Value::Obj(_) = this else {
        return Err(err("MessagePort.removeEventListener needs a port"));
    };
    if to_str(&it.heap, arg(args, 0)) != "message" {
        return Ok(Value::Undef);
    }
    let cb = arg(args, 1);
    // clone-filter-writeback: the strict_eq probe borrows the heap.
    let cur = match get_prop(&it.heap, &it.protos, this, "__msg_cbs") {
        Ok(Value::Obj(a)) => match it.heap.obj(a) {
            Obj::Arr { items, .. } => items.clone(),
            _ => Vec::new(),
        },
        _ => Vec::new(),
    };
    let kept: Vec<Value> = cur
        .into_iter()
        .filter(|c| !strict_eq(&it.heap, *c, cb))
        .collect();
    if let Ok(Value::Obj(a)) = get_prop(&it.heap, &it.protos, this, "__msg_cbs") {
        if let Obj::Arr { items, .. } = it.heap.obj_mut(a) {
            *items = kept;
        }
    }
    Ok(Value::Undef)
}

/// navigator.plugins / mimeTypes: Chrome PDF viewer persona. Real
/// plugin objects (indexed + named access, length) so presence and
/// enumeration read desktop-Chrome-like. No actual viewers behind them.
fn n_mime_obj(it: &mut Interp, typ: &str, suffixes: &str) -> Result<Value, JsError> {
    let t = Value::Str(it.heap.alloc_str(typ.to_string())?);
    let s = Value::Str(it.heap.alloc_str(suffixes.to_string())?);
    let d = Value::Str(it.heap.alloc_str("".into())?);
    Ok(Value::Obj(it.obj_pairs(vec![
        ("type".into(), t),
        ("suffixes".into(), s),
        ("description".into(), d),
    ])?))
}

fn n_plugin_item(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    // item(i)/namedItem(name): the single mime when the key matches.
    let key = to_str(&it.heap, arg(args, 0));
    let mime = get_prop(&it.heap, &it.protos, this, "0")?;
    if key == "0" {
        return Ok(mime);
    }
    let mtype = match get_prop(&it.heap, &it.protos, mime, "type") {
        Ok(Value::Str(id)) => it.heap.get_str(id).to_string(),
        _ => String::new(),
    };
    if !mtype.is_empty() && key == mtype {
        Ok(mime)
    } else {
        Ok(Value::Null)
    }
}

fn n_plugin_obj(
    it: &mut Interp,
    name: &str,
    filename: &str,
    desc: &str,
    mime: Value,
) -> Result<Value, JsError> {
    let n = Value::Str(it.heap.alloc_str(name.to_string())?);
    let f = Value::Str(it.heap.alloc_str(filename.to_string())?);
    let d = Value::Str(it.heap.alloc_str(desc.to_string())?);
    let item = Value::Obj(it.heap.alloc_obj(nat("item", n_plugin_item))?);
    let named = Value::Obj(it.heap.alloc_obj(nat("namedItem", n_plugin_item))?);
    Ok(Value::Obj(it.obj_pairs(vec![
        ("0".into(), mime),
        ("name".into(), n),
        ("filename".into(), f),
        ("description".into(), d),
        ("length".into(), Value::Num(1.0)),
        ("item".into(), item),
        ("namedItem".into(), named),
    ])?))
}

pub(crate) fn n_plugins_arr(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let pdf = n_mime_obj(it, "application/pdf", "pdf")?;
    let chrome_pdf = n_mime_obj(it, "application/x-google-chrome-pdf", "pdf")?;
    let p1 = n_plugin_obj(
        it,
        "Chrome PDF Viewer",
        "internal-pdf-viewer",
        "Portable Document Format",
        pdf,
    )?;
    let p2 = n_plugin_obj(
        it,
        "Chromium PDF Viewer",
        "internal-pdf-viewer",
        "Portable Document Format",
        chrome_pdf,
    )?;
    let item = Value::Obj(it.heap.alloc_obj(nat("item", n_plugins_item))?);
    let named = Value::Obj(it.heap.alloc_obj(nat("namedItem", n_plugins_item))?);
    let refresh = Value::Obj(it.heap.alloc_obj(nat("refresh", n_plugins_refresh))?);
    Ok(Value::Obj(it.obj_pairs(vec![
        ("0".into(), p1),
        ("1".into(), p2),
        ("length".into(), Value::Num(2.0)),
        ("item".into(), item),
        ("namedItem".into(), named),
        ("refresh".into(), refresh),
    ])?))
}

fn n_plugins_item(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    // item(i)/namedItem(name) over the two entries.
    let key = to_str(&it.heap, arg(args, 0));
    for k in ["0", "1"] {
        let p = get_prop(&it.heap, &it.protos, this, k)?;
        if key == k {
            return Ok(p);
        }
        if let Value::Obj(id) = p {
            if let Obj::Ordinary { pairs, .. } = it.heap.obj(id) {
                if let Some((_, v)) = pairs.iter().find(|(kk, _)| kk == &"name") {
                    if to_str(&it.heap, *v) == key {
                        return Ok(p);
                    }
                }
            }
        }
    }
    Ok(Value::Null)
}

fn n_plugins_refresh(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let _ = it;
    Ok(Value::Undef)
}

pub(crate) fn n_mimetypes_arr(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let m1 = n_mime_obj(it, "application/pdf", "pdf")?;
    let m2 = n_mime_obj(it, "application/x-google-chrome-pdf", "pdf")?;
    let item = Value::Obj(it.heap.alloc_obj(nat("item", n_plugins_item))?);
    let named = Value::Obj(it.heap.alloc_obj(nat("namedItem", n_plugins_item))?);
    Ok(Value::Obj(it.obj_pairs(vec![
        ("0".into(), m1),
        ("1".into(), m2),
        ("length".into(), Value::Num(2.0)),
        ("item".into(), item),
        ("namedItem".into(), named),
    ])?))
}

/// `Function(p1, .., pn, body)` / `new Function(...)`: params and body
/// are source fragments, compiled in global scope like V8 (sloppy).
/// Parse errors surface as plain errors (SyntaxError shape at catch).
fn n_function_ctor(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let mut params = Vec::with_capacity(args.len().saturating_sub(1));
    for a in args.iter().take(args.len().saturating_sub(1)) {
        params.push(to_str(&it.heap, *a));
    }
    let body = match args.last() {
        Some(v) => to_str(&it.heap, *v),
        None => String::new(),
    };
    let src = format!("(function anonymous({}){{{}}})", params.join(","), body);
    let stmts = crate::parse::parse_program(&src)?;
    let [Stmt::Expr(Expr::Func(def))] = stmts.as_slice() else {
        return Err(err("Function could not compile"));
    };
    Ok(Value::Obj(it.func_obj(def.clone(), 0)?))
}
fn n_atob(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let s = to_str(&it.heap, arg(args, 0));
    let mut clean: Vec<u8> = Vec::with_capacity(s.len());
    for b in s.bytes() {
        if matches!(b, b'\t' | b'\n' | b'\x0C' | b'\r' | b' ') {
            continue;
        }
        clean.push(b);
    }
    if clean.len() % 4 == 1 {
        return Err(err("Invalid character in atob"));
    }
    while !clean.len().is_multiple_of(4) {
        clean.push(b'=');
    }
    let mut out = String::new();
    for w in clean.as_chunks::<4>().0 {
        let pad = w.iter().rev().take_while(|&&b| b == b'=').count();
        if pad > 2 {
            return Err(err("Invalid character in atob"));
        }
        let mut n: u32 = 0;
        for (i, &b) in w.iter().enumerate() {
            if b == b'=' {
                if i < 4 - pad {
                    return Err(err("Invalid character in atob"));
                }
                n <<= 6;
            } else {
                let Some(v) = b64_val(b) else {
                    return Err(err("Invalid character in atob"));
                };
                n = (n << 6) | v as u32;
            }
        }
        out.push((n >> 16) as u8 as char);
        if pad < 2 {
            out.push(((n >> 8) & 0xFF) as u8 as char);
        }
        if pad < 1 {
            out.push((n & 0xFF) as u8 as char);
        }
    }
    Ok(Value::Str(it.heap.alloc_str(out)?))
}

fn n_btoa(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    const ALPHA: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let s = to_str(&it.heap, arg(args, 0));
    let bytes = s.as_bytes();
    if s.chars().any(|c| c as u32 > 255) {
        return Err(err("Invalid character in btoa"));
    }
    let mut out = String::new();
    for w in bytes.chunks(3) {
        let (b0, b1, b2) = (w[0], *w.get(1).unwrap_or(&0), *w.get(2).unwrap_or(&0));
        out.push(ALPHA[(b0 >> 2) as usize] as char);
        out.push(ALPHA[(((b0 & 3) << 4) | (b1 >> 4)) as usize] as char);
        out.push(if w.len() > 1 {
            ALPHA[(((b1 & 15) << 2) | (b2 >> 6)) as usize] as char
        } else {
            '='
        });
        out.push(if w.len() > 2 { ALPHA[(b2 & 63) as usize] as char } else { '=' });
    }
    Ok(Value::Str(it.heap.alloc_str(out)?))
}

// ---- async runtime: promises, microtasks, timers -----------------------------
// Synchronous engine, real ordering: handlers queue as microtasks and run at
// drain() points (end of each run(), after each fire() event dispatch). Timers
// share the drain on a virtual clock - deadlines order firing, now_ms jumps to
// each deadline instead of sleeping. Caps: 4096 timer fires per drain; the
// microtask loop ticks steps so max_steps bounds it.

/// Fresh pending promise.
fn promise_new(it: &mut Interp) -> Result<u32, JsError> {
    it.heap.alloc_obj(Obj::Promise {
        st: PromiseState::Pending {
            handlers: Vec::new(),
        },
        pairs: Vec::new(),
    })
}

/// Heap id if `v` is a Promise.
fn as_promise(it: &Interp, v: Value) -> Option<u32> {
    match v {
        Value::Obj(id) if matches!(it.heap.obj(id), Obj::Promise { .. }) => Some(id),
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
// Per-timer fires per drain: one re-arming timer (polling heartbeat,
// scheduler pump) must not starve the rest of the queue. 32 keeps
// heartbeats progressing and leaves distinct-timer bursts untouched
// (each timer gets its own 32); MAX_TIMER_FIRES stays the total backstop.
const MAX_TIMER_QUOTA: u32 = 32;

impl Interp {
    /// Settle a pending promise and queue one microtask per registered
    /// handler (a missing handler passes the outcome through). No-op on
    /// an already-settled promise.
    pub(crate) fn promise_settle(&mut self, id: u32, rejecting: bool, v: Value) {
        let st = match self.heap.obj_mut(id) {
            Obj::Promise { st, .. } => st,
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
            Obj::Promise { st: PromiseState::Fulfilled(u), .. } => Adopt::Fulfill(*u),
            Obj::Promise { st: PromiseState::Rejected(r), .. } => Adopt::Reject(*r),
            _ => Adopt::Subscribe,
        };
        match act {
            Adopt::Fulfill(u) => self.promise_settle(id, false, u),
            Adopt::Reject(r) => self.promise_settle(id, true, r),
            Adopt::Subscribe => {
                if let Obj::Promise { st: PromiseState::Pending { handlers }, .. } = self.heap.obj_mut(pid) {
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
            Obj::Promise { st: PromiseState::Pending { .. }, .. } => S::Pend,
            Obj::Promise { st: PromiseState::Fulfilled(v), .. } => S::Ful(*v),
            Obj::Promise { st: PromiseState::Rejected(r), .. } => S::Rej(*r),
            _ => S::Pend,
        };
        match s {
            S::Pend => {
                if let Obj::Promise { st: PromiseState::Pending { handlers }, .. } = self.heap.obj_mut(id) {
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
        let mut quota: std::collections::HashMap<u64, u32> = std::collections::HashMap::new();
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
                .filter(|(_, t)| quota.get(&t.seq).copied().unwrap_or(0) < MAX_TIMER_QUOTA)
                .min_by_key(|(_, t)| (t.deadline_ms, t.seq))
                .map(|(i, _)| i);
            // No eligible timer: queue dry, or only over-quota re-armers
            // left. Either way park silently like the cap path below.
            let Some(i) = pick else { break 'outer };
            fires += 1;
            if fires > MAX_TIMER_FIRES {
                // Snapshot model: live pages re-arm timers forever
                // (heartbeats, polling chains). Park the rest silently
                // instead of failing the script - CPU runaway is still
                // guarded by max_steps, and convergence needs far fewer.
                break 'outer;
            }
            self.now_ms = self.now_ms.max(self.timers[i].deadline_ms);
            let (cb, args, seq) = {
                let t = &mut self.timers[i];
                t.parked = true; // a nested drain (event dispatch) can't re-fire it
                (t.cb, t.args.clone(), t.seq)
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
            *quota.entry(seq).or_insert(0) += 1;
            // keep the vec from growing on churny pages
            if self.timers.len() > 64 {
                self.timers.retain(|t| !t.cancelled);
            }
            self.maybe_gc();
        }
        let mut unhandled = Vec::new();
        for i in 0..self.heap.objs.len() as u32 {
            if let Obj::Promise { st: PromiseState::Rejected(r), .. } = self.heap.obj(i) {
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
        Value::Obj(id) if matches!(it.heap.obj(id), Obj::Promise { .. }) => Ok(id),
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
        if matches!(it.heap.obj(id), Obj::Promise { st: PromiseState::Rejected(_), .. }))
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
        Obj::Promise { st: PromiseState::Fulfilled(v), .. } => Some((false, *v)),
        Obj::Promise { st: PromiseState::Rejected(r), .. } => Some((true, *r)),
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
    if let Obj::Promise { st: PromiseState::Pending { handlers }, .. } = it.heap.obj_mut(pid) {
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
    let seq = it.timer_seq;
    it.timer_seq = it.timer_seq.wrapping_add(1);
    it.timers.push(Timer {
        id,
        seq,
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
    fn completion_isolation() {
        // Statements inside called functions (incl. timer callbacks)
        // never leak into the top-level completion value.
        assert_eq!(disp("function f(){var q=1;q+1}f();42"), "42");
        assert_eq!(disp("var r='';[1,2].forEach(function(x){r+=x;'inner'});'outer'"), "outer");
    }

    #[test]
    fn spreads() {
        assert_eq!(num("function s(a,b,c){return a+b+c}s(...[1,2,3])"), 6.0);
        assert_eq!(disp("[0, ...[1,2], 3]"), "[0,1,2,3]");
        assert_eq!(disp("({...( {a: 1}), a: 9}).a"), "9");
        assert_eq!(disp("({x: 1, ...null}).x"), "1");
        assert_eq!(disp("({...'hi'})[1]"), "i");
        assert!(errmsg("var x = [...5]").contains("non-iterable"));
    }

    #[test]
    fn comma_operator() {
        assert_eq!(num("var x = (1, 2);x"), 2.0);
        assert_eq!(num("function f(a,b){return a-b}f(1,2)"), -1.0);
        assert_eq!(num("function f(){return 1, 2}f()"), 2.0);
        assert_eq!(num("var t=0;for(var i=0,j=10;i<3;i++,j--)t+=j;t"), 27.0);
        assert_eq!(disp("var x = 1, y = 2;x+y"), "3");
    }

    #[test]
    fn default_params() {
        assert_eq!(num("function f(a,b=5){return a+b}f(1)"), 6.0);
        assert_eq!(num("function f(a,b=5){return a+b}f(1,2)"), 3.0);
        assert_eq!(num("function f(a,b=5){return a+b}f(1,undefined)"), 6.0);
        assert_eq!(num("var g=(x=3)=>x*2;g()"), 6.0);
        assert_eq!(num("var g=(x=3)=>x*2;g(4)"), 8.0);
        assert_eq!(num("function f(a,b=a+1){return b}f(1)"), 2.0);
    }

    #[test]
    fn env_gc_on_demand() {
        // Block/call env churn past max_envs recycles instead of dying:
        // the obfuscator-style loop below needs ~thousands of envs.
        let mut it = Interp::new();
        it.max_envs = 200;
        it.run("var s=0;for(var i=0;i<5000;i++){try{s+=i}catch(e){s-=1}}")
            .unwrap();
        match it.run("s").unwrap() {
            Value::Num(n) => assert_eq!(n, 12497500.0),
            v => panic!("{v:?}"),
        }
    }

    /// Elisions read as undefined (holes have no observable slot here;
    /// length still counts them, like real arrays).
    #[test]
    fn array_expando() {
        // Webpack's chunk trick: overriding push on the instance.
        assert_eq!(
            disp("var a=[1];a.push=function(x){return 'w'+x};a.push(2)"),
            "w2"
        );
        assert_eq!(disp("var a=[1];a.foo=7;a.foo"), "7");
        assert_eq!(disp("var a=[1];a.foo=7;delete a.foo;a.foo"), "undefined");
        assert_eq!(
            disp("var a=[1,2];var k='';for(var x in a)k+=x+',';k"),
            "0,1,"
        );
        assert_eq!(disp("var a=[1];a.foo=7;Object.keys(a).join()"), "0,foo");
    }

    #[test]
    fn array_length_write() {
        assert_eq!(disp("var a=[1,2,3];a.length=1;a.length"), "1");
        assert_eq!(disp("var a=[1,2,3];a.length=1;a.join()"), "1");
        assert_eq!(disp("var a=[1];a[3]='x';a.length"), "4");
        assert_eq!(disp("var a=[1];a[3]='x';a[1]"), "undefined");
        assert!(errmsg("var a=[];a.length=-1").contains("bad array length"));
    }

    #[test]
    fn array_holes() {
        assert_eq!(disp("[5,7,,8].length"), "4");
        assert_eq!(disp("[5,7,,8][2]"), "undefined");
        assert_eq!(disp("[,]"), "[null]");
        assert_eq!(disp("[1,].length"), "1");
    }

    #[test]
    fn generators_stubbed() {
        // Eager subset: call returns an object; first next() runs the body.
        assert_eq!(disp("function*g(){yield 1;yield 2;return 9}var i=g();i.next().value"), "9");
        assert_eq!(disp("var o={*m(){yield 7;return 8}};o.m().next().value"), "8");
        assert_eq!(disp("class C{*m(){yield}}new C().m().next().value"), "undefined");
        // `yield` stays an identifier outside generators.
        assert_eq!(disp("var yield=5;yield+1"), "6");
        assert!(errmsg("class C{*constructor(){}}").contains("may not be a generator"));
        assert!(errmsg("var o={*get x(){return 1}}").contains("accessor"));
    }

    #[test]
    fn generators_eager() {
        // Call returns an object, not the function result.
        assert_eq!(disp("function*g(){return 5}typeof g()"), "object");
        assert_eq!(disp("function*g(){return 5}var i=g();typeof i.next"), "function");
        // No-yield body: value/done plus eagerness ordering (side effects
        // happen at first next(), never at call time).
        assert_eq!(disp("function*g(){return 42}var i=g();var s=i.next();s.value"), "42");
        assert_eq!(disp("function*g(){return 42}var i=g();i.next().done"), "true");
        assert_eq!(
            disp("var n=0;function*g(){n++;return 1}var i=g();var a=n;var s=i.next();a+'|'+n+'|'+s.value"),
            "0|1|1"
        );
        // `yield` still reads undefined; the whole body ran at first next().
        assert_eq!(disp("function*g(){var y=yield 5;return y===undefined}var i=g();i.next().value"), "true");
        assert_eq!(
            disp("var log=[];function*g(){log.push(1);yield 2;log.push(3);return 4}var i=g();var a=log.length;var s=i.next();a+'|'+s.value+'|'+s.done+'|'+log.length"),
            "0|4|true|2"
        );
        // Later next()s are done; return()/throw() settle immediately.
        assert_eq!(disp("function*g(){return 1}var i=g();i.next();var s=i.next();s.value+'|'+s.done"), "undefined|true");
        assert_eq!(disp("function*g(){return 1}var i=g();var s=i.return(9);s.value+'|'+s.done"), "9|true");
        assert_eq!(disp("var n=0;function*g(){n++;return 1}var i=g();i.return(5);n"), "0");
        assert_eq!(disp("function*g(){return 1}var i=g();try{i.throw(new Error('x'))}catch(e){e.message}"), "x");
        assert_eq!(disp("function*g(){return 1}var i=g();try{i.throw(7)}catch(e){e}i.next().done"), "true");
        // A body throw marks done and rethrows with the value verbatim.
        assert_eq!(disp("function*g(){throw new Error('b')}var i=g();try{i.next()}catch(e){e.message}"), "b");
        assert_eq!(disp("function*g(){throw 3}var i=g();try{i.next()}catch(e){e}i.next().done"), "true");
        // Args and receiver survive until first next().
        assert_eq!(disp("function*g(a,b){return a+b}var i=g(2,3);i.next().value"), "5");
        assert_eq!(disp("var o={x:9,*m(){return this.x}};o.m().next().value"), "9");
        // `new` on a generator function throws (V8 parity).
        assert!(errmsg("new (function*(){})").contains("not a constructor"));
        assert!(errmsg("function*g(){}new g()").contains("not a constructor"));
    }

    #[test]
    fn generator_runner_pattern() {
        // Maps-loader shape: a runner calling .next() immediately and
        // adopting the returned promise must resolve to 42.
        assert_eq!(
            out("function runner(gf){return new Promise(function(res,rej){var i=gf();function step(){var s;try{s=i.next();}catch(e){rej(e);return;}if(s.done){res(s.value);}else{Promise.resolve(s.value).then(function(v){step();},rej);}}step();});}\
                 runner(function*(){return Promise.resolve(42)}).then(function(v){console.log(v)})"),
            "42\n"
        );
        // Rejections through the same runner reject the outer promise.
        assert_eq!(
            out("function runner(gf){return new Promise(function(res,rej){var i=gf();function step(){var s;try{s=i.next();}catch(e){rej(e);return;}if(s.done){res(s.value);}else{Promise.resolve(s.value).then(function(v){step();},rej);}}step();});}\
                 runner(function*(){throw new Error('nope')}).then(function(){console.log('bad')},function(e){console.log(e.message)})"),
            "nope\n"
        );
    }

    #[test]
    fn async_object_methods() {
        assert_eq!(
            disp("var o={async m(){return 7}};o.m() instanceof Promise"),
            "true"
        );
        assert_eq!(
            out("var o={async m(){return 7}};o.m().then(function(v){console.log(v)})"),
            "7\n"
        );
        // `async` stays a plain key when not a modifier.
        assert_eq!(disp("var o={async:1};o.async"), "1");
        assert_eq!(disp("var o={async(){return 2}};o.async()"), "2");
    }

    #[test]
    fn delete_operator() {
        assert_eq!(disp("var o={a:1,b:2};delete o.a"), "true");
        assert_eq!(disp("var o={a:1};delete o.a;o.a"), "undefined");
        assert_eq!(disp("var o={a:1};delete o.a;('a' in o)"), "false");
        assert_eq!(disp("var a=[1,2,3];delete a[0];a.length"), "3");
        assert_eq!(disp("var a=[1,2,3];delete a[0];a[0]"), "undefined");
        assert_eq!(disp("var x=1;delete x"), "false");
        assert_eq!(disp("delete 1"), "true");
        assert!(errmsg("delete null.x").contains("cannot delete"));
    }

    #[test]
    fn annex_b_block_functions() {
        // Sloppy Annex B: block-level declarations hoist to fn scope.
        assert_eq!(disp("if(true){function ge(){return 42}}ge()"), "42");
        assert_eq!(disp("var f;if(true){function ge(){return 1}}f=ge;f()"), "1");
        assert_eq!(disp("function o(){if(true){function g(){return 2}}return g()}o()"), "2");
        assert_eq!(disp("typeof neverdef !== 'undefined' ? 1 : 1"), "1");
        // Single-statement positions declare on execution.
        assert_eq!(disp("if(true)function h(){return 3}h()"), "3");
    }

    #[test]
    fn error_stacks() {
        // Thrown Errors carry a V8-shaped stack (head + at-frames).
        assert_eq!(
            disp("function a(){throw new Error('x')}function b(){a()}try{b()}catch(e){e.stack.split('\\n')[0]}"),
            "Error: x"
        );
        assert_eq!(
            disp("function a(){throw new Error('x')}function b(){a()}try{b()}catch(e){e.stack.split('\\n')[1].trim()}"),
            "at a"
        );
        // Engine errors materialize with stacks too (React parses them).
        assert_eq!(
            disp("function f(){nope()}try{f()}catch(e){e instanceof Error}"),
            "true"
        );
        assert_eq!(
            disp("function f(){nope()}try{f()}catch(e){typeof e.stack}"),
            "string"
        );
        // Custom stacks survive the unwind untouched.
        assert_eq!(
            disp("var e=new Error('x');e.stack='custom';try{throw e}catch(r){r.stack}"),
            "custom"
        );
    }

    #[test]
    fn promise_expandos() {
        // Deferred pattern (i18next): resolve/reject live on the promise.
        assert_eq!(
            disp("function defer(){var e,t,n=new Promise(function(a,b){e=a;t=b});n.resolve=e;n.reject=t;return n}\
                  var d=defer();typeof d.resolve+'|'+typeof d.reject"),
            "function|function"
        );
        assert_eq!(
            disp("function defer(){var e,n=new Promise(function(a){e=a});n.resolve=e;return n}\
                  var d=defer();d.resolve(42);d instanceof Promise"),
            "true"
        );
        assert_eq!(disp("var p=new Promise(function(){});p.x=1;p.x"), "1");
        assert_eq!(disp("var p=new Promise(function(){});p.x=1;Object.keys(p).join()"), "x");
        assert_eq!(disp("var p=new Promise(function(){});p.x=1;delete p.x;('x' in p)"), "false");
    }

    #[test]
    fn sloppy_this() {
        // Bare calls coerce nullish receivers (V8 sloppy; Undef without
        // a DOM since there is no global object there).
        assert_eq!(disp("function f(){return this}f()"), "undefined");
        assert_eq!(disp("function f(){return this}f.call(null)"), "undefined");
        assert_eq!(disp("var o={m:function(){return this}};o.m()===o"), "true");
    }

    #[test]
    fn fn_name_shadowed_by_param() {
        // A param (or rest) named like the function wins over the
        // self-name (minified React schedulers do `function t(t,n)`).
        assert_eq!(disp("function t(t,n){return t}t(null,1)"), "null");
        assert_eq!(disp("function g(g){return g}g(42)"), "42");
        assert_eq!(disp("var f=function f(){return typeof f};f()"), "function");
        assert_eq!(disp("function h(){return typeof h}h()"), "function");
        // ...and the param (not the function) is what member reads see.
        assert!(errmsg("function t(t,n){var a=t.deletions}t(null,1)").contains("deletions"));
    }

    #[test]
    fn assign_order() {
        // V8: LHS reference (with side effects) evaluates before RHS.
        assert_eq!(disp("function h(e){ (e={a:1}).p={c:e}; return e.p.c===e; }h(0)"), "true");
        assert_eq!(
            disp("var log='';var o={};o[get('k')]=get('v');log;function get(s){log+=s;return s}"),
            "kv"
        );
        // Compound reads current before RHS runs.
        assert_eq!(
            disp("var log='';var o={n:1};o.n+=get('v');log;function get(s){log+=s;return s}"),
            "v"
        );
        assert_eq!(disp("var o={n:1};o.n+=2;o.n"), "3");
        assert_eq!(disp("var o={};o['k']=5;o.k"), "5");
    }

    #[test]
    fn fndecl_identity() {
        // A declaration materializes once per entry: later mutations of
        // the prototype are visible through the same binding (Babel
        // _inherits shape: prototype replaced between def and use).
        assert_eq!(
            disp("function N(){}N.prototype=Object.create({},{});\
                  Object.defineProperty(N,'prototype',{writable:false});\
                  Object.defineProperty(N.prototype,'use',{value:function(){return 7}});\
                  var zA=new N();zA.use()"),
            "7"
        );
        // Two declarations, last wins, no resurrection of the first.
        assert_eq!(disp("function f(){return 1}function f(){return 2}f()"), "2");
        // Identity is stable across the hoist/execute boundary.
        assert_eq!(disp("function f(){};var g=f;g===f"), "true");
    }

    #[test]
    fn var_hoisting() {
        // `var` reads undefined before its statement (function scope).
        assert_eq!(disp("var r=typeof v;var v=1;r"), "undefined");
        // `var` leaks out of blocks and loops.
        assert_eq!(disp("{var b=2}b"), "2");
        assert_eq!(disp("for(var i=0;i<3;i++){}i"), "3");
        assert_eq!(disp("function f(){if(true){var z=9}}f();typeof z"), "undefined");
        // ...but stays inside functions.
        assert_eq!(disp("function f(){var q=1}try{f()}catch(e){}typeof q"), "undefined");
        // `let` keeps TDZ and block scope.
        assert!(errmsg("x;let x=1").contains("not defined"));
        assert!(errmsg("{let y=1}y").contains("not defined"));
        // `var` never overwrites a hoisted function.
        assert_eq!(disp("function f(){};var f;typeof f"), "function");
    }

    #[test]
    fn for_var_hoisting() {
        // `var` in a for-init or for-in/of target hoists function-wide:
        // a path that runs before the loop must see the (undefined)
        // local, never the same-named global. React 18 prod's
        // bubbleProperties has exactly this shape
        // (`if(b)for(var e=...)...else for(e=...)...`) and used to
        // clobber the page's `var e = React.createElement` global,
        // so every update render threw "e is not a function".
        assert_eq!(
            disp("var e='global';function W(a){var b=a>0;if(b){for(var e=0;e<1;e++){}}else{for(e=0;e<1;e++){}}return e}W(0);e"),
            "global"
        );
        assert_eq!(
            disp("var k='G';function F(a){if(a){for(var k in {x:1}){}}else{k='L'}return k}F(0);k"),
            "G"
        );
        assert_eq!(
            disp("var v='G';function G(a){if(a){for(var v of [1]){}}else{v='L'}return v}G(0);v"),
            "G"
        );
        // The hoisted local reads undefined before the loop runs...
        assert_eq!(
            disp("function f(a){if(a){for(var e=0;e<1;e++){}}return typeof e}f(0)"),
            "undefined"
        );
        // ...and `let`/`const` loop targets still stay loop-scoped.
        assert_eq!(
            disp("function f(a){if(a){for(let q=0;q<1;q++){}}return typeof q}f(0)"),
            "undefined"
        );
    }

    #[test]
    fn error_subtypes() {        assert_eq!(disp("new TypeError('x').name"), "TypeError");
        assert_eq!(disp("new TypeError('x').toString()"), "TypeError: x");
        assert_eq!(disp("new RangeError('r') instanceof Error"), "true");
        assert_eq!(disp("new TypeError('t') instanceof TypeError"), "true");
        assert_eq!(disp("new SyntaxError('s').message"), "s");
        assert_eq!(disp("new ReferenceError('r').name"), "ReferenceError");
        assert_eq!(disp("typeof TypeError"), "function");
    }

    #[test]
    fn throw_chain_context() {        // Uncaught thrown Errors carry the innermost call chain.
        assert_eq!(
            errmsg("function a(){throw new Error('x')}function b(){a()}b()"),
            "Error: x (in b > a)"
        );
        // Caught throws leave no stale chain for later errors.
        assert_eq!(
            errmsg("function a(){throw new Error('x')}try{a()}catch(e){}throw new Error('y')"),
            "Error: y"
        );
    }

    #[test]
    fn define_property_keeps_value() {
        // Attribute-only descriptors don't touch the value (Babel emits
        // `defineProperty(C, "prototype", {writable:false})` per class).
        assert_eq!(
            disp("function C(){this.v=1}Object.defineProperty(C,'prototype',{writable:false});var o=new C();o.v"),
            "1"
        );
        assert_eq!(
            disp("function C(){}Object.defineProperty(C,'prototype',{writable:false});new C() instanceof C"),
            "true"
        );
        assert_eq!(disp("var o={k:3};Object.defineProperty(o,'k',{enumerable:true});o.k"), "3");
        assert_eq!(disp("var o={};Object.defineProperty(o,'k',{enumerable:true});o.k"), "undefined");
        assert_eq!(disp("var o={};Object.defineProperty(o,'k',{value:42});o.k"), "42");
    }

    #[test]
    fn proxy_forwarding() {
        // No traps: transparent forwarding to the target.
        assert_eq!(disp("var p=new Proxy({a:1},{});p.a"), "1");
        assert_eq!(disp("var p=new Proxy({a:1},{});'a' in p"), "true");
        assert_eq!(disp("var p=new Proxy({a:1},{});Object.keys(p).join()"), "a");
        assert_eq!(disp("var p=new Proxy({a:1},{});typeof p"), "object");
        assert_eq!(disp("var t={a:1};var p=new Proxy(t,{});p.b=2;t.b"), "2");
        assert_eq!(disp("var p=new Proxy({a:1},{});p instanceof Object"), "true");
        assert_eq!(
            disp("var p=new Proxy({a:1},{});Object.getPrototypeOf(p)===Object.prototype"),
            "true"
        );
        assert_eq!(disp("var p=new Proxy({s:5},{});JSON.stringify({...p})"), "{\"s\":5}");
        assert_eq!(disp("Object.prototype.toString.call(new Proxy({},{}))"), "[object Object]");
        assert_eq!(disp("var p=new Proxy({a:1},{});delete p.a;('a' in p)"), "false");
        // for-in enumerates the target (ownKeys trap gap).
        assert_eq!(disp("var s='';for(var k in new Proxy({a:1},{})){s+=k}s"), "a");
        // Target and handler must be objects.
        assert!(errmsg("new Proxy(1,{})").contains("object target"));
        assert!(errmsg("new Proxy({},1)").contains("object target"));
        assert!(errmsg("new Proxy({},null)").contains("object target"));
    }

    #[test]
    fn proxy_traps() {
        // get/has/set/deleteProperty traps run at the recv_ level.
        assert_eq!(disp("var q=new Proxy({x:1},{get:(o,k)=>k==='x'?42:o[k]});q.x"), "42");
        assert_eq!(
            disp("var q=new Proxy({},{has:(o,k)=>k==='y'});('y' in q)"),
            "true"
        );
        assert_eq!(
            disp("var q=new Proxy({},{has:(o,k)=>k==='y'});('z' in q)"),
            "false"
        );
        assert_eq!(
            disp("var r=new Proxy({m:1},{set:(o,k,v)=>{o[k]=v*10;return true}});r.m=3;r.m"),
            "30"
        );
        assert_eq!(
            disp("var q=new Proxy({x:1},{get:(o,k)=>42});delete q.x;q.x"),
            "42"
        );
        assert_eq!(
            disp("var seen='';var q=new Proxy({},{deleteProperty:(o,k)=>{seen=k;return true}});delete q.z;seen"),
            "z"
        );
    }

    #[test]
    fn reflect_basics() {
        assert_eq!(disp("Reflect.get({g:7},'g')"), "7");
        assert_eq!(disp("Reflect.has({},'toString')"), "true");
        assert_eq!(disp("var o={};Reflect.set(o,'k',9);o.k"), "9");
        assert_eq!(disp("var o={v:1};Reflect.deleteProperty(o,'v');('v' in o)"), "false");
        assert_eq!(disp("Reflect.getOwnPropertyDescriptor({v:9},'v').value"), "9");
        assert_eq!(disp("Reflect.getOwnPropertyDescriptor({},'nope')"), "undefined");
        assert_eq!(disp("Reflect.getPrototypeOf([])===Array.prototype"), "true");
        assert_eq!(disp("Reflect.ownKeys({a:1}).join()"), "a");
        assert_eq!(disp("Reflect.apply(Math.max,null,[2,9])"), "9");
        assert_eq!(disp("function C(a){this.a=a}Reflect.construct(C,['z']).a"), "z");
        // newTarget: proto comes from it while the target ctor runs.
        assert_eq!(
            disp("function P(){this.p=1}function C(){}C.prototype={};var o=Reflect.construct(P,[],C);(o instanceof C)+'|'+o.p"),
            "true|1"
        );        // Reflect.get honors the get trap.
        assert_eq!(
            disp("Reflect.get(new Proxy({x:1},{get:(o,k)=>42}),'x')"),
            "42"
        );
        // Reflect.getOwnPropertyDescriptor reads through (trap gap).
        assert_eq!(disp("Reflect.getOwnPropertyDescriptor(new Proxy({v:9},{}),'v').value"), "9");
        assert_eq!(disp("typeof Reflect"), "object");
    }

    #[test]
    fn buffer_is_view() {
        assert_eq!(disp("ArrayBuffer.isView(new Uint8Array(1))"), "true");
        assert_eq!(disp("ArrayBuffer.isView(new Uint16Array(1))"), "true");
        assert_eq!(disp("ArrayBuffer.isView(new DataView(new ArrayBuffer(1)))"), "true");
        assert_eq!(disp("ArrayBuffer.isView([])"), "false");
        assert_eq!(disp("ArrayBuffer.isView({})"), "false");
        assert_eq!(disp("ArrayBuffer.isView(new ArrayBuffer(1))"), "false");
    }

    #[test]
    fn typed_arrays() {
        // Clamping (ToUint8 mod semantics).
        assert_eq!(disp("var a=new Uint8Array([257,-1,300.5]);a[0]"), "1");
        assert_eq!(disp("var a=new Uint8Array([257,-1,300.5]);a[1]"), "255");
        assert_eq!(disp("var a=new Uint8Array([257,-1,300.5]);a[2]"), "44");
        assert_eq!(disp("new Uint8Array(3.7).length"), "3");
        assert_eq!(disp("new Uint8Array().length"), "0");
        assert!(errmsg("new Uint8Array(-1)").contains("invalid typed array"));
        // set / slice / subarray / join / fill / indexOf.
        assert_eq!(disp("var u=new Uint8Array([1,2,3,4]);u.set([9,9],2);u.join()"), "1,2,9,9");
        assert!(errmsg("new Uint8Array([1]).set([1],9)").contains("out of bounds"));
        assert_eq!(disp("new Uint8Array([1,2,3,4]).slice(1,3).join()"), "2,3");
        assert_eq!(disp("new Uint8Array([1,2,3,4]).subarray(-2).join()"), "3,4");
        assert_eq!(disp("String(new Uint8Array([1,2,3]))"), "1,2,3");
        assert_eq!(disp("JSON.stringify(new Uint8Array([1,2]))"), "{\"0\":1,\"1\":2}");
        assert_eq!(
            disp("Object.prototype.toString.call(new Uint8Array([1]))"),
            "[object Uint8Array]"
        );
        assert_eq!(disp("Object.keys(new Uint8Array([7,8])).join()"), "0,1");
        assert_eq!(disp("var u=new Uint8Array([1]);(1 in u)+'|'+('length' in u)"), "false|true");
        assert_eq!(disp("var s='';for(var x of new Uint8Array([1,2])){s+=x}s"), "12");
        assert_eq!(disp("var u=new Uint8Array([5,6]);var c=u.slice();c[0]=9;u[0]"), "5");
        assert_eq!(disp("var u=new Uint8Array(3);u.fill(7);u.join()"), "7,7,7");
        assert_eq!(disp("new Uint8Array([1,2,3]).indexOf(2)"), "1");
        assert_eq!(disp("new Uint8Array([1,2,3]).indexOf(9)"), "-1");
        assert_eq!(disp("var u=new Uint8Array(2);u[5]=9;u.length"), "2");
        assert_eq!(disp("var u=new Uint8Array([1]);delete u[0]"), "false");
        assert_eq!(disp("var u=new Uint8Array([1]);delete u[0];u[0]"), "1");
        assert_eq!(disp("var u=new Uint8Array(2);u instanceof Uint8Array"), "true");
        assert_eq!(disp("var u=new Uint8Array(2);u instanceof Object"), "true");
        assert_eq!(disp("new Uint8Array(2).byteLength"), "2");
        // ArrayBuffer + views over it (copies).
        assert_eq!(disp("new ArrayBuffer(4).byteLength"), "4");
        assert_eq!(disp("var v=new Uint8Array(new ArrayBuffer(4));v[0]=77;v[0]+'|'+v.length"), "77|4");
        assert_eq!(disp("new ArrayBuffer(8).slice(2,5).byteLength"), "3");
        assert_eq!(
            disp("Object.prototype.toString.call(new ArrayBuffer(1))"),
            "[object ArrayBuffer]"
        );
        // apply() expands typed arrays (base64 decode path).
        assert_eq!(disp("String.fromCharCode.apply(String,new Uint8Array([72,105]))"), "Hi");
        assert_eq!(disp("typeof Uint8Array"), "function");
        assert_eq!(disp("typeof ArrayBuffer"), "function");
    }

    #[test]
    fn typed_views() {
        // Write coercion per kind (oracle: node -e one-liners).
        assert_eq!(disp("new Uint16Array([70000,-1]).join()"), "4464,65535");
        assert_eq!(disp("new Int8Array([200,-200]).join()"), "-56,56");
        assert_eq!(disp("new Int32Array([4294967297,-1]).join()"), "1,-1");
        assert_eq!(disp("new Uint32Array([-1])[0]"), "4294967295");
        assert_eq!(disp("new Float32Array([0.1])[0]===Math.fround(0.1)"), "true");
        assert_eq!(disp("Uint16Array.BYTES_PER_ELEMENT"), "2");
        assert_eq!(disp("Float64Array.BYTES_PER_ELEMENT"), "8");
        // Buffer reinterpretation (little-endian) + offset/length forms.
        assert_eq!(disp("new Uint16Array(new Uint8Array([1,0,2,0])).join()"), "1,0,2,0");
        assert_eq!(disp("new Uint16Array(new ArrayBuffer(8),2,2).length"), "2");
        assert!(errmsg("new Uint16Array(new ArrayBuffer(3))").contains("mismatch"));
        assert!(errmsg("new Uint16Array(new ArrayBuffer(8),1)").contains("misaligned"));
        // Methods mirror the u8 set.
        assert_eq!(disp("var a=new Uint16Array(3);a.set([1,2],1);a.join()"), "0,1,2");
        assert_eq!(disp("var a=new Uint16Array([1,2,3]);a.fill(9,1);a.join()"), "1,9,9");
        assert_eq!(disp("new Uint16Array([1,2,3]).subarray(1).join()"), "2,3");
        assert_eq!(disp("new Int32Array([5,6]).slice(1).join()"), "6");
        assert_eq!(disp("new Uint32Array([7,8]).indexOf(8)"), "1");
        assert_eq!(disp("new Uint16Array(1) instanceof Uint16Array"), "true");
        assert_eq!(disp("new Uint16Array(3).byteLength"), "6");
        assert_eq!(
            disp("Object.prototype.toString.call(new Uint16Array(1))"),
            "[object Uint16Array]"
        );
        assert_eq!(disp("var u=new Int32Array(852);u.length"), "852");
    }

    #[test]
    fn dataview() {
        assert_eq!(
            disp("var v=new DataView(new ArrayBuffer(4));v.setUint16(0,0x1234);v.getUint16(0).toString(16)"),
            "1234"
        );
        assert_eq!(
            disp("var v=new DataView(new ArrayBuffer(4));v.setUint16(2,0x5678,true);v.getUint16(2,true).toString(16)"),
            "5678"
        );
        assert_eq!(
            disp("var v=new DataView(new ArrayBuffer(4));v.setUint16(0,0x1234);v.getUint8(1).toString(16)"),
            "34"
        );
        assert_eq!(
            disp("var v=new DataView(new ArrayBuffer(4));v.setUint16(0,0x1234);v.setUint16(2,0x5678,true);v.getUint32(0).toString(16)"),
            "12347856"
        );
        assert_eq!(disp("new DataView(new ArrayBuffer(5)).byteLength"), "5");
        assert_eq!(
            disp("Object.prototype.toString.call(new DataView(new ArrayBuffer(1)))"),
            "[object DataView]"
        );
        assert!(errmsg("new DataView(new ArrayBuffer(2)).getUint16(1)").contains("out of bounds"));
    }

    #[test]
    fn bigint_construct() {
        assert_eq!(disp("String(BigInt(42))"), "42");
        assert_eq!(disp("String(BigInt(3.99))"), "3");
        assert_eq!(disp("String(BigInt(-3.99))"), "-3");
        assert_eq!(disp("String(BigInt(1.5))"), "1");
        assert_eq!(disp("String(BigInt(true))"), "1");
        assert_eq!(disp("String(BigInt(false))"), "0");
        assert_eq!(disp("String(BigInt('123'))"), "123");
        assert_eq!(disp("String(BigInt('  -42  '))"), "-42");
        assert_eq!(disp("String(BigInt('0xff'))"), "255");
        assert_eq!(disp("String(BigInt('0B101'))"), "5");
        assert_eq!(disp("String(BigInt('0o17'))"), "15");
        assert_eq!(disp("String(BigInt('-0x10'))"), "-16");
        assert_eq!(disp("String(BigInt(''))"), "0");
        assert_eq!(disp("String(BigInt())"), "0");
        assert_eq!(disp("String(new BigInt(5))"), "5");
        assert_eq!(disp("String(BigInt(BigInt(7)))"), "7");
        // Exact past f64 (a double would print 1.2345678901234568e+29).
        assert_eq!(
            disp("String(BigInt('123456789012345678901234567890'))"),
            "123456789012345678901234567890"
        );
        // Exact f64-integer decomposition (the double 1e30, not 10^30).
        assert_eq!(disp("String(BigInt(1e30))"), "1000000000000000019884624838656");
        assert!(errmsg("BigInt(NaN)").contains("Cannot convert NaN"));
        assert!(errmsg("BigInt(Infinity)").contains("Infinity"));
        assert!(errmsg("BigInt(-Infinity)").contains("Infinity"));
        assert!(errmsg("BigInt('1.5')").contains("Cannot convert"));
        assert!(errmsg("BigInt('abc')").contains("Cannot convert"));
        assert!(errmsg("BigInt('10n')").contains("Cannot convert"));
        assert!(errmsg("BigInt('0x')").contains("Cannot convert"));
        assert!(errmsg("BigInt(undefined)").contains("undefined"));
        assert!(errmsg("BigInt(null)").contains("null"));
        assert!(errmsg("BigInt({})").contains("object"));
    }

    #[test]
    fn bigint_arith() {
        assert_eq!(disp("String(BigInt(10)+BigInt(3))"), "13");
        assert_eq!(disp("String(BigInt(10)-BigInt(30))"), "-20");
        assert_eq!(disp("String(BigInt(123456789)*BigInt(987654321))"), "121932631112635269");
        assert_eq!(disp("String(BigInt(7)/BigInt(2))"), "3");
        assert_eq!(disp("String(BigInt(-7)/BigInt(2))"), "-3");
        assert_eq!(disp("String(BigInt(7)/BigInt(-2))"), "-3");
        assert_eq!(disp("String(BigInt(-7)%BigInt(2))"), "-1");
        assert_eq!(disp("String(BigInt(7)%BigInt(-2))"), "1");
        assert_eq!(disp("String(BigInt(2)**BigInt(10))"), "1024");
        assert_eq!(disp("String(BigInt(-2)**BigInt(3))"), "-8");
        assert_eq!(disp("String(BigInt(-2)**BigInt(2))"), "4");
        assert_eq!(disp("String(BigInt(0)**BigInt(0))"), "1");
        assert_eq!(disp("String(BigInt(5)-BigInt(5))"), "0");
        assert_eq!(disp("String(-BigInt(5))"), "-5");
        assert_eq!(disp("String(-BigInt(-5))"), "5");
        assert_eq!(disp("String(~BigInt(5))"), "-6");
        assert_eq!(disp("String(~BigInt(-1))"), "0");
        assert_eq!(disp("String(~BigInt(0))"), "-1");
        assert!(errmsg("BigInt(1)/BigInt(0)").contains("Division by zero"));
        assert!(errmsg("BigInt(1)%BigInt(0)").contains("Division by zero"));
        assert!(errmsg("BigInt(2)**BigInt(-1)").contains("non-negative"));
        assert!(errmsg("BigInt(1)+1").contains("mix"));
        assert!(errmsg("1+BigInt(1)").contains("mix"));
        assert!(errmsg("BigInt(2)*2").contains("mix"));
        assert!(errmsg("BigInt(2)-'x'").contains("mix"));
    }

    #[test]
    fn bigint_shifts_bits() {
        assert_eq!(disp("String(BigInt(1)<<BigInt(8))"), "256");
        assert_eq!(disp("String(BigInt(256)>>BigInt(4))"), "16");
        assert_eq!(disp("String(-BigInt(8)>>BigInt(2))"), "-2");
        assert_eq!(disp("String(-BigInt(7)>>BigInt(2))"), "-2");
        assert_eq!(disp("String(BigInt(6)&BigInt(3))"), "2");
        assert_eq!(disp("String(BigInt(6)|BigInt(3))"), "7");
        assert_eq!(disp("String(BigInt(6)^BigInt(3))"), "5");
        assert_eq!(disp("String(BigInt(-1)&BigInt(5))"), "5");
        assert_eq!(disp("String(BigInt(-6)|BigInt(3))"), "-5");
        assert_eq!(disp("String(BigInt(-6)^BigInt(-3))"), "7");
        assert!(errmsg("BigInt(1)>>>BigInt(1)").contains("unsigned right shift"));
        assert!(errmsg("BigInt(1)<<BigInt(-1)").contains("non-negative"));
        assert!(errmsg("BigInt(1)<<1").contains("mix"));
        assert!(errmsg("BigInt(1)&1").contains("mix"));
    }

    #[test]
    fn bigint_compare() {
        assert!(boolean("BigInt(1)<BigInt(2)"));
        assert!(boolean("BigInt(2)<=BigInt(2)"));
        assert!(boolean("BigInt(3)>BigInt(2)"));
        assert!(!boolean("BigInt(2)>=BigInt(3)"));
        assert!(boolean("BigInt(10)==10"));
        assert!(!boolean("BigInt(10)===10"));
        assert!(boolean("BigInt(10)!==10"));
        assert!(boolean("BigInt(10)==BigInt(10)"));
        assert!(boolean("BigInt(10)===BigInt(10)"));
        assert!(boolean("BigInt(0)==-BigInt(0)"));
        assert!(boolean("BigInt(10)=='10'"));
        assert!(boolean("BigInt(10)=='0xa'"));
        assert!(!boolean("BigInt(10)=='a'"));
        assert!(!boolean("BigInt(5)==5.5"));
        assert!(boolean("BigInt(5)<5.5"));
        assert!(boolean("BigInt(5)>4.5"));
        assert!(!boolean("BigInt(5)==NaN"));
        assert!(!boolean("BigInt(5)<NaN"));
        assert!(boolean("BigInt(5)<Infinity"));
        assert!(boolean("BigInt(5)>-Infinity"));
        assert!(!boolean("BigInt(5)==Infinity"));
        assert!(boolean("BigInt(1)==true"));
        assert!(boolean("BigInt(0)==false"));
        assert!(!boolean("BigInt(2)==true"));
        assert!(boolean("BigInt(1)<'2'"));
        assert!(!boolean("BigInt(1)<'a'"));
        assert!(!boolean("BigInt(1)==null"));
        // Relational ops never throw on mixed pairs (only arithmetic does).
        assert!(boolean("BigInt(5)<10"));
        assert!(boolean("10>BigInt(5)"));
    }

    #[test]
    fn bigint_statics() {
        assert_eq!(disp("String(BigInt.asUintN(8, BigInt(256)))"), "0");
        assert_eq!(disp("String(BigInt.asUintN(8, BigInt(-1)))"), "255");
        assert_eq!(disp("String(BigInt.asUintN(8, BigInt(255)))"), "255");
        assert_eq!(disp("String(BigInt.asUintN(8, 256))"), "0");
        assert_eq!(disp("String(BigInt.asIntN(8, BigInt(255)))"), "-1");
        assert_eq!(disp("String(BigInt.asIntN(8, BigInt(127)))"), "127");
        assert_eq!(disp("String(BigInt.asIntN(8, BigInt(128)))"), "-128");
        assert_eq!(disp("String(BigInt.asIntN(8, BigInt(-128)))"), "-128");
        assert_eq!(disp("String(BigInt.asIntN(8, BigInt(-129)))"), "127");
        assert_eq!(disp("String(BigInt.asUintN(0, BigInt(123)))"), "0");
        assert_eq!(disp("String(BigInt.asIntN(0, BigInt(123)))"), "0");
        assert_eq!(
            disp("String(BigInt.asUintN(64, BigInt(-1)))"),
            "18446744073709551615"
        );
        assert!(errmsg("BigInt.asUintN(-1, BigInt(1))").contains("bit count"));
        assert!(errmsg("BigInt.asIntN(1.5, BigInt(1))").contains("bit count"));
        // The second arg converts like BigInt() (fractionals truncate).
        assert_eq!(disp("String(BigInt.asUintN(8, 1.5))"), "1");
    }

    #[test]
    fn bigint_string_conv() {
        assert_eq!(disp("BigInt(255).toString(16)"), "ff");
        assert_eq!(disp("BigInt(10).toString(2)"), "1010");
        assert_eq!(disp("BigInt(8).toString(8)"), "10");
        assert_eq!(disp("BigInt(35).toString(36)"), "z");
        assert_eq!(disp("BigInt(-10).toString(16)"), "-a");
        assert_eq!(disp("BigInt(123).toString()"), "123");
        assert!(errmsg("BigInt(1).toString(1)").contains("radix"));
        assert!(errmsg("BigInt(1).toString(37)").contains("radix"));
        assert_eq!(disp("String(BigInt(5).valueOf())"), "5");
        assert_eq!(disp("String(BigInt(42))"), "42");
        assert_eq!(num("Number(BigInt(42))"), 42.0);
        assert_eq!(disp("typeof BigInt(1)"), "bigint");
        assert_eq!(disp("BigInt(42)"), "42n");
        assert_eq!(
            disp("Object.prototype.toString.call(BigInt(1))"),
            "[object BigInt]"
        );
        assert_eq!(disp("BigInt(0)?'t':'f'"), "f");
        assert_eq!(disp("BigInt(1)?'t':'f'"), "t");
        assert_eq!(disp("!BigInt(0)"), "true");
        assert_eq!(disp("var x=BigInt(5);x++;String(x)"), "6");
        assert_eq!(disp("var x=BigInt(5);++x;String(x)"), "6");
        assert_eq!(disp("var x=BigInt(5);x--;String(x)"), "4");
        assert_eq!(disp("var x=BigInt(5);x++"), "5n");
        assert_eq!(disp("var m=new Map();m.set(BigInt(1),'a');m.set(BigInt(1),'b');m.get(BigInt(1))"), "b");
        assert_eq!(disp("var m=new Map();m.set(BigInt(1),'a');m.set(1,'b');m.size"), "2");
        assert_eq!(disp("var s=new Set();s.add(BigInt(1));s.add(BigInt(1));s.size"), "1");
        assert_eq!(disp("[BigInt(1)].indexOf(BigInt(1))"), "0");
        assert_eq!(disp("[BigInt(1),BigInt(2)].includes(BigInt(2))"), "true");
        // Implicit string conversion throws; explicit String()/Number() work.
        assert!(errmsg("'a'.concat(BigInt(1))").contains("string"));
        assert!(errmsg("'a'+BigInt(1)").contains("mix"));
        assert!(errmsg("BigInt(1)+'a'").contains("mix"));
        assert!(errmsg("`x${BigInt(1)}`").contains("string"));
        assert!(errmsg("JSON.stringify(BigInt(1))").contains("BigInt"));
        assert!(errmsg("JSON.stringify([BigInt(1)])").contains("BigInt"));
        assert!(errmsg("+BigInt(1)").contains("number"));
    }

    #[test]
    fn bigint_arrays() {
        assert_eq!(disp("new BigInt64Array(3).length"), "3");
        assert_eq!(disp("new BigUint64Array(2).length"), "2");
        assert_eq!(
            disp("var a=new BigInt64Array(2);a[0]=BigInt(5);a[1]=BigInt(-3);String(a[0])+','+String(a[1])"),
            "5,-3"
        );
        assert_eq!(
            disp("var a=new BigInt64Array(1);a[0]=BigInt('18446744073709551616');String(a[0])"),
            "0"
        );
        assert_eq!(
            disp("var a=new BigInt64Array(1);a[0]=BigInt('18446744073709551615');String(a[0])"),
            "-1"
        );
        assert_eq!(
            disp("var a=new BigUint64Array(1);a[0]=BigInt(-1);String(a[0])"),
            "18446744073709551615"
        );
        assert_eq!(disp("var a=new BigInt64Array(1);a[0]=5;String(a[0])"), "5");
        assert_eq!(disp("var a=new BigInt64Array(3);a.fill(BigInt(7));String(a[1])"), "7");
        assert_eq!(
            disp("var a=new BigInt64Array(4);a.fill(BigInt(9),1,3);String(a[0])+String(a[1])+String(a[2])+String(a[3])"),
            "0990"
        );
        assert_eq!(disp("BigInt64Array.BYTES_PER_ELEMENT"), "8");
        assert_eq!(disp("BigUint64Array.BYTES_PER_ELEMENT"), "8");
        assert_eq!(disp("new BigInt64Array(3).byteLength"), "24");
        assert_eq!(disp("ArrayBuffer.isView(new BigInt64Array(1))"), "true");
        assert_eq!(disp("ArrayBuffer.isView(new BigUint64Array(1))"), "true");
        assert_eq!(
            disp("Object.prototype.toString.call(new BigInt64Array(1))"),
            "[object BigInt64Array]"
        );
        assert_eq!(
            disp("Object.prototype.toString.call(new BigUint64Array(1))"),
            "[object BigUint64Array]"
        );
        assert_eq!(
            disp("var a=new BigInt64Array([BigInt(1),BigInt(2)]);a.length+','+String(a[1])"),
            "2,2"
        );
        assert_eq!(disp("new BigInt64Array(new ArrayBuffer(16)).length"), "2");
        assert_eq!(disp("new BigInt64Array(BigInt(3)).length"), "3");
        assert!(errmsg("new BigInt64Array(new ArrayBuffer(8),1)").contains("misaligned"));
        assert!(errmsg("new BigInt64Array(new ArrayBuffer(7))").contains("mismatch"));
        assert_eq!(
            disp("var s='';for(var x of new BigInt64Array([BigInt(1),BigInt(2)])){s+=String(x)};s"),
            "12"
        );
        assert_eq!(disp("Object.keys(new BigInt64Array(2)).join()"), "0,1");
        assert_eq!(
            disp("var a=new BigInt64Array(2);(0 in a)+'|'+(9 in a)+'|'+('length' in a)"),
            "true|false|true"
        );
        assert_eq!(disp("var a=new BigInt64Array(1);a.hasOwnProperty('0')"), "true");
        assert_eq!(disp("var a=new BigInt64Array([BigInt(4)]);a[0]===a[0]"), "true");
        assert_eq!(disp("var a=new BigInt64Array(1);delete a[0]"), "false");
        assert_eq!(disp("var a=new BigInt64Array(1);delete a[0];String(a[0])"), "0");
        assert_eq!(disp("var a=new BigInt64Array(1);a[5]=BigInt(9);a.length"), "1");
        assert_eq!(
            disp("var a=[...new BigInt64Array([BigInt(3)])];String(a[0])"),
            "3"
        );
        assert_eq!(
            disp("var a=Array.from(new BigUint64Array([BigInt(6)]));String(a[0])"),
            "6"
        );
        assert_eq!(disp("new BigInt64Array([BigInt(1),BigInt(-2)])"), "[1n, -2n]");
        assert!(errmsg("JSON.stringify(new BigInt64Array(1))").contains("BigInt"));
        assert_eq!(disp("new BigInt64Array(1) instanceof BigInt64Array"), "true");
        assert_eq!(disp("BigInt(1) instanceof BigInt"), "false");
        assert_eq!(disp("typeof BigInt64Array"), "function");
        assert_eq!(disp("var o={...new BigInt64Array([BigInt(8)])};String(o[0])"), "8");
        assert_eq!(disp("var s='';for(var k in new BigInt64Array([BigInt(9)])){s+=k};s"), "0");
        assert_eq!(disp("var o={'0':'x'};BigInt(0) in o"), "true");
        assert_eq!(
            disp("var b=new BigInt64Array([BigInt(1)]);var d=new DataView(b);String(d.getBigUint64(0,true))"),
            "1"
        );
    }

    #[test]
    fn dataview_bigint() {
        assert_eq!(
            disp("var d=new DataView(new ArrayBuffer(16));d.setBigInt64(0,BigInt('1234567890123456789'));String(d.getBigInt64(0))"),
            "1234567890123456789"
        );
        assert_eq!(
            disp("var d=new DataView(new ArrayBuffer(16));d.setBigInt64(0,BigInt('1234567890123456789'),true);String(d.getBigInt64(0,true))"),
            "1234567890123456789"
        );
        // Default is big-endian: an LE read of a BE-stored 1n is 2^56.
        assert_eq!(
            disp("var d=new DataView(new ArrayBuffer(8));d.setBigUint64(0,BigInt(1));String(d.getBigUint64(0,true))"),
            "72057594037927936"
        );
        assert_eq!(
            disp("var d=new DataView(new ArrayBuffer(8));d.setBigUint64(0,BigInt('18446744073709551615'));String(d.getBigUint64(0))"),
            "18446744073709551615"
        );
        assert_eq!(
            disp("var d=new DataView(new ArrayBuffer(8));d.setBigInt64(0,BigInt(-2));String(d.getBigInt64(0))"),
            "-2"
        );
        assert_eq!(
            disp("var d=new DataView(new ArrayBuffer(8));d.setBigUint64(0,BigInt('18446744073709551616'));String(d.getBigUint64(0))"),
            "0"
        );
        assert_eq!(
            disp("var d=new DataView(new ArrayBuffer(8));d.setBigInt64(0,BigInt(1))"),
            "undefined"
        );
        assert!(errmsg("new DataView(new ArrayBuffer(8)).getBigInt64(1)").contains("out of bounds"));
        assert!(errmsg("new DataView(new ArrayBuffer(8)).setBigUint64(1,BigInt(1))").contains("out of bounds"));
    }

    #[test]
    fn bufview_aliasing() {
        // Maps endianness shape: BigInt lane written after the u32 view
        // is made still reads through (single Buf, LE codec).
        assert_eq!(
            disp("var a=new BigInt64Array(1);var b=new Uint32Array(a.buffer);a[0]=BigInt(1);b[0]"),
            "1"
        );
        assert_eq!(
            disp("var a=new BigInt64Array(1);var b=new Uint32Array(a.buffer);a[0]=BigInt(1);b[1]"),
            "0"
        );
        // Cross-view visibility both directions over one ArrayBuffer.
        assert_eq!(
            disp("var g=new ArrayBuffer(4);var u8=new Uint8Array(g);var u32=new Uint32Array(g);u8[0]=1;u8[1]=0;u8[2]=0;u8[3]=0;u32[0]"),
            "1"
        );
        assert_eq!(
            disp("var g=new ArrayBuffer(4);var u8=new Uint8Array(g);var u32=new Uint32Array(g);u32[0]=258;u8[0]+','+u8[1]"),
            "2,1"
        );
        // byteOffset/length windows + alignment/range errors.
        assert_eq!(disp("new Uint16Array(new ArrayBuffer(8),2,2).length"), "2");
        assert_eq!(disp("new Uint16Array(new ArrayBuffer(8),2,2).byteOffset"), "2");
        assert_eq!(disp("new Uint16Array(new ArrayBuffer(8),2,2).byteLength"), "4");
        assert_eq!(disp("new BigInt64Array(new ArrayBuffer(16),8,1).length"), "1");
        assert!(errmsg("new Uint16Array(new ArrayBuffer(8),1)").contains("misaligned"));
        assert!(errmsg("new Uint32Array(new ArrayBuffer(8),16)").contains("misaligned"));
        assert!(errmsg("new Uint16Array(new ArrayBuffer(3))").contains("mismatch"));
        assert!(errmsg("new BigInt64Array(new ArrayBuffer(8),1)").contains("misaligned"));
        // DataView over the same Buf observes typed writes (LE lane).
        assert_eq!(
            disp("var g=new ArrayBuffer(4);var u=new Uint32Array(g);var d=new DataView(g);u[0]=287454020;dummy=0;d.getUint8(0)+','+d.getUint8(1)"),
            "68,51"
        );
        assert_eq!(
            disp("var g=new ArrayBuffer(4);var d=new DataView(g);var u=new Uint32Array(g);d.setUint32(0,1,true);u[0]"),
            "1"
        );
        // .buffer byteLength tracks the store; slice stays an owned copy.
        assert_eq!(disp("new Uint32Array(2).buffer.byteLength"), "8");
        assert_eq!(disp("new BigInt64Array(1).buffer.byteLength"), "8");
        assert_eq!(disp("new Uint8Array(3).buffer.byteLength"), "3");
        assert_eq!(
            disp("var g=new ArrayBuffer(4);var u=new Uint32Array(g);var c=u.slice();u[0]=9;c[0]"),
            "0"
        );
        assert_eq!(
            disp("var u=new Uint8Array(new ArrayBuffer(3));var c=u.slice();u[0]=9;c[0]"),
            "0"
        );
        assert_eq!(disp("ArrayBuffer.isView(new Uint32Array(new ArrayBuffer(4)))"), "true");
        assert_eq!(disp("ArrayBuffer.isView(new Uint8Array(1).buffer)"), "false");
    }

    #[test]
    fn bigint_loader_shape() {
        // The Google Maps loader shape: presence checks, wrapping helpers,
        // bigint loop counters, and switch dispatch on bigint tags.
        assert!(boolean(
            "typeof BigInt==='function'&&typeof BigInt64Array==='function'\
             &&typeof BigUint64Array==='function'&&typeof BigInt.asUintN==='function'\
             &&typeof BigInt.asIntN==='function'"
        ));
        assert_eq!(disp("String(BigInt.asUintN(32, BigInt('4294967296')))"), "0");
        assert_eq!(disp("var c=0;for(var i=BigInt(0);i<BigInt(3);i++){c++}c"), "3");
        assert_eq!(
            disp("var x=BigInt(2);switch(x){case BigInt(1):'a';break;case BigInt(2):'b';break;default:'c'}"),
            "b"
        );
    }

    #[test]
    fn date_utc() {
        assert_eq!(disp("Date.UTC(2024,0,15)"), "1705276800000");
        assert_eq!(disp("Date.UTC(99,0)"), "915148800000");
        assert_eq!(disp("Date.UTC(2024,0,15,12,30,45,123)"), "1705321845123");
        assert_eq!(disp("Date.UTC(1970,0,1)"), "0");
        assert_eq!(disp("Date.UTC(2024,5)"), "1717200000000");
        assert_eq!(disp("Date.UTC(2023,12)"), "1704067200000");
        assert_eq!(disp("Date.UTC(2024,-1,1)"), "1701388800000");
        assert_eq!(disp("isNaN(Date.UTC())"), "true");
        assert_eq!(disp("isNaN(Date.UTC(NaN))"), "true");
    }

    #[test]
    fn console_levels() {
        assert_eq!(out("console.error('e');console.warn('w');console.info('i');console.debug('d')"), "e\nw\ni\nd\n");
        assert_eq!(out("console.error()"), "\n");
    }

    #[test]
    fn history_api() {
        assert_eq!(disp("history.length"), "1");
        assert_eq!(disp("history.state"), "null");
        assert_eq!(disp("history.pushState({a:1},'','/x');history.state.a"), "1");
        assert_eq!(disp("history.pushState(null,'','/y')"), "undefined");
        assert_eq!(disp("typeof history.listen(function(){})"), "function");
        assert_eq!(disp("history.createHref('/z')"), "/z");
        assert_eq!(disp("history.back()"), "undefined");
    }
    #[test]
    fn web_storage() {
        assert_eq!(disp("localStorage.setItem('a','1');localStorage.getItem('a')"), "1");
        assert_eq!(disp("localStorage.getItem('nope')"), "null");
        assert_eq!(disp("localStorage.setItem('a',1);localStorage.length"), "1");
        assert_eq!(disp("localStorage.setItem('a',1);localStorage.key(0)"), "a");
        assert_eq!(disp("localStorage.key(9)"), "null");
        assert_eq!(disp("localStorage.setItem('a',1);localStorage.removeItem('a');localStorage.length"), "0");
        assert_eq!(disp("localStorage.setItem('a',1);localStorage.clear();localStorage.length"), "0");
        assert_eq!(disp("sessionStorage.setItem('c','v');sessionStorage.getItem('c')"), "v");
        assert_eq!(disp("localStorage.setItem('n',42);localStorage.getItem('n')"), "42");
    }

    #[test]
    fn string_substr() {
        assert_eq!(disp("'hello'.substr(1,3)"), "ell");
        assert_eq!(disp("'hello'.substr(-2)"), "lo");
        assert_eq!(disp("'hello'.substr(2)"), "llo");
        assert_eq!(disp("'hello'.substr()"), "hello");
        assert_eq!(disp("'hello'.substr(1,0)"), "");
    }

    #[test]
    fn resize_observer() {
        assert_eq!(disp("var r=new ResizeObserver(function(){});r.observe({});typeof r.disconnect"), "function");
        assert_eq!(disp("var r=new ResizeObserver(function(){});r.unobserve({})"), "undefined");
        assert!(errmsg("new ResizeObserver(1)").contains("callback"));
        assert_eq!(disp("typeof ResizeObserver"), "function");
    }

    #[test]
    fn match_media() {
        assert_eq!(disp("matchMedia('(min-width: 100px)').matches"), "false");
        assert_eq!(disp("matchMedia('(min-width: 100px)').media"), "(min-width: 100px)");
        assert_eq!(disp("var m=matchMedia('x');m.addListener(function(){});m.matches"), "false");
    }

    #[test]
    fn persona_surface() {
        // Timezone is engine-level (no DOM needed).
        assert_eq!(disp("new Date(0).getTimezoneOffset()"), "-180");
    }

    #[test]
    fn function_prototype_to_string() {
        // Monkey-patch detectors key on the native/non-native split.
        assert_eq!(disp("Function.prototype.toString.call(Array.isArray).indexOf('[native code]') !== -1"), "true");
        assert_eq!(disp("function f(){};f.toString().indexOf('[native code]')"), "-1");
        assert_eq!(disp("Object.prototype.toString.call(Array.isArray)"), "[object Function]");
        assert_eq!(disp("typeof Function.prototype.toString"), "function");
        assert!(errmsg("Function.prototype.toString.call({})").contains("needs a function"));
    }

    #[test]
    fn math_full() {
        assert_eq!(disp("Math.sin(0)"), "0");
        assert_eq!(disp("Math.cos(0)"), "1");
        assert_eq!(disp("Math.atan2(1,1)"), "0.7853981633974483");
        assert_eq!(disp("Math.exp(0)"), "1");
        assert_eq!(disp("Math.log(Math.E)"), "1");
        assert_eq!(disp("Math.cbrt(27)"), "3");
        assert_eq!(disp("Math.hypot(3,4)"), "5");
        assert_eq!(disp("Math.sign(-3)"), "-1");
        assert_eq!(disp("Math.clz32(0)"), "32");
        assert_eq!(disp("Math.clz32(1)"), "31");
        assert_eq!(disp("Math.clz32(-1)"), "0");
        assert_eq!(disp("Math.imul(2,4)"), "8");
        assert_eq!(disp("Math.SQRT2"), "1.4142135623730951");
        assert_eq!(disp("Math.LN2"), "0.6931471805599453");
        assert_eq!(disp("Math.LOG2E"), "1.4426950408889634");
        // The scheduler fallback that motivated this batch.
        assert_eq!(disp("var st=Math.log,lt=Math.LN2;(function(e){return e>>>=0,0===e?32:31-(st(e)/lt|0)|0})(1)"), "31");
    }

    #[test]
    fn math_extra() {
        assert_eq!(disp("Math.fround(0.1)===new Float32Array([0.1])[0]"), "true");
        assert_eq!(disp("Math.trunc(3.7)"), "3");
        assert_eq!(disp("Math.trunc(-3.7)"), "-3");
        assert_eq!(disp("(0x1234).toString(16)"), "1234");
        assert_eq!(disp("(255).toString(2)"), "11111111");
        assert_eq!(disp("(-10).toString(16)"), "-a");
        assert_eq!(disp("(3.5).toString()"), "3.5");
        assert_eq!(disp("(42).toString()"), "42");
        assert_eq!(disp("NaN.toString(16)"), "NaN");
        assert_eq!(disp("typeof NaN"), "number");
        assert_eq!(disp("Infinity>1e308"), "true");
        assert!(errmsg("(1).toString(37)").contains("radix"));
        assert!(errmsg("(1).toString(1)").contains("radix"));
    }

    #[test]
    fn text_codec() {
        assert_eq!(disp("new TextEncoder().encode('Hi').join()"), "72,105");
        assert_eq!(disp("new TextEncoder().encode('').length"), "0");
        assert_eq!(
            disp("new TextEncoder().encode('ñ €').join()"),
            "195,177,32,226,130,172"
        );
        assert_eq!(
            disp("new TextDecoder().decode(new Uint8Array([72,105]))"),
            "Hi"
        );
        assert_eq!(
            disp("new TextDecoder().decode(new Uint8Array([195,177]))"),
            "ñ"
        );
        assert_eq!(disp("new TextDecoder().encoding"), "utf-8");
        assert_eq!(disp("new TextDecoder('utf8').encoding"), "utf-8");
        assert_eq!(disp("new TextDecoder('latin1').encoding"), "windows-1252");
        assert_eq!(
            disp("new TextDecoder('latin1').decode(new Uint8Array([65,233,255]))"),
            "Aéÿ"
        );
        // Lossy: bad bytes become U+FFFD, never throw.
        assert_eq!(
            disp("new TextDecoder().decode(new Uint8Array([72,255,105]))"),
            "H�i"
        );
        assert_eq!(disp("typeof TextEncoder.prototype.encode"), "function");
        assert_eq!(disp("typeof TextDecoder.prototype.decode"), "function");
        assert_eq!(disp("new TextEncoder() instanceof TextEncoder"), "true");
        assert_eq!(disp("new TextDecoder() instanceof TextDecoder"), "true");
        assert!(errmsg("new TextDecoder('nope')").contains("unknown encoding"));
    }

    #[test]
    fn create_with_descriptors() {
        // Babel _inherits shape: constructor backlink + proto link.
        assert_eq!(
            disp("function X(){ }function N(){ }\
                  N.prototype=Object.create(X.prototype,{constructor:{value:N}});\
                  N.prototype.constructor===N"),
            "true"
        );
        assert_eq!(
            disp("function X(){ }function N(){ }\
                  N.prototype=Object.create(X.prototype,{constructor:{value:N}});\
                  Object.getPrototypeOf(N.prototype)===X.prototype"),
            "true"
        );
        assert_eq!(disp("var o=Object.create(null);Object.getPrototypeOf(o)"), "null");
        assert_eq!(disp("var o=Object.create({a:1},{b:{value:2}});o.a+'|'+o.b"), "1|2");
    }

    #[test]
    fn object_proto_extras() {
        assert_eq!(disp("Object.prototype.isPrototypeOf.call(Array.prototype, [])"), "true");
        assert_eq!(disp("Object.prototype.isPrototypeOf.call({}, [])"), "false");
        assert_eq!(disp("Object.prototype.isPrototypeOf.call({}, 5)"), "false");
        assert_eq!(disp("class A{}class B extends A{}Object.prototype.isPrototypeOf.call(A.prototype, new B())"), "true");
        assert_eq!(disp("({x:1}).propertyIsEnumerable('x')"), "true");
        assert_eq!(disp("({}).propertyIsEnumerable('x')"), "false");
        assert_eq!(disp("(5).valueOf()"), "5");
        assert_eq!(disp("({a:1}).valueOf().a"), "1");
    }

    #[test]
    fn array_expando_index() {
        // Non-canonical writes are named props, never errors (V8 parity).
        assert_eq!(disp("var a=[1];a['x']=9;a.x"), "9");
        assert_eq!(disp("var a=[1];a[-1]=9;a['-1']"), "9");
        assert_eq!(disp("var a=[1];a[1.5]=9;a['1.5']"), "9");
        assert_eq!(disp("var a=[1];a['1']=9;a[1]"), "9");
        assert_eq!(disp("var a=[];a[3]=7;a.length"), "4");
        assert_eq!(disp("var a=[1];a[1e15]=2;a.length"), "1");
    }

    #[test]
    fn array_from() {
        assert_eq!(disp("Array.from([1,2,3]).join()"), "1,2,3");
        assert_eq!(disp("Array.from('hi').join()"), "h,i");
        assert_eq!(disp("Array.from([1,2],function(x){return x*2}).join()"), "2,4");
        assert_eq!(disp("Array.from([1,2],function(x){return x+this.t},{t:10}).join()"), "11,12");
        assert_eq!(disp("Array.from({length:2}).length"), "2");
        assert_eq!(disp("Array.from([]).length"), "0");
    }

    #[test]
    fn spread_iterables() {
        assert_eq!(disp("[...new Set([3,1])].join()"), "3,1");
        assert_eq!(disp("[...new Map([[1,2]])][0].join()"), "1,2");
        assert_eq!(disp("[...'hi'].join()"), "h,i");
        assert_eq!(disp("[...new Uint8Array([7,8])].join()"), "7,8");
        assert_eq!(disp("[...new Uint16Array([9])].join()"), "9");
        assert_eq!(disp("Math.max(...new Set([2,9]))"), "9");
        assert_eq!(disp("var s='';for(var x of new Set([1,2])){s+=x}s"), "12");
        assert!(errmsg("[...{}]").contains("non-iterable"));
        assert!(errmsg("[...5]").contains("non-iterable"));
    }

    #[test]
    fn typed_clamped() {
        assert_eq!(disp("new Uint8ClampedArray([0.5,1.5,2.5,3.5,-1,300,NaN]).join()"), "0,2,2,4,0,255,0");
        assert_eq!(disp("var a=new Uint8ClampedArray(2);a[0]=2.5;a[1]=300;a.join()"), "2,255");
        assert_eq!(disp("Uint8ClampedArray.BYTES_PER_ELEMENT"), "1");
        assert_eq!(
            disp("Object.prototype.toString.call(new Uint8ClampedArray(1))"),
            "[object Uint8ClampedArray]"
        );
        assert_eq!(disp("new Uint8ClampedArray(2) instanceof Uint8ClampedArray"), "true");
        assert_eq!(disp("Uint8ClampedArray.of(300).join()"), "255");
    }

    #[test]
    fn typed_statics() {
        assert_eq!(disp("Uint8Array.of(137,80).join()"), "137,80");
        assert_eq!(disp("Uint8Array.from([1.7,'3'],x=>x+1).join()"), "2,31");
        assert_eq!(disp("Uint8Array.from('hi').join()"), "0,0");
        assert_eq!(disp("Uint16Array.of(70000).join()"), "4464");
        assert_eq!(disp("Uint8Array.from(new Uint8Array([5])).join()"), "5");
        assert_eq!(disp("var s=0;Uint8Array.from([1,2],function(v,i){s+=i;return v});s"), "1");
    }

    #[test]
    fn base64_globals() {
        assert_eq!(disp("atob('aGk=')"), "hi");
        assert_eq!(disp("btoa('Hi')"), "SGk=");
        assert_eq!(disp("atob('aGk')"), "hi");
        assert_eq!(disp("atob(' aGk= ')"), "hi");
        assert_eq!(disp("atob('')"), "");
        assert_eq!(disp("btoa('')"), "");
        assert_eq!(disp("atob('AP+A').length"), "3");
        assert_eq!(disp("atob('AP+A').charCodeAt(1)"), "255");
        assert_eq!(disp("btoa(atob('aGk='))"), "aGk=");
        assert!(errmsg("atob('aGkxy')").contains("Invalid character"));
        assert!(errmsg("atob('!!!')").contains("Invalid character"));
        assert!(errmsg("btoa('€')").contains("Invalid character"));
        assert_eq!(disp("typeof atob"), "function");
        // jsPDF shape: bound helpers off a facade object.
        assert_eq!(disp("var Y={atob:atob};var f=Y.atob.bind(Y);f('aGk=')"), "hi");
    }

    #[test]
    fn call_through_getter() {
        // tslib __createBinding shape: re-exported via a getter must be
        // callable, not just readable.
        assert_eq!(
            disp("var r=function(d,b){return 'ext:'+b};var m={__extends:r};var o={};\
                  Object.defineProperty(o,'__extends',{enumerable:true,get:function(){return m['__extends']}});\
                  o.__extends('D','B')"),
            "ext:B"
        );
        assert_eq!(
            disp("var o={};Object.defineProperty(o,'m',{get:function(){return function(x){return x*2}}});o.m(21)"),
            "42"
        );
        assert_eq!(
            disp("var o={arr:[1,2]};o.arr.map(function(x){return x+1}).join()"),
            "2,3"
        );
    }

    #[test]
    fn function_ctor() {
        assert_eq!(disp("Function('return 41')()"), "41");
        assert_eq!(disp("new Function('a','b','return a+b')(2,3)"), "5");
        assert_eq!(disp("Function().length"), "0");
        assert_eq!(disp("Function('a','b','return a') instanceof Function"), "true");
        assert_eq!(disp("typeof Function"), "function");
        // Global scope, not closure scope.
        assert_eq!(disp("var x=1;var f=Function('return x');var x=2;f()"), "2");
        assert!(errmsg("Function('return )')").contains("byte") || errmsg("Function('return )')").contains("expected"));
    }

    #[test]
    fn bound_construct() {
        // `new` on a bound fn constructs the target (fresh `this`,
        // bound args first), like V8.
        assert_eq!(disp("function P(a,b){this.a=a;this.b=b}var o=new (P.bind(null,1))(2);o.a"), "1");
        assert_eq!(disp("function P(a,b){this.a=a;this.b=b}var o=new (P.bind(null,1))(2);o.b"), "2");
        assert_eq!(disp("function P(){ }var o=new (P.bind(null))();o instanceof P"), "true");
        assert_eq!(
            disp("function E(t){if(!(this instanceof E))throw new TypeError('nope');this.t=t}new (E.bind(null))(5).t"),
            "5"
        );
        assert!(errmsg("new ((()=>{}).bind(null))()").contains("not a constructor"));
    }

    #[test]
    fn url_ctor() {        assert_eq!(
            disp("var u=new URL('/p?q=1#h','https://a.com/x');u.href"),
            "https://a.com/p?q=1#h"
        );
        assert_eq!(disp("var u=new URL('/p','https://a.com/x');u.protocol"), "https:");
        assert_eq!(disp("var u=new URL('/p','https://a.com/x');u.hostname"), "a.com");
        assert_eq!(disp("var u=new URL('/p','https://a.com/x');u.pathname"), "/p");
        assert_eq!(disp("var u=new URL('/p?q=1','https://a.com/x');u.search"), "?q=1");
        assert_eq!(disp("var u=new URL('/p#h','https://a.com/x');u.hash"), "#h");
        assert_eq!(disp("var u=new URL('/p','https://a.com/x');u.origin"), "https://a.com");
        assert_eq!(disp("var u=new URL('https://b.com:8080/y');u.port"), "8080");
        assert_eq!(disp("new URL('https://a.com/x') instanceof URL"), "true");
        assert_eq!(disp("URL.createObjectURL(0).slice(0,5)"), "blob:");
        assert_eq!(disp("URL.revokeObjectURL('blob:x')"), "undefined");
        assert!(errmsg("new URL(':::')").contains("invalid URL"));
    }

    #[test]
    fn labels() {
        assert_eq!(disp("var t=0;a:{t=1;break a;t=2}t"), "1");
        assert_eq!(
            disp("var i=0;outer:for(var j=0;j<5;j++){if(j===2)break outer;i++}i"),
            "2"
        );
        assert_eq!(
            disp("var s='';row:for(var r=0;r<3;r++){for(var c=0;c<3;c++){if(c===1)continue row;s+=c}}s"),
            "000"
        );
        assert_eq!(disp("var o={};var k='a';o[k]=1;o.a"), "1");
        assert_eq!(disp("var k='b';var o={[k]:2,[k+'c']:3};o.b+o.bc"), "5");
        assert!(errmsg("break nope").contains("no such label"));
        assert!(errmsg("a:{continue a}").contains("not a loop"));
    }

    #[test]
    fn destructuring_assignment() {
        assert_eq!(disp("var K;var a=[1,2];[K]=a.sort();K"), "1");
        assert_eq!(disp("var a=0,b=0;[a,b]=[b=1,a=2];a+b"), "3");
        assert_eq!(disp("var t;({x:t}={x:9});t"), "9");
        assert_eq!(disp("var a=[1,2,3];var r;[r]=a;r"), "1");
        assert_eq!(disp("var t='';[t]=['x'];t"), "x");
        assert!(errmsg("var a;[a.b]=[1]").contains("identifiers"));
        assert!(errmsg("var a;[a]+= [1]").contains("bad assignment"));
    }

    #[test]
    fn destructuring() {
        assert_eq!(disp("var [a,b]=['x','y'];a+b"), "xy");
        assert_eq!(disp("var {p,q}={p:1,q:2};p+q"), "3");
        assert_eq!(disp("var [h,,t]=[1,2,3];h+t"), "4");
        assert_eq!(disp("var [d=5,e=6]=[10];d+e"), "16");
        assert_eq!(disp("var {m=7}={};m"), "7");
        assert_eq!(disp("var [n,...r]=[1,2,3];r.length+n"), "3");
        assert_eq!(disp("var {o,...rest}={o:1,x:2};rest.x+o"), "3");
        assert_eq!(disp("var {a:{b}}={a:{b:42}};b"), "42");
        assert_eq!(disp("const [x,y]='a=b'.split('=');x+y"), "ab");
        assert!(errmsg("var [a]=null").contains("non-iterable"));
        assert!(errmsg("var [a]=1").contains("non-iterable"));
    }

    #[test]
    fn classes() {
        assert_eq!(disp("class A{};typeof A"), "function");
        assert_eq!(
            disp("class A{constructor(x){this.x=x}get(){return this.x}}new A(5).get()"),
            "5"
        );
        assert_eq!(disp("class A{};new A() instanceof A"), "true");
        assert_eq!(disp("class A{};new A().constructor===A"), "true");
        assert_eq!(disp("class A{x=10}new A().x"), "10");
        assert_eq!(disp("class A{static s=3}A.s"), "3");
        assert_eq!(disp("class A{static get D(){return 7}}A.D"), "7");
        assert_eq!(disp("class A{get g(){return 42}}new A().g"), "42");
        assert_eq!(
            disp("class A{set s(v){this.n=v}}var a=new A();a.s=9;a.n"),
            "9"
        );
        assert_eq!(
            disp("class B extends Array{};var b=new B();b instanceof B"),
            "true"
        );
        assert_eq!(
            disp("class B extends Object{constructor(){super();this.y=2}}new B().y"),
            "2"
        );
        assert_eq!(
            disp("class E extends Object{};new E() instanceof Object"),
            "true"
        );
        assert_eq!(
            disp("class N extends null{};new N() instanceof Object"),
            "false"
        );
        assert_eq!(disp("var C=class{who(){return 'n'}};new C().who()"), "n");
        assert_eq!(
            disp("var C=class Named{who(){return 'n'}};new C().who()"),
            "n"
        );
        // Parent fields install through super(), own fields shadow proto.
        assert_eq!(disp("class K{x=10}class E extends K{};new E().x"), "10");
        assert_eq!(
            disp("class K{x=10}K.prototype.x=99;class F extends K{y=20}var f=new F();f.x+','+f.y"),
            "10,20"
        );
        // super methods bind the receiver.
        assert_eq!(
            disp("class P{greet(){return 'hi '+this.n}}class C extends P{constructor(){super();this.n='bo'}go(){return super.greet()}}new C().go()"),
            "hi bo"
        );
        // Errors.
        assert!(errmsg("class A{};A()").contains("invoked with new"));
        assert!(errmsg("class A{};new A()()").contains("not a function"));
        assert!(errmsg("class A extends 5{}").contains("constructor or null"));
        assert!(errmsg("class A{constructor(){}constructor(){}}").contains("duplicate"));
        assert!(errmsg("class A{static constructor(){}}").contains("static constructor"));
        assert!(errmsg("function f(){super.x}").contains("unexpected super"));
        assert!(errmsg("super.x").contains("unexpected super"));
        assert!(errmsg("class A extends B{}").contains("not defined"));
    }

    #[test]
    fn new_target() {
        // `new C()` sees C; `.prototype` resolves on it.
        assert_eq!(disp("function C(){this.t=new.target}new C().t===C"), "true");
        assert_eq!(
            disp("function C(){this.p=new.target.prototype}new C().p===C.prototype"),
            "true"
        );
        // Plain calls (functions, methods, getters) see undefined.
        assert_eq!(disp("function f(){return new.target}f()===undefined"), "true");
        assert_eq!(disp("function f(){return new.target===undefined}f()"), "true");
        assert_eq!(
            disp("class A{m(){return new.target}}new A().m()===undefined"),
            "true"
        );
        assert_eq!(
            disp("class A{get x(){return new.target}}new A().x===undefined"),
            "true"
        );
        assert_eq!(disp("new.target===undefined"), "true");
        // Reflect.construct with explicit newTarget.
        assert_eq!(
            disp("function P(){this.nt=new.target}function N(){}Reflect.construct(P,[],N).nt===N"),
            "true"
        );
        assert_eq!(
            disp("function P(){this.p=1}function C(){}C.prototype={};var o=Reflect.construct(P,[],C);(o instanceof C)+'|'+o.p"),
            "true|1"
        );
        // Derived ctors see the derived ctor, incl. through super().
        assert_eq!(
            disp("class B extends Object{constructor(){super();this.nt=new.target}}new B().nt===B"),
            "true"
        );
        assert_eq!(
            disp("class P{}class C extends P{constructor(){super();this.nt=new.target}}new C().nt===C"),
            "true"
        );
        // Base default params run with the derived newTarget.
        assert_eq!(
            disp("class P{constructor(a=new.target){this.nt=a}}class C extends P{}new C().nt===C"),
            "true"
        );
        // Arrows inside constructors inherit, like `this`.
        assert_eq!(
            disp("function C(){var f=()=>new.target;this.t=f()}new C().t===C"),
            "true"
        );
        assert_eq!(
            disp("class B extends Object{constructor(){super();var f=()=>new.target;this.t=f()}}new B().t===B"),
            "true"
        );
        // Helper calls inside a ctor still see undefined.
        assert_eq!(
            disp("function h(){return new.target}function C(){this.t=h()}new C().t===undefined"),
            "true"
        );
        // Real-world shape: base fixes the proto from newTarget.
        assert_eq!(
            disp("function Base(){Object.setPrototypeOf(this,new.target.prototype)}class D extends Base{}var d=new D();(d instanceof D)+'|'+(d instanceof Base)"),
            "true|true"
        );
        // Errors: `new.foo` is not a meta-property.
        assert!(errmsg("new.foo()").contains("target"));
    }

    #[test]
    fn computed_class_members() {
        assert_eq!(disp("var K='k';var o={[K]:1};o.k"), "1");
        assert_eq!(
            disp("var K='k';class C{[K](){return 7}[K+'2']=8}var c=new C();c.k()+c.k2"),
            "15"
        );
        assert_eq!(
            disp("var s=Symbol('s');class C{[s](){return 3}}new C()[s]()"),
            "3"
        );
        assert_eq!(disp("class C{static ['s']=4}C.s"), "4");
    }

    #[test]
    fn computed_object_keys() {
        assert_eq!(disp("var o={['a'+'b']: 1};o.ab"), "1");
        assert_eq!(disp("var k='x';var o={[k]: 5};o.x"), "5");
        assert_eq!(disp("var o={[1+2]: 9};o[3]"), "9");
        assert_eq!(disp("var k='b';var o={a: 1,[k]: 2,'s': 3};o.a+o.b"), "3");
        assert_eq!(disp("var o={['X-Goog-Api-Key']: 7};o['X-Goog-Api-Key']"), "7");
        assert_eq!(disp("var o={[5]: 1};o[5]"), "1");
        // __proto__ stays an ordinary pair (no proto mutation).
        assert_eq!(disp("var o={__proto__: 1};o.__proto__"), "1");
    }

    #[test]
    fn computed_destructuring() {
        assert_eq!(disp("var k='ab';var o={ab: 1};var {[k]: v}=o;v"), "1");
        assert_eq!(disp("var {['z']: v = 42}={};v"), "42");
        assert_eq!(disp("var k='q';var {['z']: v = 42,[k]: w}={q: 1};v+w"), "43");
        assert_eq!(disp("var {[5]: v}={5: 8};v"), "8");
        assert_eq!(disp("var t;({['a'+'b']: t}={ab: 9});t"), "9");
        assert_eq!(disp("function f({['a'+'b']: v}){return v}f({ab: 4})"), "4");
        assert_eq!(disp("var {['a']: v,...rest}={a: 1,b: 2};v+rest.b"), "3");
    }

    #[test]
    fn computed_object_method() {
        // Plain [k]() only; async/generator prefixes and computed
        // accessors in literals stay unsupported.
        assert_eq!(disp("var k='m';var o={[k](){return 7}};o.m()"), "7");
        assert_eq!(disp("var k='m';var o={[k](){return this.x},x: 5};o[k]()"), "5");
        assert_eq!(disp("var o={m(){return 3}};o.m()"), "3");
    }

    #[test]
    fn destructuring_params() {
        assert_eq!(disp("function f({a,b}){return a+b}f({a:1,b:2})"), "3");
        assert_eq!(disp("function f([x,,z]){return x+z}f([1,2,3])"), "4");
        assert_eq!(disp("function f({a=5}={}){return a}f()"), "5");
        assert_eq!(disp("var g=({x})=>x*2;g({x:21})"), "42");
        assert_eq!(disp("function f({a:{b}}){return b}f({a:{b:7}})"), "7");
        assert!(errmsg("function f({a}){};f(null)").contains("cannot read"));
    }

    #[test]
    fn bound_functions() {
        assert_eq!(
            disp("function f(a,b){return this.x+a+b}var g=f.bind({x:1},2);g(3)"),
            "6"
        );
        assert_eq!(
            disp("var o={n:4};function f(){return this.n}var g=f.bind(o);g()"),
            "4"
        );
        assert_eq!(
            disp("[1,2].map(function(x){return x*2}.bind(null)).join()"),
            "2,4"
        );
        assert!(errmsg("var f=function(){};f.bind.call({}, 1)").contains("non-function"));
    }

    #[test]
    fn rest_params() {
        assert_eq!(disp("function f(a,...r){return r.length}f(1,2,3)"), "2");
        assert_eq!(disp("function f(a,...r){return a}f(1,2,3)"), "1");
        assert_eq!(disp("var g=(...a)=>a.length;g(1,2,3,4)"), "4");
        assert_eq!(disp("function h(...r){return r}h()"), "[]");
        assert!(errmsg("function f(...a,b){}").contains("rest param must be last"));
    }

    #[test]
    fn templates() {
        assert_eq!(disp("var n='w';`hi ${n}!`"), "hi w!");
        assert_eq!(disp("`sum=${1 + 2}`"), "sum=3");
        assert_eq!(disp("`a${`b${'c'}d`}e`"), "abcde");
        assert_eq!(disp("`esc \\` \\$`"), "esc ` $");
        assert_eq!(disp("`x=${{a: 1}.a}`"), "x=1");
        assert_eq!(out("console.log(`v=${7}`)"), "v=7\n");
        assert_eq!(disp("`\\u{41}\\x42`"), "AB");
        assert!(errmsg("`abc").contains("unterminated template"));
        assert!(errmsg("var t=`\\xg`;t").contains("invalid escape"));
    }

    #[test]
    fn tagged_templates() {
        // strings array shape: length, cooked items, values in order
        assert_eq!(disp("function t(s){return s.length}t`a${1}b`"), "2");
        assert_eq!(disp("function t(s,a,b){return a+'|'+b}t`x${1}y${2}z`"), "1|2");
        assert_eq!(disp("function t(s){return s[0]+'|'+s[1]}t`a${1}b`"), "a|b");
        assert_eq!(disp("function t(s){return s.length+':'+s[0]}t`hi`"), "1:hi");
        // Array.isArray holds for the site and its raw
        assert_eq!(
            disp("function t(s){return Array.isArray(s)+'|'+Array.isArray(s.raw)+'|'+s.raw.length}t`a${1}b`"),
            "true|true|2"
        );
        // cooked escapes resolve; raw keeps the backslash text
        assert_eq!(disp("function t(s){return s[0]}t`\\n`"), "\n");
        assert_eq!(disp("function t(s){return s.raw[0]}t`a\\nb`"), "a\\nb");
        assert_eq!(disp("function t(s){return s[0]+'|'+s.raw[0]}t`\\x41`"), "A|\\x41");
        // invalid escapes poison cooked to undefined, raw keeps text
        assert_eq!(disp("function t(s){return s[0]===undefined}t`\\u{110000}`"), "true");
        assert_eq!(disp("function t(s){return s.raw[0]}t`\\u{110000}`"), "\\u{110000}");
        assert_eq!(disp("function t(s){return s[0]+'|'+s[1]}t`a${1}\\xg`"), "a|undefined");
        // member-expression tags run with this=undefined per spec
        assert_eq!(disp("var o={tag:function(s,v){return s[0]+v}};o.tag`hi${42}`"), "hi42");
        assert_eq!(disp("var o={tag:function(s){return this===undefined}};o.tag`x`"), "true");
        // nesting both directions
        assert_eq!(disp("function t(s,v){return s[0]+v+s[1]};t`a${t`b${2}c`}d`"), "ab2cd");
        assert_eq!(disp("function t(s,v){return v};t`a${`b${3}c`}d`"), "b3c");
        // chains on the result like an ordinary call value
        assert_eq!(disp("function t(s){return {v:s[0]}};t`k`.v"), "k");
        // String.raw falls out of the shape (raw text, subs interleaved)
        assert_eq!(disp("String.raw`h\\x`"), "h\\x");
        assert_eq!(disp("String.raw`a${1}b${2}c`"), "a1b2c");
        assert_eq!(disp("String.raw({raw:['a','b']},1)"), "a1b");
        // non-function tags throw like ordinary calls
        assert!(errmsg("5`x`").contains("not a function"));
        assert!(errmsg("var t=`x`;t`t`").contains("not a function"));
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
    }

    #[test]
    fn do_while_runs_once() {
        assert_eq!(num("var t=0;do{t+=1}while(t<3);t"), 3.0);
        assert_eq!(num("var t=0;do{t+=1}while(false);t"), 1.0);
        assert_eq!(num("var t=0;do{if(t>5)break;t+=2}while(t<10);t"), 6.0);
    }

    #[test]
    fn switch_dispatch() {
        assert_eq!(
            disp("var o='';switch(2){case 1:o+='a';break;case 2:o+='b';default:o+='z'};o"),
            "bz"
        );
        assert_eq!(
            disp("var o='';switch(9){case 1:o+='a';break;default:o+='d'};o"),
            "d"
        );
        assert_eq!(disp("var o='';switch(9){case 1:o+='a'};o"), "");
        assert_eq!(
            disp("var o='';switch(1){case 1:o+='a';case 2:o+='b'};o"),
            "ab"
        );
        assert_eq!(
            disp("var o='';switch('1'){case 1:o+='n';break;default:o+='s'};o"),
            "s"
        );
        // `break` in a case exits the switch, not the enclosing loop.
        assert_eq!(
            num("var t=0;for(var i=0;i<3;i++){switch(i){case 1:break}t+=1}t"),
            3.0
        );
        assert!(errmsg("break").contains("outside loop"));
        assert!(errmsg("switch(1){default:break;default:}").contains("duplicate default"));
    }

    #[test]
    fn void_operator() {
        assert_eq!(disp("void 0"), "undefined");
        assert_eq!(disp("void(1+1)"), "undefined");
        assert_eq!(disp("var x=1;void x;x"), "1");
    }

    #[test]
    fn methods_and_accessors() {
        assert_eq!(disp("var o={m(){return 7}};o.m()"), "7");
        assert_eq!(disp("var o={n:1,m(){return this.n+1}};o.m()"), "2");
        assert_eq!(disp("var o={get x(){return 42}};o.x"), "42");
        assert_eq!(disp("var o={n:1,get g(){return this.n*2}};o.g"), "2");
        assert_eq!(disp("var o={n:0,set s(v){this.n=v}};o.s=10;o.n"), "10");
        assert_eq!(
            disp("var b={get x(){return 1},set x(v){this.y=v}};b.x=5;b.x+b.y"),
            "6"
        );
        assert_eq!(disp("var o={get(){return 1}};o.get()"), "1");
    }

    #[test]
    fn symbols() {
        assert_eq!(disp("typeof Symbol('d')"), "symbol");
        assert_eq!(disp("Symbol('d').description"), "d");
        assert_eq!(disp("Symbol().toString()"), "Symbol()");
        assert_eq!(disp("Symbol.for('k')===Symbol.for('k')"), "true");
        assert_eq!(disp("Symbol.keyFor(Symbol.for('k'))"), "k");
        assert_eq!(disp("var o={};o[Symbol.for('rk')]=7;o['Symbol(rk)']"), "7");
        assert!(errmsg("new Symbol()").contains("not a constructor"));
        // Bare calls stay legal nested in constructors (sloppy `this`
        // is the window object there, not a fresh instance).
        assert_eq!(disp("function F(){this.s=Symbol('s')}var o=new F();typeof o.s"), "symbol");
        assert!(errmsg("Reflect.construct(Symbol,[])").contains("not a constructor"));
    }

    #[test]
    fn maps_and_sets() {
        assert_eq!(disp("var m=new Map();m.set('a',1);m.get('a')"), "1");
        assert_eq!(disp("var m=new Map();m.set('a',1);m.size"), "1");
        assert_eq!(disp("var m=new Map([['a',1],['b',2]]);m.get('b')"), "2");
        assert_eq!(disp("var s=new Set([1,2,2]);s.size"), "2");
        assert_eq!(disp("var s=new Set();s.add(1);s.has(1)"), "true");
        assert_eq!(
            disp("var w=new WeakMap();var o={};w.set(o,5);w.get(o)"),
            "5"
        );
        assert!(errmsg("var w=new WeakMap();w.set(1,2)").contains("must be an object"));
    }

    #[test]
    fn for_pattern_targets() {
        assert_eq!(disp("var s='';for(var {a} of [{a:1},{a:2}])s+=a;s"), "12");
        assert_eq!(disp("var s='';for(var [x] of [[1],[2]])s+=x;s"), "12");
        assert_eq!(disp("var s='';for({a} of [{a:1},{a:2}])s+=a;s"), "12");
        assert_eq!(disp("var t=0;for(var k in {a:1,b:2})t++;t"), "2");
    }

    #[test]
    fn for_in_keys() {
        assert_eq!(disp("var o={a:1,b:2};var k='';for(var x in o)k+=x;k"), "ab");
        assert_eq!(disp("var s='';for(var i in ['x','y'])s+=i;s"), "01");
        assert_eq!(
            num("var n=0;for(var k in null)n++;for(var k in 5)n++;n"),
            0.0
        );
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
        assert_eq!(num("2**10"), 1024.0);
        assert_eq!(num("2**3**2"), 512.0);
        assert_eq!(num("2**-2"), 0.25);
        assert_eq!(num("var x=3;x**=2;x"), 9.0);
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
        // test threads have ~2MB stacks and debug frames are fat: keep
        // the depth low, the guard logic is depth-agnostic (see
        // fatal_errors_bypass_catch).
        let mut it = Interp::new();
        it.max_call_depth = 40;
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
    fn array_fill_modern() {
        // fill: full, ranged, negative, clamped, NaN-start, identity.
        assert_eq!(disp("[1,2,3].fill(9)"), "[9,9,9]");
        assert_eq!(disp("[1,2,3,4].fill(0,1,3)"), "[1,0,0,4]");
        assert_eq!(disp("[1,2,3,4].fill(0,-2)"), "[1,2,0,0]");
        assert_eq!(disp("[1,2,3,4].fill(0,-3,-1)"), "[1,0,0,4]");
        assert_eq!(disp("[1,2].fill(9,0,99)"), "[9,9]");
        assert_eq!(disp("[1,2].fill(9,5)"), "[1,2]");
        assert_eq!(disp("[1,2].fill(9,NaN)"), "[9,9]");
        assert_eq!(disp("[1,2,3].fill(0,3,1)"), "[1,2,3]");
        assert!(boolean("var fa=[1,2];fa.fill(5)===fa"));
        assert_eq!(num("new Array(128).fill(undefined).length"), 128.0);
        // the rest of the missing pure/local ES2019+ set, one assert each.
        assert_eq!(num("[3,7,9].findLast(function(x){return x>4})"), 9.0);
        assert_eq!(
            disp("[1,2].flatMap(function(x){return [x,x*10]})"),
            "[1,10,2,20]"
        );
        assert_eq!(disp("[1,2].flatMap(function(x){return x*2})"), "[2,4]");
        assert_eq!(num("[10,20,30].at(-1)"), 30.0);
        assert_eq!(num("[10,20,30].at(0)"), 10.0);
        assert_eq!(disp("[1].at(5)"), "undefined");
        assert_eq!(disp("[1,2,3,4].copyWithin(0,2)"), "[3,4,3,4]");
        assert!(boolean("var ca=[1,2,3,4];ca.copyWithin(0,2)===ca"));
        assert_eq!(disp("[7,8].keys()"), "[0,1]");
        assert_eq!(disp("[5,6].values()"), "[5,6]");
        assert_eq!(
            disp("[7,8].entries().map(function(p){return p[0]+':'+p[1]}).join(',')"),
            "0:7,1:8"
        );
        assert_eq!(disp("[3,1,2].toReversed()"), "[2,1,3]");
        assert_eq!(disp("var tr=[3,1];var rr=tr.toReversed();tr"), "[3,1]");
        assert_eq!(
            disp("[10,9,1].toSorted(function(a,b){return a-b})"),
            "[1,9,10]"
        );
        assert_eq!(disp("var ts=[3,1];var sr=ts.toSorted();ts"), "[3,1]");
        assert_eq!(disp("[1,2,3,4].toSpliced(1,2,'x')"), "[1,\"x\",4]");
        assert_eq!(disp("[1,2,3].with(1,9)"), "[1,9,3]");
        assert_eq!(disp("[1,2,3].with(-1,9)"), "[1,2,9]");
        assert!(errmsg("[1].with(5,9)").contains("out of range"));
    }

    #[test]
    fn message_channel() {
        assert_eq!(disp("typeof MessageChannel"), "function");
        assert!(boolean("var mc0=new MessageChannel();mc0.port1!==mc0.port2"));
        assert!(boolean("var mc1=new MessageChannel();mc1 instanceof MessageChannel"));
        assert_eq!(disp("var mc2=new MessageChannel();mc2.port1.start()"), "undefined");
        // Zero-timer delivery drains after the completion value, so each
        // setup posts in one run and asserts in the next (IO-test pattern).
        let mut it = Interp::new();
        it.run(
            "var got=null;var mc=new MessageChannel();\
             mc.port2.onmessage=function(e){got=e.data};\
             mc.port1.postMessage(42)",
        )
        .unwrap();
        let v = it.run("got").unwrap();
        assert_eq!(it.inspect(v), "42");
        // reverse direction on the same channel.
        it.run(
            "var back=null;\
             mc.port1.onmessage=function(e){back=e.data};\
             mc.port2.postMessage('hi')",
        )
        .unwrap();
        let v = it.run("back").unwrap();
        assert_eq!(it.inspect(v), "hi");
        // addEventListener('message') fires alongside onmessage.
        it.run(
            "var seen=[];var mc3=new MessageChannel();\
             mc3.port2.addEventListener('message',function(e){seen.push(e.data)});\
             mc3.port1.postMessage(7)",
        )
        .unwrap();
        let v = it.run("seen").unwrap();
        assert_eq!(it.inspect(v), "[7]");
        // removeEventListener detaches; a non-function onmessage is
        // ignored (never thrown), matching the on* expando style.
        it.run(
            "var n=0;var mc4=new MessageChannel();\
             function cb(e){n++};\
             mc4.port2.addEventListener('message',cb);\
             mc4.port2.removeEventListener('message',cb);\
             mc4.port2.onmessage=5;\
             mc4.port1.postMessage(1)",
        )
        .unwrap();
        let v = it.run("n").unwrap();
        assert_eq!(it.inspect(v), "0");
        // close() before the drain drops the queued message.
        it.run(
            "var gone=null;var mc5=new MessageChannel();\
             mc5.port2.onmessage=function(e){gone=e.data};\
             mc5.port1.postMessage(1);mc5.port2.close()",
        )
        .unwrap();
        let v = it.run("gone").unwrap();
        assert_eq!(it.inspect(v), "null");
        // pass-by-reference (structuredClone gap): a pre-drain mutation
        // is visible to the handler.
        it.run(
            "var rc=null;var mc6=new MessageChannel();\
             mc6.port2.onmessage=function(e){rc=e.data.x};\
             var o={x:1};mc6.port1.postMessage(o);o.x=2",
        )
        .unwrap();
        let v = it.run("rc").unwrap();
        assert_eq!(it.inspect(v), "2");
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
    fn function_meta() {
        assert_eq!(disp("function f(a,b){}f.length"), "2");
        assert_eq!(disp("function f(a,b=1){}f.length"), "1");
        assert_eq!(disp("function f(){}f.name"), "f");
        assert_eq!(disp("var o={m(){}};o.m.name"), "m");
        assert_eq!(disp("function f(){return arguments.length}f(1,2,3)"), "3");
        assert_eq!(disp("function f(){return arguments[1]}f(1,2,3)"), "2");
        assert_eq!(disp("function f(){return arguments.callee===f}f()"), "true");
        assert_eq!(disp("function f(arguments){return arguments}f(9)"), "9");
    }

    #[test]
    fn string_statics() {
        assert_eq!(disp("String.fromCharCode(72,105)"), "Hi");
        assert_eq!(disp("String.fromCharCode()"), "");
        assert_eq!(disp("String.fromCodePoint(0x1F600)"), "\u{1F600}");
        assert!(errmsg("String.fromCodePoint(-1)").contains("invalid code point"));
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
        // own-prop objects still work. Self-calibrated above install
        // (absolute values kept flaking as builtins were added).
        let mut it = Interp::with_cap(1_000_000);
        it.run("0").unwrap();
        it.heap.cap = it.heap.live() + 50;
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
            "err:nope is not defined (in ?)\n"
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
            "nope is not defined (in Promise > ?)\n"
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
        // an uncleared interval parks silently at the per-timer quota
        // (live pages re-arm forever; failing the snapshot over it helps
        // no one) - and its callbacks did run. Callbacks must not leak into
        // the top-level completion value either (last save/restore).
        // (The read lands before this run's own drain, so `n` is exactly
        // the first drain's quota-capped count.)
        let mut it = Interp::new();
        it.run("var n=0;setInterval(function(){n++},1)").unwrap();
        assert_eq!(it.run("n").unwrap(), Value::Num(MAX_TIMER_QUOTA as f64));
    }

    #[test]
    fn drain_timer_fairness() {
        // A re-arming interval must not starve later timers: once the hog
        // exhausts its per-drain quota the one-shot still fires in the same
        // drain. Pre-quota this failed - the one-shot never ran (4097 fires
        // on 1 distinct timer). The read lands before this run's own drain,
        // so `hog` is exactly the first drain's count.
        let mut it = Interp::new();
        it.run("var hog=0,fired=false;setInterval(function(){hog++},0);\
                setTimeout(function(){fired=true},5)")
            .unwrap();
        assert_eq!(
            it.run("fired?hog:-1").unwrap(),
            Value::Num(MAX_TIMER_QUOTA as f64)
        );
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
        // `stack` exists from construction (head line; frames attach on
        // first unwind).
        assert_eq!(disp("typeof new Error('x').stack"), "string");
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
        // call depth is Fatal: catch never sees it, finally still runs.
        // Depth 40, not 100: debug-build native frames are fat (~20KB per
        // JS level), and test threads only get 2MB - the guard logic is
        // depth-agnostic, so a shallower trip proves the same thing.
        let mut it = Interp::new();
        it.max_call_depth = 40;
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
