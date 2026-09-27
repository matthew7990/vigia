//! Mark-sweep GC over the flat arenas (Heap::objs, Heap::strs, envs).
//!
//! Collection runs only at safepoints - statement boundaries and between
//! drain callbacks - where every live Value is reachable from a root:
//!   - the global env (id 0) and every env on env_stack; each env's
//!     parent chain is followed transitively
//!   - in-flight call values (call_vals): callee, `this`, args - Rust
//!     locals are invisible to the marker, so call_value roots them here
//!   - last completion value and cur_native
//!   - queued work: microtasks (cb/arg/next), timers (cb/args),
//!     event listeners
//!   - the DOM wrapper cache (dom_objs) and the shared protos
//!   - every interned string: intern entries stay live so literal
//!     ids never dangle
//!
//! A marked Obj::Func marks its captured env transitively, which is what
//! keeps a closure's defining frame alive after it would otherwise drop.
//!
//! Sweep tombstones each unmarked slot in place (Obj::Freed, None str,
//! env.free) and rebuilds the freelists, so alloc_* reuses ids and the
//! arena Vecs never shrink - existing ids stay valid for life.

use crate::{Interp, Obj, PromiseState, Value};

/// Slots freed by one collection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GcStats {
    pub freed_objs: usize,
    pub freed_strs: usize,
    pub freed_envs: usize,
}

/// Mark bitsets + worklists. Ids push onto a worklist and dedupe on pop
/// via the bit; already-free slots (Freed / None / env.free) are never
/// marked so they stay on the freelist.
struct Marker {
    objs: Vec<bool>,
    strs: Vec<bool>,
    envs: Vec<bool>,
    ow: Vec<u32>,
    sw: Vec<u32>,
    ew: Vec<u32>,
}

impl Marker {
    fn val(&mut self, v: Value) {
        match v {
            Value::Str(id) => self.sw.push(id),
            Value::Obj(id) => self.ow.push(id),
            _ => {}
        }
    }

    /// Drain the worklists; children discovered while marking push back
    /// on, so loop until all three run dry.
    fn mark(&mut self, it: &Interp) {
        loop {
            let mut did = false;
            while let Some(id) = self.ow.pop() {
                did = true;
                let Some(o) = it.heap.objs.get(id as usize) else {
                    continue;
                };
                if self.objs[id as usize] || matches!(o, Obj::Freed) {
                    continue;
                }
                self.objs[id as usize] = true;
                match o {
                    Obj::Ordinary { pairs, proto } | Obj::Func { pairs, proto, .. } => {
                        if let Obj::Func { env, .. } = o {
                            self.ew.push(*env);
                        }
                        if let Some(p) = proto {
                            self.ow.push(*p);
                        }
                        for (_, v) in pairs {
                            self.val(*v);
                        }
                    }
                    Obj::Arr {
                        items,
                        proto,
                        pairs,
                    } => {
                        if let Some(p) = proto {
                            self.ow.push(*p);
                        }
                        for v in items {
                            self.val(*v);
                        }
                        for (_, v) in pairs {
                            self.val(*v);
                        }
                    }
                    Obj::Native { pairs, .. } => {
                        for (_, v) in pairs {
                            self.val(*v);
                        }
                    }
                    Obj::Promise { st, pairs, .. } => {
                        for (_, v) in pairs {
                            self.val(*v);
                        }
                        match st {
                            PromiseState::Pending { handlers } => {
                                for h in handlers {
                                    if let Some(v) = h.on_fulfill {
                                        self.val(v);
                                    }
                                    if let Some(v) = h.on_reject {
                                        self.val(v);
                                    }
                                    if h.next != u32::MAX {
                                        self.ow.push(h.next);
                                    }
                                }
                            }
                            PromiseState::Fulfilled(v) | PromiseState::Rejected(v) => {
                                self.val(*v)
                            }
                        }
                    }
                    Obj::RegExp {
                        pat, flags, proto, ..
                    } => {
                        self.sw.push(*pat);
                        self.sw.push(*flags);
                        if let Some(p) = proto {
                            self.ow.push(*p);
                        }
                    }
                    Obj::Dom { proto, .. } => {
                        if let Some(p) = proto {
                            self.ow.push(*p);
                        }
                    }
                    Obj::Style { .. } | Obj::Freed => {}
                    Obj::Proxy { target, handler } => {
                        self.ow.push(*target);
                        self.ow.push(*handler);
                    }
                    Obj::Accessor { get, set, proto } => {
                        if let Some(g) = get {
                            self.ow.push(*g);
                        }
                        if let Some(s) = set {
                            self.ow.push(*s);
                        }
                        if let Some(p) = proto {
                            self.ow.push(*p);
                        }
                    }
                    Obj::Symbol { desc, proto } => {
                        if let Some(d) = desc {
                            self.sw.push(*d);
                        }
                        if let Some(p) = proto {
                            self.ow.push(*p);
                        }
                    }
                    Obj::Map { entries, proto } | Obj::WeakMap { entries, proto } => {
                        for (k, v) in entries {
                            self.val(*k);
                            self.val(*v);
                        }
                        if let Some(p) = proto {
                            self.ow.push(*p);
                        }
                    }
                    Obj::Set { items, proto } => {
                        for v in items {
                            self.val(*v);
                        }
                        if let Some(p) = proto {
                            self.ow.push(*p);
                        }
                    }
                    Obj::Bytes { pairs, proto, .. } => {
                        for (_, v) in pairs {
                            self.val(*v);
                        }
                        if let Some(p) = proto {
                            self.ow.push(*p);
                        }
                    }
                    Obj::Typed { pairs, proto, .. } => {
                        for (_, v) in pairs {
                            self.val(*v);
                        }
                        if let Some(p) = proto {
                            self.ow.push(*p);
                        }
                    }
                    Obj::DView { proto, .. } => {
                        if let Some(p) = proto {
                            self.ow.push(*p);
                        }
                    }
                    Obj::Buf { proto, .. } => {
                        if let Some(p) = proto {
                            self.ow.push(*p);
                        }
                    }
                }
            }
            while let Some(id) = self.sw.pop() {
                did = true;
                if let Some(Some(_)) = it.heap.strs.get(id as usize) {
                    self.strs[id as usize] = true;
                }
            }
            while let Some(id) = self.ew.pop() {
                did = true;
                let Some(e) = it.envs.get(id as usize) else {
                    continue;
                };
                if self.envs[id as usize] || e.free {
                    continue;
                }
                self.envs[id as usize] = true;
                for v in e.vars.values() {
                    self.val(*v);
                }
                if let Some(p) = e.parent {
                    self.ew.push(p);
                }
            }
            if !did {
                break;
            }
        }
    }
}

impl Interp {
    /// Safepoint check: collect once live heap slots pass 70% of cap.
    /// Called between statements and between drain callbacks only, and
    /// collects only at call_depth 0 - a nested call's inner statements
    /// must not collect, because the caller's expr() frame can hold the
    /// sole reference to a temporary (mkstr() + churn() would lose the
    /// string mid-expression). At depth 0 every live Value sits in an
    /// env, a queue, or a root field.
    pub(crate) fn maybe_gc(&mut self) {
        if self.call_depth == 0 && self.heap.live() > self.heap.cap.saturating_mul(7) / 10 {
            self.gc();
        }
    }

    /// Env-only collection, safe at any call depth: Rust locals never
    /// hold envs (only Values), so every live env is reachable from the
    /// open frames (env_stack, parents included) or captured by a Func
    /// in the heap (scanned conservatively - dead Funcs over-retain,
    /// never wrongly free).
    pub(crate) fn gc_envs(&mut self) {
        let mut marked = vec![false; self.envs.len()];
        let mut stack: Vec<u32> = Vec::new();
        stack.push(0);
        stack.extend(self.env_stack.iter().copied());
        for o in &self.heap.objs {
            if let Obj::Func { env, .. } = o {
                stack.push(*env);
            }
        }
        while let Some(e) = stack.pop() {
            let Some(env) = self.envs.get(e as usize) else {
                continue;
            };
            if marked[e as usize] || env.free {
                continue;
            }
            marked[e as usize] = true;
            if let Some(p) = env.parent {
                stack.push(p);
            }
        }
        let mut free_envs = Vec::new();
        for (i, &m) in marked.iter().enumerate().skip(1) {
            if m {
                continue;
            }
            let e = &mut self.envs[i];
            if !e.free {
                e.vars.clear();
                e.parent = None;
                e.free = true;
            }
            free_envs.push(i as u32);
        }
        self.free_envs = free_envs;
        self.gc_runs += 1;
    }

    /// Full mark-sweep. Callable anytime; outside eval the root set is
    /// just globals + queues. Returns per-arena free counts.
    pub fn gc(&mut self) -> GcStats {
        self.gc_runs += 1;
        let mut m = Marker {
            objs: vec![false; self.heap.objs.len()],
            strs: vec![false; self.heap.strs.len()],
            envs: vec![false; self.envs.len()],
            ow: Vec::new(),
            sw: Vec::new(),
            ew: Vec::new(),
        };
        // roots
        m.ew.push(0); // global env
        for &e in &self.env_stack {
            m.ew.push(e);
        }
        m.val(self.last);
        m.val(self.cur_native);
        for &v in &self.call_vals {
            m.val(v);
        }
        for &v in &self.super_stack {
            m.val(v);
        }
        for p in [
            self.protos.object,
            self.protos.array,
            self.protos.function_,
            self.protos.string,
            self.protos.number,
            self.protos.date,
            self.protos.promise,
            self.protos.error,
            self.protos.regexp,
            self.protos.symbol,
            self.protos.map,
            self.protos.set,
            self.protos.weakmap,
            self.protos.url,
            self.protos.uint8array,
            self.protos.buffer,
            self.protos.dataview,
            self.protos.int8array,
            self.protos.uint8clampedarray,
            self.protos.uint16array,
            self.protos.int16array,
            self.protos.uint32array,
            self.protos.int32array,
            self.protos.float32array,
            self.protos.float64array,
            self.protos.textencoder,
            self.protos.textdecoder,
            self.protos.storage,
            self.protos.resizeobserver,
            self.protos.dom_node,
            self.protos.dom_element,
            self.protos.dom_htmlelement,
            self.protos.dom_document,
            self.protos.dom_shadowroot,
            self.protos.dom_documentfragment,
            self.protos.dom_input,
            self.protos.dom_form,
            self.protos.dom_select,
            self.protos.dom_textarea,
            self.protos.dom_button,
            self.protos.dom_anchor,
            self.protos.dom_image,
            self.protos.dom_canvas,
            self.protos.dom_iframe,
            self.protos.dom_svg,
        ] {
            if p != u32::MAX {
                m.ow.push(p);
            }
        }
        // `Symbol.for` entries live forever.
        for &id in self.symbol_registry.values() {
            m.ow.push(id);
        }
        for mt in &self.microtasks {
            if let Some(cb) = mt.cb {
                m.val(cb);
            }
            m.val(mt.arg);
            if mt.next != u32::MAX {
                m.ow.push(mt.next);
            }
        }
        for t in &self.timers {
            m.val(t.cb);
            for &a in &t.args {
                m.val(a);
            }
        }
        for ls in self.listeners.values() {
            for &(_, f) in ls {
                m.val(f);
            }
        }
        for &o in self.dom_objs.values() {
            m.ow.push(o);
        }
        for &o in self.sheets.values() {
            m.ow.push(o);
        }
        for &s in self.heap.intern.values() {
            m.sw.push(s);
        }
        m.mark(self);
        // sweep: tombstone unmarked slots in place, rebuild freelists
        let mut freed_objs = 0;
        let mut free_objs = Vec::new();
        for (i, o) in self.heap.objs.iter_mut().enumerate() {
            if m.objs[i] {
                continue;
            }
            if !matches!(o, Obj::Freed) {
                *o = Obj::Freed;
                freed_objs += 1;
            }
            free_objs.push(i as u32);
        }
        self.heap.free_objs = free_objs;
        let mut freed_strs = 0;
        let mut free_strs = Vec::new();
        for (i, s) in self.heap.strs.iter_mut().enumerate() {
            if m.strs[i] {
                continue;
            }
            if s.is_some() {
                *s = None;
                freed_strs += 1;
            }
            free_strs.push(i as u32);
        }
        self.heap.free_strs = free_strs;
        // env 0 (global) is never freed
        let mut freed_envs = 0;
        let mut free_envs = Vec::new();
        for i in 1..self.envs.len() {
            if m.envs[i] && !self.envs[i].free {
                continue;
            }
            let e = &mut self.envs[i];
            if !e.free {
                e.vars.clear();
                e.parent = None;
                e.free = true;
                freed_envs += 1;
            }
            free_envs.push(i as u32);
        }
        self.free_envs = free_envs;
        // a recycled obj id must not inherit "handled rejection" status
        self.handled_promises
            .retain(|id| m.objs.get(*id as usize).copied().unwrap_or(false));
        GcStats {
            freed_objs,
            freed_strs,
            freed_envs,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Completion value, inspected (strings bare, objects JSON).
    fn disp(it: &mut Interp, src: &str) -> String {
        let v = it.run(src).unwrap();
        it.inspect(v)
    }

    #[test]
    fn churn_stays_bounded() {
        // 500 iterations x ~2 slots against a cap with modest headroom:
        // GC must run and keep live slots under the cap. Self-calibrated
        // above install like its siblings (absolute values kept flaking
        // as builtins were added).
        let mut it = Interp::with_cap(1_000_000);
        it.run("0").unwrap();
        it.heap.cap = it.heap.live() + 1200;
        let v = it
            .run("var keep=[];for(var i=0;i<500;i++){var t={a:i,b:'x'+i};if(i%7==0){keep.push(t)}}keep.length")
            .unwrap();
        assert_eq!(v, Value::Num(72.0));
        assert!(it.gc_runs > 0, "gc never ran");
        let (o, s) = it.heap.stats();
        assert!(o + s <= it.heap.cap, "live {o}+{s} over cap {}", it.heap.cap);
    }

    #[test]
    fn cap_far_exceeded_when_garbage() {
        // ~3000 allocations against cap 500: completes only via GC reuse.
        let mut it = Interp::with_cap(500);
        let v = it.run("var t,i;for(i=0;i<1500;i++){t={n:i}}i").unwrap();
        assert_eq!(v, Value::Num(1500.0));
        assert!(it.gc_runs > 0);
    }

    #[test]
    fn closure_env_survives() {
        let mut it = Interp::new();
        it.run("var f=(function(){var x=7;return function(){return x}})()")
            .unwrap();
        // dead for-decl env + per-iteration block envs to prove sweeping
        it.run("for(var i=0;i<10;i++){var z=i}").unwrap();
        let st = it.gc();
        assert!(st.freed_envs > 0, "no dead frames freed");
        assert_eq!(it.run("f()").unwrap(), Value::Num(7.0));
    }

    #[test]
    fn timers_and_microtasks_are_roots() {
        // Tight cap just above the install footprint (self-calibrating:
        // new builtins move it automatically): the top-level churn forces
        // a collection while the promise handler sits queued in
        // microtasks; cb1's garbage then triggers another collection at
        // the drain safepoint between timer callbacks. Order: microtasks
        // first, then timers by deadline.
        let mut it = Interp::with_cap(1_000_000);
        it.run("0").unwrap();
        // Headroom for the churn peak (historically ~1170 over install):
        // tight enough that the 800+900 churn still forces collections,
        // loose enough for the script's own allocs.
        it.heap.cap = it.heap.live() + 1200;
        it.run(
            "var out=[];\
             Promise.resolve(9).then(function(v){out.push(v)});\
             setTimeout(function(){for(var i=0;i<800;i++){var t={n:i}}out.push(1)},0);\
             setTimeout(function(){out.push(2)},0);\
             for(var i=0;i<900;i++){var t={n:i}}",
        )
        .unwrap();
        assert!(it.gc_runs > 0, "gc never ran");
        assert_eq!(disp(&mut it, "out"), "[9,1,2]");
    }

    #[test]
    fn listener_and_dom_wrapper_survive() {
        let mut d = vigia_dom::Dom::new();
        vigia_html::parse("<html><body><div id=a></div></body></html>", &mut d);
        let mut it = Interp::with_cap(700);
        it.set_dom(d);
        // register listener, churn past the threshold, then click: the
        // listener Value and the node wrapper must both be GC roots
        let r = it.run(
            "var hit=0;var a=document.getElementById('a');\
             a.addEventListener('click',function(){hit=7});\
             for(var i=0;i<400;i++){var t={n:i}}\
             a.click();hit",
        );
        assert_eq!(r.unwrap(), Value::Num(7.0));
        assert!(it.gc_runs > 0, "gc never ran");
        // cached wrapper still resolves the same node afterwards
        assert_eq!(disp(&mut it, "a.id"), "a");
    }

    #[test]
    fn freelist_reuses_slots() {
        let mut it = Interp::with_cap(1000);
        it.run("for(var i=0;i<200;i++){var t={x:i}}").unwrap();
        let len = it.heap.objs.len();
        let st = it.gc();
        assert!(st.freed_objs > 100, "loop garbage not freed: {st:?}");
        // fresh allocs refill freed slots instead of growing the arena
        it.run("var a={},b={},c={},d={},e={}").unwrap();
        assert_eq!(it.heap.objs.len(), len);
    }

    #[test]
    fn interned_strings_stay() {
        let mut it = Interp::new();
        let v1 = it.run("'keepme'").unwrap();
        it.gc();
        let v2 = it.run("'keepme'").unwrap();
        assert_eq!(v1, v2); // same interned id, still readable
        if let Value::Str(id) = v2 {
            assert_eq!(it.heap.get_str(id), "keepme");
        } else {
            panic!("{v2:?}");
        }
    }

    #[test]
    fn expr_temps_survive_nested_call() {
        // mk()'s fresh return string sits in a Rust local while ch()
        // churns past the GC threshold; GC must NOT run mid-expression
        // (call_depth > 0), else the temp is swept and concat corrupts.
        // Self-calibrated above install like its sibling below.
        let mut it = Interp::with_cap(1_000_000);
        it.run("0").unwrap();
        it.heap.cap = it.heap.live() + 400;
        it.run(
            "function mk(){return 'a'+'b'}\
             function ch(){for(var i=0;i<300;i++){var t={n:i}}return 'z'}\
             var r = mk() + ch()",
        )
        .unwrap();
        assert_eq!(disp(&mut it, "r"), "abz");
    }

    #[test]
    fn promise_resolver_keeps_promise_alive() {
        // The promise is reachable only through the global resolver's
        // bound "__p" prop across the GC; res() must still settle it.
        let mut it = Interp::new();
        it.run("var res;var got=0;new Promise(function(r){res=r}).then(function(v){got=v})")
            .unwrap();
        it.gc();
        it.run("res(42)").unwrap();
        assert_eq!(it.run("got").unwrap(), Value::Num(42.0));
    }
}
