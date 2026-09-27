//! DOM bindings. `set_dom` installs the page DOM plus `document`, `window`,
//! `navigator`, `location` globals; Obj::Dom wraps a NodeId into it. Property
//! and method dispatch happens here at the access/call site, same pattern as
//! call_str/call_arr for string/array builtins - no property-map entries.
//!
//! Mutations go straight into Interp::dom; callers take the (possibly
//! mutated) DOM back with take_dom() / run_scripts().

use vigia_dom::{Dom, NodeData, NodeId};
use vigia_session::CookieJar;

use crate::ast::{Expr, Stmt};
use crate::eval::{get_prop, nat, set_prop, to_str, truthy};
use crate::{err, Interp, JsError, NetCtx, Obj, PendingSubmit, Value};

/// Same list as vigia-html: these never get a close tag when serializing.
const VOID: &[&str] = &[
    "area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source", "track",
    "wbr",
];

/// First element with `tag` still reachable from the root (detached/orphaned
/// arena nodes are skipped - the arena never frees, so callers must filter).
fn first_tag(dom: &Dom, tag: &str) -> Option<NodeId> {
    (1..dom.nodes.len() as NodeId)
        .find(|&i| dom.tag_name(i) == Some(tag) && is_desc(dom, dom.root(), i))
}

/// First <html>, else the first element under the document root.
fn doc_element(dom: &Dom) -> Option<NodeId> {
    first_tag(dom, "html").or_else(|| {
        dom.children(dom.root())
            .iter()
            .copied()
            .find(|&c| matches!(dom.node(c).data, NodeData::Element(_)))
    })
}

/// Is `n` a strict descendant of `anc`? anc = 0 (document) matches all.
fn is_desc(dom: &Dom, anc: NodeId, n: NodeId) -> bool {
    let mut cur = dom.parent(n);
    while let Some(p) = cur {
        if p == anc {
            return true;
        }
        cur = dom.parent(p);
    }
    false
}

/// Raw descendant text - no whitespace collapsing, so JS string literals
/// inside <script> survive intact (unlike actions::text_content).
fn raw_text(dom: &Dom, id: NodeId, out: &mut String) {
    for &c in dom.children(id) {
        match &dom.node(c).data {
            NodeData::Text(t) => out.push_str(t),
            NodeData::Element(_) => raw_text(dom, c, out),
            _ => {}
        }
    }
}

/// What a page script run leaves behind: the (possibly mutated) DOM,
/// per-script errors, the cookie jar back out of the net context, a
/// pending navigation requested by el.click() on <a href>, and a pending
/// form submit requested by form.submit() or __doPostBack. Following
/// either is the host's call (v1 navigation bridge).
pub struct ScriptsOutcome {
    pub dom: Dom,
    pub errors: Vec<JsError>,
    pub jar: Option<CookieJar>,
    pub pending_nav: Option<String>,
    pub pending_submit: Option<PendingSubmit>,
}

/// Most external <script src> fetches one page run may do (runaway guard).
const MAX_EXT_SCRIPTS: u32 = 32;

/// One runnable <script> in document order: inline source, or an external
/// `src` attr value (raw - resolving needs the page URL out of NetCtx).
enum ScriptSource {
    Inline(String),
    External(String),
}

/// Runnable <script> sources in document order. A `src` attr wins over any
/// inline body, like browsers. Skipped: `type` values that are not
/// javascript-ish (ld+json, templates, ...).
fn collect_scripts(dom: &Dom) -> Vec<ScriptSource> {
    let mut out = Vec::new();
    for id in 1..dom.nodes.len() as NodeId {
        if dom.tag_name(id) != Some("script") {
            continue;
        }
        let ty = dom
            .attr(id, "type")
            .unwrap_or("")
            .trim()
            .to_ascii_lowercase();
        if !matches!(
            ty.as_str(),
            "" | "text/javascript" | "application/javascript" | "module"
        ) {
            continue;
        }
        match dom.attr(id, "src") {
            Some(src) => out.push(ScriptSource::External(src.to_string())),
            None => {
                let mut s = String::new();
                raw_text(dom, id, &mut s);
                out.push(ScriptSource::Inline(s));
            }
        }
    }
    out
}

fn esc_text(t: &str, out: &mut String) {
    for c in t.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            _ => out.push(c),
        }
    }
}

fn esc_attr(v: &str, out: &mut String) {
    for c in v.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '"' => out.push_str("&quot;"),
            _ => out.push(c),
        }
    }
}

/// Serialize one node (element with its subtree, text, comment).
fn serialize_node(dom: &Dom, id: NodeId, out: &mut String) {
    match &dom.node(id).data {
        NodeData::Element(el) => {
            let tag = dom.interner.resolve(el.tag).to_string();
            out.push('<');
            out.push_str(&tag);
            for (k, v) in &el.attrs {
                out.push(' ');
                out.push_str(dom.interner.resolve(*k));
                out.push_str("=\"");
                esc_attr(v, out);
                out.push('"');
            }
            out.push('>');
            if !VOID.contains(&tag.as_str()) {
                for c in dom.children(id).to_vec() {
                    serialize_node(dom, c, out);
                }
                out.push_str("</");
                out.push_str(&tag);
                out.push('>');
            }
        }
        NodeData::Text(t) => esc_text(t, out),
        NodeData::Comment(t) => {
            out.push_str("<!--");
            out.push_str(t);
            out.push_str("-->");
        }
        NodeData::Document => {
            for c in dom.children(id).to_vec() {
                serialize_node(dom, c, out);
            }
        }
    }
}

/// innerHTML getter: children of `id` serialized as HTML.
fn serialize_into(dom: &Dom, id: NodeId, out: &mut String) {
    for c in dom.children(id).to_vec() {
        serialize_node(dom, c, out);
    }
}

impl Interp {
    /// Install `dom` plus the document/window/navigator/location globals.
    /// Call before run(). Re-installing replaces the DOM, the wrappers,
    /// the event listeners and any pending navigation - new page, clean
    /// event state.
    pub fn set_dom(&mut self, dom: Dom) {
        self.dom = Some(dom);
        self.dom_objs.clear();
        self.listeners.clear();
        self.pending_nav = None;
        self.pending_submit = None;
        self.install_builtins();
        // Heap-cap edges skip installs silently, same as install_builtins.
        let (Ok(doc), Ok(ua), Ok(href)) = (
            self.dom_wrap(0),
            self.heap.intern_str("vigia/0.1"),
            self.heap.intern_str(""),
        ) else {
            return;
        };
        self.env_declare(0, "document", doc);
        let (Ok(nav), Ok(loc)) = (
            self.obj_pairs(vec![("userAgent".into(), Value::Str(ua))]),
            self.obj_pairs(vec![("href".into(), Value::Str(href))]),
        ) else {
            return;
        };
        self.env_declare(0, "navigator", Value::Obj(nav));
        self.env_declare(0, "location", Value::Obj(loc));
        if let Ok(w) = self.obj_pairs(vec![
            ("document".into(), doc),
            ("navigator".into(), Value::Obj(nav)),
            ("location".into(), Value::Obj(loc)),
        ]) {
            if let Obj::Ordinary { pairs, .. } = self.heap.obj_mut(w) {
                pairs.push(("window".into(), Value::Obj(w)));
                // `self` (workers/global alias) and `globalThis` match window.
                pairs.push(("self".into(), Value::Obj(w)));
                pairs.push(("globalThis".into(), Value::Obj(w)));
            }
            self.env_declare(0, "window", Value::Obj(w));
            self.env_declare(0, "self", Value::Obj(w));
            self.env_declare(0, "globalThis", Value::Obj(w));
        }
        // WebForms postback helper: __doPostBack('target','arg') sets the
        // hidden fields and submits the first form.
        if let Ok(f) = self.heap.alloc_obj(nat("__doPostBack", n_do_post_back)) {
            self.env_declare(0, "__doPostBack", Value::Obj(f));
        }
    }

    /// Take the installed DOM back (mutated by any scripts that ran).
    pub fn take_dom(&mut self) -> Dom {
        self.dom.take().unwrap_or_default()
    }

    /// Run every runnable <script> in document order over one shared
    /// interp (globals persist across tags, like browsers): inline bodies
    /// eval directly, `src` bodies fetch through `net` first, so a later
    /// script sees an earlier external's globals. A script that throws -
    /// or fails to fetch - does not abort the page: errors collect into
    /// the outcome.
    /// `net` installs the page context for fetch()/click() URL resolution
    /// and external script fetches; its cookie jar is moved in and handed
    /// back in the outcome. With no `net`, external scripts skip silently.
    /// After the scripts, "DOMContentLoaded" fires on document - the
    /// common SPA boot hook.
    pub fn run_scripts(&mut self, dom: Dom, net: Option<NetCtx>) -> ScriptsOutcome {
        let scripts = collect_scripts(&dom);
        self.set_dom(dom);
        if let Some(ctx) = &net {
            let href = ctx.base.to_string();
            let _ = self.set_location_href(&href);
        }
        self.net = net;
        let mut errs = Vec::new();
        let mut fetched = 0;
        for s in &scripts {
            match s {
                ScriptSource::Inline(src) => {
                    if let Err(e) = self.run(src) {
                        errs.push(e);
                    }
                }
                ScriptSource::External(raw) => match self.fetch_script(raw, &mut fetched) {
                    Ok(Some(body)) => {
                        if let Err(e) = self.run(&body) {
                            errs.push(e);
                        }
                    }
                    // no net ctx installed: skip silently
                    Ok(None) => {}
                    Err(e) => errs.push(e),
                },
            }
        }
        if let Err(e) = self.fire(0, "DOMContentLoaded") {
            // an uncaught listener `throw` arrives as a raw value - render
            // it now, there's no script frame left to catch it
            let e = self.bound_err(e);
            errs.push(e);
        }
        ScriptsOutcome {
            dom: self.take_dom(),
            errors: errs,
            jar: self.net.take().map(|c| c.jar),
            pending_nav: self.pending_nav.take(),
            pending_submit: self.pending_submit.take(),
        }
    }

    /// Fetch an external <script src> body through the page net ctx.
    /// Ok(None) = skipped silently (no net ctx). Err = rejected or the
    /// fetch failed; the caller records it in the outcome.
    fn fetch_script(&mut self, raw: &str, fetched: &mut u32) -> Result<Option<String>, JsError> {
        let Some(ctx) = self.net.as_mut() else {
            return Ok(None);
        };
        let url = ctx
            .base
            .join(raw)
            .map_err(|e| err(format!("script src {raw}: {e}")))?;
        if !matches!(url.scheme.as_str(), "http" | "https") {
            return Err(err(format!("script src {raw}: {} scheme", url.scheme)));
        }
        if *fetched >= MAX_EXT_SCRIPTS {
            return Err(err(format!(
                "script src {raw}: over the {MAX_EXT_SCRIPTS}-script cap"
            )));
        }
        *fetched += 1;
        let res = vigia_net::fetch(&url.to_string(), &mut ctx.jar)
            .map_err(|e| err(format!("script src {url}: {e}")))?;
        Ok(Some(res.text()))
    }

    pub(crate) fn dom_ref(&self) -> Result<&Dom, JsError> {
        self.dom.as_ref().ok_or_else(|| err("no DOM installed"))
    }

    fn dom_mut(&mut self) -> Result<&mut Dom, JsError> {
        self.dom.as_mut().ok_or_else(|| err("no DOM installed"))
    }

    /// NodeId if `v` is a DOM node handle.
    pub(crate) fn as_node(&self, v: Value) -> Option<NodeId> {
        if let Value::Obj(id) = v {
            if let Obj::Dom(n) = self.heap.obj(id) {
                return Some(*n);
            }
        }
        None
    }

    pub(crate) fn as_style(&self, v: Value) -> Option<NodeId> {
        if let Value::Obj(id) = v {
            if let Obj::Style { node } = self.heap.obj(id) {
                return Some(*node);
            }
        }
        None
    }

    /// `style="a: b; c: d"` <-> declaration list (names lowercased).
    fn parse_style(attr: &str) -> Vec<(String, String)> {
        attr.split(';')
            .filter_map(|d| {
                let (k, v) = d.split_once(':')?;
                let k = k.trim().to_lowercase();
                if k.is_empty() {
                    return None;
                }
                Some((k, v.trim().to_string()))
            })
            .collect()
    }

    fn render_style(decls: &[(String, String)]) -> String {
        decls
            .iter()
            .map(|(k, v)| format!("{k}: {v}"))
            .collect::<Vec<_>>()
            .join("; ")
    }

    /// Live read of one style property (or cssText/length).
    pub(crate) fn style_get(&mut self, node: NodeId, key: &str) -> Result<Value, JsError> {
        let attr = self
            .dom_ref()?
            .attr(node, "style")
            .unwrap_or("")
            .to_string();
        if key == "cssText" {
            return self.str_val(attr);
        }
        let decls = Self::parse_style(&attr);
        if key == "length" {
            return Ok(Value::Num(decls.len() as f64));
        }
        let key = key.to_lowercase();
        match decls.iter().find(|(k, _)| *k == key) {
            Some((_, v)) => self.str_val(v.clone()),
            None => Ok(Value::Undef),
        }
    }

    /// Live write: upsert (empty value removes), cssText replaces all.
    pub(crate) fn style_set(&mut self, node: NodeId, key: &str, val: Value) -> Result<(), JsError> {
        if key == "length" {
            return Ok(()); // readonly in real JS; sloppy no-op
        }
        if key == "cssText" {
            let t = to_str(&self.heap, val);
            self.dom_mut()?.set_attr(node, "style", &t);
            return Ok(());
        }
        let attr = self
            .dom_ref()?
            .attr(node, "style")
            .unwrap_or("")
            .to_string();
        let mut decls = Self::parse_style(&attr);
        let key = key.to_lowercase();
        let t = to_str(&self.heap, val);
        if t.trim().is_empty() {
            decls.retain(|(k, _)| *k != key);
        } else {
            match decls.iter_mut().find(|(k, _)| *k == key) {
                Some((_, v)) => *v = t.trim().to_string(),
                None => decls.push((key, t.trim().to_string())),
            }
        }
        self.dom_mut()?
            .set_attr(node, "style", &Self::render_style(&decls));
        Ok(())
    }

    /// Wrap a node, reusing the cached wrapper so === identity holds.
    fn dom_wrap(&mut self, n: NodeId) -> Result<Value, JsError> {
        if let Some(&o) = self.dom_objs.get(&n) {
            return Ok(Value::Obj(o));
        }
        let o = self.heap.alloc_obj(Obj::Dom(n))?;
        self.dom_objs.insert(n, o);
        Ok(Value::Obj(o))
    }

    fn opt_node(&mut self, n: Option<NodeId>) -> Result<Value, JsError> {
        match n {
            Some(n) => self.dom_wrap(n),
            None => Ok(Value::Null),
        }
    }

    fn str_val(&mut self, s: String) -> Result<Value, JsError> {
        Ok(Value::Str(self.heap.alloc_str(s)?))
    }

    fn attr_val(&mut self, id: NodeId, name: &str) -> Result<Value, JsError> {
        let s = self.dom_ref()?.attr(id, name).unwrap_or("").to_string();
        self.str_val(s)
    }

    fn node_arr(&mut self, ids: Vec<NodeId>) -> Result<Value, JsError> {
        let mut vals = Vec::with_capacity(ids.len());
        for n in ids {
            vals.push(self.dom_wrap(n)?);
        }
        Ok(Value::Obj(self.arr_obj(vals)?))
    }

    // ---- events --------------------------------------------------------

    /// Bubble-path dispatch, simplified DOM Events: at each node on the
    /// target->document path, the inline `on<ty>` attr handler runs first,
    /// then listeners registered for `ty`. No capture phase. currentTarget
    /// updates per node; a handler error aborts dispatch.
    pub(crate) fn dispatch(
        &mut self,
        target: NodeId,
        ty: &str,
        ev: Value,
    ) -> Result<Value, JsError> {
        let mut path = vec![target];
        {
            let dom = self.dom_ref()?;
            let mut cur = dom.parent(target);
            while let Some(p) = cur {
                path.push(p);
                cur = dom.parent(p);
            }
        }
        for &n in &path {
            // stopPropagation stops later nodes; same-node handlers still run
            if self.event_stopped(ev) {
                break;
            }
            let this = self.dom_wrap(n)?;
            set_prop(&mut self.heap, ev, "currentTarget", this)?;
            if let Some(code) = self.inline_handler(n, ty) {
                self.run_inline(n, ty, &code, ev)?;
            }
            // snapshot: listeners added/removed mid-dispatch shift nothing here
            let fns: Vec<Value> = self
                .listeners
                .get(&n)
                .map(|v| v.iter().filter(|(t, _)| t == ty).map(|(_, f)| *f).collect())
                .unwrap_or_default();
            for f in fns {
                self.call_value(f, this, &[ev], None)?;
            }
        }
        set_prop(&mut self.heap, ev, "currentTarget", Value::Null)?;
        Ok(ev)
    }

    /// Inline `on<ty>` attr source for node `n`, matched case-insensitively
    /// (HTML source may write onClick); Document/Text nodes have none.
    fn inline_handler(&self, n: NodeId, ty: &str) -> Option<String> {
        let want = format!("on{ty}");
        let dom = self.dom.as_ref()?;
        let NodeData::Element(el) = &dom.node(n).data else {
            return None;
        };
        el.attrs
            .iter()
            .find(|(k, _)| dom.interner.resolve(*k).eq_ignore_ascii_case(&want))
            .map(|(_, v)| v.clone())
    }

    /// Compile an inline `on*` attr and call it: `this` = the element,
    /// `event` = the event object. The attr source becomes a function body.
    fn run_inline(&mut self, n: NodeId, ty: &str, code: &str, ev: Value) -> Result<(), JsError> {
        let src = format!("(function(event){{{code}}})");
        let stmts = crate::parse(&src).map_err(|e| err(format!("on{ty}: {e}")))?;
        let Some(Stmt::Expr(Expr::Func(def))) = stmts.into_iter().next() else {
            return Err(err(format!("on{ty}: bad handler")));
        };
        let f = Value::Obj(self.func_obj(def, 0)?);
        let this = self.dom_wrap(n)?;
        self.call_value(f, this, &[ev], None)?;
        Ok(())
    }

    /// Fresh event object of type `ty` targeted at `target`.
    fn new_event(&mut self, ty: &str, target: NodeId) -> Result<Value, JsError> {
        let ty = Value::Str(self.heap.alloc_str(ty.to_string())?);
        let tgt = self.dom_wrap(target)?;
        let pd = self
            .heap
            .alloc_obj(nat("preventDefault", n_event_prevent_default))?;
        let sp = self
            .heap
            .alloc_obj(nat("stopPropagation", n_event_stop_propagation))?;
        Ok(Value::Obj(self.obj_pairs(vec![
            ("type".into(), ty),
            ("target".into(), tgt),
            ("currentTarget".into(), Value::Null),
            ("defaultPrevented".into(), Value::Bool(false)),
            ("preventDefault".into(), Value::Obj(pd)),
            ("stopPropagation".into(), Value::Obj(sp)),
        ])?))
    }

    /// A user-built object passed to dispatchEvent: overwrite `target` and
    /// fill any missing standard props so a bare `{type:'x'}` works fully.
    fn normalize_event(&mut self, ev: Value, target: NodeId) -> Result<(), JsError> {
        let tgt = self.dom_wrap(target)?;
        set_prop(&mut self.heap, ev, "target", tgt)?;
        let pd = self
            .heap
            .alloc_obj(nat("preventDefault", n_event_prevent_default))?;
        let sp = self
            .heap
            .alloc_obj(nat("stopPropagation", n_event_stop_propagation))?;
        for (k, v) in [
            ("currentTarget", Value::Null),
            ("defaultPrevented", Value::Bool(false)),
            ("preventDefault", Value::Obj(pd)),
            ("stopPropagation", Value::Obj(sp)),
        ] {
            if matches!(get_prop(&self.heap, &self.protos, ev, k)?, Value::Undef) {
                set_prop(&mut self.heap, ev, k, v)?;
            }
        }
        Ok(())
    }

    /// Dispatch a fresh `ty` event at `target`, then drain the work queues:
    /// microtasks and timers a handler queued complete before fire()
    /// returns (this flushes early when the event was dispatched mid-script,
    /// unlike browsers which wait for the stack to unwind). Returns the
    /// event object; a dispatch error wins over drain errors.
    fn fire(&mut self, target: NodeId, ty: &str) -> Result<Value, JsError> {
        let ev = self.new_event(ty, target)?;
        // ev must outlive dispatch + drain; drain's GC can't see it as a
        // Rust local, so root it for the call's duration.
        self.call_vals.push(ev);
        let r = self.dispatch(target, ty, ev);
        let mut errs = Vec::new();
        self.drain(&mut errs);
        self.call_vals.pop();
        match r {
            Err(e) => Err(e),
            Ok(v) => match errs.into_iter().next() {
                Some(e) => Err(e),
                None => Ok(v),
            },
        }
    }

    fn event_stopped(&self, ev: Value) -> bool {
        matches!(
            get_prop(&self.heap, &self.protos, ev, "__stopped"),
            Ok(Value::Bool(true))
        )
    }

    fn event_prevented(&self, ev: Value) -> bool {
        matches!(
            get_prop(&self.heap, &self.protos, ev, "defaultPrevented"),
            Ok(Value::Bool(true))
        )
    }

    /// Reflect a navigation into the JS-visible location.href.
    fn set_location_href(&mut self, href: &str) -> Result<(), JsError> {
        if let Some(loc) = self.env_get(0, "location") {
            let s = self.heap.alloc_str(href.to_string())?;
            set_prop(&mut self.heap, loc, "href", Value::Str(s))?;
        }
        Ok(())
    }

    /// Event methods shared by elements and document (listeners live on
    /// node 0 for the latter). Returns None when `name` isn't one.
    fn event_method(
        &mut self,
        id: NodeId,
        name: &str,
        args: &[Value],
    ) -> Result<Option<Value>, JsError> {
        let arg = |i: usize| args.get(i).copied().unwrap_or(Value::Undef);
        Ok(Some(match name {
            "addEventListener" => {
                let ty = to_str(&self.heap, arg(0));
                let f = arg(1);
                let ok = matches!(f, Value::Obj(o)
                    if matches!(self.heap.obj(o), Obj::Func { .. } | Obj::Native { .. }));
                if !ok {
                    return Err(err("addEventListener needs a function"));
                }
                // dedupe on (type, same handler obj), like the standard
                let v = self.listeners.entry(id).or_default();
                if !v.iter().any(|(t, g)| *t == ty && *g == f) {
                    v.push((ty, f));
                }
                Value::Undef
            }
            "removeEventListener" => {
                let ty = to_str(&self.heap, arg(0));
                let f = arg(1);
                if let Some(v) = self.listeners.get_mut(&id) {
                    if let Some(i) = v.iter().position(|(t, g)| *t == ty && *g == f) {
                        v.remove(i);
                    }
                }
                Value::Undef
            }
            "dispatchEvent" => {
                let ev = arg(0);
                let ty = match ev {
                    Value::Obj(o) if matches!(self.heap.obj(o), Obj::Ordinary { .. }) => {
                        match get_prop(&self.heap, &self.protos, ev, "type")? {
                            Value::Str(s) => self.heap.get_str(s).to_string(),
                            _ => return Err(err("dispatchEvent: event needs a type")),
                        }
                    }
                    _ => return Err(err("dispatchEvent needs an event object")),
                };
                self.normalize_event(ev, id)?;
                let ev = self.dispatch(id, &ty, ev)?;
                Value::Bool(!self.event_prevented(ev))
            }
            "click" => {
                let ev = self.fire(id, "click")?;
                // Default action for <a href>: real navigation would need a
                // fetch + dom replace mid-eval, so we record pending_nav for
                // the host and reflect it on location.href.
                if !self.event_prevented(ev) {
                    let href = match self.dom_ref() {
                        Ok(d) if d.tag_name(id) == Some("a") => {
                            d.attr(id, "href").map(str::to_string)
                        }
                        _ => None,
                    };
                    if let Some(href) = href {
                        // `javascript:` links run their body as page code,
                        // like browsers (WebForms postbacks live here).
                        let trimmed = href.trim_start();
                        let js_body = if trimmed.len() >= 11
                            && trimmed[..11].eq_ignore_ascii_case("javascript:")
                        {
                            Some(&trimmed[11..])
                        } else {
                            None
                        };
                        if let Some(code) = js_body {
                            let code = code.trim_start_matches(|c| {
                                c == ' ' || c == '\t' || c == '\n' || c == '\r'
                            });
                            self.run(code)?;
                        } else {
                            match &self.net {
                                Some(ctx) => {
                                    let u = ctx
                                        .base
                                        .join(&href)
                                        .map_err(|e| err(format!("click: {e}")))?;
                                    // javascript:/mailto: etc aren't navigable
                                    if matches!(u.scheme.as_str(), "http" | "https") {
                                        let s = u.to_string();
                                        self.set_location_href(&s)?;
                                        self.pending_nav = Some(s);
                                    }
                                }
                                // no base: record the raw href for the host
                                None => {
                                    self.set_location_href(&href)?;
                                    self.pending_nav = Some(href);
                                }
                            }
                        }
                    }
                }
                Value::Undef
            }
            "focus" | "blur" => {
                self.fire(id, name)?;
                Value::Undef
            }
            _ => return Ok(None),
        }))
    }

    /// CSS query scoped to the subtree rooted at `id` (id 0 = whole doc).
    fn select(&mut self, id: NodeId, sel: Value) -> Result<Vec<NodeId>, JsError> {
        let sel = to_str(&self.heap, sel);
        let dom = self.dom_ref()?;
        let hits = vigia_css::query(dom, &sel).map_err(|e| err(e.to_string()))?;
        Ok(hits.into_iter().filter(|&n| is_desc(dom, id, n)).collect())
    }

    /// Property read on a DOM node handle.
    pub(crate) fn dom_get(&mut self, id: NodeId, key: &str) -> Result<Value, JsError> {
        match key {
            "nodeType" => {
                let n = match self.dom_ref()?.node(id).data {
                    NodeData::Document => 9.0,
                    NodeData::Element(_) => 1.0,
                    NodeData::Text(_) => 3.0,
                    NodeData::Comment(_) => 8.0,
                };
                return Ok(Value::Num(n));
            }
            "parentElement" => {
                let p = {
                    let dom = self.dom_ref()?;
                    dom.parent(id)
                        .filter(|&p| matches!(dom.node(p).data, NodeData::Element(_)))
                };
                return self.opt_node(p);
            }
            "children" | "childNodes" => {
                let all = key == "childNodes";
                let ids: Vec<NodeId> = {
                    let dom = self.dom_ref()?;
                    dom.children(id)
                        .iter()
                        .copied()
                        .filter(|&c| all || matches!(dom.node(c).data, NodeData::Element(_)))
                        .collect()
                };
                return self.node_arr(ids);
            }
            _ => {}
        }
        match self.dom_ref()?.node(id).data {
            NodeData::Document => match key {
                "documentElement" => {
                    let n = doc_element(self.dom_ref()?);
                    self.opt_node(n)
                }
                "body" => {
                    let n = {
                        let d = self.dom_ref()?;
                        first_tag(d, "body").or_else(|| doc_element(d))
                    };
                    self.opt_node(n)
                }
                "title" => {
                    let t = {
                        let d = self.dom_ref()?;
                        first_tag(d, "title")
                            .map(|n| vigia_actions::text_content(d, n))
                            .unwrap_or_default()
                    };
                    self.str_val(t)
                }
                "textContent" => Ok(Value::Null),
                // Snapshot, not live: forms present at access time.
                "forms" => {
                    let ids: Vec<NodeId> = {
                        let d = self.dom_ref()?;
                        (1..d.nodes.len() as NodeId)
                            .filter(|&i| {
                                matches!(d.node(i).data, NodeData::Element(_))
                                    && is_desc(d, 0, i)
                                    && d.tag_name(i) == Some("form")
                            })
                            .collect()
                    };
                    self.node_arr(ids)
                }
                _ => Ok(Value::Undef),
            },
            NodeData::Text(_) | NodeData::Comment(_) => match key {
                "textContent" | "nodeValue" => {
                    let t = match &self.dom_ref()?.node(id).data {
                        NodeData::Text(t) | NodeData::Comment(t) => t.clone(),
                        _ => String::new(),
                    };
                    self.str_val(t)
                }
                _ => Ok(Value::Undef),
            },
            NodeData::Element(_) => match key {
                "textContent" => {
                    let t = vigia_actions::text_content(self.dom_ref()?, id);
                    self.str_val(t)
                }
                "innerHTML" => {
                    let mut s = String::new();
                    serialize_into(self.dom_ref()?, id, &mut s);
                    self.str_val(s)
                }
                "outerHTML" => {
                    let mut s = String::new();
                    serialize_node(self.dom_ref()?, id, &mut s);
                    self.str_val(s)
                }
                "tagName" => {
                    let t = self
                        .dom_ref()?
                        .tag_name(id)
                        .unwrap_or("")
                        .to_ascii_uppercase();
                    self.str_val(t)
                }
                "id" => self.attr_val(id, "id"),
                "className" => self.attr_val(id, "class"),
                "value" => self.attr_val(id, "value"),
                "href" => self.attr_val(id, "href"),
                "style" => {
                    let s = self.heap.alloc_obj(Obj::Style { node: id })?;
                    Ok(Value::Obj(s))
                }
                "checked" => Ok(Value::Bool(self.dom_ref()?.attr(id, "checked").is_some())),
                "disabled" => Ok(Value::Bool(self.dom_ref()?.attr(id, "disabled").is_some())),
                _ => Ok(Value::Undef),
            },
        }
    }

    /// Property write on a DOM node handle. Unknown keys are ignored (no
    /// expando map on node handles).
    pub(crate) fn dom_set(&mut self, id: NodeId, key: &str, v: Value) -> Result<(), JsError> {
        let data = &self.dom_ref()?.node(id).data;
        if matches!(data, NodeData::Document) {
            if key == "title" {
                let t = to_str(&self.heap, v);
                let dom = self.dom_mut()?;
                match first_tag(dom, "title") {
                    Some(te) => {
                        dom.clear_children(te);
                        dom.text(te, &t);
                    }
                    None => {
                        let parent = first_tag(dom, "head")
                            .or_else(|| first_tag(dom, "html"))
                            .unwrap_or_else(|| dom.root());
                        let te = dom.element(parent, "title", vec![]);
                        dom.text(te, &t);
                    }
                }
            }
            return Ok(());
        }
        if matches!(data, NodeData::Text(_) | NodeData::Comment(_)) {
            if matches!(key, "textContent" | "nodeValue") {
                let t = to_str(&self.heap, v);
                let node = &mut self.dom_mut()?.nodes[id as usize];
                node.data = if matches!(node.data, NodeData::Comment(_)) {
                    NodeData::Comment(t)
                } else {
                    NodeData::Text(t)
                };
            }
            return Ok(());
        }
        match key {
            "textContent" => {
                let t = to_str(&self.heap, v);
                let dom = self.dom_mut()?;
                dom.clear_children(id);
                dom.text(id, &t);
            }
            "innerHTML" => {
                let t = to_str(&self.heap, v);
                // Parse under a <div> wrapper in a scratch Dom, then adopt.
                let mut scratch = Dom::new();
                vigia_html::parse(&format!("<div>{t}</div>"), &mut scratch);
                let wrap = scratch.children(scratch.root()).first().copied();
                let dom = self.dom_mut()?;
                dom.clear_children(id);
                if let Some(w) = wrap {
                    dom.adopt_children(&scratch, w, id);
                }
            }
            "id" | "className" | "value" | "href" => {
                let name = if key == "className" { "class" } else { key };
                let t = to_str(&self.heap, v);
                self.dom_mut()?.set_attr(id, name, &t);
            }
            "checked" | "disabled" => {
                let on = truthy(&self.heap, v);
                let dom = self.dom_mut()?;
                if on {
                    dom.set_attr(id, key, key);
                } else {
                    dom.remove_attr(id, key);
                }
            }
            _ => {}
        }
        Ok(())
    }

    /// Capture a form submit at submit() time: current fields plus the
    /// action resolved against the page base (or the raw action with no
    /// net context - the host reports the failure). The host performs
    /// the HTTP, like pending_nav.
    pub(crate) fn record_submit(&mut self, form: NodeId) -> Result<(), JsError> {
        let (method, action) = {
            let dom = self.dom_ref()?;
            if dom.tag_name(form) != Some("form") {
                return Err(err("submit() needs a form"));
            }
            (
                dom.attr(form, "method")
                    .unwrap_or("get")
                    .to_ascii_lowercase(),
                dom.attr(form, "action").unwrap_or("").to_string(),
            )
        };
        let fields = {
            let dom = self.dom_ref()?;
            vigia_actions::form_fields(dom, form)
        };
        let url = match &self.net {
            Some(ctx) => ctx
                .base
                .join(action.trim())
                .map_err(|e| err(format!("submit: {e}")))?
                .to_string(),
            None => action,
        };
        self.pending_submit = Some(PendingSubmit {
            method,
            url,
            fields,
        });
        Ok(())
    }

    /// `n` must not be `id` itself or one of its ancestors.
    fn check_cycle(&self, id: NodeId, n: NodeId, op: &str) -> Result<(), JsError> {
        let dom = self.dom_ref()?;
        let mut cur = Some(id);
        while let Some(p) = cur {
            if p == n {
                return Err(err(format!("cyclic {op}")));
            }
            cur = dom.parent(p);
        }
        Ok(())
    }

    /// Method call on a DOM node handle (the `o.m()` call-site dispatch).
    pub(crate) fn call_dom(
        &mut self,
        id: NodeId,
        name: &str,
        env: u32,
        arg_es: &[Expr],
    ) -> Result<Value, JsError> {
        let args = self.eval_args(env, arg_es)?;
        let arg = |i: usize| args.get(i).copied().unwrap_or(Value::Undef);
        // event methods work on any node, Document (id 0) included
        if let Some(v) = self.event_method(id, name, &args)? {
            return Ok(v);
        }
        if matches!(self.dom_ref()?.node(id).data, NodeData::Document) {
            return match name {
                "getElementById" => {
                    let want = to_str(&self.heap, arg(0));
                    let hit = {
                        let d = self.dom_ref()?;
                        (1..d.nodes.len() as NodeId).find(|&i| {
                            matches!(d.node(i).data, NodeData::Element(_))
                                && is_desc(d, 0, i)
                                && d.attr(i, "id") == Some(want.as_str())
                        })
                    };
                    self.opt_node(hit)
                }
                "getElementsByTagName" => {
                    let want = to_str(&self.heap, arg(0)).to_ascii_lowercase();
                    let ids: Vec<NodeId> = {
                        let d = self.dom_ref()?;
                        (1..d.nodes.len() as NodeId)
                            .filter(|&i| {
                                matches!(d.node(i).data, NodeData::Element(_))
                                    && is_desc(d, 0, i)
                                    && (want == "*" || d.tag_name(i) == Some(want.as_str()))
                            })
                            .collect()
                    };
                    self.node_arr(ids)
                }
                "createElement" => {
                    let tag = to_str(&self.heap, arg(0)).to_ascii_lowercase();
                    if tag.is_empty() {
                        return Err(err("createElement needs a tag"));
                    }
                    let n = {
                        let d = self.dom_mut()?;
                        let root = d.root();
                        let n = d.element(root, &tag, vec![]);
                        d.detach(n);
                        n
                    };
                    self.dom_wrap(n)
                }
                "querySelector" => {
                    let hits = self.select(id, arg(0))?;
                    self.opt_node(hits.into_iter().next())
                }
                "querySelectorAll" => {
                    let hits = self.select(id, arg(0))?;
                    self.node_arr(hits)
                }
                _ => Err(err(format!("{name} is not a function"))),
            };
        }
        match name {
            "getAttribute" => {
                let n = to_str(&self.heap, arg(0));
                match self.dom_ref()?.attr(id, &n).map(str::to_string) {
                    Some(v) => self.str_val(v),
                    None => Ok(Value::Null),
                }
            }
            "hasAttribute" => {
                let n = to_str(&self.heap, arg(0));
                Ok(Value::Bool(self.dom_ref()?.attr(id, &n).is_some()))
            }
            "setAttribute" => {
                let n = to_str(&self.heap, arg(0));
                let v = to_str(&self.heap, arg(1));
                self.dom_mut()?.set_attr(id, &n, &v);
                Ok(Value::Undef)
            }
            "removeAttribute" => {
                let n = to_str(&self.heap, arg(0));
                self.dom_mut()?.remove_attr(id, &n);
                Ok(Value::Undef)
            }
            "appendChild" => {
                let a = arg(0);
                let Some(n) = self.as_node(a) else {
                    return Err(err("appendChild needs a node"));
                };
                self.check_cycle(id, n, "appendChild")?;
                let dom = self.dom_mut()?;
                dom.detach(n);
                dom.append_child_node(id, n);
                Ok(a)
            }
            "insertBefore" => {
                let a = arg(0);
                let Some(n) = self.as_node(a) else {
                    return Err(err("insertBefore needs a node"));
                };
                self.check_cycle(id, n, "insertBefore")?;
                let before = match arg(1) {
                    Value::Null | Value::Undef => None,
                    b => {
                        let Some(m) = self.as_node(b) else {
                            return Err(err("insertBefore needs a node or null"));
                        };
                        if self.dom_ref()?.parent(m) != Some(id) {
                            return Err(err("insertBefore: not a child"));
                        }
                        Some(m)
                    }
                };
                let dom = self.dom_mut()?;
                dom.detach(n);
                dom.insert_before_node(id, n, before);
                Ok(a)
            }
            "removeChild" => {
                let a = arg(0);
                let Some(n) = self.as_node(a) else {
                    return Err(err("removeChild needs a node"));
                };
                if self.dom_ref()?.parent(n) != Some(id) {
                    return Err(err("removeChild: not a child"));
                }
                self.dom_mut()?.detach(n);
                Ok(a)
            }
            "remove" => {
                self.dom_mut()?.detach(id);
                Ok(Value::Undef)
            }
            "submit" => {
                // Only <form> submits; anything else falls to "not a
                // function" below, like browsers (only forms have it).
                if self.dom_ref()?.tag_name(id) != Some("form") {
                    return Err(err("submit is not a function"));
                }
                self.record_submit(id)?;
                Ok(Value::Undef)
            }
            "querySelector" => {
                let hits = self.select(id, arg(0))?;
                self.opt_node(hits.into_iter().next())
            }
            "querySelectorAll" => {
                let hits = self.select(id, arg(0))?;
                self.node_arr(hits)
            }
            _ => Err(err(format!("{name} is not a function"))),
        }
    }
}

// ---- event natives ------------------------------------------------------

fn n_event_prevent_default(
    it: &mut Interp,
    this: Value,
    _args: &[Value],
) -> Result<Value, JsError> {
    set_prop(&mut it.heap, this, "defaultPrevented", Value::Bool(true)).map(|()| Value::Undef)
}

fn n_event_stop_propagation(
    it: &mut Interp,
    this: Value,
    _args: &[Value],
) -> Result<Value, JsError> {
    // internal flag the dispatch loop checks between nodes
    set_prop(&mut it.heap, this, "__stopped", Value::Bool(true)).map(|()| Value::Undef)
}

/// WebForms `__doPostBack(eventTarget, eventArgument)`: stash both into
/// the first form's hidden fields (creating them when absent) and record
/// the submit. The host performs the HTTP.
fn n_do_post_back(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let target = to_str(&it.heap, args.first().copied().unwrap_or(Value::Undef));
    let argument = to_str(&it.heap, args.get(1).copied().unwrap_or(Value::Undef));
    let form = {
        let dom = it.dom_ref()?;
        (1..dom.nodes.len() as NodeId)
            .find(|&i| {
                matches!(dom.node(i).data, NodeData::Element(_))
                    && is_desc(dom, 0, i)
                    && dom.tag_name(i) == Some("form")
            })
            .ok_or_else(|| err("__doPostBack: no form"))?
    };
    for (name, val) in [("__EVENTTARGET", target), ("__EVENTARGUMENT", argument)] {
        let hit = {
            let dom = it.dom_ref()?;
            (1..dom.nodes.len() as NodeId).find(|&i| {
                is_desc(dom, form, i)
                    && dom.tag_name(i) == Some("input")
                    && dom.attr(i, "name") == Some(name)
            })
        };
        match hit {
            Some(n) => it.dom_mut()?.set_attr(n, "value", &val),
            None => {
                it.dom_mut()?.element(
                    form,
                    "input",
                    vec![
                        ("type".into(), "hidden".into()),
                        ("name".into(), name.into()),
                        ("value".into(), val),
                    ],
                );
            }
        }
    }
    it.record_submit(form)?;
    Ok(Value::Undef)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn interp(html: &str) -> Interp {
        let mut d = Dom::new();
        vigia_html::parse(html, &mut d);
        let mut it = Interp::new();
        it.set_dom(d);
        it
    }

    /// Completion value, inspected (strings bare, objects JSON).
    fn ev(it: &mut Interp, src: &str) -> String {
        let v = it.run(src).unwrap();
        it.inspect(v)
    }

    fn errmsg(it: &mut Interp, src: &str) -> String {
        it.run(src).unwrap_err().to_string()
    }

    const PAGE: &str = r#"<html><head><title>old</title></head><body>
        <div id=a class="x y"><p>one</p><p>two <b>bold</b></p></div>
        <input id=i value="v1" checked>
        <a id=l href="/next">go</a>
        </body></html>"#;

    #[test]
    fn globals() {
        let mut it = interp(PAGE);
        assert_eq!(ev(&mut it, "window.document === document"), "true");
        assert_eq!(ev(&mut it, "document.nodeType"), "9");
        assert_eq!(ev(&mut it, "navigator.userAgent"), "vigia/0.1");
        assert_eq!(ev(&mut it, "typeof location.href"), "string");
        assert_eq!(ev(&mut it, "document.body === document.body"), "true");
        assert_eq!(ev(&mut it, "document.body.nodeType"), "1");
        assert_eq!(ev(&mut it, "document.body.tagName"), "BODY");
        assert_eq!(ev(&mut it, "document.documentElement.tagName"), "HTML");
    }

    #[test]
    fn lookup() {
        let mut it = interp(PAGE);
        assert_eq!(ev(&mut it, "document.getElementById('a').id"), "a");
        assert_eq!(ev(&mut it, "document.getElementById('nope')"), "null");
        assert_eq!(
            ev(&mut it, "document.querySelector('#a p').textContent"),
            "one"
        );
        assert_eq!(ev(&mut it, "document.querySelectorAll('#a p').length"), "2");
        assert_eq!(
            ev(&mut it, "document.querySelectorAll('.nope').length"),
            "0"
        );
        assert_eq!(
            ev(&mut it, "document.getElementsByTagName('input').length"),
            "1"
        );
        assert_eq!(
            ev(&mut it, "document.getElementsByTagName('*').length > 3"),
            "true"
        );
        // element-scoped query sees only its own subtree
        assert_eq!(
            ev(
                &mut it,
                "document.getElementById('a').querySelectorAll('p').length"
            ),
            "2"
        );
        assert_eq!(
            ev(
                &mut it,
                "document.getElementById('a').querySelectorAll('input').length"
            ),
            "0"
        );
        assert!(errmsg(&mut it, "document.querySelector('[')").contains("css"));
    }

    #[test]
    fn text_content() {
        let mut it = interp(PAGE);
        assert_eq!(
            ev(&mut it, "document.getElementById('a').textContent"),
            "one two bold"
        );
        it.run("document.getElementById('a').textContent = 'flat'")
            .unwrap();
        let dom = it.take_dom();
        let a = vigia_css::query(&dom, "#a").unwrap()[0];
        assert_eq!(vigia_actions::text_content(&dom, a), "flat");
        assert_eq!(dom.children(a).len(), 1);
    }

    #[test]
    fn inner_html() {
        let mut it = interp("<body><div id=a><p>x &amp; y</p><br></div></body>");
        assert_eq!(
            ev(&mut it, "document.getElementById('a').innerHTML"),
            "<p>x &amp; y</p><br>"
        );
        it.run("document.body.innerHTML = '<h1>INJ</h1><p>t</p>'")
            .unwrap();
        let dom = it.take_dom();
        let h1 = vigia_css::query(&dom, "h1").unwrap();
        assert_eq!(vigia_actions::text_content(&dom, h1[0]), "INJ");
        assert_eq!(vigia_css::query(&dom, "body > p").unwrap().len(), 1);
    }

    #[test]
    fn attributes() {
        let mut it = interp(PAGE);
        assert_eq!(
            ev(
                &mut it,
                "var e=document.getElementById('i');e.getAttribute('value')"
            ),
            "v1"
        );
        assert_eq!(
            ev(
                &mut it,
                "document.getElementById('i').hasAttribute('checked')"
            ),
            "true"
        );
        assert_eq!(
            ev(&mut it, "document.getElementById('i').hasAttribute('nope')"),
            "false"
        );
        assert_eq!(
            ev(&mut it, "document.getElementById('i').getAttribute('nope')"),
            "null"
        );
        it.run("var e=document.getElementById('i');e.setAttribute('data-k','7');e.removeAttribute('value')").unwrap();
        let dom = it.take_dom();
        let i = vigia_css::query(&dom, "#i").unwrap()[0];
        assert_eq!(dom.attr(i, "data-k"), Some("7"));
        assert_eq!(dom.attr(i, "value"), None);
    }

    #[test]
    fn element_props() {
        let mut it = interp(PAGE);
        assert_eq!(ev(&mut it, "document.getElementById('a').className"), "x y");
        assert_eq!(ev(&mut it, "document.getElementById('l').href"), "/next");
        assert_eq!(ev(&mut it, "document.getElementById('i').checked"), "true");
        assert_eq!(
            ev(&mut it, "document.getElementById('i').disabled"),
            "false"
        );
        it.run(
            "var e=document.getElementById('i');e.id='j';e.value='v2';e.checked=false;e.disabled=true",
        )
        .unwrap();
        let dom = it.take_dom();
        let i = vigia_css::query(&dom, "#j").unwrap()[0];
        assert_eq!(dom.attr(i, "value"), Some("v2"));
        assert_eq!(dom.attr(i, "checked"), None);
        assert_eq!(dom.attr(i, "disabled"), Some("disabled"));
    }

    #[test]
    fn tree_walk() {
        let mut it = interp(PAGE);
        assert_eq!(
            ev(&mut it, "document.getElementById('a').children.length"),
            "2"
        );
        assert_eq!(
            ev(&mut it, "document.getElementById('a').children[0].tagName"),
            "P"
        );
        // childNodes on <p>two <b>bold</b></p> mixes text + element
        assert_eq!(
            ev(
                &mut it,
                "document.querySelectorAll('#a p')[1].childNodes.length"
            ),
            "2"
        );
        assert_eq!(
            ev(
                &mut it,
                "document.querySelectorAll('#a p')[1].childNodes[0].nodeType"
            ),
            "3"
        );
        assert_eq!(
            ev(
                &mut it,
                "document.querySelectorAll('#a p')[1].childNodes[0].textContent"
            ),
            "two "
        );
        assert_eq!(
            ev(&mut it, "document.querySelector('#a p').parentElement.id"),
            "a"
        );
        assert_eq!(ev(&mut it, "document.body.parentElement.tagName"), "HTML");
    }

    #[test]
    fn mutation() {
        let mut it = interp(PAGE);
        it.run(
            "var h=document.createElement('h1');h.textContent='INJ';document.body.appendChild(h)",
        )
        .unwrap();
        it.run("document.getElementById('a').appendChild(document.getElementById('l'))")
            .unwrap();
        it.run("document.getElementById('i').remove()").unwrap();
        let dom = it.take_dom();
        let h1 = vigia_css::query(&dom, "body > h1").unwrap();
        assert_eq!(vigia_actions::text_content(&dom, h1[0]), "INJ");
        // moved, not copied: link is now inside #a
        assert_eq!(vigia_css::query(&dom, "#a > a").unwrap().len(), 1);
        // detached: orphan stays in the arena but query() skips unreachable
        assert!(vigia_css::query(&dom, "#i").unwrap().is_empty());

        // removeChild returns the detached node
        let mut it = interp("<body><div id=a><b id=b>x</b></div></body>");
        assert_eq!(
            ev(
                &mut it,
                "document.getElementById('a').removeChild(document.getElementById('b')).tagName"
            ),
            "B"
        );
        assert_eq!(ev(&mut it, "document.getElementById('b')"), "null");
        let dom = it.take_dom();
        assert!(vigia_css::query(&dom, "#b").unwrap().is_empty());
        assert!(
            errmsg(&mut interp("<body></body>"), "document.body.appendChild(1)")
                .contains("needs a node")
        );
    }

    #[test]
    fn insert_before_and_style() {
        let mut it = interp("<body><div id=a><b id=b>x</b></div></body>");
        it.run(
            "var a=document.getElementById('a');var c=document.createElement('i');c.textContent='n';a.insertBefore(c,document.getElementById('b'))",
        )
        .unwrap();
        assert_eq!(
            ev(&mut it, "document.getElementById('a').innerHTML"),
            "<i>n</i><b id=\"b\">x</b>"
        );
        // null ref appends; foreign ref errors.
        it.run("var d=document.createElement('u');a.insertBefore(d,null)")
            .unwrap();
        assert!(ev(&mut it, "document.getElementById('a').innerHTML").contains("<u></u>"));
        assert!(errmsg(&mut it, "a.insertBefore(d,document.body)").contains("not a child"));
        // Live style block round-trips through the attribute.
        it.run("var e=document.createElement('div');e.style.display='none';e.style.opacity='0.5';document.body.appendChild(e)").unwrap();
        assert_eq!(ev(&mut it, "e.style.display"), "none");
        assert_eq!(ev(&mut it, "e.style.length"), "2");
        assert!(ev(&mut it, "e.style.cssText").contains("display: none"));
        assert!(ev(&mut it, "e.outerHTML").contains("style=\"display: none; opacity: 0.5\""));
        it.run("e.style.display=''").unwrap();
        assert_eq!(ev(&mut it, "e.style.length"), "1");
        assert_eq!(ev(&mut it, "e.style.missing"), "undefined");
    }

    #[test]
    fn webforms_postback() {
        let mut it = interp(
            r#"<html><body><form id=f method=post action="/go">
            <input name=user value=u><input name=__VIEWSTATE value=vs>
            </form></body></html>"#,
        );
        // document.forms snapshot.
        assert_eq!(ev(&mut it, "document.forms.length"), "1");
        assert_eq!(ev(&mut it, "document.forms[0].tagName"), "FORM");
        // form.submit() captures fields + target, performs no HTTP.
        it.run("document.forms[0].submit()").unwrap();
        let sub = it.pending_submit.clone().expect("pending submit");
        assert_eq!((sub.method.as_str(), sub.url.as_str()), ("post", "/go"));
        assert!(sub.fields.contains(&("user".into(), "u".into())));
        assert!(sub.fields.contains(&("__VIEWSTATE".into(), "vs".into())));
        // submit on a non-form is a TypeError-shaped error.
        assert!(errmsg(&mut it, "document.body.submit()").contains("not a function"));
        // __doPostBack injects the hidden pair, then submits.
        it.run("__doPostBack('ctl00$btn','')").unwrap();
        let sub = it.pending_submit.clone().expect("pending submit");
        assert!(sub
            .fields
            .contains(&("__EVENTTARGET".into(), "ctl00$btn".into())));
        let dom = it.take_dom();
        let t = vigia_css::query(&dom, "input[name=__EVENTTARGET]").unwrap();
        assert_eq!(t.len(), 1);
        assert_eq!(dom.attr(t[0], "value"), Some("ctl00$btn"));
        // WebForms without a form errors clearly.
        let mut bare = interp("<html><body></body></html>");
        assert!(errmsg(&mut bare, "__doPostBack('a','b')").contains("no form"));
    }

    #[test]
    fn javascript_href_runs() {
        let mut it = interp(
            r#"<html><body><a id=j href="javascript:document.title='pb'">go</a></body></html>"#,
        );
        it.run("document.getElementById('j').click()").unwrap();
        assert!(it.pending_nav.is_none());
        let dom = it.take_dom();
        let t = vigia_css::query(&dom, "title").unwrap();
        assert_eq!(vigia_actions::text_content(&dom, t[0]), "pb");
        // A postback link records a submit instead of navigating.
        let mut it = interp(
            r#"<html><body><form method=post action="/p"></form>
            <a id=j href="javascript:__doPostBack('t','a')">go</a></body></html>"#,
        );
        it.run("document.getElementById('j').click()").unwrap();
        assert!(it.pending_nav.is_none());
        assert!(it.pending_submit.is_some());
    }

    #[test]
    fn title_and_misc() {
        let mut it = interp(PAGE);
        assert_eq!(ev(&mut it, "document.title"), "old");
        it.run("document.title = 'new'").unwrap();
        let dom = it.take_dom();
        let t = vigia_css::query(&dom, "title").unwrap();
        assert_eq!(vigia_actions::text_content(&dom, t[0]), "new");
        // no title element: creates one under head/html
        let mut it = interp("<html><body></body></html>");
        it.run("document.title = 'made'").unwrap();
        let dom = it.take_dom();
        let t = vigia_css::query(&dom, "title").unwrap();
        assert_eq!(vigia_actions::text_content(&dom, t[0]), "made");
        // click is a no-op; unknown methods error
        let mut it = interp("<body></body>");
        assert_eq!(ev(&mut it, "document.body.click()"), "undefined");
        assert!(errmsg(&mut it, "document.body.fly()").contains("not a function"));
    }

    #[test]
    fn run_scripts_flow() {
        let mut d = Dom::new();
        vigia_html::parse(
            r#"<html><head>
                <script type="application/ld+json">{"skip":1}</script>
                <script src="ext.js"></script>
                <script>var g = 40;</script>
                </head><body>
                <script>document.body.innerHTML = '<h1>INJ</h1>'; g + 2;</script>
                <script>throwaway.undef()</script>
                <script>document.title = 'after'</script>
                </body></html>"#,
            &mut d,
        );
        let mut it = Interp::new();
        let out = it.run_scripts(d, None);
        let (dom, errs) = (out.dom, out.errors);
        assert_eq!(errs.len(), 1);
        assert!(errs[0].to_string().contains("throwaway"));
        // mutations from the scripts that ran are in the returned dom
        let h1 = vigia_css::query(&dom, "h1").unwrap();
        assert_eq!(vigia_actions::text_content(&dom, h1[0]), "INJ");
        let t = vigia_css::query(&dom, "title").unwrap();
        assert_eq!(vigia_actions::text_content(&dom, t[0]), "after");
        // innerHTML= orphaned the 3 body <script>s; head scripts stay put
        // (ld+json / external kept their text, unexecuted)
        assert_eq!(vigia_css::query(&dom, "script").unwrap().len(), 3);
        let ld = vigia_css::query(&dom, "script[type*=json]").unwrap();
        assert_eq!(vigia_actions::text_content(&dom, ld[0]), "{\"skip\":1}");
    }

    // ---- events + fetch --------------------------------------------------

    /// Serve one response per connection on a throwaway port; returns the
    /// port and the request lines observed.
    fn serve(bodies: Vec<String>) -> (u16, std::sync::Arc<std::sync::Mutex<Vec<String>>>) {
        use std::io::{Read, Write};
        let l = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
        let port = l.local_addr().unwrap().port();
        let log = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let log2 = log.clone();
        std::thread::spawn(move || {
            for body in bodies {
                let Ok((mut s, _)) = l.accept() else { return };
                let mut req = Vec::new();
                let mut chunk = [0u8; 4096];
                while !req.windows(4).any(|w| w == b"\r\n\r\n") {
                    match s.read(&mut chunk) {
                        Ok(0) | Err(_) => break,
                        Ok(n) => req.extend_from_slice(&chunk[..n]),
                    }
                }
                // read the body too (content-length) so tests can assert
                // on the payload that hit the wire
                let head = String::from_utf8_lossy(&req).to_string();
                if let Some(n) = head.lines().find_map(|l| {
                    l.to_ascii_lowercase()
                        .strip_prefix("content-length:")
                        .and_then(|v| v.trim().parse::<usize>().ok())
                }) {
                    while req
                        .windows(4)
                        .position(|w| w == b"\r\n\r\n")
                        .map(|i| req.len() - i - 4)
                        < Some(n)
                    {
                        match s.read(&mut chunk) {
                            Ok(0) | Err(_) => break,
                            Ok(m) => req.extend_from_slice(&chunk[..m]),
                        }
                    }
                }
                log2.lock()
                    .unwrap()
                    .push(String::from_utf8_lossy(&req).to_string());
                let _ = s.write_all(body.as_bytes());
            }
        });
        (port, log)
    }

    fn page_title(dom: &Dom) -> String {
        let t = vigia_css::query(dom, "title").unwrap();
        vigia_actions::text_content(dom, t[0])
    }

    #[test]
    fn inline_handler_this_and_event() {
        // the acceptance case: el.click() runs the onclick attr with
        // this = the element and the event object as `event`
        let mut it = interp(
            r#"<body><a id=l onclick="var b=document.createElement('b');b.id='x';document.body.appendChild(b);b.textContent=this.id+':'+event.type">go</a></body>"#,
        );
        it.run("document.getElementById('l').click()").unwrap();
        let dom = it.take_dom();
        let b = vigia_css::query(&dom, "#x").unwrap();
        assert_eq!(vigia_actions::text_content(&dom, b[0]), "l:click");
    }

    #[test]
    fn listeners_bubble_and_stop() {
        let mut it =
            interp(r#"<body><div id=a onclick="log.push('inline')"><p id=p>one</p></div></body>"#);
        it.run(
            "var log=[];\
             var a=document.getElementById('a');\
             a.addEventListener('click',function(e){log.push('a:'+(e.currentTarget===this)+':'+e.target.tagName)});\
             document.body.addEventListener('click',function(e){log.push('body')});\
             document.getElementById('p').click()",
        )
        .unwrap();
        // inline first, then the node's listeners, then ancestors bubble
        assert_eq!(ev(&mut it, "log.join(',')"), "inline,a:true:P,body");

        // stopPropagation on #a keeps body's listener from running, but a
        // second same-node listener still fires
        let mut it = interp(r#"<body><div id=a><p id=p>one</p></div></body>"#);
        it.run(
            "var log=[];\
             var a=document.getElementById('a');\
             a.addEventListener('click',function(e){log.push('a1');e.stopPropagation()});\
             a.addEventListener('click',function(e){log.push('a2')});\
             document.body.addEventListener('click',function(e){log.push('body')});\
             document.getElementById('p').click()",
        )
        .unwrap();
        assert_eq!(ev(&mut it, "log.join(',')"), "a1,a2");
    }

    #[test]
    fn listener_dedupe_and_remove() {
        let mut it = interp(r#"<body><div id=a></div></body>"#);
        assert_eq!(
            ev(
                &mut it,
                "var n=0;var e=document.getElementById('a');\
                 function h(){n+=1}\
                 e.addEventListener('click',h);e.addEventListener('click',h);\
                 e.click();n"
            ),
            "1"
        );
        assert_eq!(
            ev(&mut it, "e.removeEventListener('click',h);e.click();n"),
            "1"
        );
        assert!(errmsg(&mut it, "e.addEventListener('click',1)").contains("function"));
    }

    #[test]
    fn dispatch_event_and_prevent_default() {
        let mut it = interp(r#"<body><a id=l href="/nope">x</a></body>"#);
        // no listeners -> dispatchEvent returns true
        assert_eq!(
            ev(
                &mut it,
                "document.getElementById('l').dispatchEvent({type:'click'})"
            ),
            "true"
        );
        // preventDefault flips defaultPrevented and the return value
        it.run(
            "var l=document.getElementById('l');\
             l.addEventListener('click',function(e){e.preventDefault()})",
        )
        .unwrap();
        assert_eq!(ev(&mut it, "l.dispatchEvent({type:'click'})"), "false");
        // prevented default: click() does not navigate
        it.run("l.click()").unwrap();
        assert!(it.pending_nav.is_none());
        assert!(errmsg(&mut it, "l.dispatchEvent({})").contains("type"));
        assert!(errmsg(&mut it, "l.dispatchEvent(5)").contains("event object"));
    }

    #[test]
    fn click_nav_pending() {
        // no net ctx: href recorded raw; with preventDefault it isn't
        let mut it = interp(r#"<body><a id=l href="/next">x</a></body>"#);
        it.run("document.getElementById('l').click()").unwrap();
        assert_eq!(it.pending_nav.as_deref(), Some("/next"));
        assert_eq!(ev(&mut it, "location.href"), "/next");
    }

    #[test]
    fn focus_blur_fire() {
        let mut it = interp(r#"<body><input id=i></body>"#);
        assert_eq!(
            ev(
                &mut it,
                "var s='';var e=document.getElementById('i');\
                 e.addEventListener('focus',function(){s+='f'});\
                 e.addEventListener('blur',function(){s+='b'});\
                 e.focus();e.blur();s"
            ),
            "fb"
        );
    }

    #[test]
    fn listener_throw_containment() {
        // a listener that catches its own throw doesn't disturb dispatch
        let mut it = interp(r#"<body><div id=a><p id=p>x</p></div></body>"#);
        it.run(
            "var log=[];\
             var a=document.getElementById('a');\
             a.addEventListener('click',function(e){try{throw 9}catch(q){log.push('c'+q)}});\
             document.body.addEventListener('click',function(){log.push('body')});\
             document.getElementById('p').click()",
        )
        .unwrap();
        assert_eq!(ev(&mut it, "log.join(',')"), "c9,body");
        // an uncaught throw still aborts dispatch and reaches click()'s
        // caller, where a page-level try can see the value verbatim
        let mut it = interp(r#"<body><div id=a></div></body>"#);
        assert_eq!(
            ev(
                &mut it,
                "var r;\
                 document.getElementById('a').addEventListener('click',function(){throw 8});\
                 try{document.getElementById('a').click()}catch(q){r=q}r"
            ),
            "8"
        );
        // unhandled: the dispatch error is the run() error
        assert!(errmsg(&mut it, "document.getElementById('a').click()").contains("8"));
    }

    #[test]
    fn script_throw_collects() {
        // an uncaught `throw` in one <script> lands in errors; later
        // scripts still run
        let mut d = Dom::new();
        vigia_html::parse(
            "<html><body><script>throw new Error('bad')</script>\
             <script>document.title='ok'</script></body></html>",
            &mut d,
        );
        let mut it = Interp::new();
        let out = it.run_scripts(d, None);
        assert_eq!(out.errors.len(), 1);
        assert!(
            out.errors[0].to_string().contains("Error: bad"),
            "{}",
            out.errors[0]
        );
        assert_eq!(page_title(&out.dom), "ok");
        // a plain thrown value stringifies too
        let mut d = Dom::new();
        vigia_html::parse(
            "<html><body><script>throw 'zip'</script></body></html>",
            &mut d,
        );
        let mut it = Interp::new();
        let out = it.run_scripts(d, None);
        assert_eq!(out.errors.len(), 1);
        assert_eq!(out.errors[0].to_string(), "zip");
    }

    #[test]
    fn dom_content_loaded() {
        let mut d = Dom::new();
        vigia_html::parse(
            r#"<html><head><title>old</title>
               <script>document.addEventListener('DOMContentLoaded',function(e){document.title='ready:'+e.target.nodeType})</script>
               </head><body></body></html>"#,
            &mut d,
        );
        let mut it = Interp::new();
        let out = it.run_scripts(d, None);
        assert!(out.errors.is_empty(), "{:?}", out.errors);
        assert_eq!(page_title(&out.dom), "ready:9");
    }

    #[test]
    fn pending_nav_resolved_against_base() {
        let mut d = Dom::new();
        vigia_html::parse(
            "<html><body><a id=l href='/next'>x</a><script>document.getElementById('l').click()</script></body></html>",
            &mut d,
        );
        let mut it = Interp::new();
        let out = it.run_scripts(
            d,
            Some(NetCtx {
                base: vigia_url::Url::parse("http://a.com/dir/p").unwrap(),
                jar: CookieJar::new(),
                trace: None,
            }),
        );
        assert!(out.errors.is_empty(), "{:?}", out.errors);
        assert_eq!(out.pending_nav.as_deref(), Some("http://a.com/next"));
        assert!(out.jar.is_some());
    }

    #[test]
    fn fetch_needs_page_context() {
        let mut it = Interp::new();
        assert!(it
            .run("fetch('/x')")
            .unwrap_err()
            .to_string()
            .contains("page context"));
        // installed even with a dom but no net ctx
        let mut it = interp("<body></body>");
        assert!(it
            .run("fetch('/x')")
            .unwrap_err()
            .to_string()
            .contains("page context"));
    }

    #[test]
    fn fetch_promise_json_and_cookies() {
        // fetch() returns a resolved promise; text()/json() return resolved
        // promises too - handlers run at the script-boundary drain.
        let body = "{\"name\":\"x\"}";
        let resp = format!(
            "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nSet-Cookie: sid=7; Path=/\r\nContent-Length: {}\r\n\r\n{}",
            body.len(),
            body
        );
        let (port, log) = serve(vec![resp]);
        let mut d = Dom::new();
        vigia_html::parse(
            "<html><head><title>o</title></head><body><script>\
             fetch('/api?x=1').then(function(r){\
               document.title = r.status+':'+r.ok;\
               r.json().then(function(j){document.title += ':'+j.name});\
               r.text().then(function(t){document.title += ':'+t})\
             })</script></body></html>",
            &mut d,
        );
        let mut it = Interp::new();
        let out = it.run_scripts(
            d,
            Some(NetCtx {
                base: vigia_url::Url::parse(&format!("http://127.0.0.1:{port}/dir/page")).unwrap(),
                jar: CookieJar::new(),
                trace: None,
            }),
        );
        assert!(out.errors.is_empty(), "{:?}", out.errors);
        assert_eq!(page_title(&out.dom), "200:true:x:{\"name\":\"x\"}");
        // relative url resolved against the page url
        assert!(log.lock().unwrap()[0].starts_with("GET /api?x=1 HTTP/1.1"));
        // Set-Cookie landed in the jar that came back out
        let jar = out.jar.unwrap();
        assert_eq!(jar.len(), 1);
        let u = vigia_url::Url::parse(&format!("http://127.0.0.1:{port}/other")).unwrap();
        assert_eq!(jar.header_for(&u).as_deref(), Some("sid=7"));
    }

    #[test]
    fn fetch_post_init_and_net_trace() {
        // fetch(url, {method,headers,body}) sends a real POST and the
        // NetEvent trace captures it - the API-discovery primitive.
        let resp = "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: 7\r\n\r\n{\"r\":1}";
        let (port, log) = serve(vec![resp.to_string()]);
        let mut d = Dom::new();
        vigia_html::parse(
            "<html><body><script>\
             fetch('/api', {method:'POST', headers:{'Content-Type':'application/json','X-A':'b'}, body:'{\"x\":9}'})\
             .then(function(r){document.body.textContent=r.status})\
             </script></body></html>",
            &mut d,
        );
        let mut it = Interp::new();
        let trace = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
        let out = it.run_scripts(
            d,
            Some(NetCtx {
                base: vigia_url::Url::parse(&format!("http://127.0.0.1:{port}/dir/page")).unwrap(),
                jar: CookieJar::new(),
                trace: Some(trace.clone()),
            }),
        );
        assert!(out.errors.is_empty(), "{:?}", out.errors);
        let wire = log.lock().unwrap()[0].clone();
        assert!(wire.starts_with("POST /api "), "{wire}");
        assert!(wire.contains("Content-Type: application/json"), "{wire}");
        assert!(wire.contains("X-A: b"), "{wire}");
        assert!(wire.contains("{\"x\":9}"), "{wire}");
        let events = trace.borrow().clone();
        assert_eq!(events.len(), 1);
        assert_eq!(events[0].method, "POST");
        assert!(events[0].url.ends_with("/api"));
        assert_eq!(events[0].status, 200);
        assert_eq!(events[0].req_body.as_deref(), Some("{\"x\":9}"));
    }

    #[test]
    fn fetch_redirect_and_404() {
        let bodies = vec![
            "HTTP/1.1 302 Found\r\nLocation: /final\r\nContent-Length: 0\r\n\r\n".to_string(),
            "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nhi".to_string(),
            "HTTP/1.1 404 Not Found\r\nContent-Length: 0\r\n\r\n".to_string(),
        ];
        let (port, _log) = serve(bodies);
        let mut d = Dom::new();
        // second fetch inside a then-handler: still sync under the hood
        vigia_html::parse(
            "<html><head><title>o</title></head><body><script>\
             fetch('/go').then(function(a){\
               fetch('/missing').then(function(b){\
                 document.title=a.redirected+':'+a.url+'|'+b.ok+':'+b.status\
               })\
             })</script></body></html>",
            &mut d,
        );
        let mut it = Interp::new();
        let out = it.run_scripts(
            d,
            Some(NetCtx {
                base: vigia_url::Url::parse(&format!("http://127.0.0.1:{port}/")).unwrap(),
                jar: CookieJar::new(),
                trace: None,
            }),
        );
        assert!(out.errors.is_empty(), "{:?}", out.errors);
        assert_eq!(
            page_title(&out.dom),
            format!("true:http://127.0.0.1:{port}/final|false:404")
        );
    }

    #[test]
    fn fetch_network_error_rejects() {
        // port 1 is closed: fetch rejects (not throws) - a then() rejection
        // handler sees the reason
        let mut d = Dom::new();
        vigia_html::parse(
            "<html><head><title>o</title></head><body><script>\
             fetch('http://127.0.0.1:1/x').then(\
               function(){document.title='ok'},\
               function(e){document.title='err'})</script></body></html>",
            &mut d,
        );
        let mut it = Interp::new();
        let out = it.run_scripts(
            d,
            Some(NetCtx {
                base: vigia_url::Url::parse("http://127.0.0.1:1/").unwrap(),
                jar: CookieJar::new(),
                trace: None,
            }),
        );
        assert!(out.errors.is_empty(), "{:?}", out.errors);
        assert_eq!(page_title(&out.dom), "err");

        // same failure unhandled -> "unhandled rejection" drain error
        let mut d = Dom::new();
        vigia_html::parse(
            "<html><body><script>fetch('http://127.0.0.1:1/x')</script></body></html>",
            &mut d,
        );
        let mut it = Interp::new();
        let out = it.run_scripts(
            d,
            Some(NetCtx {
                base: vigia_url::Url::parse("http://127.0.0.1:1/").unwrap(),
                jar: CookieJar::new(),
                trace: None,
            }),
        );
        assert_eq!(out.errors.len(), 1);
        assert!(
            out.errors[0].to_string().contains("unhandled rejection"),
            "{}",
            out.errors[0]
        );
        assert!(
            out.errors[0].to_string().contains("fetch"),
            "{}",
            out.errors[0]
        );
    }

    // ---- async runtime on the page ------------------------------------------

    #[test]
    fn event_handler_queues_drain_before_return() {
        // a click handler's microtasks and setTimeout(0) run inside the
        // same dispatch: the DOM is already mutated when click() returns.
        let mut d = Dom::new();
        vigia_html::parse(
            r#"<html><body><div id=a></div>
               <script>
               var log=[];
               var a=document.getElementById('a');
               a.addEventListener('click',function(){
                 queueMicrotask(function(){log.push('mt')});
                 setTimeout(function(){a.setAttribute('data-done','1');log.push('t0')},0)
               });
               a.click();
               log.push('after');
               document.title=log.join(',')
               </script></body></html>"#,
            &mut d,
        );
        let mut it = Interp::new();
        let out = it.run_scripts(d, None);
        assert!(out.errors.is_empty(), "{:?}", out.errors);
        // handler ran, then mt + timer inside the dispatch, then the rest
        assert_eq!(page_title(&out.dom), "mt,t0,after");
        let a = vigia_css::query(&out.dom, "#a").unwrap()[0];
        assert_eq!(out.dom.attr(a, "data-done"), Some("1"));
    }

    #[test]
    fn await_fetch_end_to_end() {
        let body = "{\"k\":42}";
        let resp = format!(
            "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: {}\r\n\r\n{}",
            body.len(),
            body
        );
        let (port, _log) = serve(vec![resp]);
        let mut d = Dom::new();
        vigia_html::parse(
            "<html><head><title>o</title></head><body><script>\
             async function go(){\
               var r = await fetch('/j');\
               var j = await r.json();\
               document.title = 'got:'+j.k\
             }\
             go()</script></body></html>",
            &mut d,
        );
        let mut it = Interp::new();
        let out = it.run_scripts(
            d,
            Some(NetCtx {
                base: vigia_url::Url::parse(&format!("http://127.0.0.1:{port}/")).unwrap(),
                jar: CookieJar::new(),
                trace: None,
            }),
        );
        assert!(out.errors.is_empty(), "{:?}", out.errors);
        assert_eq!(page_title(&out.dom), "got:42");
    }

    #[test]
    fn async_rejection_reaches_catch() {
        // an async fn's throw becomes a rejection the caller's .catch sees
        let mut it = Interp::new();
        it.run(
            "async function f(){nope()};\
             var seen='unset';\
             f().catch(function(e){seen=e})",
        )
        .unwrap();
        assert_eq!(ev(&mut it, "seen"), "nope is not defined");
    }

    // ---- external <script src> --------------------------------------------

    /// Parse `html` and run its scripts under a NetCtx rooted at `base`.
    fn run_page(html: &str, base: &str) -> ScriptsOutcome {
        let mut d = Dom::new();
        vigia_html::parse(html, &mut d);
        Interp::new().run_scripts(
            d,
            Some(NetCtx {
                base: vigia_url::Url::parse(base).unwrap(),
                jar: CookieJar::new(),
                trace: None,
            }),
        )
    }

    #[test]
    fn external_script_runs_in_document_order() {
        let js = "function fromExt(){return 'EXT'}";
        let resp = format!(
            "HTTP/1.1 200 OK\r\nContent-Type: text/javascript\r\nContent-Length: {}\r\n\r\n{}",
            js.len(),
            js
        );
        let (port, log) = serve(vec![resp]);
        let out = run_page(
            "<html><head><title>o</title>\
             <script src=\"/ext.js\"></script>\
             <script>document.title = fromExt()</script></head><body></body></html>",
            &format!("http://127.0.0.1:{port}/dir/page"),
        );
        assert!(out.errors.is_empty(), "{:?}", out.errors);
        // relative src resolved against the page url
        assert!(log.lock().unwrap()[0].starts_with("GET /ext.js HTTP/1.1"));
        // the external's global is visible to the later inline script
        assert_eq!(page_title(&out.dom), "EXT");
        assert!(out.jar.is_some());
    }

    #[test]
    fn external_script_fetch_failure_collects() {
        // port 1 is closed: the io failure lands as a page error and the
        // later inline script still runs
        let out = run_page(
            "<html><head><title>o</title>\
             <script src=\"http://127.0.0.1:1/dead.js\"></script>\
             <script>document.title = 'alive'</script></head><body></body></html>",
            "http://127.0.0.1:1/",
        );
        assert_eq!(out.errors.len(), 1);
        assert!(
            out.errors[0].to_string().contains("dead.js"),
            "{}",
            out.errors[0]
        );
        assert_eq!(page_title(&out.dom), "alive");
    }

    #[test]
    fn external_script_eval_failure_collects() {
        // fetched fine but doesn't parse - error recorded, page survives
        let js = "this is not js {{{";
        let resp = format!(
            "HTTP/1.1 200 OK\r\nContent-Type: text/javascript\r\nContent-Length: {}\r\n\r\n{}",
            js.len(),
            js
        );
        let (port, _log) = serve(vec![resp]);
        let out = run_page(
            "<html><head><title>o</title>\
             <script src=\"bad.js\"></script>\
             <script>document.title = 'alive'</script></head><body></body></html>",
            &format!("http://127.0.0.1:{port}/"),
        );
        assert_eq!(out.errors.len(), 1);
        assert_eq!(page_title(&out.dom), "alive");
    }

    #[test]
    fn external_script_non_http_scheme_skipped() {
        let out = run_page(
            "<html><head><title>o</title>\
             <script src=\"data:text/javascript,var z=1\"></script>\
             <script src=\"javascript:void 0\"></script>\
             <script>document.title = 'ok'</script></head><body></body></html>",
            "http://a.com/",
        );
        // skipped, but each leaves an error entry as the signal
        assert_eq!(out.errors.len(), 2);
        assert!(
            out.errors[0].to_string().contains("data scheme"),
            "{}",
            out.errors[0]
        );
        assert!(
            out.errors[1].to_string().contains("javascript scheme"),
            "{}",
            out.errors[1]
        );
        assert_eq!(page_title(&out.dom), "ok");
    }

    #[test]
    fn external_script_no_net_skipped_silently() {
        let mut d = Dom::new();
        vigia_html::parse(
            "<html><head><title>o</title>\
             <script src=\"http://127.0.0.1:1/dead.js\"></script>\
             <script>document.title = 'ok'</script></head><body></body></html>",
            &mut d,
        );
        let mut it = Interp::new();
        let out = it.run_scripts(d, None);
        assert!(out.errors.is_empty(), "{:?}", out.errors);
        assert_eq!(page_title(&out.dom), "ok");
    }
}
