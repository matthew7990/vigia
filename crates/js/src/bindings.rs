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
use crate::eval::{
    arg, get_prop, nat, n_connection, n_const_false, n_geolocation, n_indexed_db,
    n_mimetypes_arr, n_plugins_arr, n_send_beacon, n_user_agent_data, set_prop, to_num, to_str,
    truthy,
};
use crate::{err, po, Interp, JsError, NativeFn, NetCtx, Obj, PendingSubmit, Value};

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

/// First element with `tag` in `anc`'s subtree (for implementation-created
/// documents living detached in the same arena).
fn first_desc_tag(dom: &Dom, anc: NodeId, tag: &str) -> Option<NodeId> {
    let mut stack = dom.children(anc).to_vec();
    while let Some(n) = stack.pop() {
        if dom.tag_name(n) == Some(tag) {
            return Some(n);
        }
        stack.extend(dom.children(n).iter().copied());
    }
    None
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
    Inline(NodeId, String),
    External(NodeId, String),
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
            Some(src) => out.push(ScriptSource::External(id, src.to_string())),
            None => {
                let mut s = String::new();
                raw_text(dom, id, &mut s);
                out.push(ScriptSource::Inline(id, s));
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
        NodeData::Document | NodeData::Fragment => {
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

/// Sentinel listener-map key for `window` (no arena node; must never
/// reach dom.parent/dom_wrap - dispatch_window handles it separately).
pub(crate) const WIN_EVENTS: NodeId = u32::MAX;

impl Interp {
    /// Install `dom` plus the document/window/navigator/location globals.
    /// Call before run(). Re-installing replaces the DOM, the wrappers,
    /// the event listeners and any pending navigation - new page, clean
    /// event state.
    pub fn set_dom(&mut self, dom: Dom) {
        self.dom = Some(dom);
        self.dom_objs.clear();
        self.sheets.clear();
        self.canvases.clear();
        self.ctx2ds.clear();
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
        // Navigator needs several strings; build them first, then the
        // object (heap-cap edges skip the install silently, as elsewhere).
        // Defaults are Chrome-shaped constants; --stealth only swaps the
        // UA family to match the wire profile (applied in run_scripts).
        let Ok(en_us) = self.heap.alloc_str("en-US".into()) else {
            return;
        };
        let langs = match self.heap.alloc_str("en".into()) {
            Ok(en) => self.arr_obj(vec![Value::Str(en_us), Value::Str(en)]).ok(),
            Err(_) => None,
        };
        let nav_pairs: Result<Vec<(String, Value)>, JsError> = (|| {
            let heap = &mut self.heap;
            let mut v = vec![
                ("userAgent".into(), Value::Str(ua)),
                (
                    "appVersion".into(),
                    Value::Str(heap.alloc_str("5.0 (X11; Linux x86_64)".into())?),
                ),
                ("platform".into(), Value::Str(heap.alloc_str("Linux x86_64".into())?)),
                ("language".into(), Value::Str(en_us)),
                ("product".into(), Value::Str(heap.alloc_str("Gecko".into())?)),
                ("productSub".into(), Value::Str(heap.alloc_str("20030107".into())?)),
                ("appName".into(), Value::Str(heap.alloc_str("Netscape".into())?)),
                ("appCodeName".into(), Value::Str(heap.alloc_str("Mozilla".into())?)),
                ("vendor".into(), Value::Str(heap.alloc_str("".into())?)),
                ("hardwareConcurrency".into(), Value::Num(8.0)),
                ("deviceMemory".into(), Value::Num(8.0)),
                ("maxTouchPoints".into(), Value::Num(0.0)),
                ("cookieEnabled".into(), Value::Bool(true)),
                ("doNotTrack".into(), Value::Null),
                ("pdfViewerEnabled".into(), Value::Bool(true)),
                ("onLine".into(), Value::Bool(true)),
                (
                    "javaEnabled".into(),
                    Value::Obj(heap.alloc_obj(nat("javaEnabled", n_const_false))?),
                ),
                (
                    "sendBeacon".into(),
                    Value::Obj(heap.alloc_obj(nat("sendBeacon", n_send_beacon))?),
                ),
            ];
            if let Some(l) = langs {
                v.push(("languages".into(), Value::Obj(l)));
            }
            Ok(v)
        })();
        // Object-valued navigator members (built via their natives so
        // shapes stay in one place).
        let mut nav_extra: Vec<(String, Value)> = Vec::new();
        for (k, mk) in [
            ("connection", n_connection as NativeFn),
            ("geolocation", n_geolocation),
            ("userAgentData", n_user_agent_data),
            ("indexedDB", n_indexed_db),
        ] {
            match mk(self, Value::Undef, &[]) {
                Ok(v) => nav_extra.push((k.into(), v)),
                Err(_) => break,
            }
        }
        for (k, mk) in [("plugins", n_plugins_arr as NativeFn), ("mimeTypes", n_mimetypes_arr)] {
            match mk(self, Value::Undef, &[]) {
                Ok(v) => nav_extra.push((k.into(), v)),
                Err(_) => break,
            }
        }
        let (Ok(nav_pairs), Ok(loc)) = (
            nav_pairs,
            self.obj_pairs(vec![("href".into(), Value::Str(href))]),
        ) else {
            return;
        };
        let Ok(nav) = self.obj_pairs(nav_pairs) else {
            return;
        };
        for (k, v) in nav_extra {
            let _ = set_prop(&mut self.heap, Value::Obj(nav), &k, v);
        }
        self.env_declare(0, "navigator", Value::Obj(nav));
        self.env_declare(0, "location", Value::Obj(loc));
        // Populate href + derived parts (routers read pathname at boot).
        let _ = self.set_location_href("");
        // `window` mirrors the global scope (real browsers alias them):
        // seed with document/navigator/location plus every global so far
        // (builtins like atob included). Later script-defined globals
        // read through bare identifiers; `window.x` reads for those are
        // a documented gap (writes land on window itself and do read
        // back within the page).
        let mut wp = vec![
            ("document".into(), doc),
            ("navigator".into(), Value::Obj(nav)),
            ("location".into(), Value::Obj(loc)),
        ];
        for (k, v) in &self.envs[0].vars {
            if !wp.iter().any(|(ek, _)| ek == k) {
                wp.push((k.clone(), *v));
            }
        }
        if let Ok(w) = self.obj_pairs(wp) {
            if let Obj::Ordinary { pairs, .. } = self.heap.obj_mut(w) {
                pairs.push(("window".into(), Value::Obj(w)));
                // `self` (workers/global alias) and `globalThis` match window.
                pairs.push(("self".into(), Value::Obj(w)));
                pairs.push(("globalThis".into(), Value::Obj(w)));
            }
            self.env_declare(0, "window", Value::Obj(w));
            self.env_declare(0, "self", Value::Obj(w));
            self.env_declare(0, "globalThis", Value::Obj(w));
            self.wind = Some(w);
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
        // --stealth: navigator UA family must match the wire profile or
        // the mismatch itself is the bot signal.
        if self.net.as_ref().is_some_and(|c| c.jar.stealth) {
            self.apply_stealth_ua();
        }
        let mut errs = Vec::new();
        let mut fetched = 0;
        for (n, s) in scripts.iter().enumerate() {
            match s {
                ScriptSource::Inline(id, src) => {
                    // document.currentScript during this run (V8 parity).
                    let prev = self.cur_script.replace(*id);
                    let r = self.run(src);
                    self.cur_script = prev;
                    if let Err(e) = r {
                        errs.push(Self::tag_err(format!("inline#{n}"), e));
                    }
                }
                ScriptSource::External(id, raw) => match self.fetch_script(raw, &mut fetched) {
                    Ok(Some(body)) => {
                        let prev = self.cur_script.replace(*id);
                        let r = self.run(&body);
                        self.cur_script = prev;
                        if let Err(e) = r {
                            errs.push(Self::tag_err(format!("src {raw}"), e));
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

    /// --stealth navigator override: Chrome 126 Linux UA family, same
    /// strings the net layer sends on the wire (vigia_net::UA_STEALTH).
    fn apply_stealth_ua(&mut self) {
        let Some(nav) = self.env_get(0, "navigator") else {
            return;
        };
        let ua = vigia_net::UA_STEALTH;
        let app_ver = ua.strip_prefix("Mozilla/").unwrap_or(ua);
        let pairs = [
            ("userAgent", ua.to_string()),
            ("appVersion", app_ver.to_string()),
            ("vendor", "Google Inc.".to_string()),
            ("product", "Gecko".to_string()),
            ("productSub", "20030107".to_string()),
            ("appName", "Netscape".to_string()),
            ("appCodeName", "Mozilla".to_string()),
        ];
        for (k, v) in pairs {
            let Ok(id) = self.heap.alloc_str(v) else {
                return;
            };
            let _ = set_prop(&mut self.heap, nav, k, Value::Str(id));
        }
    }

    /// Prefix a script-run error with which script failed (Msg/Fatal carry
    /// text; thrown values pass through untouched).
    fn tag_err(tag: String, e: JsError) -> JsError {
        match e {
            JsError::Msg(m) => JsError::Msg(format!("{tag}: {m}")),
            JsError::Fatal(m) => JsError::Fatal(format!("{tag}: {m}")),
            t => t,
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

    /// Remove an attribute (delete operator path from eval).
    pub(crate) fn dom_remove_attr(&mut self, id: NodeId, name: &str) -> Result<(), JsError> {
        self.dom_mut()?.remove_attr(id, name);
        Ok(())
    }

    /// NodeId if `v` is a DOM node handle.
    pub(crate) fn as_node(&self, v: Value) -> Option<NodeId> {
        if let Value::Obj(id) = v {
            if let Obj::Dom { node: n, .. } = self.heap.obj(id) {
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

    /// camelCase -> kebab-case ("backgroundColor" -> "background-color").
    /// Single words and already-kebab names pass through; CSS variables
    /// (--*) keep their case.
    fn style_key(key: &str) -> String {
        if key.starts_with("--") || (!key.contains(char::is_uppercase)) {
            return key.to_lowercase();
        }
        let mut out = String::with_capacity(key.len() + 4);
        for c in key.chars() {
            if c.is_ascii_uppercase() {
                out.push('-');
                out.push(c.to_ascii_lowercase());
            } else {
                out.push(c);
            }
        }
        out
    }

    /// kebab-case -> camelCase ("font-size" -> "fontSize"; "--*" untouched).
    fn style_camel(key: &str) -> String {
        if key.starts_with("--") || !key.contains('-') {
            return key.to_string();
        }
        let mut out = String::with_capacity(key.len());
        let mut up = false;
        for c in key.chars() {
            if c == '-' {
                up = true;
            } else if up {
                out.extend(c.to_uppercase());
                up = false;
            } else {
                out.push(c);
            }
        }
        out
    }

    /// Live read of one style property (or cssText/length). Property
    /// methods (setProperty/getPropertyValue/removeProperty) arrive as
    /// natives carrying the node id, like the IDB denial timer does.
    pub(crate) fn style_get(&mut self, node: NodeId, key: &str) -> Result<Value, JsError> {
        for (n, f) in [
            ("setProperty", n_style_set_prop as NativeFn),
            ("getPropertyValue", n_style_get_prop),
            ("removeProperty", n_style_remove_prop),
        ] {
            if key == n {
                let m = self.heap.alloc_obj(nat(n, f))?;
                let _ = set_prop(
                    &mut self.heap,
                    Value::Obj(m),
                    "__node",
                    Value::Num(node as f64),
                );
                return Ok(Value::Obj(m));
            }
        }
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
        let key = Self::style_key(key);
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
        let key = Self::style_key(key);
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
    /// The virtual prototype follows the node kind/tag (inputs answer
    /// HTMLInputElement.prototype and so on), so instanceof works.
    fn dom_wrap(&mut self, n: NodeId) -> Result<Value, JsError> {
        if let Some(&o) = self.dom_objs.get(&n) {
            return Ok(Value::Obj(o));
        }
        let proto = {
            let dom = self.dom_ref()?;
            match &dom.node(n).data {
                NodeData::Document => po(self.protos.dom_document),
                NodeData::Fragment => po(self.protos.dom_documentfragment),
                NodeData::Element(el) => {
                    let pr = self.protos;
                    match dom.interner.resolve(el.tag) {
                        "input" => po(pr.dom_input),
                        "form" => po(pr.dom_form),
                        "select" => po(pr.dom_select),
                        "textarea" => po(pr.dom_textarea),
                        "button" => po(pr.dom_button),
                        "a" => po(pr.dom_anchor),
                        "img" => po(pr.dom_image),
                        "canvas" => po(pr.dom_canvas),
                        "iframe" => po(pr.dom_iframe),
                        "svg" => po(pr.dom_svg),
                        _ => po(pr.dom_htmlelement),
                    }
                }
                _ => None,
            }
        };
        let o = self.heap.alloc_obj(Obj::Dom { node: n, proto })?;
        self.dom_objs.insert(n, o);
        Ok(Value::Obj(o))
    }

    /// DOMTokenList facade for an element's class attr (cached for ===).
    /// Methods carry the node id and mutate live; length/value are
    /// accessors over the same attribute.
    fn class_list_for(&mut self, n: NodeId) -> Result<Value, JsError> {
        if let Some(&o) = self.token_lists.get(&n) {
            return Ok(Value::Obj(o));
        }
        let mut pairs = vec![("__node".into(), Value::Num(n as f64))];
        for (nm, f) in [
            ("add", n_tokens_add as NativeFn),
            ("remove", n_tokens_remove),
            ("toggle", n_tokens_toggle),
            ("contains", n_tokens_contains),
            ("item", n_tokens_item),
            ("replace", n_tokens_replace),
        ] {
            let m = self.heap.alloc_obj(nat(nm, f))?;
            let _ = set_prop(&mut self.heap, Value::Obj(m), "__node", Value::Num(n as f64));
            pairs.push((nm.into(), Value::Obj(m)));
        }
        let proto = po(self.protos.object);
        for (nm, get, set) in [
            ("length", n_tokens_len as NativeFn, None),
            ("value", n_tokens_value_get, Some(n_tokens_value_set)),
        ] {
            let g = self.heap.alloc_obj(nat(nm, get))?;
            let _ = set_prop(&mut self.heap, Value::Obj(g), "__node", Value::Num(n as f64));
            let s = match set {
                Some(f) => {
                    let s = self.heap.alloc_obj(nat(nm, f))?;
                    let _ = set_prop(
                        &mut self.heap,
                        Value::Obj(s),
                        "__node",
                        Value::Num(n as f64),
                    );
                    Some(s)
                }
                None => None,
            };
            let acc = self.heap.alloc_obj(Obj::Accessor { get: Some(g), set: s, proto })?;
            pairs.push((nm.into(), Value::Obj(acc)));
        }
        let o = self.obj_pairs(pairs)?;
        self.token_lists.insert(n, o);
        Ok(Value::Obj(o))
    }

    /// CSSStyleSheet facade for a <style>/<link> node (cached for ===).
    /// Rules are {cssText} stubs - no cascade runs on them here; enough
    /// for emotion-style insertRule loops (ownerNode match + length).
    fn sheet_for(&mut self, n: NodeId) -> Result<Value, JsError> {
        if let Some(&o) = self.sheets.get(&n) {
            return Ok(Value::Obj(o));
        }
        let owner = self.dom_wrap(n)?;
        let rules = Value::Obj(self.arr_obj(Vec::new())?);
        let mut pairs = vec![
            ("ownerNode".into(), owner),
            ("cssRules".into(), rules),
        ];
        for (nm, f) in [
            ("insertRule", n_sheet_insert as NativeFn),
            ("deleteRule", n_sheet_delete),
        ] {
            pairs.push((nm.into(), Value::Obj(self.heap.alloc_obj(nat(nm, f))?)));
        }
        if self.dom_ref()?.tag_name(n) == Some("link") {
            let href = self.dom_ref()?.attr(n, "href").unwrap_or("").to_string();
            pairs.push(("href".into(), Value::Str(self.heap.alloc_str(href)?)));
        }
        let o = self.obj_pairs(pairs)?;
        self.sheets.insert(n, o);
        Ok(Value::Obj(o))
    }

    fn opt_node(&mut self, n: Option<NodeId>) -> Result<Value, JsError> {
        match n {
            Some(n) => self.dom_wrap(n),
            None => Ok(Value::Null),
        }
    }

    /// document.implementation facade (fresh object per read, like a host
    /// object): createHTMLDocument only.
    fn impl_obj(&mut self) -> Result<Value, JsError> {
        let m = self.heap.alloc_obj(nat("createHTMLDocument", n_create_html_doc))?;
        let imp = self.obj_pairs(vec![("createHTMLDocument".into(), Value::Obj(m))])?;
        Ok(Value::Obj(imp))
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

    /// Dispatch at the `window` sentinel: its own listeners only, `this`
    /// = the window object, no bubble path and no drain (dispatchEvent
    /// is synchronous, like browsers).
    pub(crate) fn dispatch_window(&mut self, ty: &str, ev: Value) -> Result<Value, JsError> {
        let this = self
            .env_get(0, "window")
            .unwrap_or(Value::Undef);
        set_prop(&mut self.heap, ev, "target", this)?;
        set_prop(&mut self.heap, ev, "currentTarget", this)?;
        let fns: Vec<Value> = self
            .listeners
            .get(&WIN_EVENTS)
            .map(|v| v.iter().filter(|(t, _)| t == ty).map(|(_, f)| *f).collect())
            .unwrap_or_default();
        for f in fns {
            if self.event_stopped(ev) {
                break;
            }
            self.call_value(f, this, &[ev], None)?;
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

    /// Fresh window event object (target/currentTarget filled by the
    /// dispatch path): same shape as new_event with the window object.
    fn new_window_event(&mut self, ty: &str) -> Result<Value, JsError> {
        let ty = Value::Str(self.heap.alloc_str(ty.to_string())?);
        let tgt = self.env_get(0, "window").unwrap_or(Value::Undef);
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
        // The window sentinel has no arena node: listeners only + drain.
        if target == WIN_EVENTS {
            let ev = self.new_window_event(&ty)?;
            self.call_vals.push(ev);
            let r = self.dispatch_window(&ty, ev);
            let mut errs = Vec::new();
            self.drain(&mut errs);
            self.call_vals.pop();
            return match r {
                Err(e) => Err(e),
                Ok(v) => match errs.into_iter().next() {
                    Some(e) => Err(e),
                    None => Ok(v),
                },
            };
        }        let ev = self.new_event(ty, target)?;
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

    /// Reflect a navigation into the JS-visible location object: href
    /// plus the derived parts routers read (pathname/search/hash/...).
    /// Unparseable hrefs still set href with sane part defaults.
    pub(crate) fn set_location_href(&mut self, href: &str) -> Result<(), JsError> {
        let Some(loc) = self.env_get(0, "location") else {
            return Ok(());
        };
        let url = vigia_url::Url::parse(href).ok();
        let str_prop = |it: &mut Interp, k: &str, v: String| -> Result<(), JsError> {
            let id = it.heap.alloc_str(v)?;
            set_prop(&mut it.heap, loc, k, Value::Str(id))?;
            Ok(())
        };
        str_prop(self, "href", href.to_string())?;
        match url {
            Some(u) => {
                str_prop(self, "protocol", format!("{}:", u.scheme))?;
                str_prop(
                    self,
                    "host",
                    if u.host.is_empty() {
                        String::new()
                    } else {
                        u.host_header()
                    },
                )?;
                str_prop(self, "hostname", u.host.clone())?;
                str_prop(
                    self,
                    "port",
                    u.port.map(|p| p.to_string()).unwrap_or_default(),
                )?;
                str_prop(self, "pathname", u.path.clone())?;
                str_prop(
                    self,
                    "search",
                    u.query.as_deref().map(|q| format!("?{q}")).unwrap_or_default(),
                )?;
                str_prop(
                    self,
                    "hash",
                    u.fragment.as_deref().map(|f| format!("#{f}")).unwrap_or_default(),
                )?;
                str_prop(
                    self,
                    "origin",
                    if u.host.is_empty() {
                        "null".into()
                    } else {
                        format!("{}://{}", u.scheme, u.host_header())
                    },
                )?;
            }
            None => {
                // Path-absolute fallback (no base to join against, e.g.
                // bare test envs): split path/query/hash by hand.
                let (rest, hash) = match href.split_once('#') {
                    Some((r, h)) => (r, format!("#{h}")),
                    None => (href, String::new()),
                };
                let (path, search) = match rest.split_once('?') {
                    Some((p, q)) => (p, format!("?{q}")),
                    None => (rest, String::new()),
                };
                for (k, v) in [
                    ("protocol", ""),
                    ("host", ""),
                    ("hostname", ""),
                    ("port", ""),
                    ("pathname", if path.is_empty() { "/" } else { path }),
                    ("search", search.as_str()),
                    ("hash", hash.as_str()),
                    ("origin", "null"),
                ] {
                    str_prop(self, k, v.into())?;
                }
            }
        }
        Ok(())
    }

    /// Event methods shared by elements and document (listeners live on
    /// node 0 for the latter, on WIN_EVENTS for window). Returns None
    /// when `name` isn't one.
    pub(crate) fn event_method(
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
                // The window sentinel has no arena node: separate path.
                if id == WIN_EVENTS {
                    let ev = self.dispatch_window(&ty, ev)?;
                    return Ok(Some(Value::Bool(!self.event_prevented(ev))));
                }
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
                    NodeData::Fragment => 11.0,
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
            "parentNode" => {
                let p = self.dom_ref()?.parent(id);
                return self.opt_node(p);
            }
            "ownerDocument" => {
                // V8: every node belongs to a document (detached ones to
                // their creator); the document itself has none (null).
                let n = {
                    let dom = self.dom_ref()?;
                    if matches!(dom.node(id).data, NodeData::Document) {
                        None
                    } else {
                        let mut cur = id;
                        while let Some(p) = dom.parent(cur) {
                            cur = p;
                        }
                        Some(
                            if matches!(dom.node(cur).data, NodeData::Document) {
                                cur
                            } else {
                                dom.root()
                            },
                        )
                    }
                };
                return self.opt_node(n);
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
            "firstChild" | "lastChild" | "firstElementChild" | "lastElementChild" => {
                let kids: Vec<NodeId> = {
                    let dom = self.dom_ref()?;
                    dom.children(id).to_vec()
                };
                let elem_only = key.contains("Element");
                let mut it: Box<dyn Iterator<Item = NodeId>> = if key.starts_with("first") {
                    Box::new(kids.into_iter())
                } else {
                    Box::new(kids.into_iter().rev())
                };
                let pick = if elem_only {
                    let dom = self.dom_ref()?;
                    it.find(|&c| matches!(dom.node(c).data, NodeData::Element(_)))
                } else {
                    it.next()
                };
                return self.opt_node(pick);
            }
            "nextSibling" | "previousSibling" | "nextElementSibling" | "previousElementSibling" => {
                let sibs: Vec<NodeId> = {
                    let dom = self.dom_ref()?;
                    match dom.parent(id) {
                        Some(p) => dom.children(p).to_vec(),
                        None => Vec::new(),
                    }
                };
                let pos = sibs.iter().position(|&c| c == id);
                let elem_only = key.contains("Element");
                let mut seq: Box<dyn Iterator<Item = NodeId>> = if key.starts_with("next") {
                    match pos {
                        Some(i) => Box::new(sibs.into_iter().skip(i + 1)),
                        None => Box::new(Vec::new().into_iter()),
                    }
                } else {
                    match pos {
                        Some(i) => Box::new(sibs.into_iter().take(i).rev()),
                        None => Box::new(Vec::new().into_iter()),
                    }
                };
                let pick = if elem_only {
                    let dom = self.dom_ref()?;
                    seq.find(|&c| matches!(dom.node(c).data, NodeData::Element(_)))
                } else {
                    seq.next()
                };
                return self.opt_node(pick);
            }
            _ => {}
        }
        match self.dom_ref()?.node(id).data {
            NodeData::Document => match key {
                "documentElement" => {
                    let n = {
                        let d = self.dom_ref()?;
                        if id == d.root() {
                            doc_element(d)
                        } else {
                            first_desc_tag(d, id, "html").or_else(|| {
                                d.children(id).iter().copied().find(|&c| {
                                    matches!(d.node(c).data, NodeData::Element(_))
                                })
                            })
                        }
                    };
                    self.opt_node(n)
                }
                "body" => {
                    let n = {
                        let d = self.dom_ref()?;
                        if id == d.root() {
                            first_tag(d, "body").or_else(|| doc_element(d))
                        } else {
                            first_desc_tag(d, id, "body")
                        }
                    };
                    self.opt_node(n)
                }
                "head" => {
                    let n = {
                        let d = self.dom_ref()?;
                        if id == d.root() {
                            first_tag(d, "head").or_else(|| doc_element(d))
                        } else {
                            first_desc_tag(d, id, "head")
                        }
                    };
                    self.opt_node(n)
                }
                "title" => {
                    let t = {
                        let d = self.dom_ref()?;
                        let te = if id == d.root() {
                            first_tag(d, "title")
                        } else {
                            first_desc_tag(d, id, "title")
                        };
                        te.map(|n| vigia_actions::text_content(d, n))
                            .unwrap_or_default()
                    };
                    self.str_val(t)
                }
                "textContent" => Ok(Value::Null),
                "implementation" => self.impl_obj(),
                "currentScript" => self.opt_node(self.cur_script),
                "compatMode" => self.str_val("CSS1Compat".into()),
                "characterSet" => self.str_val("UTF-8".into()),
                "contentType" => self.str_val("text/html".into()),
                "referrer" => self.str_val(String::new()),
                "hidden" => Ok(Value::Bool(false)),
                "visibilityState" => self.str_val("visible".into()),
                "designMode" => self.str_val("off".into()),
                "domain" => {
                    let h = match self.env_get(0, "location") {
                        Some(loc) => match get_prop(&self.heap, &self.protos, loc, "hostname") {
                            Ok(Value::Str(id)) => self.heap.get_str(id).to_string(),
                            _ => String::new(),
                        },
                        None => String::new(),
                    };
                    self.str_val(h)
                }
                "activeElement" => {
                    let n = {
                        let d = self.dom_ref()?;
                        first_tag(d, "body")
                    };
                    self.opt_node(n)
                }
                "scrollingElement" => {
                    let n = doc_element(self.dom_ref()?);
                    self.opt_node(n)
                }
                "cookie" => {
                    // document.cookie: jar view minus HttpOnly. Page URL
                    // prefers the net ctx base, else the live location.
                    let url = self
                        .net
                        .as_ref()
                        .map(|c| c.base.clone())
                        .or_else(|| {
                            self.env_get(0, "location").and_then(|loc| {
                                match get_prop(&self.heap, &self.protos, loc, "href") {
                                    Ok(Value::Str(id)) => {
                                        vigia_url::Url::parse(self.heap.get_str(id)).ok()
                                    }
                                    _ => None,
                                }
                            })
                        });
                    match (url, self.net.as_ref()) {
                        (Some(u), Some(ctx)) => {
                            let s = ctx.jar.cookies_for_js(&u);
                            self.str_val(s)
                        }
                        _ => self.str_val(String::new()),
                    }
                }
                "styleSheets" => {
                    // One facade per <style> (+stylesheet <link>), arena
                    // order; link rules stay empty (no fetching).
                    let ids: Vec<NodeId> = {
                        let d = self.dom_ref()?;
                        (1..d.nodes.len() as NodeId)
                            .filter(|&i| {
                                d.tag_name(i).is_some_and(|t| {
                                    t == "style"
                                        || (t == "link"
                                            && d.attr(i, "rel").is_some_and(|r| {
                                                r.split_whitespace().any(|w| {
                                                    w.eq_ignore_ascii_case("stylesheet")
                                                })
                                            }))
                                }) && is_desc(d, 0, i)
                            })
                            .collect()
                    };
                    let mut out = Vec::with_capacity(ids.len());
                    for n in ids {
                        out.push(self.sheet_for(n)?);
                    }
                    Ok(Value::Obj(self.arr_obj(out)?))
                }
                "defaultView" => {
                    // The window the document belongs to (single page here).
                    Ok(self.env_get(0, "window").unwrap_or(Value::Undef))
                }
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
            NodeData::Fragment => match key {
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
                "nodeName" => self.str_val("#document-fragment".into()),
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
                "width" | "height" => {
                    // Canvas defaults (300x150 like V8); other tags only
                    // reflect an explicit attribute.
                    let (tag, a) = {
                        let d = self.dom_ref()?;
                        (
                            d.tag_name(id).unwrap_or("").to_string(),
                            d.attr(id, key).unwrap_or("").to_string(),
                        )
                    };
                    if !a.is_empty() {
                        match a.parse::<f64>() {
                            Ok(n) => Ok(Value::Num(n)),
                            Err(_) => Ok(Value::Undef),
                        }
                    } else if tag == "canvas" {
                        Ok(Value::Num(if key == "width" { 300.0 } else { 150.0 }))
                    } else {
                        Ok(Value::Undef)
                    }
                },
                "style" => {
                    let s = self.heap.alloc_obj(Obj::Style { node: id })?;
                    Ok(Value::Obj(s))
                }
                "classList" => self.class_list_for(id),
                "checked" => Ok(Value::Bool(self.dom_ref()?.attr(id, "checked").is_some())),
                "disabled" => Ok(Value::Bool(self.dom_ref()?.attr(id, "disabled").is_some())),
                "sheet" => match self.dom_ref()?.tag_name(id) {
                    Some("style") | Some("link") => self.sheet_for(id),
                    _ => Ok(Value::Null),
                },
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
            if key == "cookie" {
                // document.cookie = "k=v; expires=...; path=/...": store
                // into the page jar (Set-Cookie shape). No jar without a
                // net context (bare runs) - sloppy no-op there.
                let s = to_str(&self.heap, v);
                let base = self.net.as_ref().map(|c| c.base.clone());
                if let (Some(u), Some(ctx)) = (base, self.net.as_mut()) {
                    ctx.jar.store_header(&u, &s);
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
            "width" | "height" => {
                // Reflected dimension (canvas/img): stored as attribute.
                let tag = self.dom_ref()?.tag_name(id).unwrap_or("").to_string();
                if tag == "canvas" || tag == "img" {
                    let n = to_num(&self.heap, v);
                    if !n.is_nan() {
                        let _ = self
                            .dom_mut()?
                            .set_attr(id, key, &format!("{}", n.max(0.0) as u32));
                    }
                    // Resizing a canvas clears it (even to the same size);
                    // drop the buffer so ops lazily rebuild it transparent.
                    // setAttribute bypasses this and only takes effect via
                    // the size check in canvas_ensure (documented gap).
                    if tag == "canvas" {
                        self.canvases.remove(&id);
                    }
                }
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
    /// Fallback for DOM method calls the direct dispatch doesn't know:
    /// resolve `name` on the wrapper's prototype chain (constructor,
    /// hasOwnProperty, inherited bag methods) and call it with the
    /// wrapper as receiver. None when absent (the caller errors).
    fn dom_proto_call(
        &mut self,
        id: NodeId,
        name: &str,
        args: &[Value],
    ) -> Result<Option<Value>, JsError> {
        use crate::eval::walk_props;
        let Some(&w) = self.dom_objs.get(&id) else {
            return Ok(None);
        };
        let p = match self.heap.obj(w) {
            Obj::Dom { proto, .. } => *proto,
            _ => None,
        };
        let Some(p) = p else { return Ok(None) };
        let f = walk_props(&self.heap, &self.protos, Some(p), name)?;
        match f {
            Value::Undef => Ok(None),
            _ => Ok(Some(self.call_value(f, Value::Obj(w), args, Some(name))?)),
        }
    }

    pub(crate) fn call_dom(
        &mut self,
        id: NodeId,
        name: &str,
        env: u32,
        arg_es: &[Expr],
    ) -> Result<Value, JsError> {
        let args = self.eval_args(env, arg_es)?;
        self.call_dom_vals(id, name, &args)
    }

    /// DOM method call with already-evaluated args (shared by the direct
    /// dispatch and the prototype-bag natives, so `document.createElement`
    /// also resolves as a value).
    pub(crate) fn call_dom_vals(
        &mut self,
        id: NodeId,
        name: &str,
        args: &[Value],
    ) -> Result<Value, JsError> {
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
                "getElementsByClassName" => {
                    let want = to_str(&self.heap, arg(0));
                    let ids: Vec<NodeId> = {
                        let d = self.dom_ref()?;
                        (1..d.nodes.len() as NodeId)
                            .filter(|&i| {
                                matches!(d.node(i).data, NodeData::Element(_))
                                    && is_desc(d, 0, i)
                                    && d.attr(i, "class").is_some_and(|c| {
                                        c.split_whitespace().any(|w| w == want)
                                    })
                            })
                            .collect()
                    };
                    self.node_arr(ids)
                }
                "getElementsByName" => {
                    let want = to_str(&self.heap, arg(0));
                    let ids: Vec<NodeId> = {
                        let d = self.dom_ref()?;
                        (1..d.nodes.len() as NodeId)
                            .filter(|&i| {
                                matches!(d.node(i).data, NodeData::Element(_))
                                    && is_desc(d, 0, i)
                                    && d.attr(i, "name") == Some(want.as_str())
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
                // Namespace ignored (HTML parser lowercases everything;
                // svg tags still answer SVGElement via dom_wrap).
                "createElementNS" => {
                    let tag = to_str(&self.heap, arg(1)).to_ascii_lowercase();
                    if tag.is_empty() {
                        return Err(err("createElementNS needs a tag"));
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
                "createTextNode" => {
                    let t = to_str(&self.heap, arg(0));
                    let n = self.dom_mut()?.text_node(&t);
                    self.dom_wrap(n)
                }
                "createDocumentFragment" => {
                    let n = self.dom_mut()?.fragment_node();
                    self.dom_wrap(n)
                }
                "createEvent" => {
                    let want = to_str(&self.heap, arg(0));
                    let kind = match want.as_str() {
                        "MouseEvents" => "MouseEvent",
                        "KeyboardEvent" | "KeyEvents" => "KeyboardEvent",
                        "CustomEvent" => "CustomEvent",
                        "Event" | "Events" | "HTMLEvents" | "UIEvents" => "Event",
                        _ => return Err(err(format!("createEvent: unknown type {want}"))),
                    };
                    blank_event(self, kind)
                }
                "implementation" => self.impl_obj(),
                "hasFocus" => Ok(Value::Bool(true)),
                "createComment" => {
                    let t = to_str(&self.heap, arg(0));
                    let n = self.dom_mut()?.comment_node(&t);
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
                _ => match self.dom_proto_call(id, name, &args)? {
                    Some(v) => Ok(v),
                    None => Err(err(format!("{name} is not a function"))),
                },
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
                // Fragments splice their children in (V8); the fragment
                // itself stays detached and is returned.
                if matches!(self.dom_ref()?.node(n).data, NodeData::Fragment) {
                    let kids: Vec<NodeId> = self.dom_ref()?.children(n).to_vec();
                    let dom = self.dom_mut()?;
                    for k in kids {
                        dom.detach(k);
                        dom.append_child_node(id, k);
                    }
                    return Ok(a);
                }
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
                if matches!(self.dom_ref()?.node(n).data, NodeData::Fragment) {
                    let kids: Vec<NodeId> = self.dom_ref()?.children(n).to_vec();
                    let dom = self.dom_mut()?;
                    for k in kids {
                        dom.detach(k);
                        dom.insert_before_node(id, k, before);
                    }
                    return Ok(a);
                }
                self.check_cycle(id, n, "insertBefore")?;
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
            "cloneNode" => {
                let deep = truthy(&self.heap, arg(0));
                let n = self.dom_mut()?.clone_node(id, deep);
                self.dom_wrap(n)
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
            "getContext" => {
                // Only <canvas> has it; anything else reads "not a
                // function". "2d" (default) yields the stub context;
                // webgl/others are null (no GPU backend here).
                if self.dom_ref()?.tag_name(id) != Some("canvas") {
                    return Err(err("getContext is not a function"));
                }
                let mode = to_str(&self.heap, arg(0)).to_ascii_lowercase();
                if mode == "2d" {
                    canvas_ctx2d(self, id)
                } else {
                    Ok(Value::Null)
                }
            }
            "toDataURL" => {
                if self.dom_ref()?.tag_name(id) != Some("canvas") {
                    return Err(err("toDataURL is not a function"));
                }
                let url = self.canvas_data_url(id)?;
                self.str_val(url)
            }
            "querySelector" => {
                let hits = self.select(id, arg(0))?;
                self.opt_node(hits.into_iter().next())
            }
            "querySelectorAll" => {
                let hits = self.select(id, arg(0))?;
                self.node_arr(hits)
            }
            "getElementsByTagName" => {
                let want = to_str(&self.heap, arg(0)).to_ascii_lowercase();
                let ids: Vec<NodeId> = {
                    let d = self.dom_ref()?;
                    (1..d.nodes.len() as NodeId)
                        .filter(|&i| {
                            matches!(d.node(i).data, NodeData::Element(_))
                                && is_desc(d, id, i)
                                && (want == "*" || d.tag_name(i) == Some(want.as_str()))
                        })
                        .collect()
                };
                self.node_arr(ids)
            }
            "getElementsByClassName" => {
                let want = to_str(&self.heap, arg(0));
                let ids: Vec<NodeId> = {
                    let d = self.dom_ref()?;
                    (1..d.nodes.len() as NodeId)
                        .filter(|&i| {
                            matches!(d.node(i).data, NodeData::Element(_))
                                && is_desc(d, id, i)
                                && d.attr(i, "class").is_some_and(|c| {
                                    c.split_whitespace().any(|w| w == want)
                                })
                        })
                        .collect()
                };
                self.node_arr(ids)
            }
            "contains" => {
                // Node.contains: self or a descendant (non-nodes: false).
                let hit = match self.as_node(arg(0)) {
                    Some(o) => id == o || is_desc(self.dom_ref()?, id, o),
                    None => false,
                };
                Ok(Value::Bool(hit))
            }
            "matches" => {
                if !matches!(self.dom_ref()?.node(id).data, NodeData::Element(_)) {
                    return Err(err("matches is not a function"));
                }
                let sel = to_str(&self.heap, arg(0));
                let dom = self.dom_ref()?;
                let hits = vigia_css::query(dom, &sel).map_err(|e| err(e.to_string()))?;
                Ok(Value::Bool(hits.contains(&id)))
            }
            "closest" => {
                if !matches!(self.dom_ref()?.node(id).data, NodeData::Element(_)) {
                    return Err(err("closest is not a function"));
                }
                let sel = to_str(&self.heap, arg(0));
                let dom = self.dom_ref()?;
                let hits = vigia_css::query(dom, &sel).map_err(|e| err(e.to_string()))?;
                let mut cur = Some(id);
                let mut found = None;
                while let Some(c) = cur {
                    if matches!(self.dom_ref()?.node(c).data, NodeData::Element(_))
                        && hits.contains(&c)
                    {
                        found = Some(c);
                        break;
                    }
                    cur = self.dom_ref()?.parent(c);
                }
                self.opt_node(found)
            }
            "getBoundingClientRect" => {
                if !matches!(self.dom_ref()?.node(id).data, NodeData::Element(_)) {
                    return Err(err("getBoundingClientRect is not a function"));
                }
                // No layout engine: zero geometry (honest, documented).
                Ok(Value::Obj(zero_rect(self)?))
            }
            "getClientRects" => {
                if !matches!(self.dom_ref()?.node(id).data, NodeData::Element(_)) {
                    return Err(err("getClientRects is not a function"));
                }
                // Attached elements read as one (zero) rect, detached as
                // none - the V8 shape without a layout engine.
                if is_desc(self.dom_ref()?, 0, id) {
                    let r = Value::Obj(zero_rect(self)?);
                    Ok(Value::Obj(self.arr_obj(vec![r])?))
                } else {
                    Ok(Value::Obj(self.arr_obj(Vec::new())?))
                }
            }
            _ => match self.dom_proto_call(id, name, &args)? {
                Some(v) => Ok(v),
                None => Err(err(format!("{name} is not a function"))),
            },
        }
    }
}

// ---- event natives ------------------------------------------------------

/// document.implementation.createHTMLDocument(title?): detached html >
/// head (+title) + body in the page arena; subtree reads work on it while
/// root-scoped page queries skip it (detached).
fn n_create_html_doc(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let title = to_str(&it.heap, args.first().copied().unwrap_or(Value::Undef));
    let n = {
        let dom = it.dom_mut()?;
        let doc = dom.document_node();
        let html = dom.element(doc, "html", vec![]);
        let head = dom.element(html, "head", vec![]);
        if !title.is_empty() {
            let te = dom.element(head, "title", vec![]);
            dom.text(te, &title);
        }
        dom.element(html, "body", vec![]);
        doc
    };
    it.dom_wrap(n)
}

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

// ---- constructible events -----------------------------------------------

/// Extra-key value kinds for EVENT_EXTRAS.
const EV_NUM: u8 = 0;
const EV_BOOL: u8 = 1;
const EV_STR: u8 = 2;
const EV_VAL: u8 = 3;

/// Per-ctor extra keys from the init dict: (ctor, key, kind). NUM reads
/// to_num (default 0), BOOL reads truthy (default false), STR reads
/// to_str (default ""), VAL passes through (default null).
const EVENT_EXTRAS: &[(&str, &str, u8)] = &[
    ("CustomEvent", "detail", EV_VAL),
    ("MouseEvent", "screenX", EV_NUM),
    ("MouseEvent", "screenY", EV_NUM),
    ("MouseEvent", "clientX", EV_NUM),
    ("MouseEvent", "clientY", EV_NUM),
    ("MouseEvent", "ctrlKey", EV_BOOL),
    ("MouseEvent", "altKey", EV_BOOL),
    ("MouseEvent", "shiftKey", EV_BOOL),
    ("MouseEvent", "metaKey", EV_BOOL),
    ("MouseEvent", "button", EV_NUM),
    ("MouseEvent", "buttons", EV_NUM),
    ("MouseEvent", "relatedTarget", EV_VAL),
    ("KeyboardEvent", "key", EV_STR),
    ("KeyboardEvent", "code", EV_STR),
    ("KeyboardEvent", "keyCode", EV_NUM),
    ("KeyboardEvent", "which", EV_NUM),
    ("KeyboardEvent", "ctrlKey", EV_BOOL),
    ("KeyboardEvent", "altKey", EV_BOOL),
    ("KeyboardEvent", "shiftKey", EV_BOOL),
    ("KeyboardEvent", "metaKey", EV_BOOL),
    ("KeyboardEvent", "repeat", EV_BOOL),
    ("KeyboardEvent", "isComposing", EV_BOOL),
];

/// Proto bag for an event ctor name (unknown names fall back to Event).
fn event_bag(it: &Interp, kind: &str) -> u32 {
    match kind {
        "CustomEvent" => it.protos.custom_event,
        "MouseEvent" => it.protos.mouse_event,
        "KeyboardEvent" => it.protos.keyboard_event,
        _ => it.protos.event,
    }
}

/// One init-dict read per value kind (non-object init means all defaults;
/// absent keys also mean defaults).
fn init_flag(it: &Interp, init: Value, k: &str) -> bool {
    if !matches!(init, Value::Obj(_)) {
        return false;
    }
    match get_prop(&it.heap, &it.protos, init, k) {
        Ok(v) => truthy(&it.heap, v),
        Err(_) => false,
    }
}

fn init_num(it: &Interp, init: Value, k: &str) -> f64 {
    if !matches!(init, Value::Obj(_)) {
        return 0.0;
    }
    match get_prop(&it.heap, &it.protos, init, k) {
        Ok(Value::Undef) | Err(_) => 0.0,
        Ok(v) => to_num(&it.heap, v),
    }
}

fn init_str(it: &Interp, init: Value, k: &str) -> String {
    if !matches!(init, Value::Obj(_)) {
        return String::new();
    }
    match get_prop(&it.heap, &it.protos, init, k) {
        Ok(Value::Undef) | Err(_) => String::new(),
        Ok(v) => to_str(&it.heap, v),
    }
}

fn init_val(it: &Interp, init: Value, k: &str) -> Value {
    if !matches!(init, Value::Obj(_)) {
        return Value::Null;
    }
    match get_prop(&it.heap, &it.protos, init, k) {
        Ok(Value::Undef) | Err(_) => Value::Null,
        Ok(v) => v,
    }
}

/// Shared body for constructed and createEvent-blank events: base props
/// plus the ctor's table extras. Ordinary object, so dispatch fills the
/// dispatch-time props via normalize_event untouched.
fn event_fill(
    it: &mut Interp,
    target: Value,
    kind: &str,
    ty: &str,
    init: Value,
) -> Result<(), JsError> {
    let bubbles = init_flag(it, init, "bubbles");
    let cancelable = init_flag(it, init, "cancelable");
    let composed = init_flag(it, init, "composed");
    let stamp = it.perf_elapsed();
    let ty = Value::Str(it.heap.alloc_str(ty.to_string())?);
    set_prop(&mut it.heap, target, "type", ty)?;
    set_prop(&mut it.heap, target, "bubbles", Value::Bool(bubbles))?;
    set_prop(&mut it.heap, target, "cancelable", Value::Bool(cancelable))?;
    set_prop(&mut it.heap, target, "composed", Value::Bool(composed))?;
    set_prop(&mut it.heap, target, "timeStamp", Value::Num(stamp))?;
    for (k, key, ek) in EVENT_EXTRAS {
        if *k != kind {
            continue;
        }
        let v = match ek {
            &EV_NUM => Value::Num(init_num(it, init, key)),
            &EV_BOOL => Value::Bool(init_flag(it, init, key)),
            &EV_STR => Value::Str(it.heap.alloc_str(init_str(it, init, key))?),
            _ => init_val(it, init, key),
        };
        set_prop(&mut it.heap, target, key, v)?;
    }
    if kind == "MouseEvent" || kind == "KeyboardEvent" {
        let m = Value::Obj(it.heap.alloc_obj(nat("getModifierState", n_event_mod_state))?);
        set_prop(&mut it.heap, target, "getModifierState", m)?;
    }
    Ok(())
}

/// getModifierState on mouse/keyboard events: modifier keys read live
/// off the event, every other key false; never throws.
fn n_event_mod_state(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let Value::Str(id) = arg(args, 0) else {
        return Ok(Value::Bool(false));
    };
    let prop = match it.heap.get_str(id) {
        "Control" => "ctrlKey",
        "Alt" => "altKey",
        "Shift" => "shiftKey",
        "Meta" => "metaKey",
        _ => return Ok(Value::Bool(false)),
    };
    match get_prop(&it.heap, &it.protos, this, prop) {
        Ok(v) => Ok(Value::Bool(truthy(&it.heap, v))),
        Err(_) => Ok(Value::Bool(false)),
    }
}

/// `new Event/CustomEvent/MouseEvent/KeyboardEvent(type, init?)`: one
/// native dispatching on its own name. `this` from `new` already carries
/// the ctor's prototype; bare calls allocate under it.
pub(crate) fn n_event_ctor(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let kind = match it.cur_native {
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::Native { name, .. } => *name,
            _ => "?",
        },
        _ => "?",
    };
    let t = args.first().copied().unwrap_or(Value::Undef);
    if matches!(t, Value::Undef) {
        return Err(err("Event needs a type"));
    }
    let ty = to_str(&it.heap, t);
    let init = args.get(1).copied().unwrap_or(Value::Undef);
    let target = match this {
        Value::Obj(_) => this,
        _ => {
            let proto = po(event_bag(it, kind));
            Value::Obj(it.heap.alloc_obj(Obj::Ordinary {
                pairs: Vec::new(),
                proto,
            })?)
        }
    };
    event_fill(it, target, kind, &ty, init)?;
    Ok(target)
}

/// Blank event for document.createEvent, with an initEvent native that
/// mutates type/bubbles/cancelable in place.
fn blank_event(it: &mut Interp, kind: &str) -> Result<Value, JsError> {
    let proto = po(event_bag(it, kind));
    let target = Value::Obj(it.heap.alloc_obj(Obj::Ordinary {
        pairs: Vec::new(),
        proto,
    })?);
    event_fill(it, target, kind, "", Value::Undef)?;
    let m = Value::Obj(it.heap.alloc_obj(nat("initEvent", n_event_init))?);
    set_prop(&mut it.heap, target, "initEvent", m)?;
    Ok(target)
}

fn n_event_init(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    if !matches!(this, Value::Obj(_)) {
        return Err(err("initEvent needs an event"));
    }
    let t = to_str(&it.heap, args.first().copied().unwrap_or(Value::Undef));
    let b = truthy(&it.heap, args.get(1).copied().unwrap_or(Value::Undef));
    let c = truthy(&it.heap, args.get(2).copied().unwrap_or(Value::Undef));
    let t = Value::Str(it.heap.alloc_str(t)?);
    set_prop(&mut it.heap, this, "type", t)?;
    set_prop(&mut it.heap, this, "bubbles", Value::Bool(b))?;
    set_prop(&mut it.heap, this, "cancelable", Value::Bool(c))?;
    Ok(Value::Undef)
}

/// Prototype-bag DOM methods (so `document.createElement` also resolves
/// as a value, like V8): re-dispatch by the native's own name with the
/// receiver node. Unknown names still fail at call time.
pub(crate) fn n_dom_method(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {    let name = match it.cur_native {
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::Native { name, .. } => *name,
            _ => "?",
        },
        _ => "?",
    };
    let Some(n) = it.as_node(this) else {
        return Err(err("DOM method needs a node receiver"));
    };
    it.call_dom_vals(n, name, args)
}

// ---- canvas -------------------------------------------------------------
// Software 2d rasterizer: real RGBA pixels behind the ctx stub so
// feature-detects and pixel reads behave. Paths, text, gradients and
// shadows stay no-ops (their method names remain wired so pages that
// stringify natives still see them).

/// Live pixel buffer of one canvas node (RGBA, row-major).
#[derive(Clone, Default)]
pub(crate) struct CanvasBuf {
    w: u32,
    h: u32,
    px: Vec<u8>,
}

/// Per-canvas pixel budget: getContext('2d') throws past this instead of
/// allocating (a 10000x10000 fingerprint probe must fail, not OOM).
const CANVAS_MAX_AREA: u64 = 16 * 1024 * 1024;

/// Canvas dimension from the live attr, mirroring dom_get (300x150
/// defaults, invalid text falls back to the default, negatives clamp).
fn canvas_dim(dom: &Dom, node: NodeId, key: &str, def: u32) -> u32 {
    match dom.attr(node, key).unwrap_or("") {
        "" => def,
        a => match a.parse::<f64>() {
            Ok(n) if !n.is_nan() => n.max(0.0).min(u32::MAX as f64) as u32,
            _ => def,
        },
    }
}

/// Ensure a transparent buffer matching the live attrs. Rebuilds when the
/// size drifted (e.g. via setAttribute, which bypasses dom_set); throws a
/// RangeError-style error past the area cap instead of allocating.
fn canvas_ensure(it: &mut Interp, node: NodeId) -> Result<(), JsError> {
    let (w, h) = {
        let d = it.dom_ref()?;
        (
            canvas_dim(d, node, "width", 300),
            canvas_dim(d, node, "height", 150),
        )
    };
    if w as u64 * h as u64 > CANVAS_MAX_AREA {
        return Err(err("RangeError: canvas area over the 16M pixel budget"));
    }
    let fresh = match it.canvases.get(&node) {
        Some(b) if b.w == w && b.h == h => false,
        _ => true,
    };
    if fresh {
        it.canvases.insert(
            node,
            CanvasBuf {
                w,
                h,
                px: vec![0; w as usize * h as usize * 4],
            },
        );
    }
    Ok(())
}

/// Canvas node behind a ctx call: carried on the method native itself
/// (token_lists pattern), falling back to the ctx object's own marker so
/// detached method refs still resolve.
fn ctx_node(it: &Interp, this: Value) -> Option<NodeId> {
    for v in [it.cur_native, this] {
        if let Ok(Value::Num(n)) = get_prop(&it.heap, &it.protos, v, "__node") {
            return Some(n as NodeId);
        }
    }
    None
}

/// Validated style string stored under the hidden key (`__fillStyle` /
/// `__strokeStyle`), parsed fresh on every fill. Absent/unparseable falls
/// back to opaque black (the setter only stores valid colors, so the
/// fallback only fires for detached-`this` calls).
fn ctx_color(it: &Interp, this: Value, hidden: &str) -> [u8; 4] {
    match get_prop(&it.heap, &it.protos, this, hidden) {
        Ok(Value::Str(id)) => parse_color(it.heap.get_str(id)).unwrap_or([0, 0, 0, 255]),
        _ => [0, 0, 0, 255],
    }
}

/// Clip a float rect to the buffer; None = empty or non-finite (no-op).
fn rect_clip(bw: u32, bh: u32, x: f64, y: f64, w: f64, h: f64) -> Option<(u32, u32, u32, u32)> {
    if !(x.is_finite() && y.is_finite() && w.is_finite() && h.is_finite()) {
        return None;
    }
    let (x0, y0, w0, h0) = (x.trunc() as i64, y.trunc() as i64, w.trunc() as i64, h.trunc() as i64);
    if w0 <= 0 || h0 <= 0 {
        return None;
    }
    let (cx0, cy0) = (x0.max(0), y0.max(0));
    let (cx1, cy1) = ((x0 + w0).min(bw as i64), (y0 + h0).min(bh as i64));
    if cx1 <= cx0 || cy1 <= cy0 {
        return None;
    }
    Some((cx0 as u32, cy0 as u32, cx1 as u32, cy1 as u32))
}

fn hex_nybble(c: u8) -> Option<u8> {
    match c {
        b'0'..=b'9' => Some(c - b'0'),
        b'a'..=b'f' => Some(c - b'a' + 10),
        b'A'..=b'F' => Some(c - b'A' + 10),
        _ => None,
    }
}

/// CSS color subset: #rgb, #rrggbb, #rrggbbaa, rgb()/rgba() in comma or
/// space syntax (channels 0-255 clamped, alpha 0-1), the 16 basic named
/// colors plus transparent. Anything else is invalid (a fillStyle=
/// assignment of it is ignored, like V8).
fn parse_color(s: &str) -> Option<[u8; 4]> {
    let t = s.trim();
    if let Some(h) = t.strip_prefix('#') {
        let b = h.as_bytes();
        let pair = |i: usize| Some(hex_nybble(b[i])? * 16 + hex_nybble(b[i + 1])?);
        return match b.len() {
            3 => Some([
                hex_nybble(b[0])? * 17,
                hex_nybble(b[1])? * 17,
                hex_nybble(b[2])? * 17,
                255,
            ]),
            6 => Some([pair(0)?, pair(2)?, pair(4)?, 255]),
            8 => Some([pair(0)?, pair(2)?, pair(4)?, pair(6)?]),
            _ => None,
        };
    }
    let low = t.to_ascii_lowercase();
    let inner = if let Some(r) = low.strip_prefix("rgba(") {
        r.strip_suffix(')')?
    } else if let Some(r) = low.strip_prefix("rgb(") {
        r.strip_suffix(')')?
    } else {
        return match low.as_str() {
            "black" => Some([0, 0, 0, 255]),
            "silver" => Some([192, 192, 192, 255]),
            "gray" | "grey" => Some([128, 128, 128, 255]),
            "white" => Some([255, 255, 255, 255]),
            "maroon" => Some([128, 0, 0, 255]),
            "red" => Some([255, 0, 0, 255]),
            "purple" => Some([128, 0, 128, 255]),
            "fuchsia" => Some([255, 0, 255, 255]),
            "green" => Some([0, 128, 0, 255]),
            "lime" => Some([0, 255, 0, 255]),
            "olive" => Some([128, 128, 0, 255]),
            "yellow" => Some([255, 255, 0, 255]),
            "navy" => Some([0, 0, 128, 255]),
            "blue" => Some([0, 0, 255, 255]),
            "teal" => Some([0, 128, 128, 255]),
            "aqua" => Some([0, 255, 255, 255]),
            "transparent" => Some([0, 0, 0, 0]),
            _ => None,
        };
    };
    // Slash alpha (`rgb(1 2 3 / .5)`) normalizes to a plain 4th part.
    let spaced = inner.replace('/', " ");
    let parts: Vec<&str> = if inner.contains(',') {
        inner.split(',').map(str::trim).collect()
    } else {
        spaced.split_whitespace().collect()
    };
    if parts.len() != 3 && parts.len() != 4 {
        return None;
    }
    let ch = |p: &str| {
        let n: f64 = p.parse().ok()?;
        if !n.is_finite() {
            return None;
        }
        Some(n.round().clamp(0.0, 255.0) as u8)
    };
    let a = match parts.get(3) {
        None => 255,
        Some(p) => {
            let n: f64 = p.parse().ok()?;
            if !n.is_finite() {
                return None;
            }
            (n.clamp(0.0, 1.0) * 255.0).round() as u8
        }
    };
    Some([ch(parts[0])?, ch(parts[1])?, ch(parts[2])?, a])
}

/// 2d context for a canvas node, cached per node for === identity.
/// fillStyle/strokeStyle are validating accessors (invalid assignments
/// ignored, like V8) over hidden `__fillStyle`/`__strokeStyle` expandos;
/// fill ops re-parse those each call. Everything not drawing pixels stays
/// on the pre-existing noop.
fn canvas_ctx2d(it: &mut Interp, node: NodeId) -> Result<Value, JsError> {
    if let Some(&o) = it.ctx2ds.get(&node) {
        return Ok(Value::Obj(o));
    }
    let (w, h) = {
        let d = it.dom_ref()?;
        (
            canvas_dim(d, node, "width", 300),
            canvas_dim(d, node, "height", 150),
        )
    };
    if w as u64 * h as u64 > CANVAS_MAX_AREA {
        return Err(err("RangeError: canvas area over the 16M pixel budget"));
    }
    let mut pairs: Vec<(String, Value)> = Vec::new();
    for (n, f) in [
        ("fillRect", n_ctx_fill_rect as NativeFn),
        ("clearRect", n_ctx_clear_rect),
        ("strokeRect", n_ctx_noop),
        ("fillText", n_ctx_noop),
        ("strokeText", n_ctx_noop),
        ("drawImage", n_ctx_draw_image),
        ("putImageData", n_ctx_put_image),
        ("beginPath", n_ctx_noop),
        ("closePath", n_ctx_noop),
        ("moveTo", n_ctx_noop),
        ("lineTo", n_ctx_noop),
        ("arc", n_ctx_noop),
        ("rect", n_ctx_noop),
        ("fill", n_ctx_noop),
        ("stroke", n_ctx_noop),
        ("clip", n_ctx_noop),
        ("save", n_ctx_noop),
        ("restore", n_ctx_noop),
        ("translate", n_ctx_noop),
        ("scale", n_ctx_noop),
        ("rotate", n_ctx_noop),
        ("setTransform", n_ctx_noop),
        ("transform", n_ctx_noop),
        ("measureText", n_ctx_measure),
        ("getImageData", n_ctx_get_image_data),
        ("createImageData", n_ctx_create_image_data),
        ("createLinearGradient", n_ctx_gradient),
        ("createRadialGradient", n_ctx_gradient),
        ("createPattern", n_ctx_pattern),
    ] {
        let m = it.heap.alloc_obj(nat(n, f))?;
        let _ = set_prop(&mut it.heap, Value::Obj(m), "__node", Value::Num(node as f64));
        pairs.push((n.into(), Value::Obj(m)));
    }
    let o = it.obj_pairs(pairs)?;
    // Validating style accessors (invoke_getter/invoke_setter run these on
    // read/write); the validated string persists on a hidden expando.
    for key in ["fillStyle", "strokeStyle"] {
        let g = it.heap.alloc_obj(nat(key, n_ctx_style_get))?;
        let s = it.heap.alloc_obj(nat(key, n_ctx_style_set))?;
        let proto = po(it.protos.object);
        let acc = it
            .heap
            .alloc_obj(Obj::Accessor { get: Some(g), set: Some(s), proto })?;
        if let Obj::Ordinary { pairs, .. } = it.heap.obj_mut(o) {
            pairs.push((key.into(), Value::Obj(acc)));
        }
    }
    let _ = set_prop(&mut it.heap, Value::Obj(o), "__node", Value::Num(node as f64));
    // ctx.canvas backref (wraps the same node, identity preserved).
    if let Ok(w) = it.dom_wrap(node) {
        let _ = set_prop(&mut it.heap, Value::Obj(o), "canvas", w);
    }
    it.ctx2ds.insert(node, o);
    Ok(Value::Obj(o))
}

/// fillStyle/strokeStyle getter: hidden validated value or "#000000".
/// The key comes from the native's own name (one fn serves both).
fn n_ctx_style_get(it: &mut Interp, this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let name = match it.cur_native {
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::Native { name, .. } => *name,
            _ => "fillStyle",
        },
        _ => "fillStyle",
    };
    let key = format!("__{name}");
    match get_prop(&it.heap, &it.protos, this, &key) {
        Ok(Value::Str(id)) => Ok(Value::Str(id)),
        _ => Ok(Value::Str(it.heap.alloc_str("#000000".into())?)),
    }
}

/// fillStyle/strokeStyle setter: stores only valid colors, ignores the
/// rest (V8 keeps the old value on invalid assignment).
fn n_ctx_style_set(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let name = match it.cur_native {
        Value::Obj(id) => match it.heap.obj(id) {
            Obj::Native { name, .. } => *name,
            _ => "fillStyle",
        },
        _ => "fillStyle",
    };
    let raw = to_str(&it.heap, args.first().copied().unwrap_or(Value::Undef));
    if parse_color(&raw).is_some() {
        let key = format!("__{name}");
        let id = it.heap.alloc_str(raw)?;
        set_prop(&mut it.heap, this, &key, Value::Str(id))?;
    }
    Ok(Value::Undef)
}

fn n_ctx_fill_rect(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let Some(node) = ctx_node(it, this) else {
        return Ok(Value::Undef);
    };
    let nums: Vec<f64> = (0..4)
        .map(|i| to_num(&it.heap, args.get(i).copied().unwrap_or(Value::Undef)))
        .collect();
    let color = ctx_color(it, this, "__fillStyle");
    canvas_ensure(it, node)?;
    if let Some((x0, y0, x1, y1)) = rect_clip(
        it.canvases.get(&node).map(|b| b.w).unwrap_or(0),
        it.canvases.get(&node).map(|b| b.h).unwrap_or(0),
        nums[0], nums[1], nums[2], nums[3],
    ) {
        if let Some(b) = it.canvases.get_mut(&node) {
            let w = b.w as usize;
            for y in y0 as usize..y1 as usize {
                let base = y * w * 4;
                for px in b.px[base + x0 as usize * 4..base + x1 as usize * 4].chunks_exact_mut(4) {
                    px.copy_from_slice(&color);
                }
            }
        }
    }
    Ok(Value::Undef)
}

fn n_ctx_clear_rect(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let Some(node) = ctx_node(it, this) else {
        return Ok(Value::Undef);
    };
    let nums: Vec<f64> = (0..4)
        .map(|i| to_num(&it.heap, args.get(i).copied().unwrap_or(Value::Undef)))
        .collect();
    canvas_ensure(it, node)?;
    if let Some((x0, y0, x1, y1)) = rect_clip(
        it.canvases.get(&node).map(|b| b.w).unwrap_or(0),
        it.canvases.get(&node).map(|b| b.h).unwrap_or(0),
        nums[0], nums[1], nums[2], nums[3],
    ) {
        if let Some(b) = it.canvases.get_mut(&node) {
            let w = b.w as usize;
            for y in y0 as usize..y1 as usize {
                let base = y * w * 4;
                for px in b.px[base + x0 as usize * 4..base + x1 as usize * 4].chunks_exact_mut(4) {
                    px.copy_from_slice(&[0, 0, 0, 0]);
                }
            }
        }
    }
    Ok(Value::Undef)
}

fn n_ctx_noop(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let _ = it;
    Ok(Value::Undef)
}

/// measureText(): zero-width metrics (no font engine behind it).
fn n_ctx_measure(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    Ok(Value::Obj(it.obj_pairs(vec![(
        "width".into(),
        Value::Num(0.0),
    )])?))
}

/// drawImage canvas-source only (img/video sources have no decoder here,
/// so they no-op): 3-arg blit, 5-arg nearest-neighbor scale, 9-arg
/// source-rect + scale. Out-of-range source pixels clip (dest untouched);
/// negative dest sizes mirror; non-positive source sizes no-op.
fn n_ctx_draw_image(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let Some(dst_node) = ctx_node(it, this) else {
        return Ok(Value::Undef);
    };
    let num = |i: usize| to_num(&it.heap, args.get(i).copied().unwrap_or(Value::Undef));
    let (sx, sy, sw, sh, dx, dy, dw, dh) = match args.len() {
        3 => (0.0, 0.0, 0.0, 0.0, num(1), num(2), 0.0, 0.0),
        5 => (0.0, 0.0, 0.0, 0.0, num(1), num(2), num(3), num(4)),
        9 => (num(1), num(2), num(3), num(4), num(5), num(6), num(7), num(8)),
        _ => return Err(err("drawImage needs 3, 5 or 9 arguments")),
    };
    let src_node = match it.as_node(args.first().copied().unwrap_or(Value::Undef)) {
        Some(n) if it.dom_ref().map(|d| d.tag_name(n) == Some("canvas")).unwrap_or(false) => n,
        _ => return Ok(Value::Undef),
    };
    canvas_ensure(it, src_node)?;
    canvas_ensure(it, dst_node)?;
    // Snapshot the source: self-draws must read pre-blit pixels, and two
    // HashMap entries cannot borrow mutably at once.
    let (src_w, src_h, src_px) = match it.canvases.get(&src_node) {
        Some(b) => (b.w, b.h, b.px.clone()),
        None => return Ok(Value::Undef),
    };
    let (mut sx, mut sy, mut sw, mut sh) = (
        sx.trunc() as i64,
        sy.trunc() as i64,
        sw.trunc() as i64,
        sh.trunc() as i64,
    );
    let (dx, dy, mut dw, mut dh) = (dx.trunc() as i64, dy.trunc() as i64, dw.trunc() as i64, dh.trunc() as i64);
    if args.len() <= 5 {
        // Natural size (3-arg) or full-source scale (5-arg).
        sx = 0;
        sy = 0;
        sw = src_w as i64;
        sh = src_h as i64;
        if args.len() == 3 {
            dw = sw;
            dh = sh;
        }
    }
    if sw <= 0 || sh <= 0 || dw == 0 || dh == 0 {
        return Ok(Value::Undef);
    }
    let Some(dst) = it.canvases.get_mut(&dst_node) else {
        return Ok(Value::Undef);
    };
    // Dest iteration range clipped to the buffer so huge scales cannot
    // spin; per-pixel source bounds checks do the source-side clipping.
    let (adw, adh) = (dw.abs(), dh.abs());
    let (mut i0, mut i1) = (0i64, adw);
    let (mut j0, mut j1) = (0i64, adh);
    if dw > 0 {
        i1 = i1.min(dst.w as i64 - dx);
        i0 = i0.max(-dx);
    } else {
        i1 = i1.min(dx + 1);
        i0 = i0.max(dx - dst.w as i64 + 1);
    }
    if dh > 0 {
        j1 = j1.min(dst.h as i64 - dy);
        j0 = j0.max(-dy);
    } else {
        j1 = j1.min(dy + 1);
        j0 = j0.max(dy - dst.h as i64 + 1);
    }
    if i1 <= i0 || j1 <= j0 {
        return Ok(Value::Undef);
    }
    let dwid = dst.w as usize;
    for j in j0..j1 {
        let py = if dh > 0 { dy + j } else { dy - j };
        let qy = sy + j * sh / adh;
        if qy < 0 || qy >= src_h as i64 {
            continue;
        }
        for i in i0..i1 {
            let px = if dw > 0 { dx + i } else { dx - i };
            let qx = sx + i * sw / adw;
            if qx < 0 || qx >= src_w as i64 {
                continue;
            }
            let s = (qy as usize * src_w as usize + qx as usize) * 4;
            let d = (py as usize * dwid + px as usize) * 4;
            dst.px[d..d + 4].copy_from_slice(&src_px[s..s + 4]);
        }
    }
    Ok(Value::Undef)
}

/// ImageData {width,height,data} builder shared by get/put/create paths.
fn image_data_obj(it: &mut Interp, w: u32, h: u32, px: &[u8]) -> Result<Value, JsError> {
    let items: Vec<Value> = px.iter().map(|b| Value::Num(*b as f64)).collect();
    let data = Value::Obj(it.arr_obj(items)?);
    Ok(Value::Obj(it.obj_pairs(vec![
        ("width".into(), Value::Num(w as f64)),
        ("height".into(), Value::Num(h as f64)),
        ("data".into(), data),
    ])?))
}

/// getImageData(x,y,w,h): real clipped pixels, data a plain Array of
/// numbers. Zero/negative sizes and fully-outside rects throw like V8.
fn n_ctx_get_image_data(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let Some(node) = ctx_node(it, this) else {
        return Err(err("getImageData needs a 2d context"));
    };
    let num = |i: usize| to_num(&it.heap, args.get(i).copied().unwrap_or(Value::Undef));
    let (sx, sy, sw, sh) = (num(0).trunc() as i64, num(1).trunc() as i64, num(2), num(3));
    if !sw.is_finite() || !sh.is_finite() || sw <= 0.0 || sh <= 0.0 {
        return Err(err("IndexSizeError: getImageData size must be positive"));
    }
    canvas_ensure(it, node)?;
    let (bw, bh, px) = match it.canvases.get(&node) {
        Some(b) => (b.w as i64, b.h as i64, b.px.clone()),
        None => return Err(err("IndexSizeError: getImageData outside the canvas")),
    };
    let (x0, y0) = (sx.max(0), sy.max(0));
    let (x1, y1) = ((sx + sw as i64).min(bw), (sy + sh as i64).min(bh));
    if x1 <= x0 || y1 <= y0 {
        return Err(err("IndexSizeError: getImageData outside the canvas"));
    }
    let mut out = Vec::with_capacity((x1 - x0) as usize * (y1 - y0) as usize * 4);
    for y in y0..y1 {
        let base = y as usize * bw as usize * 4;
        out.extend_from_slice(&px[base + x0 as usize * 4..base + x1 as usize * 4]);
    }
    image_data_obj(it, (x1 - x0) as u32, (y1 - y0) as u32, &out)
}

/// putImageData(img,dx,dy,...): blits all of img at (dx,dy), clipped to
/// the buffer. The dirty-rect form is accepted and ignored (full blit).
fn n_ctx_put_image(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let Some(node) = ctx_node(it, this) else {
        return Ok(Value::Undef);
    };
    let img = args.first().copied().unwrap_or(Value::Undef);
    let num = |i: usize| to_num(&it.heap, args.get(i).copied().unwrap_or(Value::Undef));
    let (dx, dy) = (num(1).trunc() as i64, num(2).trunc() as i64);
    let iw = match get_prop(&it.heap, &it.protos, img, "width") {
        Ok(v) => to_num(&it.heap, v).trunc() as i64,
        Err(_) => return Err(err("putImageData needs ImageData")),
    };
    let ih = match get_prop(&it.heap, &it.protos, img, "height") {
        Ok(v) => to_num(&it.heap, v).trunc() as i64,
        Err(_) => return Err(err("putImageData needs ImageData")),
    };
    let items: Vec<Value> = match get_prop(&it.heap, &it.protos, img, "data") {
        Ok(Value::Obj(id)) => match it.heap.obj(id) {
            Obj::Arr { items, .. } => items.clone(),
            _ => return Err(err("putImageData needs ImageData")),
        },
        _ => return Err(err("putImageData needs ImageData")),
    };
    if iw <= 0 || ih <= 0 {
        return Ok(Value::Undef);
    }
    canvas_ensure(it, node)?;
    let Some(dst) = it.canvases.get_mut(&node) else {
        return Ok(Value::Undef);
    };
    let (bw, bh) = (dst.w as i64, dst.h as i64);
    let byte = |v: Value| {
        let n = to_num(&it.heap, v);
        if !n.is_finite() {
            0
        } else {
            n.round().clamp(0.0, 255.0) as u8
        }
    };
    for r in 0..ih {
        let y = dy + r;
        if y < 0 || y >= bh {
            continue;
        }
        for c in 0..iw {
            let x = dx + c;
            if x < 0 || x >= bw {
                continue;
            }
            let s = (r * iw + c) as usize * 4;
            let d = (y as usize * bw as usize + x as usize) * 4;
            for k in 0..4 {
                dst.px[d + k] = items.get(s + k).copied().map(byte).unwrap_or(0);
            }
        }
    }
    Ok(Value::Undef)
}

/// createImageData(w,h): transparent black {width,height,data}.
fn n_ctx_create_image_data(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let num = |i: usize| to_num(&it.heap, args.get(i).copied().unwrap_or(Value::Undef));
    let (w, h) = (num(0), num(1));
    if !w.is_finite() || !h.is_finite() || w <= 0.0 || h <= 0.0 {
        return Err(err("IndexSizeError: createImageData size must be positive"));
    }
    let (w, h) = (w.trunc() as u64, h.trunc() as u64);
    if w * h > CANVAS_MAX_AREA {
        return Err(err("RangeError: ImageData over the 16M pixel budget"));
    }
    let px = vec![0u8; w as usize * h as usize * 4];
    image_data_obj(it, w as u32, h as u32, &px)
}

/// Standard base64 alphabet, no line breaks. n_btoa (eval.rs) encodes
/// Latin-1 &str for JS; BMP needs raw bytes, hence this local encoder.
fn b64_encode(bytes: &[u8]) -> String {
    const ALPHA: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut out = String::with_capacity((bytes.len() + 2) / 3 * 4);
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
    out
}

/// Minimal 32-bit BI_RGB BMP (bottom-up BGRA rows) of the live buffer.
fn canvas_bmp(buf: &CanvasBuf) -> Vec<u8> {
    let row = buf.w as usize * 4;
    let img_sz = (row * buf.h as usize) as u32;
    let mut out = Vec::with_capacity(54 + img_sz as usize);
    out.extend_from_slice(b"BM");
    out.extend_from_slice(&(54 + img_sz).to_le_bytes());
    out.extend_from_slice(&[0u8; 4]);
    out.extend_from_slice(&54u32.to_le_bytes());
    out.extend_from_slice(&40u32.to_le_bytes());
    out.extend_from_slice(&(buf.w as i32).to_le_bytes());
    out.extend_from_slice(&(buf.h as i32).to_le_bytes());
    out.extend_from_slice(&1u16.to_le_bytes());
    out.extend_from_slice(&32u16.to_le_bytes());
    out.extend_from_slice(&0u32.to_le_bytes());
    out.extend_from_slice(&img_sz.to_le_bytes());
    out.extend_from_slice(&[0u8; 16]);
    for y in (0..buf.h).rev() {
        let base = y as usize * row;
        for x in 0..buf.w as usize {
            let p = base + x * 4;
            out.push(buf.px[p + 2]);
            out.push(buf.px[p + 1]);
            out.push(buf.px[p]);
            out.push(buf.px[p + 3]);
        }
    }
    out
}

impl Interp {
    /// toDataURL(): `data:image/bmp;base64,...` of the live pixels
    /// (type/quality args ignored - one honest encoding, not a stub).
    fn canvas_data_url(&mut self, node: NodeId) -> Result<String, JsError> {
        canvas_ensure(self, node)?;
        let bmp = match self.canvases.get(&node) {
            Some(b) => canvas_bmp(b),
            None => Vec::new(),
        };
        Ok(format!("data:image/bmp;base64,{}", b64_encode(&bmp)))
    }
}

/// Gradient stub: only addColorStop, a no-op.
fn n_ctx_gradient(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let stop = Value::Obj(it.heap.alloc_obj(nat("addColorStop", n_ctx_noop))?);
    Ok(Value::Obj(it.obj_pairs(vec![("addColorStop".into(), stop)])?))
}

/// createPattern(): null (no rasterizer to source a pattern from).
fn n_ctx_pattern(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let _ = it;
    Ok(Value::Null)
}

// ---- Image --------------------------------------------------------------

/// `new Image(w?, h?)`: detached <img> like browsers (width/height
/// reflected when numeric). No document in bare runs - throw there.
pub(crate) fn n_image_ctor(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let n = {
        // dom_mut errors with no document installed.
        let d = it.dom_mut().map_err(|_| err("Image needs a document"))?;
        let root = d.root();
        let n = d.element(root, "img", vec![]);
        d.detach(n);
        n
    };
    for (i, dim) in ["width", "height"].iter().enumerate() {
        let v = to_num(&it.heap, args.get(i).copied().unwrap_or(Value::Undef));
        if !v.is_nan() {
            it.dom_mut()?.set_attr(n, dim, &format!("{}", v.max(0.0) as u32));
        }
    }
    it.dom_wrap(n)
}

// ---- getComputedStyle ----------------------------------------------------

/// window.getComputedStyle(el): snapshot object (not live). Inline
/// declarations win under both kebab and camel keys; the props the
/// collectors read (backgroundColor, font*, visibility, position,
/// transitions, opacity) fall back to desktop defaults. No cascade
/// runs here - documented gap. getPropertyValue returns "" when
/// absent, like V8.
pub(crate) fn n_get_computed_style(
    it: &mut Interp,
    _this: Value,
    args: &[Value],
) -> Result<Value, JsError> {
    let el = args.first().copied().unwrap_or(Value::Undef);
    let Some(n) = it.as_node(el) else {
        return Err(err("getComputedStyle needs an element"));
    };
    let attr = it.dom_ref()?.attr(n, "style").unwrap_or("").to_string();
    let decls = Interp::parse_style(&attr);
    let clean = |mut v: String| {
        // Computed values never carry the priority suffix.
        if let Some(b) = v.to_ascii_lowercase().rfind("!important") {
            v.truncate(b);
        }
        v.trim().to_string()
    };
    let mut resolved: Vec<(String, String)> = decls
        .iter()
        .map(|(k, v)| (k.clone(), clean(v.clone())))
        .collect();
    let defaults = [
        ("background-color", "rgba(0, 0, 0, 0)"),
        ("color", "rgb(0, 0, 0)"),
        ("font-family", "Arial"),
        ("font-size", "16px"),
        ("font-weight", "400"),
        ("visibility", "visible"),
        ("position", "static"),
        ("display", "block"),
        ("opacity", "1"),
        ("transition-duration", "0s"),
        ("transition-delay", "0s"),
    ];
    // `font: 12px Arial` shorthand feeds font-family when no longhand.
    let mut shorthand_font: Option<String> = None;
    for (k, v) in &resolved {
        if k == "font" {
            if let Some(fam) = v.split_whitespace().last() {
                shorthand_font = Some(fam.replace(['"', '\''], ""));
            }
        }
    }
    for (k, d) in defaults {
        if !resolved.iter().any(|(kk, _)| kk == k) {
            let v = if k == "font-family" {
                shorthand_font.clone().unwrap_or_else(|| d.to_string())
            } else {
                d.to_string()
            };
            resolved.push((k.to_string(), v));
        }
    }
    let mut pairs: Vec<(String, Value)> = Vec::with_capacity(resolved.len() * 2 + 2);
    for (k, v) in &resolved {
        let s = Value::Str(it.heap.alloc_str(v.clone())?);
        pairs.push((k.clone(), s));
        let c = Interp::style_camel(k);
        if c != *k {
            pairs.push((c, Value::Str(it.heap.alloc_str(v.clone())?)));
        }
    }
    pairs.push(("length".into(), Value::Num(resolved.len() as f64)));
    let gpv = Value::Obj(it.heap.alloc_obj(nat("getPropertyValue", n_computed_get_prop))?);
    pairs.push(("getPropertyValue".into(), gpv));
    Ok(Value::Obj(it.obj_pairs(pairs)?))
}

/// Computed getPropertyValue(name): resolved value or "" (never
/// undefined, like V8). Custom properties (--*) read verbatim.
fn n_computed_get_prop(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let raw = to_str(&it.heap, args.first().copied().unwrap_or(Value::Undef));
    let key = if raw.starts_with("--") {
        raw
    } else {
        Interp::style_key(&raw)
    };
    match get_prop(&it.heap, &it.protos, this, &key)? {
        Value::Str(id) => Ok(Value::Str(id)),
        Value::Num(n) => Ok(Value::Str(it.heap.alloc_str(n.to_string())?)),
        _ => {
            let e = it.heap.alloc_str(String::new())?;
            Ok(Value::Str(e))
        }
    }
}

// ---- style property methods ----------------------------------------------

fn style_native_node(it: &Interp) -> Option<NodeId> {
    match get_prop(&it.heap, &it.protos, it.cur_native, "__node").ok()? {
        Value::Num(n) => Some(n as NodeId),
        _ => None,
    }
}

/// style.setProperty(name, value): upsert; empty value removes.
fn n_style_set_prop(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let Some(n) = style_native_node(it) else {
        return Err(err("setProperty needs a style"));
    };
    let name = to_str(&it.heap, args.first().copied().unwrap_or(Value::Undef));
    let val = to_str(&it.heap, args.get(1).copied().unwrap_or(Value::Undef));
    let slot = it.heap.alloc_str(val)?;
    it.style_set(n, &name, Value::Str(slot))?;
    Ok(Value::Undef)
}

/// style.getPropertyValue(name): value or "" (V8 parity).
fn n_style_get_prop(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let Some(n) = style_native_node(it) else {
        return Err(err("getPropertyValue needs a style"));
    };
    let name = to_str(&it.heap, args.first().copied().unwrap_or(Value::Undef));
    match it.style_get(n, &name)? {
        Value::Undef => Ok(Value::Str(it.heap.alloc_str(String::new())?)),
        v => Ok(v),
    }
}

/// style.removeProperty(name): drop it, return the old value or "".
fn n_style_remove_prop(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let Some(n) = style_native_node(it) else {
        return Err(err("removeProperty needs a style"));
    };
    let name = to_str(&it.heap, args.first().copied().unwrap_or(Value::Undef));
    let old = it.style_get(n, &name)?;
    let empty = it.heap.alloc_str(String::new())?;
    it.style_set(n, &name, Value::Str(empty))?;
    match old {
        Value::Undef => Ok(Value::Str(it.heap.alloc_str(String::new())?)),
        v => Ok(v),
    }
}

// ---- classList (DOMTokenList) --------------------------------------------

/// Live token list of the class attribute (whitespace-split).
fn tokens_read(it: &Interp, n: NodeId) -> Vec<String> {
    it.dom_ref()
        .map(|d| {
            d.attr(n, "class")
                .unwrap_or("")
                .split_whitespace()
                .map(str::to_string)
                .collect()
        })
        .unwrap_or_default()
}

fn tokens_node(it: &Interp) -> Result<NodeId, JsError> {
    match style_native_node(it) {
        Some(n) => Ok(n),
        None => Err(err("classList method needs a classList")),
    }
}

/// Zero DOMRect: no layout engine, so geometry is all zeros.
pub(crate) fn zero_rect(it: &mut Interp) -> Result<u32, JsError> {
    it.obj_pairs(vec![
        ("x".into(), Value::Num(0.0)),
        ("y".into(), Value::Num(0.0)),
        ("width".into(), Value::Num(0.0)),
        ("height".into(), Value::Num(0.0)),
        ("top".into(), Value::Num(0.0)),
        ("left".into(), Value::Num(0.0)),
        ("bottom".into(), Value::Num(0.0)),
        ("right".into(), Value::Num(0.0)),
    ])
}

fn n_tokens_add(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let n = tokens_node(it)?;
    let mut toks = tokens_read(it, n);
    for a in args {
        let t = to_str(&it.heap, *a);
        if t.is_empty() || t.split_whitespace().count() != 1 {
            return Err(err("classList.add: invalid token"));
        }
        if !toks.iter().any(|x| x == &t) {
            toks.push(t);
        }
    }
    it.dom_mut()?.set_attr(n, "class", &toks.join(" "));
    Ok(Value::Undef)
}

fn n_tokens_remove(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let n = tokens_node(it)?;
    let mut toks = tokens_read(it, n);
    for a in args {
        let t = to_str(&it.heap, *a);
        if t.is_empty() || t.split_whitespace().count() != 1 {
            return Err(err("classList.remove: invalid token"));
        }
        toks.retain(|x| x != &t);
    }
    it.dom_mut()?.set_attr(n, "class", &toks.join(" "));
    Ok(Value::Undef)
}

fn n_tokens_toggle(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let n = tokens_node(it)?;
    let t = to_str(&it.heap, args.first().copied().unwrap_or(Value::Undef));
    if t.is_empty() || t.split_whitespace().count() != 1 {
        return Err(err("classList.toggle: invalid token"));
    }
    let mut toks = tokens_read(it, n);
    let has = toks.iter().any(|x| x == &t);
    let force = args.get(1).copied();
    let want = match force {
        Some(v) if !matches!(v, Value::Undef) => truthy(&it.heap, v),
        _ => !has,
    };
    if want && !has {
        toks.push(t);
    } else if !want {
        toks.retain(|x| x != &t);
    }
    it.dom_mut()?.set_attr(n, "class", &toks.join(" "));
    Ok(Value::Bool(want))
}

fn n_tokens_contains(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let n = tokens_node(it)?;
    let t = to_str(&it.heap, args.first().copied().unwrap_or(Value::Undef));
    Ok(Value::Bool(tokens_read(it, n).iter().any(|x| x == &t)))
}

fn n_tokens_item(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let n = tokens_node(it)?;
    let i = to_num(&it.heap, args.first().copied().unwrap_or(Value::Undef));
    let toks = tokens_read(it, n);
    if i.is_nan() || i < 0.0 || i as usize >= toks.len() {
        return Ok(Value::Null);
    }
    it.str_val(toks[i as usize].clone())
}

fn n_tokens_replace(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let n = tokens_node(it)?;
    let old = to_str(&it.heap, args.first().copied().unwrap_or(Value::Undef));
    let new = to_str(&it.heap, args.get(1).copied().unwrap_or(Value::Undef));
    let mut toks = tokens_read(it, n);
    let hit = toks.iter().position(|x| x == &old);
    match hit {
        Some(i) => {
            toks[i] = new;
            it.dom_mut()?.set_attr(n, "class", &toks.join(" "));
            Ok(Value::Bool(true))
        }
        None => Ok(Value::Bool(false)),
    }
}

fn n_tokens_len(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let n = tokens_node(it)?;
    Ok(Value::Num(tokens_read(it, n).len() as f64))
}

fn n_tokens_value_get(it: &mut Interp, _this: Value, _args: &[Value]) -> Result<Value, JsError> {
    let n = tokens_node(it)?;
    let c = it.dom_ref()?.attr(n, "class").unwrap_or("").to_string();
    it.str_val(c)
}

fn n_tokens_value_set(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    let n = tokens_node(it)?;
    let v = to_str(&it.heap, args.first().copied().unwrap_or(Value::Undef));
    it.dom_mut()?.set_attr(n, "class", v.trim());
    Ok(Value::Undef)
}

/// sheet.insertRule(rule, index=0): store a {cssText} stub, return index.
/// sheet.deleteRule(index): drop it. No parsing, no cascade.
fn n_sheet_insert(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let css = to_str(&it.heap, arg(args, 0));
    let rules = match get_prop(&it.heap, &it.protos, this, "cssRules")? {
        Value::Obj(id) => id,
        _ => return Err(err("insertRule needs a stylesheet")),
    };
    let at = to_num(&it.heap, arg(args, 1));
    let cs = Value::Str(it.heap.alloc_str(css)?);
    let rule = Value::Obj(it.obj_pairs(vec![("cssText".into(), cs)])?);
    if let Obj::Arr { items, .. } = it.heap.obj_mut(rules) {
        let i = (if at.is_nan() { 0.0 } else { at }.max(0.0) as usize).min(items.len());
        items.insert(i, rule);
        return Ok(Value::Num(i as f64));
    }
    Err(err("insertRule needs a stylesheet"))
}

fn n_sheet_delete(it: &mut Interp, this: Value, args: &[Value]) -> Result<Value, JsError> {
    let rules = match get_prop(&it.heap, &it.protos, this, "cssRules")? {
        Value::Obj(id) => id,
        _ => return Err(err("deleteRule needs a stylesheet")),
    };
    let at = to_num(&it.heap, arg(args, 0));
    if let Obj::Arr { items, .. } = it.heap.obj_mut(rules) {
        if at >= 0.0 && at.fract() == 0.0 {
            let i = at as usize;
            if i < items.len() {
                items.remove(i);
            }
        }
    }
    Ok(Value::Undef)
}

/// Bare addEventListener/removeEventListener/dispatchEvent resolve to
/// the window target in browsers; same here (sentinel registry).
pub(crate) fn n_win_add_event_listener(
    it: &mut Interp,
    _this: Value,
    args: &[Value],
) -> Result<Value, JsError> {
    match it.event_method(WIN_EVENTS, "addEventListener", args)? {
        Some(v) => Ok(v),
        None => Ok(Value::Undef),
    }
}

pub(crate) fn n_win_remove_event_listener(
    it: &mut Interp,
    _this: Value,
    args: &[Value],
) -> Result<Value, JsError> {
    match it.event_method(WIN_EVENTS, "removeEventListener", args)? {
        Some(v) => Ok(v),
        None => Ok(Value::Undef),
    }
}

pub(crate) fn n_win_dispatch_event(it: &mut Interp, _this: Value, args: &[Value]) -> Result<Value, JsError> {
    match it.event_method(WIN_EVENTS, "dispatchEvent", args)? {
        Some(v) => Ok(v),
        None => Ok(Value::Undef),
    }
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
        // window mirrors the global scope (builtins included).
        assert_eq!(ev(&mut it, "window.atob === atob"), "true");
        assert_eq!(ev(&mut it, "window.Uint8Array === Uint8Array"), "true");
        assert_eq!(ev(&mut it, "window.window === window"), "true");
        assert_eq!(ev(&mut it, "globalThis.atob('aGk=')"), "hi");
        assert_eq!(ev(&mut it, "window.matchMedia('x').matches"), "false");
        // Writes through window land as real globals (and vice versa).
        assert_eq!(ev(&mut it, "window.FullCalendarVDom={x:1};FullCalendarVDom.x"), "1");
        assert_eq!(ev(&mut it, "var wv=41;window.wv"), "41");
        assert_eq!(ev(&mut it, "'atob' in window"), "true");
        assert_eq!(ev(&mut it, "window.newglobal=7;delete window.newglobal;'newglobal' in window"), "false");
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
        assert_eq!(
            ev(&mut it, "document.querySelector('#a p').parentNode.id"),
            "a"
        );
        // parentNode (unlike parentElement) sees non-element parents.
        assert_eq!(
            ev(&mut it, "document.documentElement.parentNode.nodeType"),
            "9"
        );
        assert_eq!(ev(&mut it, "document.parentNode"), "null");
    }

    #[test]
    fn style_sheets() {
        let mut it = interp("<html><head><style id=s>.a{color:red}</style></head><body></body></html>");
        assert_eq!(ev(&mut it, "document.styleSheets.length"), "1");
        assert_eq!(
            ev(&mut it, "document.styleSheets[0].ownerNode === document.getElementById('s')"),
            "true"
        );
        assert_eq!(
            ev(
                &mut it,
                "var sh=document.getElementById('s').sheet;sh.insertRule('.b{}',0);sh.cssRules.length"
            ),
            "1"
        );
        assert_eq!(
            ev(
                &mut it,
                "var sh=document.getElementById('s').sheet;sh.insertRule('.b{}',0);sh.cssRules[0].cssText"
            ),
            ".b{}"
        );
        assert_eq!(ev(&mut it, "document.getElementById('s').sheet === document.getElementById('s').sheet"), "true");
        assert_eq!(ev(&mut it, "document.createElement('div').sheet"), "null");
    }

    #[test]
    fn implementation_doc() {
        // jQuery support shape: detached doc with working body.
        let mut it = interp(PAGE);
        assert_eq!(
            ev(
                &mut it,
                "var d=document.implementation.createHTMLDocument('');\
                 d.body.innerHTML='<form></form><form></form>';d.body.childNodes.length"
            ),
            "2"
        );
        assert_eq!(
            ev(
                &mut it,
                "var d=document.implementation.createHTMLDocument('t');d.title"
            ),
            "t"
        );
        // The fake doc stays out of page queries.
        assert_eq!(ev(&mut it, "document.getElementsByTagName('body').length"), "1");
        assert_eq!(ev(&mut it, "document.head.tagName"), "HEAD");
        assert_eq!(
            ev(&mut it, "document.createElementNS('http://www.w3.org/2000/svg','circle').tagName"),
            "CIRCLE"
        );
        assert_eq!(ev(&mut it, "document.getElementById('a').ownerDocument === document"), "true");
        assert_eq!(ev(&mut it, "document.ownerDocument"), "null");
        assert_eq!(
            ev(&mut it, "var d=document.implementation.createHTMLDocument('');d.body.ownerDocument===d"),
            "true"
        );
        assert_eq!(ev(&mut it, "navigator.appVersion.indexOf('MSIE')"), "-1");
        assert_eq!(ev(&mut it, "document.defaultView === window"), "true");
        assert_eq!(ev(&mut it, "location.pathname"), "/");
        assert_eq!(ev(&mut it, "window.location.pathname"), "/");
        assert_eq!(ev(&mut it, "history.pushState(null,'','/app?q=1#h');location.pathname"), "/app");
        assert_eq!(ev(&mut it, "location.search"), "?q=1");
        assert_eq!(ev(&mut it, "location.hash"), "#h");
        assert_eq!(ev(&mut it, "location.href.slice(-10)"), "/app?q=1#h");
    }

    #[test]
    fn get_elements_by() {
        let mut it = interp("<body><div id=a class='x y'><p class='x'>t</p></div><input name=n1></body>");
        assert_eq!(ev(&mut it, "document.getElementsByClassName('x').length"), "2");
        assert_eq!(ev(&mut it, "document.getElementById('a').getElementsByClassName('x').length"), "1");
        assert_eq!(ev(&mut it, "document.getElementsByTagName('p').length"), "1");
        assert_eq!(ev(&mut it, "document.getElementsByName('n1').length"), "1");
        assert_eq!(ev(&mut it, "typeof document.body.getElementsByTagName"), "function");
    }

    #[test]
    fn dom_methods_as_values() {
        // canUseDOM shape: resolves as a value, not just at call time.
        let mut it = interp(PAGE);
        assert_eq!(ev(&mut it, "typeof document.createElement"), "function");
        assert_eq!(ev(&mut it, "typeof document.body.appendChild"), "function");
        assert_eq!(ev(&mut it, "typeof document.body.hasOwnProperty"), "function");
        assert_eq!(
            ev(&mut it, "var f=document.createElement;var d=f.call(document,'div');d.tagName"),
            "DIV"
        );
        assert_eq!(ev(&mut it, "document.body.constructor === HTMLElement"), "true");
    }

    #[test]
    fn dom_hierarchy() {
        let mut it = interp(PAGE);
        assert_eq!(ev(&mut it, "document.body instanceof HTMLElement"), "true");
        assert_eq!(ev(&mut it, "document.body instanceof Element"), "true");
        assert_eq!(ev(&mut it, "document.body instanceof Node"), "true");
        assert_eq!(ev(&mut it, "document instanceof Document"), "true");
        assert_eq!(ev(&mut it, "document.body.constructor === HTMLElement"), "true");
        assert_eq!(
            ev(&mut it, "Object.getPrototypeOf(document.body) === HTMLElement.prototype"),
            "true"
        );
        assert_eq!(ev(&mut it, "document.body instanceof Document"), "false");
        assert_eq!(ev(&mut it, "typeof Element"), "function");
        assert!(errmsg(&mut interp(PAGE), "new Element()").contains("Illegal constructor"));
        assert_eq!(ev(&mut it, "document.getElementById('i').constructor === HTMLInputElement"), "true");
        assert_eq!(ev(&mut it, "document.getElementById('i') instanceof HTMLElement"), "true");
        assert_eq!(ev(&mut it, "document.getElementById('l') instanceof HTMLAnchorElement"), "true");
        assert_eq!(ev(&mut it, "document.createDocumentFragment() instanceof DocumentFragment"), "true");
        assert_eq!(ev(&mut it, "document.createElement('iframe') instanceof HTMLIFrameElement"), "true");
    }

    #[test]
    fn sloppy_this_window() {
        // With a DOM installed, top-level and bare-call `this` is window.
        let mut it = interp(PAGE);
        assert_eq!(ev(&mut it, "this === window"), "true");
        assert_eq!(ev(&mut it, "function f(){return this}f()===window"), "true");
        assert_eq!(ev(&mut it, "this.dT_"), "undefined");
        // Sloppy this-write creates a real global through window.
        assert_eq!(ev(&mut it, "function f(){this.wx9=7} f();wx9"), "7");
    }

    #[test]
    fn performance_surface() {
        let mut it = interp(PAGE);
        assert_eq!(ev(&mut it, "typeof performance.now()"), "number");
        assert_eq!(ev(&mut it, "typeof performance.timeOrigin"), "number");
        assert_eq!(ev(&mut it, "performance.getEntriesByType('x').length"), "0");
        assert_eq!(ev(&mut it, "typeof PerformanceResourceTiming"), "function");
        // document.currentScript tracks the running element.
        let mut it2 = interp("<html><head><script id=s>var x=1</script></head><body></body></html>");
        let dom = it2.take_dom();
        let s = vigia_css::query(&dom, "script").unwrap()[0];
        it2.set_dom(dom);
        it2.cur_script = Some(s);
        assert_eq!(ev(&mut it2, "document.currentScript.tagName"), "SCRIPT");
        assert_eq!(ev(&mut it2, "document.currentScript === document.getElementsByTagName('script')[0]"), "true");
    }

    #[test]
    fn stealth_ua_sync() {
        // --stealth: JS navigator matches the wire UA (mismatch = bot flag).
        let html = "<html><body></body></html>";
        let mut d = Dom::new();
        vigia_html::parse(html, &mut d);
        let mut it = Interp::new();
        let mut jar = CookieJar::new();
        jar.stealth = true;
        let out = it.run_scripts(
            d,
            Some(NetCtx {
                base: vigia_url::Url::parse("http://a.com/").unwrap(),
                jar,
                trace: None,
            }),
        );
        assert!(out.errors.is_empty(), "{:?}", out.errors);
        assert_eq!(ev(&mut it, "navigator.userAgent.indexOf('Chrome/126') !== -1"), "true");
        assert_eq!(ev(&mut it, "navigator.vendor"), "Google Inc.");
        assert_eq!(ev(&mut it, "window.navigator === navigator"), "true");
    }

    #[test]
    fn navigator_extras() {
        let mut it = interp(PAGE);
        assert_eq!(ev(&mut it, "navigator.sendBeacon('/x')"), "true");
        assert_eq!(ev(&mut it, "navigator.connection.effectiveType"), "4g");
        assert_eq!(ev(&mut it, "navigator.geolocation.toString()"), "[object Geolocation]");
        assert_eq!(ev(&mut it, "navigator.userAgentData.platform"), "Linux");
        assert_eq!(ev(&mut it, "navigator.userAgentData.brands.length"), "3");
        assert_eq!(ev(&mut it, "typeof navigator.indexedDB.open"), "function");
        assert_eq!(ev(&mut it, "typeof IDBRequest"), "function");
        // getHighEntropyValues resolves the static dict (microtasks drain
        // after the completion value, so read back in a second run).
        assert_eq!(
            ev(&mut it, "var p=navigator.userAgentData.getHighEntropyValues();p instanceof Promise"),
            "true"
        );
        it.run("var r='none';navigator.userAgentData.getHighEntropyValues().then(function(d){r=d.platform})").unwrap();
        assert_eq!(ev(&mut it, "r"), "Linux");
        // Plugins persona: length + named lookup.
        assert_eq!(ev(&mut it, "navigator.plugins.length"), "2");
        assert_eq!(ev(&mut it, "navigator.plugins[0].name"), "Chrome PDF Viewer");
        assert_eq!(ev(&mut it, "navigator.plugins.namedItem('Chromium PDF Viewer').filename"), "internal-pdf-viewer");
        assert_eq!(ev(&mut it, "navigator.mimeTypes.length"), "2");
        assert_eq!(ev(&mut it, "navigator.mimeTypes[0].type"), "application/pdf");
        assert_eq!(ev(&mut it, "navigator.plugins.item(5)"), "null");
    }

    #[test]
    fn canvas_and_computed() {
        let mut it = interp(PAGE);
        // Canvas iface + 2d stub (stormcaster monkey-patch signals read
        // native fns; main.js drawing calls must not throw).
        assert_eq!(ev(&mut it, "typeof HTMLCanvasElement"), "function");
        assert_eq!(ev(&mut it, "var c=document.createElement('canvas');c instanceof HTMLCanvasElement"), "true");
        assert_eq!(ev(&mut it, "var c=document.createElement('canvas');typeof c.getContext"), "function");
        assert_eq!(
            ev(&mut it, "var c=document.createElement('canvas');var x=c.getContext('2d');x.fillStyle='red';x.fillRect(0,0,10,10);x.measureText('hi').width"),
            "0"
        );
        assert_eq!(ev(&mut it, "var c=document.createElement('canvas');c.getContext('webgl')"), "null");
        assert_eq!(ev(&mut it, "var c=document.createElement('canvas');c.toDataURL().slice(0,22)"), "data:image/bmp;base64,");
        assert_eq!(ev(&mut it, "var c=document.createElement('canvas');c.width"), "300");
        assert_eq!(ev(&mut it, "var c=document.createElement('canvas');c.width=100;c.width"), "100");
        assert_eq!(ev(&mut it, "var d=document.createElement('div');try{d.getContext('2d')}catch(e){'throws'}"), "throws");
        // Image ctor builds a detached img.
        assert_eq!(ev(&mut it, "var i=new Image();i instanceof HTMLImageElement"), "true");
        assert_eq!(ev(&mut it, "var i=new Image(16,32);i.width"), "16");
        // getComputedStyle snapshot + style property methods.
        assert_eq!(ev(&mut it, "var d=document.createElement('div');typeof getComputedStyle(d).length"), "number");
        assert_eq!(ev(&mut it, "var d=document.createElement('div');getComputedStyle(d).visibility"), "visible");
        assert_eq!(
            ev(&mut it, "var d=document.createElement('div');d.style.cssText='background-color: red !important';getComputedStyle(d).backgroundColor"),
            "red"
        );
        assert_eq!(
            ev(&mut it, "var d=document.createElement('div');d.style.cssText='font: 12px Arial !important';getComputedStyle(d).fontFamily"),
            "Arial"
        );
        assert_eq!(
            ev(&mut it, "var d=document.createElement('div');getComputedStyle(d).getPropertyValue('--bs-position')"),
            ""
        );
        assert_eq!(
            ev(&mut it, "var d=document.createElement('div');d.style.setProperty('display','none');d.style.display"),
            "none"
        );
        assert_eq!(
            ev(&mut it, "var d=document.createElement('div');d.style.backgroundColor='blue';d.style.getPropertyValue('background-color')"),
            "blue"
        );
    }

    #[test]
    fn canvas_fill_and_readback() {
        let mut it = interp(PAGE);
        // fill red rect then getImageData pixel equals 255,0,0,255.
        assert_eq!(
            ev(&mut it, "var c=document.createElement('canvas');c.width=4;c.height=4;var x=c.getContext('2d');x.fillStyle='#ff0000';x.fillRect(0,0,2,2);var d=x.getImageData(0,0,1,1).data;d[0]===255&&d[1]===0&&d[2]===0&&d[3]===255"),
            "true"
        );
        // Comma rgb() green pixel shape.
        assert_eq!(
            ev(&mut it, "var c=document.createElement('canvas');c.width=4;c.height=4;var x=c.getContext('2d');x.fillStyle='rgb(0,255,0)';x.fillRect(1,1,1,1);var d=x.getImageData(1,1,1,1).data;d[0]===0&&d[1]===255&&d[2]===0&&d[3]===255"),
            "true"
        );
        // Space-syntax rgba with alpha.
        assert_eq!(
            ev(&mut it, "var c=document.createElement('canvas');var x=c.getContext('2d');x.fillStyle='rgba(0 0 255 / 0.5)';x.fillRect(0,0,1,1);var d=x.getImageData(0,0,1,1).data;d[2]===255&&d[3]===128"),
            "true"
        );
        // Untouched pixels stay transparent black.
        assert_eq!(
            ev(&mut it, "var c=document.createElement('canvas');c.width=4;c.height=4;var x=c.getContext('2d');var d=x.getImageData(3,3,1,1).data;d[0]===0&&d[1]===0&&d[2]===0&&d[3]===0"),
            "true"
        );
    }

    #[test]
    fn canvas_clear_rect() {
        let mut it = interp(PAGE);
        assert_eq!(
            ev(&mut it, "var c=document.createElement('canvas');c.width=4;c.height=4;var x=c.getContext('2d');x.fillStyle='red';x.fillRect(0,0,4,4);x.clearRect(0,0,2,2);var d=x.getImageData(0,0,1,1).data;d[0]===0&&d[1]===0&&d[2]===0&&d[3]===0"),
            "true"
        );
        // Pixels outside the cleared rect survive.
        assert_eq!(
            ev(&mut it, "var c=document.createElement('canvas');c.width=4;c.height=4;var x=c.getContext('2d');x.fillStyle='red';x.fillRect(0,0,4,4);x.clearRect(0,0,2,2);var d=x.getImageData(3,3,1,1).data;d[0]===255&&d[3]===255"),
            "true"
        );
    }

    #[test]
    fn canvas_draw_image() {
        let mut it = interp(PAGE);
        // Canvas-to-canvas 3-arg blit copies a pixel.
        assert_eq!(
            ev(&mut it, "var a=document.createElement('canvas');a.width=2;a.height=2;var ax=a.getContext('2d');ax.fillStyle='#00ff00';ax.fillRect(0,0,2,2);var b=document.createElement('canvas');b.width=2;b.height=2;var bx=b.getContext('2d');bx.drawImage(a,0,0);var d=bx.getImageData(1,1,1,1).data;d[0]===0&&d[1]===255&&d[2]===0&&d[3]===255"),
            "true"
        );
        // 5-arg nearest-neighbor upscale spreads the pixel.
        assert_eq!(
            ev(&mut it, "var a=document.createElement('canvas');a.width=1;a.height=1;var ax=a.getContext('2d');ax.fillStyle='blue';ax.fillRect(0,0,1,1);var b=document.createElement('canvas');b.width=4;b.height=4;var bx=b.getContext('2d');bx.drawImage(a,0,0,4,4);var d=bx.getImageData(3,3,1,1).data;d[2]===255&&d[3]===255"),
            "true"
        );
        // 9-arg source-rect pick.
        assert_eq!(
            ev(&mut it, "var a=document.createElement('canvas');a.width=2;a.height=1;var ax=a.getContext('2d');ax.fillStyle='red';ax.fillRect(0,0,1,1);ax.fillStyle='lime';ax.fillRect(1,0,1,1);var b=document.createElement('canvas');b.width=2;b.height=1;var bx=b.getContext('2d');bx.drawImage(a,1,0,1,1,0,0,1,1);var d=bx.getImageData(0,0,1,1).data;d[1]===255&&d[0]===0"),
            "true"
        );
        // Non-canvas sources no-op without throwing.
        assert_eq!(
            ev(&mut it, "var b=document.createElement('canvas');b.width=2;b.height=2;var bx=b.getContext('2d');bx.drawImage(document.createElement('div'),0,0);'ok'"),
            "ok"
        );
    }

    #[test]
    fn canvas_put_image_data() {
        let mut it = interp(PAGE);
        // createImageData is transparent black; put/get roundtrips a pixel.
        assert_eq!(
            ev(&mut it, "var c=document.createElement('canvas');c.width=4;c.height=4;var x=c.getContext('2d');var im=x.createImageData(2,2);im.data[0]=255;im.data[3]=255;x.putImageData(im,1,1);var d=x.getImageData(1,1,1,1).data;d[0]===255&&d[1]===0&&d[2]===0&&d[3]===255"),
            "true"
        );
        assert_eq!(
            ev(&mut it, "var c=document.createElement('canvas');var x=c.getContext('2d');var im=x.createImageData(1,1);im.width===1&&im.height===1&&im.data[0]===0&&im.data[3]===0"),
            "true"
        );
        // Dirty-rect form accepted (ignored, full blit).
        assert_eq!(
            ev(&mut it, "var c=document.createElement('canvas');c.width=4;c.height=4;var x=c.getContext('2d');var im=x.createImageData(1,1);im.data[2]=255;im.data[3]=255;x.putImageData(im,2,2,0,0,1,1);var d=x.getImageData(2,2,1,1).data;d[2]===255&&d[3]===255"),
            "true"
        );
    }

    #[test]
    fn canvas_resize_clears() {
        let mut it = interp(PAGE);
        // Even a same-value width write resets the buffer.
        assert_eq!(
            ev(&mut it, "var c=document.createElement('canvas');c.width=4;c.height=4;var x=c.getContext('2d');x.fillStyle='red';x.fillRect(0,0,4,4);c.width=4;var d=x.getImageData(0,0,1,1).data;d[3]===0"),
            "true"
        );
        assert_eq!(
            ev(&mut it, "var c=document.createElement('canvas');c.width=4;c.height=4;var x=c.getContext('2d');x.fillStyle='red';x.fillRect(0,0,4,4);c.height=2;var d=x.getImageData(0,0,1,1).data;d[3]===0"),
            "true"
        );
    }

    #[test]
    fn canvas_invalid_fill_style_keeps_color() {
        let mut it = interp(PAGE);
        assert_eq!(
            ev(&mut it, "var c=document.createElement('canvas');c.width=2;c.height=2;var x=c.getContext('2d');x.fillStyle='#00ff00';x.fillStyle='nope';x.fillRect(0,0,2,2);var d=x.getImageData(0,0,1,1).data;d[0]===0&&d[1]===255&&d[2]===0&&d[3]===255"),
            "true"
        );
        // Readback also keeps the old value.
        assert_eq!(
            ev(&mut it, "var c=document.createElement('canvas');var x=c.getContext('2d');x.fillStyle='#00ff00';x.fillStyle='nope';x.fillStyle"),
            "#00ff00"
        );
        // Default is opaque black.
        assert_eq!(
            ev(&mut it, "var c=document.createElement('canvas');var x=c.getContext('2d');x.fillStyle"),
            "#000000"
        );
    }

    #[test]
    fn canvas_data_url_bmp() {
        let mut it = interp(PAGE);
        assert_eq!(
            ev(&mut it, "var c=document.createElement('canvas');c.width=2;c.height=2;c.toDataURL().slice(0,22)"),
            "data:image/bmp;base64,"
        );
        // A red pixel roundtrips through BMP bytes (BM magic + red in the
        // bottom-up BGRA row): decode the tail past the 54-byte header.
        assert_eq!(
            ev(&mut it, "var c=document.createElement('canvas');c.width=1;c.height=1;var x=c.getContext('2d');x.fillStyle='red';x.fillRect(0,0,1,1);var u=c.toDataURL();u.slice(0,22)==='data:image/bmp;base64,'&&atob(u.slice(22)).length===58"),
            "true"
        );
    }

    #[test]
    fn canvas_ctx_identity() {
        let mut it = interp(PAGE);
        assert_eq!(
            ev(&mut it, "var c=document.createElement('canvas');c.getContext('2d')===c.getContext('2d')"),
            "true"
        );
        assert_eq!(
            ev(&mut it, "var c=document.createElement('canvas');var x=c.getContext('2d');x.canvas===c"),
            "true"
        );
    }

    #[test]
    fn canvas_oversize_throws() {
        let mut it = interp(PAGE);
        assert_eq!(
            ev(&mut it, "var c=document.createElement('canvas');c.width=10000;c.height=10000;try{c.getContext('2d');'no-throw'}catch(e){'throws'}"),
            "throws"
        );
        // Fully-outside getImageData throws too.
        assert_eq!(
            ev(&mut it, "var c=document.createElement('canvas');c.width=4;c.height=4;var x=c.getContext('2d');try{x.getImageData(99,99,2,2);'no-throw'}catch(e){'throws'}"),
            "throws"
        );
    }

    #[test]
    fn traversal_and_tokens() {
        let mut it = interp(
            "<html><body><div id=a class='x y'><p id=b>hi</p></div></body></html>",
        );
        // classList live on the class attribute.
        assert_eq!(ev(&mut it, "var d=document.getElementById('a');d.classList.length"), "2");
        assert_eq!(ev(&mut it, "var d=document.getElementById('a');d.classList.contains('x')"), "true");
        assert_eq!(
            ev(&mut it, "var d=document.getElementById('a');d.classList.add('z');d.className"),
            "x y z"
        );
        assert_eq!(
            ev(&mut it, "var d=document.getElementById('a');d.classList.remove('x');d.classList.value"),
            "y z"
        );
        assert_eq!(ev(&mut it, "var d=document.getElementById('a');d.classList.toggle('y')"), "false");
        assert_eq!(ev(&mut it, "var d=document.getElementById('a');d.classList === d.classList"), "true");
        assert_eq!(ev(&mut it, "var d=document.getElementById('a');d.classList.item(0)"), "z");
        // contains / matches / closest.
        assert_eq!(
            ev(&mut it, "var a=document.getElementById('a');var b=document.getElementById('b');a.contains(b)"),
            "true"
        );
        assert_eq!(
            ev(&mut it, "var b=document.getElementById('b');b.contains(b)"),
            "true"
        );
        assert_eq!(ev(&mut it, "var b=document.getElementById('b');b.matches('p')"), "true");
        assert_eq!(ev(&mut it, "var b=document.getElementById('b');b.matches('div')"), "false");
        assert_eq!(
            ev(&mut it, "var b=document.getElementById('b');b.closest('div').id"),
            "a"
        );
        assert_eq!(ev(&mut it, "var b=document.getElementById('b');b.closest('.nope')"), "null");
        // Geometry without a layout engine: zero rect, attached reads one.
        assert_eq!(ev(&mut it, "var b=document.getElementById('b');b.getBoundingClientRect().width"), "0");
        assert_eq!(ev(&mut it, "var b=document.getElementById('b');b.getClientRects().length"), "1");
        assert_eq!(ev(&mut it, "var d=document.createElement('div');d.getClientRects().length"), "0");
    }

    #[test]
    fn persona_surface() {
        // Navigator constants (Chrome-shaped in both modes).
        let mut it = interp(PAGE);
        assert_eq!(ev(&mut it, "navigator.product"), "Gecko");
        assert_eq!(ev(&mut it, "navigator.appName"), "Netscape");
        assert_eq!(ev(&mut it, "navigator.hardwareConcurrency"), "8");
        assert_eq!(ev(&mut it, "navigator.languages.join()"), "en-US,en");
        assert_eq!(ev(&mut it, "navigator.cookieEnabled"), "true");
        assert_eq!(ev(&mut it, "navigator.javaEnabled()"), "false");
        assert_eq!(ev(&mut it, "navigator.maxTouchPoints"), "0");
        assert_eq!(ev(&mut it, "typeof navigator.webdriver"), "undefined");
        // Screen + viewport persona.
        assert_eq!(ev(&mut it, "screen.width"), "1920");
        assert_eq!(ev(&mut it, "screen.colorDepth"), "24");
        assert_eq!(ev(&mut it, "screen.orientation.type"), "landscape-primary");
        assert_eq!(ev(&mut it, "innerWidth"), "1366");
        assert_eq!(ev(&mut it, "devicePixelRatio"), "1");
        assert_eq!(ev(&mut it, "window.innerWidth"), "1366");
        // Document props.
        assert_eq!(ev(&mut it, "document.compatMode"), "CSS1Compat");
        assert_eq!(ev(&mut it, "document.characterSet"), "UTF-8");
        assert_eq!(ev(&mut it, "document.hidden"), "false");
        assert_eq!(ev(&mut it, "document.visibilityState"), "visible");
        assert_eq!(ev(&mut it, "document.hasFocus()"), "true");
        assert_eq!(ev(&mut it, "document.designMode"), "off");
    }

    #[test]
    fn window_events() {
        let mut it = interp(PAGE);
        // Registration on window (method + bare global), then dispatch.
        it.run("var hits=[];window.addEventListener('x',function(e){hits.push(e.type)})")
            .unwrap();
        it.run("addEventListener('y',function(){hits.push('y')})").unwrap();
        assert_eq!(ev(&mut it, "hits.length"), "0");
        it.run("window.dispatchEvent({type:'x'})").unwrap();
        it.run("dispatchEvent({type:'y'})").unwrap();
        assert_eq!(ev(&mut it, "hits.join()"), "x,y");
        // removeEventListener detaches.
        it.run("var f=function(){hits.push('z')};window.addEventListener('z',f);window.removeEventListener('z',f);window.dispatchEvent({type:'z'})").unwrap();
        assert_eq!(ev(&mut it, "hits.join()"), "x,y");
    }

    #[test]
    fn document_cookie() {
        // Bot-manager shape: write via document.cookie, read back, jar
        // keeps it for wire requests, HttpOnly stays hidden from JS.
        let html = "<html><body><script>document.cookie='uzmx=v1; path=/';document.cookie='other=2; path=/';if(document.cookie.indexOf('uzmx=v1')<0)throw new Error('no readback')</script></body></html>";
        let mut d = Dom::new();
        vigia_html::parse(html, &mut d);
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
        let jar = out.jar.unwrap();
        assert_eq!(
            jar.header_for(&vigia_url::Url::parse("http://a.com/x").unwrap()).as_deref(),
            Some("uzmx=v1; other=2")
        );
        // HttpOnly set server-side never surfaces in document.cookie.
        let mut jar2 = CookieJar::new();
        jar2.store_header(
            &vigia_url::Url::parse("http://a.com/").unwrap(),
            "sess=s3cr3t; HttpOnly; path=/",
        );
        assert_eq!(
            jar2.cookies_for_js(&vigia_url::Url::parse("http://a.com/").unwrap()),
            ""
        );
        assert!(jar2
            .header_for(&vigia_url::Url::parse("http://a.com/").unwrap())
            .is_some());
    }

    #[test]
    fn sibling_navigation() {        let mut it = interp("<body><div id=a><b id=b>x</b>tail<i id=c>y</i></div></body>");
        assert_eq!(ev(&mut it, "document.getElementById('a').firstChild.tagName"), "B");
        assert_eq!(ev(&mut it, "document.getElementById('a').lastChild.tagName"), "I");
        assert_eq!(ev(&mut it, "document.getElementById('b').nextSibling.textContent"), "tail");
        assert_eq!(
            ev(&mut it, "document.getElementById('c').previousSibling.textContent"),
            "tail"
        );
        assert_eq!(ev(&mut it, "document.getElementById('b').nextElementSibling.tagName"), "I");
        assert_eq!(
            ev(&mut it, "document.getElementById('c').previousElementSibling.tagName"),
            "B"
        );
        assert_eq!(ev(&mut it, "document.getElementById('b').previousSibling"), "null");
        assert_eq!(ev(&mut it, "document.getElementById('c').nextSibling"), "null");
        assert_eq!(ev(&mut it, "document.body.firstElementChild.tagName"), "DIV");
        // jQuery support shape: clone().clone().lastChild.checked.
        assert_eq!(
            ev(
                &mut it,
                "var d=document.createElement('div');d.innerHTML=\"<input type='checkbox' checked='checked'/ mother's brother\";\
                 d.cloneNode(true).cloneNode(true).lastChild.checked"
            ),
            "true"
        );
    }

    #[test]
    fn mutation() {
        let mut it = interp(PAGE);
        it.run(
            "var h=document.createElement('h1');h.textContent='INJ';document.body.appendChild(h)",
        )
        .unwrap();
        // createTextNode/createComment: detached until linked.
        it.run("var t=document.createTextNode('hi');document.body.appendChild(t)")
            .unwrap();
        it.run("var c=document.createComment('note');document.body.appendChild(c)")
            .unwrap();
        // Fragments splice children on append (V8); nodeType 11.
        it.run(
            "var f=document.createDocumentFragment();var b=document.createElement('b');\
             b.textContent='bf';f.appendChild(b);document.body.appendChild(f)",
        )
        .unwrap();
        assert_eq!(ev(&mut it, "document.createDocumentFragment().nodeType"), "11");
        // cloneNode: shallow copies bare, deep copies the subtree.
        it.run("var dc=document.getElementById('a').cloneNode(true);dc.id='ac';document.body.appendChild(dc)")
            .unwrap();
        assert_eq!(ev(&mut it, "document.getElementById('ac').textContent"), "one two bold");
        it.run("document.getElementById('a').appendChild(document.getElementById('l'))")
            .unwrap();
        it.run("document.getElementById('i').remove()").unwrap();
        let dom = it.take_dom();
        let h1 = vigia_css::query(&dom, "body > h1").unwrap();
        assert_eq!(vigia_actions::text_content(&dom, h1[0]), "INJ");
        assert!(vigia_actions::text_content(&dom, vigia_css::query(&dom, "body").unwrap()[0])
            .contains("hi"));
        assert_eq!(vigia_css::query(&dom, "body > b").unwrap().len(), 1);
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
    fn constructible_events() {
        let mut it = interp(r#"<body><div id=a></div></body>"#);
        // each type: type + one default + one init-provided value
        assert_eq!(ev(&mut it, "var e0=new Event('x');e0.type"), "x");
        assert_eq!(ev(&mut it, "e0.bubbles"), "false");
        assert_eq!(
            ev(&mut it, "var e1=new Event('y',{bubbles:true});e1.bubbles"),
            "true"
        );
        assert_eq!(
            ev(&mut it, "var c0=new CustomEvent('k',{detail:7});c0.detail"),
            "7"
        );
        assert_eq!(ev(&mut it, "new CustomEvent('k').detail"), "null");
        assert_eq!(
            ev(&mut it, "var m0=new MouseEvent('c',{clientX:5});m0.clientX"),
            "5"
        );
        assert_eq!(ev(&mut it, "m0.screenX"), "0");
        assert_eq!(
            ev(&mut it, "var k0=new KeyboardEvent('d',{key:'Enter'});k0.key"),
            "Enter"
        );
        assert_eq!(ev(&mut it, "k0.keyCode"), "0");
        // missing type throws
        assert!(errmsg(&mut it, "new Event()").contains("type"));
        assert!(errmsg(&mut it, "new CustomEvent(undefined)").contains("type"));
        // instanceof both directions
        assert_eq!(ev(&mut it, "m0 instanceof Event"), "true");
        assert_eq!(ev(&mut it, "k0 instanceof Event"), "true");
        assert_eq!(ev(&mut it, "c0 instanceof Event"), "true");
        assert_eq!(ev(&mut it, "e0 instanceof MouseEvent"), "false");
        assert_eq!(ev(&mut it, "m0 instanceof MouseEvent"), "true");
        // createEvent + initEvent roundtrip
        assert_eq!(
            ev(
                &mut it,
                "var r=document.createEvent('Event');r.initEvent('go',true,false);r.type"
            ),
            "go"
        );
        assert_eq!(ev(&mut it, "r.bubbles"), "true");
        assert_eq!(ev(&mut it, "r.cancelable"), "false");
        assert_eq!(
            ev(
                &mut it,
                "var rm=document.createEvent('MouseEvents');rm.initEvent('mc',false,true);rm.type"
            ),
            "mc"
        );
        assert_eq!(ev(&mut it, "rm.clientX"), "0");
        // dispatchEvent with a constructed CustomEvent keeps detail
        assert_eq!(
            ev(
                &mut it,
                "var got=0;var a=document.getElementById('a');\
                 a.addEventListener('k',function(e){got=e.detail});\
                 a.dispatchEvent(new CustomEvent('k',{detail:7}));got"
            ),
            "7"
        );
        // unknown createEvent name throws
        assert!(errmsg(&mut it, "document.createEvent('Nope')").contains("unknown"));
    }

    #[test]
    fn intersection_observer_visible() {
        let mut it = interp(PAGE);
        assert_eq!(ev(&mut it, "typeof IntersectionObserver"), "function");
        assert!(errmsg(&mut it, "new IntersectionObserver(1)").contains("callback"));
        assert_eq!(
            ev(&mut it, "typeof new IntersectionObserver(function(){},{threshold:0.5}).observe"),
            "function"
        );
        // observe fires one all-visible entry per target; the zero timer
        // drains after the completion value, so read back in a second run.
        it.run(
            "var got=null;var seen=null;var el=document.getElementById('a');\
             var o=new IntersectionObserver(function(e,obs){got=e;seen=obs});\
             o.observe(el)",
        )
        .unwrap();
        assert_eq!(ev(&mut it, "got.length"), "1");
        assert_eq!(ev(&mut it, "got[0].isIntersecting"), "true");
        assert_eq!(ev(&mut it, "got[0].intersectionRatio"), "1");
        assert_eq!(ev(&mut it, "got[0].target === el"), "true");
        assert_eq!(ev(&mut it, "seen === o"), "true");
        assert_eq!(ev(&mut it, "got[0].rootBounds"), "null");
        assert_eq!(ev(&mut it, "typeof got[0].time"), "number");
        assert_eq!(ev(&mut it, "typeof got[0].boundingClientRect"), "object");
        // non-node target throws; re-observing dedupes to one entry.
        assert!(errmsg(&mut it, "o.observe({})").contains("node"));
        it.run("var g2=null;var o3=new IntersectionObserver(function(e){g2=e});o3.observe(el);o3.observe(el)")
            .unwrap();
        assert_eq!(ev(&mut it, "g2.length"), "1");
        // takeRecords already drained empty.
        assert_eq!(ev(&mut it, "Array.isArray(o.takeRecords())"), "true");
        assert_eq!(ev(&mut it, "o.takeRecords().length"), "0");
    }

    #[test]
    fn intersection_observer_cancel() {
        let mut it = interp(PAGE);
        // disconnect before the drain means the callback never fires.
        it.run(
            "var fired=false;var el=document.getElementById('a');\
             var o=new IntersectionObserver(function(){fired=true});\
             o.observe(el);o.disconnect();",
        )
        .unwrap();
        assert_eq!(ev(&mut it, "fired"), "false");
        // unobserve drops one target while the other still fires.
        it.run(
            "var n=0;var b=document.body;\
             var o2=new IntersectionObserver(function(e){n=e.length});\
             o2.observe(el);o2.observe(b);o2.unobserve(el);",
        )
        .unwrap();
        assert_eq!(ev(&mut it, "n"), "1");
    }

    #[test]
    fn event_modifier_state() {
        let mut it = interp(PAGE);
        assert_eq!(
            ev(&mut it, "new KeyboardEvent('d',{ctrlKey:true}).getModifierState('Control')"),
            "true"
        );
        assert_eq!(
            ev(&mut it, "new KeyboardEvent('d',{ctrlKey:true}).getModifierState('Alt')"),
            "false"
        );
        assert_eq!(
            ev(&mut it, "new KeyboardEvent('d',{ctrlKey:true}).getModifierState('CapsLock')"),
            "false"
        );
        assert_eq!(
            ev(&mut it, "new MouseEvent('c',{shiftKey:true}).getModifierState('Shift')"),
            "true"
        );
        assert_eq!(ev(&mut it, "new MouseEvent('c').getModifierState('Meta')"), "false");
        assert_eq!(ev(&mut it, "new MouseEvent('c').getModifierState(5)"), "false");
        assert_eq!(ev(&mut it, "new MouseEvent('c').getModifierState()"), "false");
        assert_eq!(
            ev(&mut it, "document.createEvent('MouseEvents').getModifierState('Alt')"),
            "false"
        );
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
        assert_eq!(out.errors[0].to_string(), "inline#0: zip");
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
        assert_eq!(ev(&mut it, "seen"), "nope is not defined (in f)");
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
