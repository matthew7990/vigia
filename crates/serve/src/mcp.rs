//! Minimal MCP-over-HTTP: JSON-RPC 2.0 single messages (arrays accepted).
//! Tool calls map onto the same `call_op` dispatch the REST endpoints use -
//! this layer only translates envelopes, never reimplements ops.

use vigia_json::Json;

use crate::Server;

const PROTOCOL: &str = "2024-11-05";

/// op failure already rendered as an {ok:false,error} body vs a
/// protocol-level JSON-RPC error.
enum McpFail {
    Op(Json),
    Rpc(i64, String),
}

impl Server {
    /// POST /mcp. A message that produces no response (notifications/*)
    /// comes back as 202 with an empty body.
    pub(crate) fn mcp(&self, body: &[u8]) -> (u16, String) {
        let text = String::from_utf8_lossy(body);
        match Json::parse(text.trim()) {
            Err(e) => (
                400,
                rpc_err(&Json::Null, -32700, &e.to_string()).to_string(),
            ),
            Ok(Json::Arr(items)) => {
                let resp: Vec<Json> = items.iter().filter_map(|m| self.mcp_msg(m)).collect();
                if resp.is_empty() {
                    (202, String::new())
                } else {
                    (200, Json::Arr(resp).to_string())
                }
            }
            Ok(msg) => match self.mcp_msg(&msg) {
                Some(r) => (200, r.to_string()),
                None => (202, String::new()),
            },
        }
    }

    /// One JSON-RPC message -> its response object, or None for
    /// notifications (no reply, per JSON-RPC).
    fn mcp_msg(&self, msg: &Json) -> Option<Json> {
        let Json::Obj(_) = msg else {
            return Some(rpc_err(&Json::Null, -32600, "invalid request"));
        };
        let id = msg.get("id").cloned().unwrap_or(Json::Null);
        let Some(Json::Str(method)) = msg.get("method") else {
            return Some(rpc_err(&id, -32600, "missing method"));
        };
        if method.starts_with("notifications/") {
            return None;
        }
        let params = msg.get("params").cloned().unwrap_or(Json::Obj(vec![]));
        Some(match method.as_str() {
            "initialize" => rpc_ok(
                id,
                Json::Obj(vec![
                    ("protocolVersion".into(), s(PROTOCOL)),
                    (
                        "capabilities".into(),
                        Json::Obj(vec![("tools".into(), Json::Obj(vec![]))]),
                    ),
                    (
                        "serverInfo".into(),
                        Json::Obj(vec![
                            ("name".into(), s("vigia")),
                            ("version".into(), s(env!("CARGO_PKG_VERSION"))),
                        ]),
                    ),
                ]),
            ),
            "ping" => rpc_ok(id, Json::Obj(vec![])),
            "tools/list" => rpc_ok(id, Json::Obj(vec![("tools".into(), tools())])),
            "tools/call" => {
                let name = match params.get("name") {
                    Some(Json::Str(n)) => n.clone(),
                    _ => return Some(rpc_err(&id, -32602, "tools/call needs params.name")),
                };
                let args = params
                    .get("arguments")
                    .cloned()
                    .unwrap_or(Json::Obj(vec![]));
                match self.mcp_tool(&name, &args) {
                    Ok(j) => rpc_ok(id, tool_result(&j, false)),
                    Err(McpFail::Op(j)) => rpc_ok(id, tool_result(&j, true)),
                    Err(McpFail::Rpc(code, msg)) => rpc_err(&id, code, &msg),
                }
            }
            _ => rpc_err(&id, -32601, "method not found"),
        })
    }

    /// Tool name -> the same ops the REST endpoints hit. Any non-200 op
    /// result is a tool-level error (isError), not a protocol error.
    fn mcp_tool(&self, name: &str, args: &Json) -> Result<Json, McpFail> {
        let op = match name {
            "vigia_session_new" => None,
            "vigia_session_close" => None,
            "vigia_snap" => Some("snap"),
            "vigia_click" => Some("click"),
            "vigia_fill" => Some("fill"),
            "vigia_submit" => Some("submit"),
            "vigia_extract" => Some("extract"),
            "vigia_eval" => Some("eval"),
            "vigia_net" => Some("net"),
            _ => return Err(McpFail::Rpc(-32602, format!("unknown tool: {name}"))),
        };
        let (status, j) = match op {
            None if name == "vigia_session_new" => self.create_session(args),
            None => match session_id(args) {
                Ok(id) => self.delete_session(id),
                Err(msg) => (400, crate::err_json(&msg)),
            },
            Some(op) => match session_id(args) {
                Ok(id) => self.call_op(id, op, args.clone()),
                Err(msg) => (400, crate::err_json(&msg)),
            },
        };
        if status == 200 {
            Ok(j)
        } else {
            Err(McpFail::Op(j))
        }
    }
}

fn session_id(args: &Json) -> Result<u64, String> {
    match args.get("session_id") {
        Some(Json::Num(n)) if *n >= 0.0 && n.fract() == 0.0 => Ok(*n as u64),
        Some(Json::Str(s)) => s.parse().map_err(|_| "bad session_id".to_string()),
        Some(_) => Err("session_id must be an integer".into()),
        None => Err("missing field: session_id".into()),
    }
}

/// MCP tool result envelope: the op's JSON body stringified as text content.
fn tool_result(j: &Json, is_error: bool) -> Json {
    let mut r = vec![(
        "content".into(),
        Json::Arr(vec![Json::Obj(vec![
            ("type".into(), s("text")),
            ("text".into(), s(&j.to_string())),
        ])]),
    )];
    if is_error {
        r.push(("isError".into(), Json::Bool(true)));
    }
    Json::Obj(r)
}

fn rpc_ok(id: Json, result: Json) -> Json {
    Json::Obj(vec![
        ("jsonrpc".into(), s("2.0")),
        ("id".into(), id),
        ("result".into(), result),
    ])
}

fn rpc_err(id: &Json, code: i64, msg: &str) -> Json {
    Json::Obj(vec![
        ("jsonrpc".into(), s("2.0")),
        ("id".into(), id.clone()),
        (
            "error".into(),
            Json::Obj(vec![
                ("code".into(), Json::Num(code as f64)),
                ("message".into(), s(msg)),
            ]),
        ),
    ])
}

fn s(v: &str) -> Json {
    Json::Str(v.into())
}

fn prop(ty: &str, desc: &str) -> Json {
    Json::Obj(vec![
        ("type".into(), s(ty)),
        ("description".into(), s(desc)),
    ])
}

fn tool(name: &str, desc: &str, props: Vec<(&str, Json)>, required: &[&str]) -> Json {
    Json::Obj(vec![
        ("name".into(), s(name)),
        ("description".into(), s(desc)),
        (
            "inputSchema".into(),
            Json::Obj(vec![
                ("type".into(), s("object")),
                (
                    "properties".into(),
                    Json::Obj(props.into_iter().map(|(k, v)| (k.into(), v)).collect()),
                ),
                (
                    "required".into(),
                    Json::Arr(required.iter().map(|r| s(r)).collect()),
                ),
            ]),
        ),
    ])
}

fn sid() -> (&'static str, Json) {
    ("session_id", prop("integer", "id from vigia_session_new"))
}

fn tools() -> Json {
    Json::Arr(vec![
        tool(
            "vigia_session_new",
            "create a browsing session; returns {id}",
            vec![
                ("js", prop("boolean", "run page scripts on every load")),
                (
                    "vars",
                    prop("object", "name->string $VAR bindings for the run op"),
                ),
            ],
            &[],
        ),
        tool(
            "vigia_snap",
            "fetch a url in the session and return its semantic snapshot",
            vec![sid(), ("url", prop("string", "absolute http(s) url"))],
            &["session_id", "url"],
        ),
        tool(
            "vigia_click",
            "follow snapshot ref #n (link or submit control) on the current page",
            vec![sid(), ("ref", prop("integer", "snapshot ref number"))],
            &["session_id", "ref"],
        ),
        tool(
            "vigia_fill",
            "set the value of form control #n on the current page",
            vec![
                sid(),
                ("ref", prop("integer", "snapshot ref number")),
                ("value", prop("string", "value to set")),
            ],
            &["session_id", "ref", "value"],
        ),
        tool(
            "vigia_submit",
            "submit a form on the current page",
            vec![
                sid(),
                ("form", prop("string", "optional css selector for the form")),
                ("data", prop("object", "field overrides, name->value")),
            ],
            &["session_id"],
        ),
        tool(
            "vigia_extract",
            "css query over the current page; returns matching nodes",
            vec![sid(), ("css", prop("string", "css selector"))],
            &["session_id", "css"],
        ),
        tool(
            "vigia_eval",
            "evaluate javascript in the session's live page context",
            vec![sid(), ("code", prop("string", "javascript source"))],
            &["session_id", "code"],
        ),
        tool(
            "vigia_net",
            "list the fetch() calls the page's JS made (endpoint discovery)",
            vec![sid()],
            &["session_id"],
        ),
        tool(
            "vigia_session_close",
            "delete a session and free its state",
            vec![sid()],
            &["session_id"],
        ),
    ])
}
