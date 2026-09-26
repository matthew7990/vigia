//! End-to-end tests: real TCP against a Server on port 0 plus a fixed HTML
//! fixture server.

use std::io::{Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};

use vigia_json::Json;
use vigia_serve::Server;

const INDEX: &str = "<!doctype html><html><head><title>Home</title></head><body>\
<h1 id=\"t\">Hello Vigia</h1><a href=\"/two\">next</a>\
<form action=\"/sub\" method=\"post\"><input name=\"q\"><input type=\"submit\" value=\"Go\"></form>\
</body></html>";

const TWO: &str = "<html><body><h1>Page Two</h1></body></html>";

fn serve_req(stream: &mut TcpStream) -> (String, String) {
    let mut buf = Vec::new();
    let mut chunk = [0u8; 4096];
    let head_end = loop {
        let n = stream.read(&mut chunk).unwrap_or(0);
        if n == 0 {
            return (String::new(), String::new());
        }
        buf.extend_from_slice(&chunk[..n]);
        if let Some(p) = buf.windows(4).position(|w| w == b"\r\n\r\n") {
            break p;
        }
    };
    let head = String::from_utf8_lossy(&buf[..head_end]).into_owned();
    let path = head.split_whitespace().nth(1).unwrap_or("/").to_string();
    let len: usize = head
        .split("\r\n")
        .find_map(|l| l.strip_prefix("Content-Length:"))
        .and_then(|v| v.trim().parse().ok())
        .unwrap_or(0);
    let mut body = buf.split_off(head_end + 4);
    while body.len() < len {
        let n = stream.read(&mut chunk).unwrap_or(0);
        if n == 0 {
            break;
        }
        body.extend_from_slice(&chunk[..n]);
    }
    (path, String::from_utf8_lossy(&body).into_owned())
}

/// Fixed pages: /, /two, and POST /sub which echoes its form body.
fn page_server() -> SocketAddr {
    let l = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = l.local_addr().unwrap();
    std::thread::spawn(move || {
        for c in l.incoming() {
            let Ok(mut c) = c else { continue };
            std::thread::spawn(move || {
                let (path, body) = serve_req(&mut c);
                if path.is_empty() {
                    return;
                }
                let page = match path.as_str() {
                    "/two" => TWO.to_string(),
                    "/sub" => format!("<html><body><h1>Submitted</h1><p>{body}</p></body></html>"),
                    _ => INDEX.to_string(),
                };
                let resp = format!(
                    "HTTP/1.1 200 OK\r\nContent-Type: text/html\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{page}",
                    page.len()
                );
                let _ = c.write_all(resp.as_bytes());
            });
        }
    });
    addr
}

/// One request -> (status, parsed json body or Null).
fn http(addr: SocketAddr, method: &str, path: &str, body: &str) -> (u16, Json) {
    let mut s = TcpStream::connect(addr).unwrap();
    let req = format!(
        "{method} {path} HTTP/1.1\r\nHost: {addr}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{body}",
        body.len()
    );
    s.write_all(req.as_bytes()).unwrap();
    let mut raw = String::new();
    s.read_to_string(&mut raw).unwrap();
    let status: u16 = raw[9..12].parse().unwrap();
    let text = raw.split("\r\n\r\n").nth(1).unwrap_or("");
    let body = Json::parse(text).unwrap_or(Json::Null);
    (status, body)
}

/// Raw variant for endpoints that answer with an empty body (MCP 202).
fn http_raw(addr: SocketAddr, method: &str, path: &str, body: &str) -> (u16, String) {
    let mut s = TcpStream::connect(addr).unwrap();
    let req = format!(
        "{method} {path} HTTP/1.1\r\nHost: {addr}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{body}",
        body.len()
    );
    s.write_all(req.as_bytes()).unwrap();
    let mut raw = String::new();
    s.read_to_string(&mut raw).unwrap();
    let status: u16 = raw[9..12].parse().unwrap();
    let text = raw.split("\r\n\r\n").nth(1).unwrap_or("").to_string();
    (status, text)
}

fn num(j: &Json, key: &str) -> f64 {
    match j.get(key) {
        Some(Json::Num(n)) => *n,
        other => panic!("{key} missing or not a number: {other:?}"),
    }
}

fn text_of(j: &Json, key: &str) -> String {
    match j.get(key) {
        Some(Json::Str(s)) => s.clone(),
        other => panic!("{key} missing or not a string: {other:?}"),
    }
}

fn new_session(addr: SocketAddr) -> u64 {
    let (st, j) = http(addr, "POST", "/session", "{}");
    assert_eq!(st, 200, "session create failed: {j}");
    num(&j, "id") as u64
}

#[test]
fn rest_session_roundtrip() {
    let srv = Server::start("127.0.0.1:0").unwrap();
    let base = srv.addr();
    let page = page_server();
    let url = format!("http://{page}/");

    let id = new_session(base);

    // /sessions lists it
    let (st, j) = http(base, "GET", "/sessions", "");
    assert_eq!(st, 200);
    let Json::Arr(list) = j else {
        panic!("bad /sessions")
    };
    assert!(list.iter().any(|e| num(e, "id") == id as f64));

    // snap
    let (st, j) = http(
        base,
        "POST",
        &format!("/session/{id}/snap"),
        &format!("{{\"url\":\"{url}\"}}"),
    );
    assert_eq!(st, 200, "snap failed: {j}");
    assert_eq!(num(&j, "status"), 200.0);
    assert!(text_of(&j, "snapshot").contains("Hello Vigia"));

    // extract
    let (st, j) = http(
        base,
        "POST",
        &format!("/session/{id}/extract"),
        "{\"css\":\"h1\"}",
    );
    assert_eq!(st, 200);
    let nodes = j.get("nodes").unwrap();
    let Json::Arr(nodes) = nodes else {
        panic!("no nodes")
    };
    assert_eq!(text_of(&nodes[0], "text"), "Hello Vigia");
    assert_eq!(text_of(&nodes[0], "role"), "heading");

    // eval mutates the dom; extract reflects it (mutation persisted)
    let (st, j) = http(
        base,
        "POST",
        &format!("/session/{id}/eval"),
        "{\"code\":\"document.getElementById('t').textContent='Mutated'; 40+2\"}",
    );
    assert_eq!(st, 200, "eval failed: {j}");
    assert_eq!(text_of(&j, "result"), "42");
    let (_, j) = http(
        base,
        "POST",
        &format!("/session/{id}/extract"),
        "{\"css\":\"h1\"}",
    );
    let Json::Arr(nodes) = j.get("nodes").unwrap() else {
        panic!("no nodes")
    };
    assert_eq!(text_of(&nodes[0], "text"), "Mutated");

    // globals persist across evals
    let (st, _) = http(
        base,
        "POST",
        &format!("/session/{id}/eval"),
        "{\"code\":\"var kept=9\"}",
    );
    assert_eq!(st, 200);
    let (_, j) = http(
        base,
        "POST",
        &format!("/session/{id}/eval"),
        "{\"code\":\"kept*5\"}",
    );
    assert_eq!(text_of(&j, "result"), "45");

    // click #1 (the link) navigates to /two
    let (st, j) = http(base, "POST", &format!("/session/{id}/click"), "{\"ref\":1}");
    assert_eq!(st, 200, "click failed: {j}");
    assert!(text_of(&j, "snapshot").contains("Page Two"));

    // back to index, fill + submit the form
    http(
        base,
        "POST",
        &format!("/session/{id}/snap"),
        &format!("{{\"url\":\"{url}\"}}"),
    );
    let (st, j) = http(
        base,
        "POST",
        &format!("/session/{id}/fill"),
        "{\"ref\":2,\"value\":\"abc\"}",
    );
    assert_eq!(st, 200, "fill failed: {j}");
    let (st, j) = http(base, "POST", &format!("/session/{id}/submit"), "{}");
    assert_eq!(st, 200, "submit failed: {j}");
    let snap = text_of(&j, "snapshot");
    assert!(snap.contains("Submitted"), "got: {snap}");
    assert!(snap.contains("q=abc"), "got: {snap}");

    // delete; further ops 404
    let (st, j) = http(base, "DELETE", &format!("/session/{id}"), "");
    assert_eq!(st, 200);
    assert_eq!(j.get("ok"), Some(&Json::Bool(true)));
    let (st, _) = http(
        base,
        "POST",
        &format!("/session/{id}/eval"),
        "{\"code\":\"1\"}",
    );
    assert_eq!(st, 404);
}

#[test]
fn run_op_drives_vig_scripts() {
    let srv = Server::start("127.0.0.1:0").unwrap();
    let base = srv.addr();
    let page = page_server();
    let id = new_session(base);

    let script = format!("snap http://{page}/\\nextract h1\\nexpect \\\"Hello Vigia\\\"");
    let body = format!("{{\"script\":\"{script}\"}}");
    let (st, j) = http(base, "POST", &format!("/session/{id}/run"), &body);
    assert_eq!(st, 200, "run failed: {j}");
    let out = text_of(&j, "out");
    assert!(out.contains("- h1 'Hello Vigia'"), "got out: {out}");
    let Json::Arr(audit) = j.get("audit").unwrap() else {
        panic!("no audit")
    };
    assert_eq!(audit.len(), 3);
    assert!(audit.iter().all(|e| e.get("ok") == Some(&Json::Bool(true))));

    // vars resolve $NAME in script args
    let (st, j) = http(
        base,
        "POST",
        "/session",
        "{\"vars\":{\"TARGET\":\"hello\"}}",
    );
    assert_eq!(st, 200);
    let id2 = num(&j, "id") as u64;
    let script = format!("snap http://{page}/\\nexpect $TARGET");
    let (st, j) = http(
        base,
        "POST",
        &format!("/session/{id2}/run"),
        &format!("{{\"script\":\"{script}\"}}"),
    );
    // "hello" is not in the snapshot text ("Hello Vigia" - case differs)
    assert_eq!(st, 200);
    assert_eq!(j.get("ok"), Some(&Json::Bool(false)));
}

#[test]
fn mcp_roundtrip() {
    let srv = Server::start("127.0.0.1:0").unwrap();
    let base = srv.addr();
    let page = page_server();

    let (st, j) = http(
        base,
        "POST",
        "/mcp",
        "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\"}",
    );
    assert_eq!(st, 200);
    let r = j.get("result").unwrap();
    assert_eq!(text_of(r, "protocolVersion"), "2024-11-05");
    assert_eq!(text_of(r.get("serverInfo").unwrap(), "name"), "vigia");

    // notification -> 202, empty body
    let (st, body) = http_raw(
        base,
        "POST",
        "/mcp",
        "{\"jsonrpc\":\"2.0\",\"method\":\"notifications/initialized\"}",
    );
    assert_eq!(st, 202);
    assert!(body.is_empty());

    let (st, j) = http(
        base,
        "POST",
        "/mcp",
        "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"tools/list\"}",
    );
    assert_eq!(st, 200);
    let Json::Arr(tools) = j.get("result").unwrap().get("tools").unwrap() else {
        panic!("no tools")
    };
    assert_eq!(tools.len(), 8);

    // create a session via tools/call
    let (st, j) = http(
        base,
        "POST",
        "/mcp",
        "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"tools/call\",\"params\":{\"name\":\"vigia_session_new\",\"arguments\":{}}}",
    );
    assert_eq!(st, 200);
    let Json::Arr(content) = j.get("result").unwrap().get("content").unwrap() else {
        panic!("no content")
    };
    let text = text_of(&content[0], "text");
    let created = Json::parse(&text).unwrap();
    let id = num(&created, "id") as u64;

    // snap through the same op dispatch
    let call = format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"tools/call\",\"params\":{{\"name\":\"vigia_snap\",\"arguments\":{{\"session_id\":{id},\"url\":\"http://{page}/\"}}}}}}"
    );
    let (st, j) = http(base, "POST", "/mcp", &call);
    assert_eq!(st, 200);
    let r = j.get("result").unwrap();
    assert!(r.get("isError").is_none(), "snap isError: {r}");
    let Json::Arr(content) = r.get("content").unwrap() else {
        panic!("no content")
    };
    let text = text_of(&content[0], "text");
    let snap = Json::parse(&text).unwrap();
    assert!(text_of(&snap, "snapshot").contains("Hello Vigia"));

    // op-level failure (bad css on a live session) -> isError, not protocol error
    let (st, j) = http(
        base,
        "POST",
        "/mcp",
        &format!(
            "{{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"tools/call\",\"params\":{{\"name\":\"vigia_extract\",\"arguments\":{{\"session_id\":{id},\"css\":\"[[[\"}}}}}}"
        ),
    );
    assert_eq!(st, 200);
    assert_eq!(
        j.get("result").unwrap().get("isError"),
        Some(&Json::Bool(true))
    );

    // unknown session id -> also an op-level isError result
    let (st, j) = http(
        base,
        "POST",
        "/mcp",
        "{\"jsonrpc\":\"2.0\",\"id\":6,\"method\":\"tools/call\",\"params\":{\"name\":\"vigia_extract\",\"arguments\":{\"session_id\":999,\"css\":\"h1\"}}}",
    );
    assert_eq!(st, 200);
    assert_eq!(
        j.get("result").unwrap().get("isError"),
        Some(&Json::Bool(true))
    );

    // unknown method / unknown tool
    let (st, j) = http(
        base,
        "POST",
        "/mcp",
        "{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"bogus/method\"}",
    );
    assert_eq!(st, 200);
    assert_eq!(num(j.get("error").unwrap(), "code"), -32601.0);

    let (st, j) = http(
        base,
        "POST",
        "/mcp",
        "{\"jsonrpc\":\"2.0\",\"id\":8,\"method\":\"tools/call\",\"params\":{\"name\":\"nope\",\"arguments\":{}}}",
    );
    assert_eq!(st, 200);
    assert_eq!(num(j.get("error").unwrap(), "code"), -32602.0);

    // close
    let (st, _) = http(
        base,
        "POST",
        "/mcp",
        &format!(
            "{{\"jsonrpc\":\"2.0\",\"id\":9,\"method\":\"tools/call\",\"params\":{{\"name\":\"vigia_session_close\",\"arguments\":{{\"session_id\":{id}}}}}}}"
        ),
    );
    assert_eq!(st, 200);
}

#[test]
fn error_paths() {
    let srv = Server::start("127.0.0.1:0").unwrap();
    let base = srv.addr();

    let (st, j) = http(base, "GET", "/health", "");
    assert_eq!(st, 200);
    assert_eq!(j.get("ok"), Some(&Json::Bool(true)));

    let (st, _) = http(base, "GET", "/nope", "");
    assert_eq!(st, 404);
    let (st, _) = http(base, "PUT", "/health", "");
    assert_eq!(st, 405);

    let (st, _) = http(base, "POST", "/session", "{bad json");
    assert_eq!(st, 400);

    let id = new_session(base);
    // extract with no page -> 409
    let (st, j) = http(
        base,
        "POST",
        &format!("/session/{id}/extract"),
        "{\"css\":\"h1\"}",
    );
    assert_eq!(st, 409);
    assert_eq!(j.get("ok"), Some(&Json::Bool(false)));
    // missing required field -> 400
    let (st, _) = http(base, "POST", &format!("/session/{id}/snap"), "{}");
    assert_eq!(st, 400);
    // unknown op -> 404
    let (st, _) = http(base, "POST", &format!("/session/{id}/bogus"), "{}");
    assert_eq!(st, 404);
    // bad id -> 400
    let (st, _) = http(base, "POST", "/session/abc/eval", "{}");
    assert_eq!(st, 400);
}
