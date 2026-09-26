//! Own HTTP/1.1 client on `std::net` - request line, headers, chunked
//! decoding, redirects, gzip via `vigia-inflate`. TLS is isolated behind
//! `vigia-tls` (the project's one declared dependency exception).
//! Sync and connection-close on purpose; keep-alive pooling is a measured
//! optimization for later.

use std::fmt;
use std::io::{self, Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::time::{Duration, Instant};

use vigia_session::CookieJar;
use vigia_url::Url;

const MAX_REDIRECTS: u32 = 10;
const MAX_HEADER: usize = 64 * 1024;
const MAX_WIRE: usize = 8 * 1024 * 1024;
const MAX_BODY: usize = 16 * 1024 * 1024;
const UA: &str = "vigia/0.1 (+https://github.com/matthew7990/vigia)";

#[derive(Debug)]
pub enum Error {
    Url(vigia_url::UrlError),
    Io(io::Error),
    Tls(String),
    /// Server sent something that is not valid HTTP/1.x.
    Protocol(&'static str),
    /// A hard cap (header, wire, body, redirects) was hit.
    Limit(&'static str),
    Inflate(vigia_inflate::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Url(e) => write!(f, "url: {e}"),
            Self::Io(e) => write!(f, "io: {e}"),
            Self::Tls(m) => write!(f, "tls: {m}"),
            Self::Protocol(m) => write!(f, "protocol: {m}"),
            Self::Limit(m) => write!(f, "limit: {m}"),
            Self::Inflate(e) => write!(f, "inflate: {e}"),
        }
    }
}

impl std::error::Error for Error {}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Self {
        Self::Io(e)
    }
}
impl From<vigia_url::UrlError> for Error {
    fn from(e: vigia_url::UrlError) -> Self {
        Self::Url(e)
    }
}
impl From<vigia_inflate::Error> for Error {
    fn from(e: vigia_inflate::Error) -> Self {
        Self::Inflate(e)
    }
}

/// Wall-clock split of one fetch, for the speed metric.
#[derive(Debug, Default, Clone, Copy)]
pub struct Timings {
    /// DNS + TCP connect.
    pub connect: Duration,
    /// TLS handshake (0 on plain http).
    pub tls: Duration,
    /// Request sent -> status line received.
    pub ttfb: Duration,
    /// Whole request end to end.
    pub total: Duration,
}

#[derive(Debug)]
pub struct Response {
    pub status: u16,
    pub headers: Vec<(String, String)>,
    /// Decoded body (gzip/deflate transparently inflated).
    pub body: Vec<u8>,
    /// After redirects.
    pub final_url: Url,
    /// Bytes read off the wire (compressed size).
    pub wire_bytes: usize,
    pub redirects: u32,
    pub timings: Timings,
}

impl Response {
    /// Body decoded to UTF-8 - BOM, Content-Type charset, then <meta> sniff.
    pub fn text(&self) -> String {
        let ct = self
            .headers
            .iter()
            .find(|(k, _)| k == "content-type")
            .map(|(_, v)| v.as_str());
        vigia_charset::decode_auto(&self.body, vigia_charset::charset_of(ct).as_deref())
    }
}

// TlsStream is a few KB of handshake state; boxing just to quiet the
// lint buys nothing for a two-variant enum.
#[allow(clippy::large_enum_variant)]
enum Conn {
    Plain(TcpStream),
    Tls(vigia_tls::TlsStream),
}

impl Read for Conn {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        match self {
            Self::Plain(t) => t.read(buf),
            Self::Tls(t) => t.read(buf),
        }
    }
}

impl Write for Conn {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        match self {
            Self::Plain(t) => t.write(buf),
            Self::Tls(t) => t.write(buf),
        }
    }
    fn flush(&mut self) -> io::Result<()> {
        match self {
            Self::Plain(t) => t.flush(),
            Self::Tls(t) => t.flush(),
        }
    }
}

/// Counts bytes read off the wire.
struct Metered<C> {
    inner: C,
    n: usize,
}

impl<C: Read> Metered<C> {
    fn take(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let n = self.inner.read(buf)?;
        self.n += n;
        if self.n > MAX_WIRE {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "wire cap exceeded",
            ));
        }
        Ok(n)
    }

    fn byte(&mut self) -> io::Result<Option<u8>> {
        let mut b = [0u8; 1];
        match self.inner.read(&mut b)? {
            0 => Ok(None),
            _ => {
                self.n += 1;
                Ok(Some(b[0]))
            }
        }
    }
}

/// GET `url`, following redirects, applying cookies from `jar` both ways.
pub fn fetch(url: &str, jar: &mut CookieJar) -> Result<Response, Error> {
    run(url, "GET", None, &[], jar)
}

/// POST `url` with an application/x-www-form-urlencoded body.
pub fn post_form(url: &Url, encoded: &str, jar: &mut CookieJar) -> Result<Response, Error> {
    run(&url.to_string(), "POST", Some(encoded.as_bytes()), &[], jar)
}

/// Full request: any method, caller headers on top of the defaults
/// (later duplicates win), any body. The API-replay primitive.
pub fn req(
    url: &str,
    method: &str,
    headers: &[(String, String)],
    body: Option<&[u8]>,
    jar: &mut CookieJar,
) -> Result<Response, Error> {
    run(url, method, body, headers, jar)
}

/// Request loop with redirect handling. POST on 301/302/303 downgrades to
/// GET (browser behavior); 307/308 re-send the body.
fn run(
    url: &str,
    method: &str,
    body: Option<&[u8]>,
    headers: &[(String, String)],
    jar: &mut CookieJar,
) -> Result<Response, Error> {
    let mut current = Url::parse(url)?;
    let mut method = method;
    let mut body = body;
    let mut redirects = 0;
    let mut timings = Timings::default();
    loop {
        let res = request(&current, jar, method, body, headers)?;
        timings.connect += res.timings.connect;
        timings.tls += res.timings.tls;
        timings.ttfb += res.timings.ttfb;
        timings.total += res.timings.total;
        let status = res.status;
        if matches!(status, 301 | 302 | 303 | 307 | 308) {
            if redirects >= MAX_REDIRECTS {
                return Err(Error::Limit("too many redirects"));
            }
            let loc = res
                .headers
                .iter()
                .find(|(k, _)| k == "location")
                .map(|(_, v)| v.trim().to_string())
                .ok_or(Error::Protocol("redirect without location"))?;
            current = res.final_url.join(&loc)?;
            if matches!(status, 301..=303) && method != "GET" {
                method = "GET";
                body = None;
            }
            redirects += 1;
            continue;
        }
        return Ok(Response {
            status: res.status,
            headers: res.headers,
            body: res.body,
            final_url: res.final_url,
            wire_bytes: res.wire_bytes,
            redirects,
            timings,
        });
    }
}

struct StepResponse {
    status: u16,
    headers: Vec<(String, String)>,
    body: Vec<u8>,
    final_url: Url,
    wire_bytes: usize,
    timings: Timings,
}

fn request(
    url: &Url,
    jar: &mut CookieJar,
    method: &str,
    body: Option<&[u8]>,
    extra_headers: &[(String, String)],
) -> Result<StepResponse, Error> {
    let t_total = Instant::now();

    let host = url.host.clone();
    let port = url.port_or_default();
    let addr = if host.contains(':') {
        format!("[{host}]:{port}")
    } else {
        format!("{host}:{port}")
    };
    let tcp = TcpStream::connect(
        addr.to_socket_addrs()?
            .next()
            .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, "no address for host"))?,
    )?;
    tcp.set_read_timeout(Some(Duration::from_secs(20)))?;
    tcp.set_write_timeout(Some(Duration::from_secs(20)))?;
    tcp.set_nodelay(true)?;
    let t_connected = Instant::now();

    let mut conn = if url.is_https() {
        let tls = vigia_tls::connect(tcp, &host).map_err(Error::Tls)?;
        Conn::Tls(tls)
    } else {
        Conn::Plain(tcp)
    };
    let t_tls = Instant::now();

    let mut req = format!(
        "{method} {} HTTP/1.1\r\nHost: {}\r\nUser-Agent: {UA}\r\nAccept: text/html,application/xhtml+xml,application/json;q=0.9,*/*;q=0.5\r\nAccept-Encoding: gzip, deflate\r\nAccept-Language: en-US,en;q=0.9\r\nConnection: close\r\n",
        url.request_target(),
        url.host_header(),
    );
    if let Some(cookie) = jar.header_for(url) {
        let _ = fmt::Write::write_fmt(&mut req, format_args!("Cookie: {cookie}\r\n"));
    }
    let custom_ct = extra_headers
        .iter()
        .any(|(k, _)| k.eq_ignore_ascii_case("content-type"));
    if let Some(b) = body {
        if !custom_ct {
            req.push_str("Content-Type: application/x-www-form-urlencoded\r\n");
        }
        let _ = fmt::Write::write_fmt(&mut req, format_args!("Content-Length: {}\r\n", b.len()));
    }
    for (k, v) in extra_headers {
        let _ = fmt::Write::write_fmt(&mut req, format_args!("{k}: {v}\r\n"));
    }
    req.push_str("\r\n");
    conn.write_all(req.as_bytes())?;
    if let Some(b) = body {
        conn.write_all(b)?;
    }
    conn.flush()?;

    let mut m = Metered { inner: conn, n: 0 };
    let status_line = read_line(&mut m, MAX_HEADER)?;
    let status = parse_status(&status_line)?;
    let t_ttfb = Instant::now();

    let mut headers = Vec::new();
    loop {
        let line = read_line(&mut m, MAX_HEADER)?;
        if line.is_empty() {
            break;
        }
        let (k, v) = line
            .split_once(':')
            .ok_or(Error::Protocol("bad header line"))?;
        headers.push((k.trim().to_ascii_lowercase(), v.trim().to_string()));
    }

    for (k, v) in &headers {
        if k == "set-cookie" {
            jar.store_header(url, v);
        }
    }

    let body = if matches!(status, 100..=199 | 204 | 304) {
        Vec::new()
    } else {
        let te = header(&headers, "transfer-encoding");
        if te.is_some_and(|t| t.to_ascii_lowercase().contains("chunked")) {
            read_chunked(&mut m)?
        } else if let Some(len) = header(&headers, "content-length") {
            let n: usize = len
                .trim()
                .parse()
                .map_err(|_| Error::Protocol("bad content-length"))?;
            if n > MAX_WIRE {
                return Err(Error::Limit("content-length over cap"));
            }
            read_exact_n(&mut m, n)?
        } else {
            read_to_end(&mut m)?
        }
    };

    let body = match header(&headers, "content-encoding").map(|s| s.to_ascii_lowercase()) {
        Some(enc) if enc.contains("gzip") => vigia_inflate::gzip_decode(&body, MAX_BODY)?,
        Some(enc) if enc.contains("deflate") => vigia_inflate::zlib_decode(&body, MAX_BODY)?,
        _ => body,
    };

    Ok(StepResponse {
        status,
        headers,
        body,
        final_url: url.clone(),
        wire_bytes: m.n,
        timings: Timings {
            connect: t_connected - t_total,
            tls: t_tls - t_connected,
            ttfb: t_ttfb - t_tls,
            total: t_total.elapsed(),
        },
    })
}

fn header<'a>(headers: &'a [(String, String)], name: &str) -> Option<&'a str> {
    headers
        .iter()
        .find(|(k, _)| k == name)
        .map(|(_, v)| v.as_str())
}

fn parse_status(line: &str) -> Result<u16, Error> {
    if !line.starts_with("HTTP/") {
        return Err(Error::Protocol("bad status line"));
    }
    line.split_whitespace()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .ok_or(Error::Protocol("bad status code"))
}

/// Read a CRLF-terminated line (LF tolerated). Returns without the terminator.
fn read_line(m: &mut Metered<Conn>, cap: usize) -> Result<String, Error> {
    let mut buf = Vec::with_capacity(128);
    loop {
        let Some(b) = m.byte()? else {
            return if buf.is_empty() {
                Err(Error::Protocol("eof before status line"))
            } else {
                break;
            };
        };
        if b == b'\n' {
            if buf.last() == Some(&b'\r') {
                buf.pop();
            }
            break;
        }
        if buf.len() >= cap {
            return Err(Error::Limit("header line too long"));
        }
        buf.push(b);
    }
    String::from_utf8(buf).map_err(|_| Error::Protocol("non-utf8 header"))
}

fn read_chunked(m: &mut Metered<Conn>) -> Result<Vec<u8>, Error> {
    let mut out = Vec::new();
    loop {
        let line = read_line(m, 128)?;
        let size_str = line.split(';').next().unwrap_or("").trim();
        let size =
            usize::from_str_radix(size_str, 16).map_err(|_| Error::Protocol("bad chunk size"))?;
        if size == 0 {
            // Trailer section: read until empty line.
            loop {
                let t = read_line(m, MAX_HEADER)?;
                if t.is_empty() {
                    return Ok(out);
                }
            }
        }
        if out.len() + size > MAX_WIRE {
            return Err(Error::Limit("chunked body over cap"));
        }
        let chunk = read_exact_n(m, size)?;
        out.extend_from_slice(&chunk);
        expect_crlf(m)?;
    }
}

fn expect_crlf(m: &mut Metered<Conn>) -> Result<(), Error> {
    match (m.byte()?, m.byte()?) {
        (Some(b'\r'), Some(b'\n')) => Ok(()),
        _ => Err(Error::Protocol("missing chunk CRLF")),
    }
}

fn read_exact_n(m: &mut Metered<Conn>, n: usize) -> Result<Vec<u8>, Error> {
    let mut buf = vec![0u8; n];
    let mut got = 0;
    while got < n {
        match m.take(&mut buf[got..])? {
            0 => return Err(Error::Protocol("eof mid-body")),
            k => got += k,
        }
    }
    buf.truncate(got);
    Ok(buf)
}

fn read_to_end(m: &mut Metered<Conn>) -> Result<Vec<u8>, Error> {
    let mut buf = Vec::new();
    loop {
        let mut chunk = [0u8; 8192];
        match m.take(&mut chunk) {
            Ok(0) => break,
            Ok(n) => buf.extend_from_slice(&chunk[..n]),
            // TLS close_notify-less shutdowns surface as UnexpectedEof; keep
            // what arrived (common with `Connection: close`).
            Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => break,
            Err(e) => return Err(e.into()),
        }
    }
    Ok(buf)
}
