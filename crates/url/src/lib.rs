//! Own URL parser and resolver - the piece redirects, cookies and links stand
//! on. Pragmatic WHATWG-style subset for http/https plus opaque schemes.
//! No IDN/punycode, no percent-decoding of components (only encoding of
//! characters that must not appear raw).

use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Url {
    pub scheme: String,
    /// Host without brackets for IPv6, lowercased. Empty for opaque schemes.
    pub host: String,
    pub port: Option<u16>,
    /// Starts with '/' on hierarchical URLs; arbitrary text on opaque ones.
    pub path: String,
    pub query: Option<String>,
    pub fragment: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UrlError {
    Empty,
    MissingScheme,
    BadScheme,
    MissingHost,
    BadPort,
}

impl fmt::Display for UrlError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::Empty => "empty url",
            Self::MissingScheme => "missing scheme",
            Self::BadScheme => "bad scheme",
            Self::MissingHost => "missing host",
            Self::BadPort => "bad port",
        };
        f.write_str(s)
    }
}

impl std::error::Error for UrlError {}

pub fn default_port(scheme: &str) -> Option<u16> {
    match scheme {
        "http" => Some(80),
        "https" => Some(443),
        "ws" => Some(80),
        "wss" => Some(443),
        "ftp" => Some(21),
        _ => None,
    }
}

fn is_special(scheme: &str) -> bool {
    default_port(scheme).is_some()
}

fn split_once_opt<'a>(s: &'a str, pat: char) -> (&'a str, Option<&'a str>) {
    match s.split_once(pat) {
        Some((a, b)) => (a, Some(b)),
        None => (s, None),
    }
}

impl Url {
    pub fn parse(input: &str) -> Result<Self, UrlError> {
        let input = input.trim_matches(|c: char| c <= ' ');
        if input.is_empty() {
            return Err(UrlError::Empty);
        }

        // scheme = ALPHA *(ALPHA / DIGIT / "+" / "-" / ".")
        let colon = input.find(':').ok_or(UrlError::MissingScheme)?;
        let scheme = &input[..colon];
        if scheme.is_empty()
            || !scheme.as_bytes()[0].is_ascii_alphabetic()
            || !scheme
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'+' | b'-' | b'.'))
        {
            return Err(UrlError::BadScheme);
        }
        let scheme = scheme.to_ascii_lowercase();
        let rest = &input[colon + 1..];

        if !is_special(&scheme) {
            // Opaque: mailto:, data:, tel:, etc.
            let (no_frag, frag) = split_once_opt(rest, '#');
            let (path, query) = split_once_opt(no_frag, '?');
            return Ok(Url {
                scheme,
                host: String::new(),
                port: None,
                path: path.to_string(),
                query: query.map(str::to_string),
                fragment: frag.map(str::to_string),
            });
        }

        let mut rest = rest;
        if let Some(r) = rest.strip_prefix("//") {
            rest = r;
        }
        let auth_end = rest.find(['/', '?', '#']).unwrap_or(rest.len());
        let (auth, after) = rest.split_at(auth_end);
        let (host, port) = parse_authority(auth)?;
        if host.is_empty() {
            return Err(UrlError::MissingHost);
        }

        let (no_frag, frag) = split_once_opt(after, '#');
        let (pq, query) = split_once_opt(no_frag, '?');
        let mut path = if pq.is_empty() { "/".to_string() } else { pq.to_string() };
        normalize_path(&mut path);
        path = pct_encode(&path, C_PATH);
        Ok(Url {
            scheme,
            host,
            port,
            path,
            query: query.map(|q| pct_encode(&q, C_QUERY)),
            fragment: frag.map(str::to_string),
        })
    }

    /// Resolve `input` (possibly relative) against this URL.
    pub fn join(&self, input: &str) -> Result<Url, UrlError> {
        let input = input.trim_matches(|c: char| c <= ' ');
        if input.is_empty() {
            let mut u = self.clone();
            u.fragment = None;
            return Ok(u);
        }
        if looks_like_scheme(input) {
            return Url::parse(input);
        }
        if !is_special(&self.scheme) {
            return Err(UrlError::MissingHost);
        }

        let (scheme, host, port, mut path, query);

        let (rest, frag) = split_once_opt(input, '#');
        if let Some(r) = rest.strip_prefix("//") {
            let (h, p) = parse_authority(r.split(['/', '?']).next().unwrap_or(r))?;
            let tail = &r[r.find(['/', '?']).unwrap_or(r.len())..];
            let (pq, q) = split_once_opt(tail, '?');
            scheme = self.scheme.clone();
            host = h;
            port = p;
            path = if pq.is_empty() { "/".to_string() } else { pq.to_string() };
            query = q.map(str::to_string);
        } else if rest.starts_with('/') {
            scheme = self.scheme.clone();
            host = self.host.clone();
            port = self.port;
            let (p_only, q) = split_once_opt(rest, '?');
            path = p_only.to_string();
            query = q.map(str::to_string);
        } else {
            let (p_only, q) = split_once_opt(rest, '?');
            scheme = self.scheme.clone();
            host = self.host.clone();
            port = self.port;
            if p_only.is_empty() {
                path = self.path.clone();
                query = if q.is_some() {
                    q.map(str::to_string)
                } else {
                    self.query.clone()
                };
            } else {
                let dir = match self.path.rfind('/') {
                    Some(i) => &self.path[..i + 1],
                    None => "/",
                };
                path = format!("{dir}{p_only}");
                query = q.map(str::to_string);
            }
        }

        normalize_path(&mut path);
        path = pct_encode(&path, C_PATH);
        Ok(Url {
            scheme,
            host,
            port,
            path,
            query: query.map(|q| pct_encode(&q, C_QUERY)),
            fragment: frag.map(str::to_string),
        })
    }

    pub fn is_https(&self) -> bool {
        self.scheme == "https"
    }

    /// "host" or "host:port" - for the Host header and SNI display.
    pub fn host_header(&self) -> String {
        match self.port {
            Some(p) if Some(p) != default_port(&self.scheme) => format!("{}:{}", self.host, p),
            _ => self.host.clone(),
        }
    }

    pub fn authority(&self) -> String {
        self.host_header()
    }

    pub fn port_or_default(&self) -> u16 {
        self.port.or_else(|| default_port(&self.scheme)).unwrap_or(80)
    }

    /// path + query, never empty - what goes on the request line.
    pub fn request_target(&self) -> String {
        match &self.query {
            Some(q) => format!("{}?{}", self.path, q),
            None => self.path.clone(),
        }
    }
}

fn looks_like_scheme(s: &str) -> bool {
    match s.find(':') {
        None => false,
        Some(i) => {
            let cand = &s[..i];
            !cand.is_empty()
                && cand.as_bytes()[0].is_ascii_alphabetic()
                && cand
                    .bytes()
                    .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'+' | b'-' | b'.'))
        }
    }
}

fn parse_authority(auth: &str) -> Result<(String, Option<u16>), UrlError> {
    // Userinfo is rejected: credentials in URLs are an anti-pattern we don't carry.
    let auth = match auth.rfind('@') {
        Some(i) => &auth[i + 1..],
        None => auth,
    };
    if let Some(rest) = auth.strip_prefix('[') {
        // IPv6 literal.
        let end = rest.find(']').ok_or(UrlError::MissingHost)?;
        let host = &rest[..end];
        let tail = &rest[end + 1..];
        let port = match tail.strip_prefix(':') {
            Some(p) => Some(p.parse::<u16>().map_err(|_| UrlError::BadPort)?),
            None => None,
        };
        return Ok((host.to_string(), port));
    }
    match auth.rsplit_once(':') {
        Some((h, p)) => Ok((
            h.to_ascii_lowercase(),
            Some(p.parse::<u16>().map_err(|_| UrlError::BadPort)?),
        )),
        None => Ok((auth.to_ascii_lowercase(), None)),
    }
}

/// RFC 3986 section 5.2.4 dot-segment removal, in place.
fn normalize_path(path: &mut String) {
    if !path.contains('.') {
        return;
    }
    let absolute = path.starts_with('/');
    let trailing = path.ends_with('/') || path.ends_with("/.") || path.ends_with("/..");
    let mut out: Vec<&str> = Vec::new();
    for seg in path.split('/') {
        match seg {
            "." => {}
            ".." => {
                out.pop();
            }
            s => out.push(s),
        }
    }
    let mut joined = out.join("/");
    if absolute && !joined.starts_with('/') {
        joined.insert(0, '/');
    }
    if trailing && !joined.ends_with('/') {
        joined.push('/');
    }
    if joined.is_empty() {
        joined.push('/');
    }
    *path = joined;
}

// Percent-encode sets (minimal - only what must never appear raw).
const C_PATH: &str = " \"<>\\^`{|}";
const C_QUERY: &str = " \"#<>";

fn pct_encode(s: &str, extra: &str) -> String {
    if !s.bytes().any(|b| b < 0x20 || b >= 0x7F || extra.contains(b as char)) {
        return s.to_string();
    }
    let mut out = String::with_capacity(s.len());
    for &b in s.as_bytes() {
        if b < 0x20 || b >= 0x7F || extra.contains(b as char) {
            let _ = std::fmt::Write::write_fmt(&mut out, format_args!("%{b:02X}"));
        } else {
            out.push(b as char);
        }
    }
    out
}

impl fmt::Display for Url {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.scheme)?;
        if self.host.is_empty() {
            write!(f, ":{}", self.path)?;
        } else {
            if self.host.contains(':') && !self.host.starts_with('[') {
                write!(f, "://[{}]", self.host)?;
            } else {
                write!(f, "://{}", self.host)?;
            }
            if let Some(p) = self.port {
                write!(f, ":{p}")?;
            }
            write!(f, "{}", self.path)?;
        }
        if let Some(q) = &self.query {
            write!(f, "?{q}")?;
        }
        if let Some(fr) = &self.fragment {
            write!(f, "#{fr}")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_full() {
        let u = Url::parse("HTTPS://Example.COM:8443/a/../b?x=1#f").unwrap();
        assert_eq!(u.scheme, "https");
        assert_eq!(u.host, "example.com");
        assert_eq!(u.port, Some(8443));
        assert_eq!(u.path, "/b");
        assert_eq!(u.query.as_deref(), Some("x=1"));
        assert_eq!(u.fragment.as_deref(), Some("f"));
    }

    #[test]
    fn default_path_and_port() {
        let u = Url::parse("http://example.com").unwrap();
        assert_eq!(u.path, "/");
        assert_eq!(u.port_or_default(), 80);
        assert_eq!(u.host_header(), "example.com");
    }

    #[test]
    fn joins() {
        let b = Url::parse("https://a.com/dir/page").unwrap();
        assert_eq!(b.join("x").unwrap().to_string(), "https://a.com/dir/x");
        assert_eq!(b.join("/y").unwrap().to_string(), "https://a.com/y");
        assert_eq!(
            b.join("//b.com/z").unwrap().to_string(),
            "https://b.com/z"
        );
        assert_eq!(
            b.join("?q=1").unwrap().to_string(),
            "https://a.com/dir/page?q=1"
        );
        assert_eq!(
            b.join("http://c.com/").unwrap().to_string(),
            "http://c.com/"
        );
    }

    #[test]
    fn display_keeps_port() {
        let u = Url::parse("http://127.0.0.1:8890/login").unwrap();
        assert_eq!(u.to_string(), "http://127.0.0.1:8890/login");
        assert_eq!(u.join("/x").unwrap().to_string(), "http://127.0.0.1:8890/x");
    }

    #[test]
    fn ipv6() {
        let u = Url::parse("http://[::1]:8080/x").unwrap();
        assert_eq!(u.host, "::1");
        assert_eq!(u.port, Some(8080));
    }
}
