//! Session state: cookie jar over `vigia-url`. Correct RFC 6265 matching -
//! domain-match requires a label boundary ("a.com" must not match
//! "evila.com"), path-match requires a segment boundary, Secure only over
//! https. Profile persistence is the next iteration; the jar is the seam.

use vigia_url::Url;

#[derive(Debug, Clone)]
pub struct Cookie {
    pub name: String,
    pub value: String,
    pub domain: String,
    pub path: String,
    pub secure: bool,
    /// No Domain attribute: cookie goes to the exact host only (RFC 6265 5.3).
    pub host_only: bool,
    /// HttpOnly: not readable by JS - matters once vigia-js exists.
    pub http_only: bool,
}

#[derive(Debug, Default)]
pub struct CookieJar {
    cookies: Vec<Cookie>,
}

impl CookieJar {
    pub fn new() -> Self {
        Self::default()
    }

    /// Store a `Set-Cookie` header value received from `url`.
    pub fn store_header(&mut self, url: &Url, header: &str) {
        let mut parts = header.split(';');
        let Some(nv) = parts.next() else { return };
        let Some((name, value)) = nv.split_once('=') else { return };

        let mut cookie = Cookie {
            name: name.trim().to_string(),
            value: value.trim().to_string(),
            domain: url.host.clone(),
            path: default_path(&url.path),
            secure: false,
            host_only: true,
            http_only: false,
        };
        for part in parts {
            let part = part.trim();
            if let Some((k, v)) = part.split_once('=') {
                match k.to_ascii_lowercase().as_str() {
                    "domain" => {
                        cookie.domain = v.trim_start_matches('.').to_string();
                        cookie.host_only = false;
                    }
                    "path" => cookie.path = v.to_string(),
                    _ => {}
                }
            } else if part.eq_ignore_ascii_case("secure") {
                cookie.secure = true;
            } else if part.eq_ignore_ascii_case("httponly") {
                cookie.http_only = true;
            }
        }
        self.cookies.retain(|c| !(c.name == cookie.name && c.domain == cookie.domain));
        self.cookies.push(cookie);
    }

    /// `Cookie:` header value for `url`, if any cookie matches.
    pub fn header_for(&self, url: &Url) -> Option<String> {
        let pairs: Vec<String> = self
            .cookies
            .iter()
            .filter(|c| {
                (if c.host_only {
                    url.host == c.domain
                } else {
                    domain_match(&url.host, &c.domain)
                }) && path_match(&url.path, &c.path)
                    && (!c.secure || url.is_https())
            })
            .map(|c| format!("{}={}", c.name, c.value))
            .collect();
        (!pairs.is_empty()).then(|| pairs.join("; "))
    }

    pub fn len(&self) -> usize {
        self.cookies.len()
    }

    /// Load a persisted jar. Missing file = empty jar; malformed lines are
    /// skipped, not fatal.
    pub fn load(path: &std::path::Path) -> Self {
        let mut jar = Self::new();
        let Ok(text) = std::fs::read_to_string(path) else {
            return jar;
        };
        for line in text.lines() {
            let f: Vec<&str> = line.split('\t').collect();
            if f.len() != 7 {
                continue;
            }
            jar.cookies.push(Cookie {
                name: f[0].to_string(),
                domain: f[1].to_string(),
                path: f[2].to_string(),
                secure: f[3] == "1",
                host_only: f[4] == "1",
                http_only: f[5] == "1",
                value: unescape(f[6]),
            });
        }
        jar
    }

    /// Persist the jar. Own format: TSV, cookie value percent-escaped.
    pub fn save(&self, path: &std::path::Path) -> std::io::Result<()> {
        if let Some(dir) = path.parent() {
            std::fs::create_dir_all(dir)?;
        }
        let mut out = String::new();
        for c in &self.cookies {
            out.push_str(&format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                c.name,
                c.domain,
                c.path,
                c.secure as u8,
                c.host_only as u8,
                c.http_only as u8,
                escape(&c.value),
            ));
        }
        std::fs::write(path, out)
    }
}

fn escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for &b in s.as_bytes() {
        match b {
            b'%' | b'\t' | b'\n' | b'\r' | 0x00..=0x1F | 0x7F..=0xFF => {
                let _ = std::fmt::Write::write_fmt(&mut out, format_args!("%{b:02X}"));
            }
            _ => out.push(b as char),
        }
    }
    out
}

fn unescape(s: &str) -> String {
    let bytes = s.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' && i + 2 < bytes.len() {
            if let Ok(b) = u8::from_str_radix(&s[i + 1..i + 3], 16) {
                out.push(b);
                i += 3;
                continue;
            }
        }
        out.push(bytes[i]);
        i += 1;
    }
    String::from_utf8_lossy(&out).into_owned()
}

/// RFC 6265 5.1.3: string match OR suffix on a label boundary.
fn domain_match(host: &str, domain: &str) -> bool {
    host == domain
        || (host.len() > domain.len()
            && host.ends_with(domain)
            && host.as_bytes()[host.len() - domain.len() - 1] == b'.')
}

/// RFC 6265 5.1.4: string match, or prefix ending at a segment boundary.
fn path_match(path: &str, cookie_path: &str) -> bool {
    if path == cookie_path {
        return true;
    }
    if let Some(rest) = path.strip_prefix(cookie_path) {
        return cookie_path.ends_with('/') || rest.starts_with('/');
    }
    false
}

/// RFC 6265 5.1.4 default-path: path up to but not including the last '/'.
fn default_path(path: &str) -> String {
    match path.rfind('/') {
        Some(0) | None => "/".to_string(),
        Some(i) => path[..i].to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn u(s: &str) -> Url {
        Url::parse(s).unwrap()
    }

    #[test]
    fn roundtrip() {
        let mut jar = CookieJar::new();
        jar.store_header(&u("https://a.com/"), "sid=42; Path=/; Secure");
        assert_eq!(jar.header_for(&u("https://a.com/x")), Some("sid=42".into()));
        assert_eq!(jar.header_for(&u("https://b.com/x")), None);
        // Secure cookie is not sent over plain http.
        assert_eq!(jar.header_for(&u("http://a.com/x")), None);
    }

    #[test]
    fn domain_boundary() {
        let mut jar = CookieJar::new();
        // No Domain attr -> host-only: subdomains must NOT receive it.
        jar.store_header(&u("https://a.com/"), "sid=1; Path=/");
        assert_eq!(jar.header_for(&u("https://evila.com/")), None);
        assert_eq!(jar.header_for(&u("https://sub.a.com/")), None);
        // Explicit Domain -> subdomains do receive it.
        jar.store_header(&u("https://a.com/"), "w=1; Path=/; Domain=a.com");
        assert_eq!(jar.header_for(&u("https://sub.a.com/")), Some("w=1".into()));
    }

    #[test]
    fn path_boundary() {
        let mut jar = CookieJar::new();
        jar.store_header(&u("https://a.com/app/"), "s=1; Path=/app");
        assert_eq!(jar.header_for(&u("https://a.com/app/x")), Some("s=1".into()));
        assert_eq!(jar.header_for(&u("https://a.com/apple")), None);
    }
}
