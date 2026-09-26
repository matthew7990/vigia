//! Session state: a minimal cookie jar. Profile persistence (disk-backed
//! jars per named profile) is the next iteration — the jar is the seam.

#[derive(Debug, Clone)]
pub struct Cookie {
    pub name: String,
    pub value: String,
    pub domain: String,
    pub path: String,
    pub secure: bool,
}

#[derive(Debug, Default)]
pub struct CookieJar {
    cookies: Vec<Cookie>,
}

impl CookieJar {
    pub fn new() -> Self {
        Self::default()
    }

    /// Store a `Set-Cookie` header value. Pragmatic parse: name=value plus
    /// Domain/Path/Secure attributes; expires handling is roadmap.
    pub fn store_header(&mut self, url: &str, header: &str) {
        let mut parts = header.split(';');
        let Some(nv) = parts.next() else { return };
        let Some((name, value)) = nv.split_once('=') else { return };

        let host = host_of(url);
        let mut cookie = Cookie {
            name: name.trim().to_string(),
            value: value.trim().to_string(),
            domain: host.clone(),
            path: "/".to_string(),
            secure: false,
        };
        for part in parts {
            let part = part.trim();
            if let Some((k, v)) = part.split_once('=') {
                match k.to_ascii_lowercase().as_str() {
                    "domain" => cookie.domain = v.trim_start_matches('.').to_string(),
                    "path" => cookie.path = v.to_string(),
                    _ => {}
                }
            } else if part.eq_ignore_ascii_case("secure") {
                cookie.secure = true;
            }
        }
        self.cookies.retain(|c| !(c.name == cookie.name && c.domain == cookie.domain));
        self.cookies.push(cookie);
    }

    /// `Cookie:` header value for `url`, if any cookie matches host+path.
    pub fn header_for(&self, url: &str) -> Option<String> {
        let host = host_of(url);
        let path = path_of(url);
        let pairs: Vec<String> = self
            .cookies
            .iter()
            .filter(|c| host.ends_with(&c.domain) && path.starts_with(&c.path))
            .map(|c| format!("{}={}", c.name, c.value))
            .collect();
        if pairs.is_empty() {
            None
        } else {
            Some(pairs.join("; "))
        }
    }

    pub fn len(&self) -> usize {
        self.cookies.len()
    }
}

fn host_of(url: &str) -> String {
    let after_scheme = url.split("://").nth(1).unwrap_or(url);
    after_scheme.split('/').next().unwrap_or("").to_string()
}

fn path_of(url: &str) -> String {
    let after_host = url.split("://").nth(1).unwrap_or("");
    match after_host.find('/') {
        Some(i) => after_host[i..].to_string(),
        None => "/".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip() {
        let mut jar = CookieJar::new();
        jar.store_header("https://a.com/", "sid=42; Path=/; Secure");
        assert_eq!(jar.header_for("https://a.com/x"), Some("sid=42".into()));
        assert_eq!(jar.header_for("https://b.com/x"), None);
    }
}
