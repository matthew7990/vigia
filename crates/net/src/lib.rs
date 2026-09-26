//! Minimal HTTP layer. Sync, streaming, capped reads. No async runtime —
//! concurrency is a roadmap decision (thread-per-session or io_uring, TBD).

use ureq::ResponseExt;
use vigia_session::CookieJar;

#[derive(Debug)]
pub struct Response {
    pub status: u16,
    pub body: String,
    pub final_url: String,
}

#[derive(Debug, thiserror::Error)]
pub enum FetchError {
    #[error("http: {0}")]
    Http(#[from] ureq::Error),
    #[error("io: {0}")]
    Io(#[from] std::io::Error),
}

const MAX_BODY: u64 = 8 * 1024 * 1024; // 8 MiB cap — scraping target, not media

const UA: &str = "vigia/0.1 (+https://github.com/matthew7990/vigia)";

/// GET `url`, applying cookies from `jar` and storing any Set-Cookie back.
pub fn fetch(url: &str, jar: &mut CookieJar) -> Result<Response, FetchError> {
    let mut req = ureq::get(url).header("User-Agent", UA);
    if let Some(cookie) = jar.header_for(url) {
        req = req.header("Cookie", cookie);
    }
    let mut res = req.call()?;
    let status = res.status().as_u16();
    let final_url = res.get_uri().to_string();

    if let Some(set_cookie) = res.headers().get("set-cookie") {
        if let Ok(v) = set_cookie.to_str() {
            jar.store_header(&final_url, v);
        }
    }

    let body = res
        .body_mut()
        .with_config()
        .limit(MAX_BODY)
        .read_to_string()?;
    Ok(Response { status, body, final_url })
}
