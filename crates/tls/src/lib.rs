//! TLS boundary — the project's single declared third-party dependency,
//! isolated behind `connect()` so the rest of vigia never names it.
//! Contract: own TLS 1.3 (X25519, AES-GCM, SHA-256) replaces this crate in
//! phase 2, validated against it as reference.

use std::net::TcpStream;
use std::sync::OnceLock;

use rustls::pki_types::ServerName;
use rustls::{ClientConfig, ClientConnection, RootCertStore, StreamOwned};

fn config() -> &'static ClientConfig {
    static CFG: OnceLock<ClientConfig> = OnceLock::new();
    CFG.get_or_init(|| {
        let roots = RootCertStore::from_iter(webpki_roots::TLS_SERVER_ROOTS.iter().cloned());
        ClientConfig::builder()
            .with_root_certificates(roots)
            .with_no_client_auth()
    })
}

/// Opaque TLS stream — callers outside this crate never name rustls types.
pub struct TlsStream(StreamOwned<ClientConnection, TcpStream>);

impl std::io::Read for TlsStream {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.0.read(buf)
    }
}

impl std::io::Write for TlsStream {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.0.write(buf)
    }
    fn flush(&mut self) -> std::io::Result<()> {
        self.0.flush()
    }
}

/// Wrap an already-connected TCP stream in TLS, verifying `host` against the
/// Mozilla root set. `host` is bare (no port, no IPv6 brackets).
pub fn connect(tcp: TcpStream, host: &str) -> Result<TlsStream, String> {
    let name = ServerName::try_from(host.to_string()).map_err(|e| format!("bad server name: {e}"))?;
    let conn = ClientConnection::new(std::sync::Arc::new(config().clone()), name)
        .map_err(|e| e.to_string())?;
    Ok(TlsStream(StreamOwned::new(conn, tcp)))
}
