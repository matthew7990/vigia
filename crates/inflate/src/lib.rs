//! Own DEFLATE decoder (RFC 1951) with gzip (RFC 1952) and zlib (RFC 1950)
//! wrappers. Bit-at-a-time decode — simple and auditable. A table-driven
//! fast path is a measured optimization for later, not a v1 need.

const MAXBITS: usize = 15;
const MAXLCODES: usize = 286;
const MAXDCODES: usize = 30;
const FIXLCODES: usize = 288;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// Input ended mid-stream.
    Truncated,
    /// Compressed data is malformed.
    Invalid(&'static str),
    /// Output exceeded the caller's hard cap (anti zip-bomb).
    TooBig,
    /// Stored block LEN/NLEN mismatch.
    BadStoredLen,
    /// gzip header/trailer invalid (magic, method, CRC32, ISIZE).
    BadGzip,
    /// zlib header/trailer invalid (FCHECK, FDICT, Adler32).
    BadZlib,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Truncated => f.write_str("unexpected end of input"),
            Self::Invalid(m) => write!(f, "invalid deflate stream: {m}"),
            Self::TooBig => f.write_str("output exceeds limit"),
            Self::BadStoredLen => f.write_str("stored block: LEN/NLEN mismatch"),
            Self::BadGzip => f.write_str("invalid gzip wrapper"),
            Self::BadZlib => f.write_str("invalid zlib wrapper"),
        }
    }
}

impl std::error::Error for Error {}

/// Bit reader, LSB-first per RFC 1951. Tracks byte position so callers can
/// locate the end of the compressed stream (needed for wrapper trailers).
struct Bits<'a> {
    data: &'a [u8],
    pos: usize,
    buf: u32,
    cnt: u32,
}

impl<'a> Bits<'a> {
    fn new(data: &'a [u8]) -> Self {
        Bits { data, pos: 0, buf: 0, cnt: 0 }
    }

    fn need(&mut self, n: u32) -> Result<(), Error> {
        while self.cnt < n {
            let b = *self.data.get(self.pos).ok_or(Error::Truncated)?;
            self.pos += 1;
            self.buf |= (b as u32) << self.cnt;
            self.cnt += 8;
        }
        Ok(())
    }

    /// Read n bits (0..=25), LSB-first.
    fn take(&mut self, n: u32) -> Result<u32, Error> {
        self.need(n)?;
        let v = self.buf & ((1 << n) - 1);
        self.buf >>= n;
        self.cnt -= n;
        Ok(v)
    }

    /// Drop bits up to the next byte boundary (stored blocks).
    fn align(&mut self) {
        let rem = self.cnt % 8;
        self.buf >>= rem;
        self.cnt -= rem;
    }

    /// Bytes consumed, counting the partially-consumed byte as whole.
    fn consumed(&self) -> usize {
        self.pos
    }
}

/// Huffman decoding table: canonical codes, decoded bit-by-bit.
struct Huffman {
    count: [u16; MAXBITS + 1],
    symbol: Vec<u16>,
}

impl Huffman {
    fn new(lengths: &[u8]) -> Result<Huffman, Error> {
        let mut h = Huffman {
            count: [0; MAXBITS + 1],
            symbol: vec![0; lengths.len()],
        };
        for &len in lengths {
            h.count[len as usize] += 1;
        }
        if h.count[0] as usize == lengths.len() {
            return Ok(h); // no codes at all — decode() will always fail
        }

        // Over-subscription check (incomplete sets are legal).
        let mut left: i32 = 1;
        for len in 1..=MAXBITS {
            left <<= 1;
            left -= h.count[len] as i32;
            if left < 0 {
                return Err(Error::Invalid("over-subscribed code lengths"));
            }
        }

        let mut offs = [0u16; MAXBITS + 1];
        for len in 1..MAXBITS {
            offs[len + 1] = offs[len] + h.count[len];
        }
        for (sym, &len) in lengths.iter().enumerate() {
            if len != 0 {
                h.symbol[offs[len as usize] as usize] = sym as u16;
                offs[len as usize] += 1;
            }
        }
        Ok(h)
    }

    /// Decode one symbol. Returns -1 while the code is still incomplete.
    fn decode(&self, s: &mut Bits) -> Result<u16, Error> {
        let mut code: i32 = 0;
        let mut first: i32 = 0;
        let mut index: i32 = 0;
        for len in 1..=MAXBITS {
            code |= s.take(1)? as i32;
            let count = self.count[len] as i32;
            if code - first < count {
                return Ok(self.symbol[(index + (code - first)) as usize]);
            }
            index += count;
            first = (first + count) << 1;
            code <<= 1;
        }
        Err(Error::Invalid("no matching code"))
    }
}

const LENGTHS_BASE: [u16; 29] = [
    3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131,
    163, 195, 227, 258,
];
const LENGTHS_EXTRA: [u32; 29] = [
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0,
];
const DIST_BASE: [u16; 30] = [
    1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
    2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577,
];
const DIST_EXTRA: [u32; 30] = [
    0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13,
    13,
];
const CLEN_ORDER: [usize; 19] = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];

/// Raw DEFLATE bitstream (no wrapper). `limit` caps output size.
pub fn inflate(data: &[u8], limit: usize) -> Result<Vec<u8>, Error> {
    let mut s = Bits::new(data);
    let mut out = Vec::new();
    loop {
        let last = s.take(1)? != 0;
        match s.take(2)? {
            0 => stored(&mut s, &mut out, limit)?,
            1 => {
                let (lit, dist) = fixed_tables()?;
                codes(&mut s, &mut out, &lit, &dist, limit)?;
            }
            2 => {
                let (lit, dist) = dynamic_tables(&mut s)?;
                codes(&mut s, &mut out, &lit, &dist, limit)?;
            }
            _ => return Err(Error::Invalid("block type 3")),
        }
        if last {
            return Ok(out);
        }
    }
}

/// Like `inflate`, but also reports where the bitstream ended (wrapper trailers).
fn inflate_span(data: &[u8], limit: usize) -> Result<(Vec<u8>, usize), Error> {
    let mut s = Bits::new(data);
    let mut out = Vec::new();
    loop {
        let last = s.take(1)? != 0;
        match s.take(2)? {
            0 => stored(&mut s, &mut out, limit)?,
            1 => {
                let (lit, dist) = fixed_tables()?;
                codes(&mut s, &mut out, &lit, &dist, limit)?;
            }
            2 => {
                let (lit, dist) = dynamic_tables(&mut s)?;
                codes(&mut s, &mut out, &lit, &dist, limit)?;
            }
            _ => return Err(Error::Invalid("block type 3")),
        }
        if last {
            return Ok((out, s.consumed()));
        }
    }
}

fn stored(s: &mut Bits, out: &mut Vec<u8>, limit: usize) -> Result<(), Error> {
    s.align();
    let len = s.take(16)? as usize;
    let nlen = s.take(16)? as usize;
    if len != (!nlen & 0xFFFF) {
        return Err(Error::BadStoredLen);
    }
    for _ in 0..len {
        let b = s.take(8)? as u8;
        if out.len() >= limit {
            return Err(Error::TooBig);
        }
        out.push(b);
    }
    Ok(())
}

fn fixed_tables() -> Result<(Huffman, Huffman), Error> {
    let mut litlen = [0u8; FIXLCODES];
    for (n, len) in litlen.iter_mut().enumerate() {
        *len = match n {
            0..=143 => 8,
            144..=255 => 9,
            256..=279 => 7,
            _ => 8,
        };
    }
    let dist = [5u8; MAXDCODES];
    Ok((Huffman::new(&litlen)?, Huffman::new(&dist)?))
}

fn dynamic_tables(s: &mut Bits) -> Result<(Huffman, Huffman), Error> {
    let nlen = s.take(5)? as usize + 257;
    let ndist = s.take(5)? as usize + 1;
    let ncode = s.take(4)? as usize + 4;
    if nlen > MAXLCODES || ndist > MAXDCODES {
        return Err(Error::Invalid("too many lengths"));
    }

    let mut clen = [0u8; 19];
    for &idx in CLEN_ORDER.iter().take(ncode) {
        clen[idx] = s.take(3)? as u8;
    }
    let clen_h = Huffman::new(&clen)?;

    let mut lengths = vec![0u8; nlen + ndist];
    let mut i = 0;
    while i < nlen + ndist {
        let sym = clen_h.decode(s)?;
        match sym {
            0..=15 => {
                lengths[i] = sym as u8;
                i += 1;
            }
            16 => {
                if i == 0 {
                    return Err(Error::Invalid("repeat with no previous length"));
                }
                let prev = lengths[i - 1];
                let rep = 3 + s.take(2)? as usize;
                if i + rep > nlen + ndist {
                    return Err(Error::Invalid("repeat overrun"));
                }
                for _ in 0..rep {
                    lengths[i] = prev;
                    i += 1;
                }
            }
            17 | 18 => {
                let rep = if sym == 17 { 3 + s.take(3)? } else { 11 + s.take(7)? } as usize;
                if i + rep > nlen + ndist {
                    return Err(Error::Invalid("zero-run overrun"));
                }
                i += rep; // already zeroed
            }
            _ => return Err(Error::Invalid("bad code-length symbol")),
        }
    }
    if lengths[256] == 0 {
        return Err(Error::Invalid("missing end-of-block code"));
    }
    Ok((
        Huffman::new(&lengths[..nlen])?,
        Huffman::new(&lengths[nlen..])?,
    ))
}

fn codes(
    s: &mut Bits,
    out: &mut Vec<u8>,
    lit: &Huffman,
    dist: &Huffman,
    limit: usize,
) -> Result<(), Error> {
    loop {
        let sym = lit.decode(s)?;
        match sym {
            0..=255 => {
                if out.len() >= limit {
                    return Err(Error::TooBig);
                }
                out.push(sym as u8);
            }
            256 => return Ok(()),
            _ => {
                let sym = (sym - 257) as usize;
                if sym >= 29 {
                    return Err(Error::Invalid("bad length symbol"));
                }
                let len = LENGTHS_BASE[sym] as usize + s.take(LENGTHS_EXTRA[sym])? as usize;
                let dsym = dist.decode(s)? as usize;
                if dsym >= 30 {
                    return Err(Error::Invalid("bad distance symbol"));
                }
                let distance = DIST_BASE[dsym] as usize + s.take(DIST_EXTRA[dsym])? as usize;
                if distance > out.len() {
                    return Err(Error::Invalid("distance too far back"));
                }
                if out.len() + len > limit {
                    return Err(Error::TooBig);
                }
                let start = out.len() - distance;
                for i in 0..len {
                    let b = out[start + i];
                    out.push(b);
                }
            }
        }
    }
}

/// zlib (RFC 1950) wrapper. Also accepts a bare DEFLATE stream as a fallback —
/// HTTP "deflate" is famously ambiguous in the wild.
pub fn zlib_decode(data: &[u8], limit: usize) -> Result<Vec<u8>, Error> {
    if data.len() >= 6 {
        let cmf = data[0];
        let flg = data[1];
        let ok = (cmf & 0x0F) == 8 && ((cmf as usize) << 8 | flg as usize) % 31 == 0;
        if ok {
            if flg & 0x20 != 0 {
                return Err(Error::BadZlib); // preset dictionary unsupported
            }
            let (out, used) = inflate_span(&data[2..], limit)?;
            let t = 2 + used;
            if t + 4 > data.len() {
                return Err(Error::Truncated);
            }
            let want = u32::from_be_bytes([data[t], data[t + 1], data[t + 2], data[t + 3]]);
            if want != adler32(&out) {
                return Err(Error::BadZlib);
            }
            return Ok(out);
        }
    }
    inflate(data, limit)
}

/// gzip (RFC 1952) wrapper. Verifies CRC32 + ISIZE trailer.
pub fn gzip_decode(data: &[u8], limit: usize) -> Result<Vec<u8>, Error> {
    if data.len() < 18 || data[0] != 0x1F || data[1] != 0x8B || data[2] != 8 {
        return Err(Error::BadGzip);
    }
    let flg = data[3];
    if flg & 0xE0 != 0 {
        return Err(Error::BadGzip);
    }
    let mut i = 10;
    if flg & 0x04 != 0 {
        // FEXTRA
        if i + 2 > data.len() {
            return Err(Error::Truncated);
        }
        let xlen = u16::from_le_bytes([data[i], data[i + 1]]) as usize;
        i += 2 + xlen;
    }
    for mask in [0x08u8, 0x10] {
        // FNAME, FCOMMENT — zero-terminated
        if flg & mask != 0 {
            match data[i..].iter().position(|&b| b == 0) {
                Some(n) => i += n + 1,
                None => return Err(Error::Truncated),
            }
        }
    }
    if flg & 0x02 != 0 {
        i += 2; // FHCRC — skipped, trailer CRC covers output
    }
    if i >= data.len() {
        return Err(Error::Truncated);
    }

    let (out, used) = inflate_span(&data[i..], limit)?;
    let t = i + used;
    if t + 8 > data.len() {
        return Err(Error::Truncated);
    }
    let crc = u32::from_le_bytes([data[t], data[t + 1], data[t + 2], data[t + 3]]);
    let isize = u32::from_le_bytes([data[t + 4], data[t + 5], data[t + 6], data[t + 7]]);
    if crc != crc32(&out) || isize != (out.len() as u32) {
        return Err(Error::BadGzip);
    }
    Ok(out)
}

const CRC_TABLE: [u32; 256] = build_crc_table();

const fn build_crc_table() -> [u32; 256] {
    let mut table = [0u32; 256];
    let mut n = 0;
    while n < 256 {
        let mut c = n as u32;
        let mut k = 0;
        while k < 8 {
            c = if c & 1 != 0 { 0xEDB8_8320 ^ (c >> 1) } else { c >> 1 };
            k += 1;
        }
        table[n] = c;
        n += 1;
    }
    table
}

pub fn crc32(data: &[u8]) -> u32 {
    let mut c = 0xFFFF_FFFFu32;
    for &b in data {
        c = CRC_TABLE[((c ^ b as u32) & 0xFF) as usize] ^ (c >> 8);
    }
    c ^ 0xFFFF_FFFF
}

pub fn adler32(data: &[u8]) -> u32 {
    const MOD: u32 = 65521;
    let mut a = 1u32;
    let mut b = 0u32;
    for &byte in data {
        a = (a + byte as u32) % MOD;
        b = (b + a) % MOD;
    }
    (b << 16) | a
}
