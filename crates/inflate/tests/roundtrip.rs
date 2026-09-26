use vigia_inflate::{adler32, crc32, gzip_decode, inflate, zlib_decode};

#[test]
fn gzip_dynamic_block() {
    let data = include_bytes!("data/lorem.txt.gz");
    let want = include_bytes!("data/lorem.txt");
    assert_eq!(gzip_decode(data, usize::MAX).unwrap(), want);
}

#[test]
fn deflate_fixed_block() {
    let data = include_bytes!("data/short.deflate");
    let want = include_bytes!("data/short.txt");
    assert_eq!(inflate(data, usize::MAX).unwrap(), want);
}

#[test]
fn deflate_stored_block() {
    let data = include_bytes!("data/stored.deflate");
    let want = include_bytes!("data/short.txt");
    assert_eq!(inflate(data, usize::MAX).unwrap(), want);
}

#[test]
fn zlib_wrapped() {
    let data = include_bytes!("data/lorem.zlib");
    let want = include_bytes!("data/lorem.txt");
    assert_eq!(zlib_decode(data, usize::MAX).unwrap(), want);
}

#[test]
fn limit_is_enforced() {
    let data = include_bytes!("data/lorem.txt.gz");
    assert!(gzip_decode(data, 100).is_err());
}

#[test]
fn checksums() {
    assert_eq!(crc32(b"123456789"), 0xCBF4_3926);
    assert_eq!(adler32(b"123456789"), 0x091E_01DE);
}
