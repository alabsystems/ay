// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_single_byte() {
    assert_eq!(read_u32(&[0x05], 0).unwrap(), (5, 1));
    assert_eq!(read_u64(&[0x05], 0).unwrap(), (5, 1));
}

#[test]
fn test_multi_byte() {
    // 300 = 0b100101100 → LEB128: [0xAC, 0x02]
    assert_eq!(read_u32(&[0xAC, 0x02], 0).unwrap(), (300, 2));
    assert_eq!(read_u64(&[0xAC, 0x02], 0).unwrap(), (300, 2));
}

#[test]
fn test_offset() {
    let data = [0x00, 0x05, 0x00];
    assert_eq!(read_u32(&data, 1).unwrap(), (5, 2));
}

#[test]
fn test_truncated() {
    assert!(read_u32(&[0x80], 0).is_err());
    assert!(read_u64(&[0x80], 0).is_err());
}

#[test]
fn test_overflow_u32() {
    // 5 continuation bytes = 35 bits > 32
    assert!(read_u32(&[0x80, 0x80, 0x80, 0x80, 0x80, 0x01], 0).is_err());
}

#[test]
fn test_overflow_u64() {
    // 10 continuation bytes = 70 bits > 64
    assert!(read_u64(
        &[0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x01],
        0
    )
    .is_err());
}

#[test]
fn test_overflow_u32_final_byte_high_bits() {
    // 2^32 = [0x80, 0x80, 0x80, 0x80, 0x10]: the 5th byte has no continuation
    // bit, so the old code silently truncated to Ok(0) — a clause terminator
    // in binary DRAT. Must be Leb128Overflow instead.
    let err = read_u32(&[0x80, 0x80, 0x80, 0x80, 0x10], 0).unwrap_err();
    assert!(matches!(err, ParseError::Leb128Overflow { position: 0 }));
    // Largest chunk that still fits at shift 28 is 0x0f (u32::MAX) — accepted.
    assert_eq!(
        read_u32(&[0xFF, 0xFF, 0xFF, 0xFF, 0x0F], 0).unwrap(),
        (u32::MAX, 5)
    );
    // Smallest over-width chunk beyond it must be rejected.
    assert!(read_u32(&[0xFF, 0xFF, 0xFF, 0xFF, 0x1F], 0).is_err());
}

#[test]
fn test_overflow_u64_final_byte_high_bits() {
    // 2^64 = 9 continuation bytes then 0x02: the 10th byte has no continuation
    // bit, so the old code silently truncated to Ok(0). Must be Leb128Overflow.
    let mut data = vec![0x80u8; 9];
    data.push(0x02);
    let err = read_u64(&data, 0).unwrap_err();
    assert!(matches!(err, ParseError::Leb128Overflow { position: 0 }));
    // u64::MAX = 9 bytes of 0xFF then 0x01 — the largest valid final chunk.
    let mut max = vec![0xFFu8; 9];
    max.push(0x01);
    assert_eq!(read_u64(&max, 0).unwrap(), (u64::MAX, 10));
    // Any final chunk above 1 at shift 63 must be rejected.
    let mut over = vec![0xFFu8; 9];
    over.push(0x03);
    assert!(read_u64(&over, 0).is_err());
}

#[test]
fn test_zero_value() {
    assert_eq!(read_u32(&[0x00], 0).unwrap(), (0, 1));
    assert_eq!(read_u64(&[0x00], 0).unwrap(), (0, 1));
}

#[test]
fn test_max_u32() {
    // u32::MAX = 4294967295 = LEB128: [0xFF, 0xFF, 0xFF, 0xFF, 0x0F]
    let (val, pos) = read_u32(&[0xFF, 0xFF, 0xFF, 0xFF, 0x0F], 0).unwrap();
    assert_eq!(val, u32::MAX);
    assert_eq!(pos, 5);
}

#[test]
fn test_roundtrip_u64() {
    // Encode then decode a large value
    let val: u64 = 1_000_000;
    let mut encoded = Vec::new();
    let mut v = val;
    loop {
        let byte = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            encoded.push(byte);
            break;
        }
        encoded.push(byte | 0x80);
    }
    let (decoded, _) = read_u64(&encoded, 0).unwrap();
    assert_eq!(decoded, val);
}
