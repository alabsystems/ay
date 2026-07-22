// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! LEB128 varint encoding for proof-tap micro-op records.
//!
//! All record scalars are LEB128-encoded (proof-tap spec, "Micro-op format"):
//! unsigned values directly, signed values via zigzag. Encodings are
//! length-minimal; decoding is bounds-checked and fails closed on truncated or
//! oversized input.

/// Maximum encoded size of a u128 LEB128 varint (ceil(128 / 7) = 19 bytes).
#[cfg(test)]
pub(crate) const MAX_VARINT_BYTES: usize = 19;

/// Appends `value` as an unsigned LEB128 varint.
pub(crate) fn encode_u128(out: &mut Vec<u8>, mut value: u128) {
    loop {
        let byte = (value & 0x7f) as u8;
        value >>= 7;
        if value == 0 {
            out.push(byte);
            return;
        }
        out.push(byte | 0x80);
    }
}

/// Appends `value` as an unsigned LEB128 varint.
pub(crate) fn encode_u64(out: &mut Vec<u8>, value: u64) {
    encode_u128(out, u128::from(value));
}

/// Appends `value` as a zigzag-mapped LEB128 varint.
pub(crate) fn encode_i128(out: &mut Vec<u8>, value: i128) {
    // Zigzag: map i128 to u128 so small magnitudes stay short.
    let zigzag = ((value << 1) ^ (value >> 127)) as u128;
    encode_u128(out, zigzag);
}

/// Decoding failure: truncated input or a varint wider than the target type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct VarintError;

/// Reads an unsigned LEB128 varint from `bytes[*pos..]`, advancing `*pos`.
pub(crate) fn decode_u128(bytes: &[u8], pos: &mut usize) -> Result<u128, VarintError> {
    let mut value: u128 = 0;
    let mut shift: u32 = 0;
    loop {
        let &byte = bytes.get(*pos).ok_or(VarintError)?;
        *pos += 1;
        let payload = u128::from(byte & 0x7f);
        // The final (19th) byte may only carry the top 2 bits of a u128.
        if shift >= 128 || (shift == 126 && payload > 0x3) {
            return Err(VarintError);
        }
        value |= payload << shift;
        if byte & 0x80 == 0 {
            return Ok(value);
        }
        shift += 7;
    }
}

/// Reads an unsigned LEB128 varint that must fit in a u64.
pub(crate) fn decode_u64(bytes: &[u8], pos: &mut usize) -> Result<u64, VarintError> {
    let wide = decode_u128(bytes, pos)?;
    u64::try_from(wide).map_err(|_| VarintError)
}

/// Reads a zigzag-mapped LEB128 varint.
pub(crate) fn decode_i128(bytes: &[u8], pos: &mut usize) -> Result<i128, VarintError> {
    let zigzag = decode_u128(bytes, pos)?;
    Ok(((zigzag >> 1) as i128) ^ -((zigzag & 1) as i128))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn u128_round_trips_across_magnitudes() {
        let samples: &[u128] = &[
            0,
            1,
            127,
            128,
            300,
            u128::from(u32::MAX),
            u128::from(u64::MAX),
            u128::MAX,
            (1 << 63) - 1,
            1 << 100,
        ];
        for &v in samples {
            let mut buf = Vec::new();
            encode_u128(&mut buf, v);
            assert!(buf.len() <= MAX_VARINT_BYTES);
            let mut pos = 0;
            assert_eq!(decode_u128(&buf, &mut pos), Ok(v), "value {v}");
            assert_eq!(pos, buf.len());
        }
    }

    #[test]
    fn i128_zigzag_round_trips_signed_values() {
        let samples: &[i128] = &[0, 1, -1, 63, -64, 64, -65, i128::MAX, i128::MIN, -1000000];
        for &v in samples {
            let mut buf = Vec::new();
            encode_i128(&mut buf, v);
            let mut pos = 0;
            assert_eq!(decode_i128(&buf, &mut pos), Ok(v), "value {v}");
            assert_eq!(pos, buf.len());
        }
    }

    #[test]
    fn truncated_input_fails_closed() {
        let mut buf = Vec::new();
        encode_u128(&mut buf, 1u128 << 40);
        buf.pop();
        let mut pos = 0;
        assert_eq!(decode_u128(&buf, &mut pos), Err(VarintError));
    }

    #[test]
    fn oversized_varint_fails_closed() {
        // 20 continuation bytes can never be a valid u128 varint.
        let buf = vec![0x80u8; 20];
        let mut pos = 0;
        assert_eq!(decode_u128(&buf, &mut pos), Err(VarintError));
    }

    #[test]
    fn u64_narrowing_fails_on_wide_values() {
        let mut buf = Vec::new();
        encode_u128(&mut buf, u128::from(u64::MAX) + 1);
        let mut pos = 0;
        assert_eq!(decode_u64(&buf, &mut pos), Err(VarintError));
    }
}
