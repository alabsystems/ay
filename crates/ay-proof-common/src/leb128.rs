// Copyright 2026 Andrew Yates
// LEB128 (Little Endian Base 128) unsigned integer decoder.
// Used by binary DRAT and LRAT proof formats.

use crate::error::ParseError;

/// Read a LEB128-encoded unsigned integer as `u64` from `data` starting at `pos`.
/// Returns `(value, new_pos)`.
pub fn read_u64(data: &[u8], mut pos: usize) -> Result<(u64, usize), ParseError> {
    let start = pos;
    let mut value: u64 = 0;
    let mut shift: u32 = 0;
    loop {
        if pos >= data.len() {
            return Err(ParseError::UnexpectedEof { position: pos });
        }
        let byte = data[pos];
        pos += 1;
        let chunk = u64::from(byte & 0x7f);
        // At shift 63 only the lowest chunk bit fits in a u64; anything larger
        // would be silently shifted out, decoding an over-width value as a
        // wrong (possibly zero, i.e. clause-terminator) result.
        if shift == 63 && chunk > 1 {
            return Err(ParseError::Leb128Overflow { position: start });
        }
        value |= chunk << shift;
        if byte & 0x80 == 0 {
            return Ok((value, pos));
        }
        shift += 7;
        if shift >= 64 {
            return Err(ParseError::Leb128Overflow { position: start });
        }
    }
}

/// Read a LEB128-encoded unsigned integer as `u32` from `data` starting at `pos`.
/// Returns `(value, new_pos)`.
pub fn read_u32(data: &[u8], mut pos: usize) -> Result<(u32, usize), ParseError> {
    let start = pos;
    let mut value: u32 = 0;
    let mut shift: u32 = 0;
    loop {
        if pos >= data.len() {
            return Err(ParseError::UnexpectedEof { position: pos });
        }
        let byte = data[pos];
        pos += 1;
        let chunk = u32::from(byte & 0x7f);
        // At shift 28 only the lowest 4 chunk bits fit in a u32; anything
        // larger would be silently shifted out, decoding an over-width value
        // as a wrong (possibly zero, i.e. clause-terminator) result.
        if shift == 28 && chunk > 0x0f {
            return Err(ParseError::Leb128Overflow { position: start });
        }
        value |= chunk << shift;
        if byte & 0x80 == 0 {
            return Ok((value, pos));
        }
        shift += 7;
        if shift >= 32 {
            return Err(ParseError::Leb128Overflow { position: start });
        }
    }
}

#[cfg(test)]
#[path = "leb128_tests.rs"]
mod tests;
