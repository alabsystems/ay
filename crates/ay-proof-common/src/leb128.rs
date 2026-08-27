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
        // Loop precondition, checked at the TOP so it DOMINATES the `<< shift`
        // below in straight-line control flow. This check used to sit at the
        // bottom, immediately after `shift += 7`. That is semantically the same
        // point -- nothing observable happens between the bottom of one iteration
        // and the top of the next, and the overflow check still precedes the EOF
        // check, so every input produces the identical `Result` -- but it left the
        // bound reachable only ACROSS THE BACK-EDGE. Relating it to the use then
        // requires an inductive loop invariant (`shift ≡ 0 mod 7 ∧ shift ≤ 63`),
        // which the verifier cannot infer and which STILL has no first-class
        // spelling: the resolver maps only `requires` and `ensures` to contract
        // builtins, `trust::invariant` stays a passthrough no-op, and there is no
        // `decreases` attribute at all (see contracts.rs). The erasing
        // `invariant!` macro that this comment used to name is gone, but nothing
        // replaced it, so the hoist is still load-bearing rather than a
        // workaround awaiting a macro. Hoisted here, no invariant is needed: the
        // guard and the use are on one path.
        if shift >= 64 {
            return Err(ParseError::Leb128Overflow { position: start });
        }
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
    }
}

/// Read a LEB128-encoded unsigned integer as `u32` from `data` starting at `pos`.
/// Returns `(value, new_pos)`.
pub fn read_u32(data: &[u8], mut pos: usize) -> Result<(u32, usize), ParseError> {
    let start = pos;
    let mut value: u32 = 0;
    let mut shift: u32 = 0;
    loop {
        // Hoisted to the top for the same reason as `read_u64` above: the guard
        // must dominate the `<< shift` on one straight-line path, not reach it
        // across the loop back-edge. Semantically identical to the bottom check
        // it replaces -- same relative order against the EOF check, same Result
        // for every input.
        if shift >= 32 {
            return Err(ParseError::Leb128Overflow { position: start });
        }
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
    }
}

#[cfg(test)]
#[path = "leb128_tests.rs"]
mod tests;
