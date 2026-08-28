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
        // which the verifier cannot infer.
        //
        // THE TRUST-ONLY SPELLING EXISTS AND THE HOIST STAYS ANYWAY (measured
        // 2026-08-27, trust-e26541e3). The attribute surface still has no
        // checked invariant/decreases pair; the Trust compiler's native grammar
        // does. Raw native clauses cannot live in this stock-Rust source, but
        // the explicit Trust lane can probe the equivalent function.
        //
        // It was tried. This `loop` was rewritten as
        //   `while shift < 64 invariant shift <= 64 decreases (64 - shift)`
        // — a faithful rewrite, since the hoisted guard IS the loop condition —
        // and the result was 10 obligations instead of 5, with all 5 new ones
        // UNSUPPORTED. The compiler names the gap itself:
        //
        //     e45.transition.call-effect: bb6: loop invariant `shift <= 64` has
        //     no complete exact transition model at bb1
        //
        // The CHC construction emits no transition relation for a loop whose
        // body contains a call with effects; it falls back to a flattened
        // single-formula encoding where the loop-carried locals are free
        // variables, and then correctly refuses to read a refutation of that
        // over-approximation as a refutation of the program. The modular half
        // of the invariant is refused outright — `invariant shift % 7 == 0`
        // gives "references an unsupported or ambiguous MIR value".
        //
        // So the clause would be honest but inert: five UNSUPPORTED rows and a
        // rewrite of hot parsing code for zero proof gain. The hoist remains
        // load-bearing. Revisit when the loop-transition model lands; the
        // blocker is the CHC construction, no longer the grammar.
        //
        // The bare `loop invariant P` form was newer than the measured
        // trust-e26541e3 snapshot; only the `while` probe parsed there.
        //
        // Hoisted here, no invariant is needed: the guard and the use are on
        // one path.
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
