// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Per-literal and per-clause 64-bit signatures.
//!
//! The signature of a literal `l` is a single-bit bitmap, where the bit
//! position is derived from splitmix of the sign-tagged variable index.
//! Single-bit-per-literal was chosen because:
//!
//! * `OR`-ing signatures is associative and commutative, so clause
//!   signatures can be constructed incrementally in any order.
//! * The filter operation reduces to bitmap `AND/NOT/popcount`, which
//!   compiles to 3 instructions on x86-64 and is vectorisable in
//!   Phase 2.
//! * Hash collisions only make the filter *more* conservative (they
//!   cause it to over-approximate the "may be unit" set), preserving
//!   soundness — see the module-level docs on `lib.rs`.
//!
//! The mixing constant `0x9E37_79B9_7F4A_7C15` is the 64-bit fractional
//! part of the golden ratio used by the splitmix64 PRNG.  It is a
//! well-studied full-period multiplier with good avalanche properties.

/// Splitmix64 multiplier constant — the 64-bit fractional part of the
/// golden ratio.  Used by [splitmix64](https://prng.di.unimi.it/splitmix64.c).
const SPLITMIX_MULT: u64 = 0x9E37_79B9_7F4A_7C15;

/// Return the 64-bit one-hot signature bit for the given DIMACS literal.
///
/// The input is a non-zero signed integer: positive `v` means "variable
/// `v` is true," negative `-v` means "variable `v` is false."  The bit
/// position is computed by splitmix-mixing the (variable, sign) pair
/// into a single `u64` and reducing modulo 64.
///
/// Collisions are expected and tolerated — see module docs for the
/// soundness argument.
///
/// # Panics
///
/// Panics on `literal == 0`, which is not a valid DIMACS literal.
#[inline]
#[must_use]
pub fn literal_bit(literal: i32) -> u64 {
    assert!(literal != 0, "DIMACS literal cannot be zero");
    // Encode (variable, sign) as a single u64 so that `+v` and `-v` hash
    // to different bit positions.  We use 2*var + sign_bit so that the
    // sign toggles the lowest bit of the pre-mix input, maximising the
    // avalanche distance between `+v` and `-v` after the multiply.
    let var_idx = u64::from(literal.unsigned_abs());
    let sign_bit = u64::from(literal < 0);
    let mixed_input = (var_idx << 1) ^ sign_bit;

    // One round of splitmix64.
    let mut z = mixed_input.wrapping_mul(SPLITMIX_MULT);
    z ^= z >> 30;
    z = z.wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z ^= z >> 27;
    z = z.wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^= z >> 31;

    1u64 << (z & 63)
}

/// A 64-bit signature summarising the set of literals in one clause.
///
/// `ClauseSignature(OR_{l ∈ clause} literal_bit(l))`.
///
/// Collisions in the one-hot hash mean two distinct literals may share
/// a bit; the signature is therefore a *superset* bitmap.  This is
/// intentional: it never falsely excludes a literal, only falsely
/// includes additional bits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct ClauseSignature(pub u64);

impl ClauseSignature {
    /// Construct a clause signature by OR-ing the bits of every literal.
    ///
    /// Empty input returns `ClauseSignature(0)`.  Although the empty
    /// clause is the canonical conflict, callers should not normally
    /// invoke this path — an empty clause is detected by exact BCP
    /// before it reaches the filter.  The signature of the empty clause
    /// is `0`, which means `popcount(sig & !mask) == 0`, so the filter
    /// correctly flags it as "may be unit or falsified."
    #[must_use]
    pub fn from_literals(literals: &[i32]) -> Self {
        let mut sig = 0u64;
        for &lit in literals {
            sig |= literal_bit(lit);
        }
        Self(sig)
    }

    /// Construct from a raw `u64` — exposed for tests and for the
    /// Phase 2 scan kernel where signatures are rebuilt in bulk.
    #[must_use]
    pub const fn from_raw(sig: u64) -> Self {
        Self(sig)
    }

    /// Return the underlying 64-bit word.
    #[inline]
    #[must_use]
    pub const fn bits(self) -> u64 {
        self.0
    }
}

#[cfg(test)]
mod unit_tests {
    use super::*;

    #[test]
    fn literal_bit_is_one_hot() {
        for lit in [1, -1, 2, -2, 42, -42, 1000, -1000] {
            let bit = literal_bit(lit);
            assert_eq!(bit.count_ones(), 1, "literal_bit must be one-hot");
        }
    }

    #[test]
    fn literal_bit_polarity_collision_rate_is_low() {
        // Positive and negative of the same variable generally hash to
        // different bits, but with a 64-bit target and single-bit
        // outputs, the birthday-collision rate is ~1/64.  Rather than
        // assert no collisions (which would be wrong — collisions are
        // harmless for soundness), we assert the *rate* stays below
        // the 1/16 threshold we'd expect for a well-mixed hash.
        let mut collisions = 0usize;
        let n = 512;
        for var in 1..=n {
            if literal_bit(var) == literal_bit(-var) {
                collisions += 1;
            }
        }
        #[allow(clippy::cast_precision_loss)]
        let rate = collisions as f64 / f64::from(n);
        assert!(
            rate < 1.0 / 16.0,
            "polarity collision rate {rate:.3} exceeds 1/16 — hash mixing is broken"
        );
    }

    #[test]
    #[should_panic(expected = "DIMACS literal cannot be zero")]
    fn literal_bit_rejects_zero() {
        let _ = literal_bit(0);
    }

    #[test]
    fn clause_signature_is_or_of_bits() {
        let lits = [1i32, -2, 3];
        let expected = literal_bit(1) | literal_bit(-2) | literal_bit(3);
        assert_eq!(ClauseSignature::from_literals(&lits).bits(), expected);
    }

    #[test]
    fn clause_signature_empty_is_zero() {
        assert_eq!(ClauseSignature::from_literals(&[]).bits(), 0);
    }
}
