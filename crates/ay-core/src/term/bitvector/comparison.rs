// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Unsigned maximum of a width-`w` bitvector, i.e. `2^w - 1` (all ones).
fn bv_unsigned_max(width: u32) -> BigInt {
    (BigInt::one() << width) - BigInt::one()
}

/// Unsigned *representation* of the signed maximum of a width-`w` bitvector,
/// i.e. `2^(w-1) - 1`. Requires `width >= 1` (guaranteed by `get_bv_width`,
/// which rejects zero-width sorts).
fn bv_signed_max_bits(width: u32) -> BigInt {
    (BigInt::one() << width.saturating_sub(1)) - BigInt::one()
}

/// Unsigned *representation* of the signed minimum of a width-`w` bitvector,
/// i.e. `2^(w-1)` (two's complement `-2^(w-1)`). Requires `width >= 1`.
fn bv_signed_min_bits(width: u32) -> BigInt {
    BigInt::one() << width.saturating_sub(1)
}

impl TermStore {
    /// Is `id` the bitvector constant `expected` at width `width`?
    ///
    /// Fail-closed: a non-constant term, a non-bitvector term, or a constant
    /// whose declared width differs from `width` all answer `false`, so the
    /// range-bound rules below never fire on an ill-typed (cross-width)
    /// comparison, which has no defined SMT-LIB value.
    fn bv_const_is(&self, id: TermId, width: u32, expected: &BigInt) -> bool {
        matches!(self.get_bitvec(id), Some((v, w)) if w == width && v == expected)
    }

    /// Create unsigned bitvector less-than comparison with constant folding
    ///
    /// Simplifications:
    /// - Constant folding: bvult(#x01, #x02) → true
    /// - Reflexivity: bvult(x, x) → false
    /// - Zero lower bound: bvult(x, 0) → false (nothing is less than 0 unsigned)
    /// - Unsigned upper bound: bvult(2^w-1, x) → false (nothing exceeds all-ones)
    /// - Zero argument: bvult(0, x) → x != 0 (but we just return the comparison)
    pub fn mk_bvult(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(lhs), Sort::BitVec(_)) && matches!(self.sort(rhs), Sort::BitVec(_)),
            "BUG: mk_bvult expects BitVec args"
        );
        debug_assert!(
            self.sort(lhs) == self.sort(rhs),
            "BUG: mk_bvult expects same-width BitVec args"
        );
        // Reflexivity: x < x = false
        if lhs == rhs {
            return self.false_term();
        }

        // Constant folding (unsigned comparison)
        if let (Some((v1, _)), Some((v2, _))) = (self.get_bitvec(lhs), self.get_bitvec(rhs)) {
            return self.mk_bool(v1 < v2);
        }

        // Zero lower bound: bvult(x, 0) = false
        if let Some((v, _)) = self.get_bitvec(rhs) {
            if v.is_zero() {
                return self.false_term();
            }
        }

        // Unsigned upper bound: bvult(2^w-1, x) = false.
        //
        // SOUNDNESS: the unsigned interpretation of every width-`w` bitvector
        // lies in `[0, 2^w-1]`, so `all-ones <u x` is unsatisfiable for every
        // width-`w` `x`. Rewriting it to `false` is an EQUIVALENCE — it
        // preserves every model in both directions, so UNSAT stays UNSAT and
        // SAT stays SAT. This is the exact dual of the `bvult(x, 0) = false`
        // rule above. Both operand widths must agree (`bv_const_is` checks the
        // constant's width against the symbolic side's); a cross-width compare
        // is ill-typed and stays symbolic.
        if let Some(width) = self.get_bv_width(rhs) {
            if self.bv_const_is(lhs, width, &bv_unsigned_max(width)) {
                return self.false_term();
            }
        }

        self.intern(
            TermData::App(Symbol::named("bvult"), vec![lhs, rhs]),
            Sort::Bool,
        )
    }

    /// Create unsigned bitvector less-than-or-equal comparison with constant folding
    ///
    /// Simplifications:
    /// - Constant folding: bvule(#x01, #x02) → true
    /// - Reflexivity: bvule(x, x) → true
    /// - Zero argument: bvule(0, x) → true (0 is <= everything unsigned)
    /// - Unsigned upper bound: bvule(x, 2^w-1) → true (all-ones bounds everything)
    pub fn mk_bvule(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(lhs), Sort::BitVec(_)) && matches!(self.sort(rhs), Sort::BitVec(_)),
            "BUG: mk_bvule expects BitVec args"
        );
        debug_assert!(
            self.sort(lhs) == self.sort(rhs),
            "BUG: mk_bvule expects same-width BitVec args"
        );
        // Reflexivity: x <= x = true
        if lhs == rhs {
            return self.true_term();
        }

        // Constant folding (unsigned comparison)
        if let (Some((v1, _)), Some((v2, _))) = (self.get_bitvec(lhs), self.get_bitvec(rhs)) {
            return self.mk_bool(v1 <= v2);
        }

        // Zero left: bvule(0, x) = true
        if let Some((v, _)) = self.get_bitvec(lhs) {
            if v.is_zero() {
                return self.true_term();
            }
        }

        // Unsigned upper bound: bvule(x, 2^w-1) = true.
        //
        // SOUNDNESS: as in `mk_bvult` — the unsigned interpretation of a
        // width-`w` bitvector is in `[0, 2^w-1]`, so `x <=u all-ones` is a
        // validity of the fixed-width bitvector theory and rewriting it to
        // `true` preserves every model in both directions. Same-width guard
        // as above.
        //
        // This is the missing dual of the `bvule(0, x)` rule. It closes a real
        // asymmetry — the Trust/model-checker-consumer panic-freedom encoding emits
        // machine-integer range facts as the PAIR `0 <=u x /\ x <=u UMAX` and
        // only the first half folded — but MEASURE BEFORE CLAIMING A SPEEDUP:
        // an A/B on `bv_new_clause_count_for_tests` (ay-chc
        // `live_var_range_facts_are_verdict_neutral_and_clause_free_*`) shows
        // the unfolded upper bound already cost ZERO extra bit-blasting
        // clauses, because later preprocessing discharged it. The value here
        // is a smaller/normalized term graph, not a measured solve-time win.
        if let Some(width) = self.get_bv_width(lhs) {
            if self.bv_const_is(rhs, width, &bv_unsigned_max(width)) {
                return self.true_term();
            }
        }

        self.intern(
            TermData::App(Symbol::named("bvule"), vec![lhs, rhs]),
            Sort::Bool,
        )
    }

    /// Create unsigned bitvector greater-than comparison
    ///
    /// Normalized to bvult: bvugt(a, b) → bvult(b, a)
    pub fn mk_bvugt(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        self.mk_bvult(rhs, lhs)
    }

    /// Create unsigned bitvector greater-than-or-equal comparison
    ///
    /// Normalized to bvule: bvuge(a, b) → bvule(b, a)
    pub fn mk_bvuge(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        self.mk_bvule(rhs, lhs)
    }

    /// Helper to interpret a bitvector as a signed (two's complement) value
    pub(super) fn to_signed(value: &BigInt, width: u32) -> BigInt {
        // Saturating: width >= 1 for every valid BitVec sort (see get_bv_width).
        let max_positive = BigInt::one() << width.saturating_sub(1);
        if value >= &max_positive {
            // Negative value: value - 2^width
            let modulus = BigInt::one() << width;
            value - modulus
        } else {
            value.clone()
        }
    }

    /// Helper to convert a signed value back to unsigned bitvector representation
    pub(super) fn from_signed(value: &BigInt, width: u32) -> BigInt {
        if value.is_negative() {
            // Negative value: add 2^width to get unsigned representation
            let modulus = BigInt::one() << width;
            value + modulus
        } else {
            value.clone()
        }
    }

    /// Create signed bitvector less-than comparison with constant folding
    ///
    /// Simplifications:
    /// - Constant folding: bvslt(#xFF, #x01) → true (8-bit: -1 < 1)
    /// - Reflexivity: bvslt(x, x) → false
    /// - Signed range: bvslt(x, SMIN) → false, bvslt(SMAX, x) → false
    pub fn mk_bvslt(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(lhs), Sort::BitVec(_)) && matches!(self.sort(rhs), Sort::BitVec(_)),
            "BUG: mk_bvslt expects BitVec args"
        );
        debug_assert!(
            self.sort(lhs) == self.sort(rhs),
            "BUG: mk_bvslt expects same-width BitVec args"
        );
        // Reflexivity: x < x = false
        if lhs == rhs {
            return self.false_term();
        }

        // Constant folding (signed comparison)
        if let (Some((v1, w1)), Some((v2, _))) = (self.get_bitvec(lhs), self.get_bitvec(rhs)) {
            let s1 = Self::to_signed(v1, w1);
            let s2 = Self::to_signed(v2, w1);
            return self.mk_bool(s1 < s2);
        }

        // Signed range bounds: bvslt(x, SMIN) = false and bvslt(SMAX, x) = false.
        //
        // SOUNDNESS: the two's-complement interpretation of a width-`w`
        // bitvector lies in `[-2^(w-1), 2^(w-1)-1]`, so nothing is strictly
        // below the signed minimum and nothing is strictly above the signed
        // maximum. Both rewrites are EQUIVALENCES (model-preserving in both
        // directions). `SMIN`/`SMAX` are matched on their unsigned bit
        // patterns `2^(w-1)` / `2^(w-1)-1` and the constant's declared width
        // must equal the symbolic side's, so an ill-typed cross-width compare
        // stays symbolic.
        //
        // NOTE the trap this deliberately avoids: `bvsle(x, all-ones)` is NOT
        // a tautology — all-ones is signed `-1`, not the signed maximum.
        if let Some(width) = self.get_bv_width(lhs) {
            if self.bv_const_is(rhs, width, &bv_signed_min_bits(width)) {
                return self.false_term();
            }
        }
        if let Some(width) = self.get_bv_width(rhs) {
            if self.bv_const_is(lhs, width, &bv_signed_max_bits(width)) {
                return self.false_term();
            }
        }

        self.intern(
            TermData::App(Symbol::named("bvslt"), vec![lhs, rhs]),
            Sort::Bool,
        )
    }

    /// Create signed bitvector less-than-or-equal comparison with constant folding
    ///
    /// Simplifications:
    /// - Constant folding: bvsle(#xFF, #x01) → true (8-bit: -1 <= 1)
    /// - Reflexivity: bvsle(x, x) → true
    /// - Signed range: bvsle(x, SMAX) → true, bvsle(SMIN, x) → true
    pub fn mk_bvsle(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        debug_assert!(
            matches!(self.sort(lhs), Sort::BitVec(_)) && matches!(self.sort(rhs), Sort::BitVec(_)),
            "BUG: mk_bvsle expects BitVec args"
        );
        debug_assert!(
            self.sort(lhs) == self.sort(rhs),
            "BUG: mk_bvsle expects same-width BitVec args"
        );
        // Reflexivity: x <= x = true
        if lhs == rhs {
            return self.true_term();
        }

        // Constant folding (signed comparison)
        if let (Some((v1, w1)), Some((v2, _))) = (self.get_bitvec(lhs), self.get_bitvec(rhs)) {
            let s1 = Self::to_signed(v1, w1);
            let s2 = Self::to_signed(v2, w1);
            return self.mk_bool(s1 <= s2);
        }

        // Signed range bounds: bvsle(x, SMAX) = true and bvsle(SMIN, x) = true.
        //
        // SOUNDNESS: dual of the `mk_bvslt` rules — the two's-complement value
        // of a width-`w` bitvector is in `[-2^(w-1), 2^(w-1)-1]`, so both are
        // validities of the theory and rewriting them to `true` preserves
        // every model in both directions. Same-width guard as above; and note
        // again that all-ones is signed `-1`, NOT `SMAX`, so `bvsle(x, ~0)`
        // deliberately does not fold here.
        if let Some(width) = self.get_bv_width(lhs) {
            if self.bv_const_is(rhs, width, &bv_signed_max_bits(width)) {
                return self.true_term();
            }
        }
        if let Some(width) = self.get_bv_width(rhs) {
            if self.bv_const_is(lhs, width, &bv_signed_min_bits(width)) {
                return self.true_term();
            }
        }

        self.intern(
            TermData::App(Symbol::named("bvsle"), vec![lhs, rhs]),
            Sort::Bool,
        )
    }

    /// Create signed bitvector greater-than comparison
    ///
    /// Normalized to bvslt: bvsgt(a, b) → bvslt(b, a)
    pub fn mk_bvsgt(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        self.mk_bvslt(rhs, lhs)
    }

    /// Create signed bitvector greater-than-or-equal comparison
    ///
    /// Normalized to bvsle: bvsge(a, b) → bvsle(b, a)
    pub fn mk_bvsge(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        self.mk_bvsle(rhs, lhs)
    }
}
