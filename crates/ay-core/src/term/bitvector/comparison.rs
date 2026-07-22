// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl TermStore {
    /// Create unsigned bitvector less-than comparison with constant folding
    ///
    /// Simplifications:
    /// - Constant folding: bvult(#x01, #x02) → true
    /// - Reflexivity: bvult(x, x) → false
    /// - Zero lower bound: bvult(x, 0) → false (nothing is less than 0 unsigned)
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
        let max_positive = BigInt::one() << (width - 1);
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
