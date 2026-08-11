// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl TermStore {
    /// Create bitvector addition with constant folding and simplifications
    ///
    /// Simplifications:
    /// - Constant folding: bvadd(#x01, #x02) → #x03
    /// - Identity: bvadd(x, 0) → x, bvadd(0, x) → x
    pub fn mk_bvadd(&mut self, args: Vec<TermId>) -> TermId {
        let (a, b, width, args) = match self.prepare_bv_binary_op("bvadd", args) {
            Ok(parts) => parts,
            Err(fallback) => return fallback,
        };

        // Constant folding
        if let (Some((v1, w1)), Some((v2, _))) = (self.get_bitvec(a), self.get_bitvec(b)) {
            let result = Self::bv_mask(&(v1 + v2), w1);
            return self.mk_bitvec(result, w1);
        }

        // Identity: x + 0 = x
        if let Some((v, _)) = self.get_bitvec(b) {
            if v.is_zero() {
                return a;
            }
        }
        if let Some((v, _)) = self.get_bitvec(a) {
            if v.is_zero() {
                return b;
            }
        }

        // Modular cancellation: x + (y - x) = y and (y - x) + x = y.
        if let TermData::App(Symbol::Named(name), sub_args) = self.get(b) {
            if name == "bvsub" && sub_args.len() == 2 && sub_args[1] == a {
                return sub_args[0];
            }
        }
        if let TermData::App(Symbol::Named(name), sub_args) = self.get(a) {
            if name == "bvsub" && sub_args.len() == 2 && sub_args[1] == b {
                return sub_args[0];
            }
        }

        self.mk_bv_binary_app("bvadd", args, width)
    }

    /// Create bitvector subtraction with constant folding and simplifications
    ///
    /// Simplifications:
    /// - Constant folding: bvsub(#x03, #x01) → #x02
    /// - Identity: bvsub(x, 0) → x
    /// - Self-subtraction: bvsub(x, x) → 0
    pub fn mk_bvsub(&mut self, args: Vec<TermId>) -> TermId {
        let (a, b, width, args) = match self.prepare_bv_binary_op("bvsub", args) {
            Ok(parts) => parts,
            Err(fallback) => return fallback,
        };

        // Constant folding (subtraction wraps around)
        if let (Some((v1, w1)), Some((v2, _))) = (self.get_bitvec(a), self.get_bitvec(b)) {
            let modulus = BigInt::one() << w1;
            let result = Self::bv_mask(&((v1 - v2) % &modulus + &modulus), w1);
            return self.mk_bitvec(result, w1);
        }

        // Identity: x - 0 = x
        if let Some((v, _)) = self.get_bitvec(b) {
            if v.is_zero() {
                return a;
            }
        }

        // Self-subtraction: x - x = 0
        if a == b {
            return self.mk_bitvec(BigInt::zero(), width);
        }

        self.mk_bv_binary_app("bvsub", args, width)
    }

    /// Create bitvector multiplication with constant folding and simplifications
    ///
    /// Simplifications:
    /// - Constant folding: bvmul(#x02, #x03) → #x06
    /// - Zero: bvmul(x, 0) → 0, bvmul(0, x) → 0
    /// - Identity: bvmul(x, 1) → x, bvmul(1, x) → x
    /// - Power-of-2 multiply to shift (mul2concat):
    ///   bvmul(x, 2^k) → concat(extract(x, n-k-1, 0), bv_zero(k))
    ///   Eliminates multiplier circuit for power-of-2 constants.
    ///   Reference: Z3 bv_rewriter.cpp:2483-2492
    /// - Negative power-of-2 multiply: bvmul(x, -(2^k)) → bvneg(bvmul(x, 2^k))
    ///   where -(2^k) is the constant whose two's-complement negation is an exact
    ///   power of 2. Composes the (already-sound) mul2concat and bvneg rules.
    /// - Sparse constant multiply: constants with at most four non-zero signed
    ///   binary digits are lowered to at most three modular additions/subtractions.
    pub fn mk_bvmul(&mut self, args: Vec<TermId>) -> TermId {
        let (a, b, width, args) = match self.prepare_bv_binary_op("bvmul", args) {
            Ok(parts) => parts,
            Err(fallback) => return fallback,
        };

        // Constant folding
        if let (Some((v1, w1)), Some((v2, _))) = (self.get_bitvec(a), self.get_bitvec(b)) {
            let result = Self::bv_mask(&(v1 * v2), w1);
            return self.mk_bitvec(result, w1);
        }

        // Try simplifying with the constant operand (either order).
        // `x` is the non-constant operand, `b`/`a` the constant.
        if let Some((v, _)) = self.get_bitvec(b) {
            let v = v.clone();
            if let Some(result) = self.try_bvmul_by_const(a, &v, width) {
                return result;
            }
        }
        if let Some((v, _)) = self.get_bitvec(a) {
            let v = v.clone();
            if let Some(result) = self.try_bvmul_by_const(b, &v, width) {
                return result;
            }
        }

        self.mk_bv_binary_app("bvmul", args, width)
    }

    /// Try to simplify `bvmul(x, v)` where `v` is a `width`-bit constant value
    /// (the non-negative masked representative in `[0, 2^width)`).
    ///
    /// Returns `Some(result)` if a sound rewrite applies, `None` otherwise.
    ///
    /// Every rule here is value-preserving in `Z/2^width` (modular ring), hence
    /// equisatisfiable:
    /// - x * 0 = 0
    /// - x * 1 = x
    /// - x * (2^w - 1) = -x         (all-ones is -1 mod 2^w)
    /// - x * 2^k = x << k           (mul2concat)
    /// - x * -(2^k) = -(x << k)     (since -(2^k) ≡ 2^w - 2^k mod 2^w)
    /// - sparse constants use a bounded non-adjacent-form shift/add expansion
    fn try_bvmul_by_const(&mut self, x: TermId, v: &BigInt, width: u32) -> Option<TermId> {
        let zero = BigInt::zero();
        let one = BigInt::one();
        let all_ones = Self::bv_ones(width);

        // x * 0 = 0
        if *v == zero {
            return Some(self.mk_bitvec(zero, width));
        }
        // x * 1 = x
        if *v == one {
            return Some(x);
        }
        // x * -1 = -x  (all-ones eliminates the multiplier for negate-by-multiply)
        if *v == all_ones {
            return Some(self.mk_bvneg(x));
        }
        // x * 2^k = x << k  (mul2concat, no multiplier circuit)
        if let Some(k) = Self::bv_log2_exact(v) {
            return Some(self.mk_bvmul_pow2(x, k, width));
        }
        // x * -(2^k) = -(x << k). Detect by negating into two's complement:
        // neg = (2^width - v) mod 2^width; if neg is an exact power of two 2^k
        // (with 0 < k < width), then v == -(2^k) mod 2^width.
        // k == 0 (neg == 1, i.e. v == -1) is already handled by the all-ones
        // branch above, so bv_log2_exact(neg) == 0 will not be reached here.
        let modulus = BigInt::one() << width;
        let neg = Self::bv_mask(&(&modulus - v), width);
        if let Some(k) = Self::bv_log2_exact(&neg) {
            if k > 0 && k < width {
                let shifted = self.mk_bvmul_pow2(x, k, width);
                return Some(self.mk_bvneg(shifted));
            }
        }

        // Lower only genuinely sparse constants. Non-adjacent form (NAF) has
        // minimum weight among signed-binary representations, so this cap is a
        // direct bound on term and circuit growth rather than a heuristic tied
        // to the unsigned popcount. Centering at zero also gives small negative
        // constants (for example 2^w - 3) the same cheap representation as 3.
        const MAX_SIGNED_DIGITS: usize = 4;
        let half_modulus = &modulus >> 1u32;
        let centered = if v > &half_modulus {
            v - &modulus
        } else {
            v.clone()
        };
        let digits = Self::bv_bounded_naf(&centered, MAX_SIGNED_DIGITS)?;
        debug_assert!(
            digits.len() >= 2,
            "single NAF digits use an earlier fast path"
        );

        // Sum positive and negative components separately, then subtract once.
        // This makes 3*x become (4*x)-x (one adder circuit), rather than
        // (-x)+(4*x) (a negation plus an adder).
        let mut positive = Vec::new();
        let mut negative = Vec::new();
        for (shift, is_positive) in digits {
            let component = self.mk_bvmul_pow2(x, shift, width);
            if is_positive {
                positive.push(component);
            } else {
                negative.push(component);
            }
        }

        let positive = positive
            .into_iter()
            .reduce(|lhs, rhs| self.mk_bvadd(vec![lhs, rhs]));
        let negative = negative
            .into_iter()
            .reduce(|lhs, rhs| self.mk_bvadd(vec![lhs, rhs]));
        match (positive, negative) {
            (Some(lhs), Some(rhs)) => Some(self.mk_bvsub(vec![lhs, rhs])),
            (Some(result), None) => Some(result),
            (None, Some(result)) => Some(self.mk_bvneg(result)),
            // Defensive: decline the rewrite if a future NAF producer ever
            // violates its non-empty contract.
            (None, None) => None,
        }
    }

    /// Return the non-zero signed digits `(shift, is_positive)` of `value` in
    /// non-adjacent form, or `None` when their count exceeds `max_digits`.
    ///
    /// The cap is checked before any terms are constructed, so declining the
    /// rewrite cannot leave unused intermediate terms in the store.
    fn bv_bounded_naf(value: &BigInt, max_digits: usize) -> Option<Vec<(u32, bool)>> {
        let is_negative = value.sign() == num_bigint::Sign::Minus;
        let mut remaining = if is_negative { -value } else { value.clone() };
        let one = BigInt::one();
        let three = BigInt::from(3u8);
        let mut shift = 0u32;
        let mut digits = Vec::new();

        while !remaining.is_zero() {
            if (&remaining & &one) == one {
                let positive_for_abs = (&remaining & &three) == one;
                if digits.len() == max_digits {
                    return None;
                }
                digits.push((shift, positive_for_abs != is_negative));
                if positive_for_abs {
                    remaining -= &one;
                } else {
                    remaining += &one;
                }
            }
            remaining >>= 1u32;
            shift = shift.checked_add(1)?;
        }

        Some(digits)
    }

    /// Build `bvmul(x, 2^k)` for a `width`-bit operand as a constant shift-left,
    /// lowered to `concat(extract(x, width-k-1, 0), bv_zero(k))` (mul2concat).
    /// For `k >= width` the product is `0 mod 2^width`.
    fn mk_bvmul_pow2(&mut self, x: TermId, k: u32, width: u32) -> TermId {
        if k == 0 {
            return x;
        }
        if k >= width {
            return self.mk_bitvec(BigInt::zero(), width);
        }
        // bvmul(x, 2^k) → concat(extract(x, width-k-1, 0), bv_zero(k))
        let extracted = self.mk_bvextract(width - k - 1, 0, x);
        let zero_bits = self.mk_bitvec(BigInt::zero(), k);
        self.mk_bvconcat(vec![extracted, zero_bits])
    }
}
