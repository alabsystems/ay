// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl TermStore {
    /// Create bitvector left shift with constant folding
    ///
    /// Simplifications:
    /// - Constant folding: bvshl(x, c) when both are constants
    /// - Identity: bvshl(x, 0) → x
    /// - Zero: bvshl(0, x) → 0
    /// - Large shift: bvshl(x, c) → 0 when c >= width
    /// - Constant shift to concat: bvshl(x, K) → concat(extract(x, n-K-1, 0), bv_zero(K))
    ///   Eliminates barrel-shifter circuit for constant shift amounts.
    ///   Reference: Z3 bv_rewriter, Yices2 term_manager.c:5298-5493
    pub fn mk_bvshl(&mut self, args: Vec<TermId>) -> TermId {
        let (a, b, width, args) = match self.prepare_bv_binary_op("bvshl", args) {
            Ok(parts) => parts,
            Err(fallback) => return fallback,
        };
        let zero = BigInt::zero();

        // Constant folding
        if let (Some((v1, w1)), Some((v2, _))) = (self.get_bitvec(a), self.get_bitvec(b)) {
            // SMT-LIB shifts saturate (NOT modulo width): a shift >= width
            // yields 0, never wraps. Handled by the `shift >= w1` guard below.
            if let Some(shift) = v2.to_u32() {
                if shift >= w1 {
                    return self.mk_bitvec(zero, w1);
                }
                let result = Self::bv_mask(&(v1 << shift), w1);
                return self.mk_bitvec(result, w1);
            }
        }

        // Identity: x << 0 = x
        if let Some((v, _)) = self.get_bitvec(b) {
            if *v == zero {
                return a;
            }
            // Large shift produces zero
            if let Some(shift) = v.to_u32() {
                if shift >= width {
                    return self.mk_bitvec(zero, width);
                }
                // Constant-shift-to-concat: bvshl(x, K) → concat(extract(x, n-K-1, 0), bv_zero(K))
                // This avoids building a barrel-shifter circuit for constant shifts.
                let extracted = self.mk_bvextract(width - shift - 1, 0, a);
                let zero_bits = self.mk_bitvec(BigInt::zero(), shift);
                return self.mk_bvconcat(vec![extracted, zero_bits]);
            }
        }

        // Zero shifted is zero
        if let Some((v, _)) = self.get_bitvec(a) {
            if *v == zero {
                return self.mk_bitvec(zero, width);
            }
        }

        self.mk_bv_binary_app("bvshl", args, width)
    }

    /// Create bitvector logical right shift with constant folding
    ///
    /// Simplifications:
    /// - Constant folding: bvlshr(x, c) when both are constants
    /// - Identity: bvlshr(x, 0) → x
    /// - Zero: bvlshr(0, x) → 0
    /// - Large shift: bvlshr(x, c) → 0 when c >= width
    /// - Constant shift to concat: bvlshr(x, K) → concat(bv_zero(K), extract(x, n-1, K))
    ///   Eliminates barrel-shifter circuit for constant shift amounts.
    ///   Reference: Z3 bv_rewriter, Yices2 term_manager.c:5298-5493
    pub fn mk_bvlshr(&mut self, args: Vec<TermId>) -> TermId {
        let (a, b, width, args) = match self.prepare_bv_binary_op("bvlshr", args) {
            Ok(parts) => parts,
            Err(fallback) => return fallback,
        };
        let zero = BigInt::zero();

        // Constant folding
        if let (Some((v1, w1)), Some((v2, _))) = (self.get_bitvec(a), self.get_bitvec(b)) {
            if let Some(shift) = v2.to_u32() {
                if shift >= w1 {
                    return self.mk_bitvec(zero, w1);
                }
                let result = v1 >> shift;
                return self.mk_bitvec(result, w1);
            }
        }

        // Identity: x >> 0 = x
        if let Some((v, _)) = self.get_bitvec(b) {
            if *v == zero {
                return a;
            }
            // Large shift produces zero
            if let Some(shift) = v.to_u32() {
                // `high = width - 1` phrased so `width >= 1` is local: the
                // `None` arm coincides with `shift >= width` (a zero width
                // satisfies it for every shift), so both keep the exact
                // saturate-to-zero result the guard always produced.
                let (Some(high), true) = (width.checked_sub(1), shift < width) else {
                    return self.mk_bitvec(zero, width);
                };
                // Constant-shift-to-concat: bvlshr(x, K) →
                // concat(bv_zero(K), extract(x, n-1, K)). Keep the concat RAW:
                // `mk_bvconcat` canonicalizes a zero high half back to
                // `zero_extend`, while the pinned external Alethe checker has
                // checked `bitblast_concat`/`bitblast_extract` rules but no
                // `zero_extend` rule. This is a semantic normalization, not a
                // proof assertion; the printer still has to derive every use.
                let extracted = self.mk_bvextract(high, shift, a);
                let zero_bits = self.mk_bitvec(BigInt::zero(), shift);
                return self.intern(
                    TermData::App(Symbol::named("concat"), vec![zero_bits, extracted]),
                    Sort::bitvec(width),
                );
            }
        }

        // Zero shifted is zero
        if let Some((v, _)) = self.get_bitvec(a) {
            if *v == zero {
                return self.mk_bitvec(zero, width);
            }
        }

        self.mk_bv_binary_app("bvlshr", args, width)
    }

    /// Create bitvector arithmetic right shift with constant folding
    ///
    /// Simplifications:
    /// - Constant folding: bvashr(x, c) when both are constants
    /// - Identity: bvashr(x, 0) → x
    /// - Zero: bvashr(0, x) → 0
    /// - Constant shift to extract: bvashr(x, K) → sign_extend(K, extract(x, n-1, K))
    ///   Eliminates barrel-shifter circuit for constant shift amounts.
    ///   Reference: Z3 bv_rewriter, Yices2 term_manager.c:5298-5493
    pub fn mk_bvashr(&mut self, args: Vec<TermId>) -> TermId {
        let (a, b, width, args) = match self.prepare_bv_binary_op("bvashr", args) {
            Ok(parts) => parts,
            Err(fallback) => return fallback,
        };
        let zero = BigInt::zero();

        // Constant folding
        if let (Some((v1, w1)), Some((v2, _))) = (self.get_bitvec(a), self.get_bitvec(b)) {
            if let Some(shift) = v2.to_u32() {
                // Saturating: constants carry the width of their BitVec sort, so w1 >= 1.
                let sign_bit = BigInt::one() << w1.saturating_sub(1);
                let is_negative = v1 >= &sign_bit;

                if shift >= w1 {
                    // All bits become sign bit
                    if is_negative {
                        return self.mk_bitvec(Self::bv_ones(w1), w1);
                    } else {
                        return self.mk_bitvec(zero, w1);
                    }
                }

                let mut result = v1 >> shift;
                // Sign extend: fill upper bits with sign bit. `shift < w1`
                // holds (the `shift >= w1` arm returned above), so the
                // saturating form is exact on every reachable input and the
                // subtraction is total.
                if is_negative {
                    let fill_mask = Self::bv_ones(shift) << (w1.saturating_sub(shift));
                    result |= fill_mask;
                }
                return self.mk_bitvec(Self::bv_mask(&result, w1), w1);
            }
        }

        // Identity: x >>> 0 = x
        if let Some((v, _)) = self.get_bitvec(b) {
            if *v == zero {
                return a;
            }
            // Large shift: all bits become sign bit (symbolic, so create term)
            if let Some(shift) = v.to_u32() {
                // `high = width - 1` phrased so `width >= 1` is local; the
                // `None` arm coincides with `shift >= width` (a zero width
                // satisfies it for every shift) and falls through with it.
                if let (Some(high), true) = (width.checked_sub(1), shift < width) {
                    // Constant-shift-to-extract: bvashr(x, K) → sign_extend(K, extract(x, n-1, K))
                    // This avoids building a barrel-shifter circuit for constant shifts.
                    let extracted = self.mk_bvextract(high, shift, a);
                    return self.mk_bvsign_extend(shift, extracted);
                }
                // bvashr(x, K>=n) is either all-zeros or all-ones depending on sign.
                // Cannot simplify further without knowing the sign bit at this level.
                // Fall through to create the bvashr term.
            }
        }

        // Zero shifted is zero
        if let Some((v, _)) = self.get_bitvec(a) {
            if *v == zero {
                return self.mk_bitvec(zero, width);
            }
        }

        self.mk_bv_binary_app("bvashr", args, width)
    }
}
