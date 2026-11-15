// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV division, remainder, and signed modulo bit-blasting operations.

use super::*;

mod zero_padding;

impl BvSolver<'_> {
    /// Bit-blast unsigned division and remainder together
    /// Returns (quotient, remainder)
    pub(crate) fn bitblast_udiv_urem(&mut self, a: &BvBits, b: &BvBits) -> (BvBits, BvBits) {
        if !self.encoding_complete() {
            return (Vec::new(), Vec::new());
        }

        assert_eq!(a.len(), b.len());
        let n = a.len();

        if n == 0 {
            return (Vec::new(), Vec::new());
        }

        if let Some(result) = self.try_zero_padded_division(a, b) {
            return result;
        }
        if !self.encoding_complete() {
            return (Vec::new(), Vec::new());
        }

        // Restoring division:
        // rem = 0
        // for i = n-1..0:
        //   rem = (rem << 1) | a[i]
        //   if rem >= b:
        //     rem = rem - b
        //     q[i] = 1
        //   else:
        //     q[i] = 0
        //
        // For b = 0, this naturally yields q = all_ones and r = a.

        let mut rem = self.const_bits(0, n);
        let Some(mut q_msb_first) = self.counted_bits(n) else {
            return (Vec::new(), Vec::new());
        };

        for i in (0..n).rev() {
            if !self.encoding_step() {
                return (Vec::new(), Vec::new());
            }
            // rem = (rem << 1) | a[i]: `rem` is always `n` bits wide, so this
            // keeps its low `n - 1` bits (here `n >= 1`).
            let Some(mut shifted) = self.counted_bits(n) else {
                return (Vec::new(), Vec::new());
            };
            shifted.push(a[i]);
            for &bit in rem.iter().take(n - 1) {
                if !self.encoding_step() {
                    return (Vec::new(), Vec::new());
                }
                shifted.push(bit);
            }
            rem = shifted;

            // The subtraction carry is the unsigned no-borrow bit (rem >= b),
            // so comparison and difference share the same ripple-carry chain.
            let (rem_minus_b, rem_ge_b) = self.bitblast_sub_with_carry(&rem, b);
            rem = self.bitwise_mux(&rem_minus_b, &rem, rem_ge_b);

            q_msb_first.push(rem_ge_b);
        }

        if !self.encoding.counted_admit(q_msb_first.len(), 0) {
            return (Vec::new(), Vec::new());
        }
        q_msb_first.reverse();
        (q_msb_first, rem)
    }

    /// Check if a bitvector is zero
    pub(crate) fn is_zero(&mut self, bits: &BvBits) -> CnfLit {
        if !self.encoding_complete() {
            return 0;
        }

        // All bits must be 0
        // is_zero = NOT(bit[0] OR bit[1] OR ... OR bit[n-1])
        if bits.is_empty() {
            return self.fresh_true();
        }

        // Create OR of all bits, then negate
        let any_set = self.mk_or_many(bits);
        neg_lit(any_set)
    }

    /// Create OR of many literals
    pub(super) fn mk_or_many(&mut self, lits: &[CnfLit]) -> CnfLit {
        if !self.encoding_complete() {
            return 0;
        }

        let Some((&first, rest)) = lits.split_first() else {
            return self.fresh_false();
        };
        if rest.is_empty() {
            return first;
        }

        let mut result = first;
        for &lit in rest {
            if !self.encoding_step() {
                return 0;
            }
            result = self.mk_or(result, lit);
        }
        result
    }

    /// Cached unsigned division+remainder: shares one `bitblast_udiv_urem`
    /// circuit between `bvudiv(x,y)` and `bvurem(x,y)` (#4873).
    pub(super) fn bitblast_udiv_urem_cached(
        &mut self,
        a_term: TermId,
        b_term: TermId,
    ) -> (BvBits, BvBits) {
        if !self.encoding_complete() || !self.encoding.counted_admit(1, 0) {
            return (Vec::new(), Vec::new());
        }

        if let Some(cached) = self.unsigned_div_cache.get(&(a_term, b_term)) {
            let Some(copied) = self.copy_division_pair(&cached.0, &cached.1) else {
                return (Vec::new(), Vec::new());
            };
            return copied;
        }
        // Division/remainder by a CONSTANT POWER OF TWO is a shift / mask —
        // O(width) — instead of the O(width^2) restoring-division circuit below.
        // This matters a lot for solver-generated VCs: e.g. the model-checker-consumer/kani
        // pointer→object-id arithmetic emits many `(bvudiv addr 0x100000)`
        // (÷2^20) over 64-bit addresses; bit-blasting each as a full divider is
        // ~width^2 gates and dominates the variable count (#div-by-pow2).
        if let Some(result) = self.try_udiv_urem_by_const_pow2(a_term, b_term) {
            if !self.encoding_complete() {
                return (Vec::new(), Vec::new());
            }
            if !self.cache_unsigned_division((a_term, b_term), &result) {
                return (Vec::new(), Vec::new());
            }
            return result;
        }
        let a = self.get_bits(a_term);
        let b = self.get_bits(b_term);
        let result = self.bitblast_udiv_urem(&a, &b);
        if !self.encoding_complete() {
            return (Vec::new(), Vec::new());
        }
        if !self.cache_unsigned_division((a_term, b_term), &result) {
            return (Vec::new(), Vec::new());
        }
        result
    }

    fn copy_division_pair(&self, q: &[CnfLit], r: &[CnfLit]) -> Option<(BvBits, BvBits)> {
        Some((self.counted_copy_bits(q)?, self.counted_copy_bits(r)?))
    }

    fn cache_unsigned_division(
        &mut self,
        key: (TermId, TermId),
        result: &(BvBits, BvBits),
    ) -> bool {
        let Some(copied) = self.copy_division_pair(&result.0, &result.1) else {
            return false;
        };
        if !counted::memory::map(&mut self.unsigned_div_cache, &self.encoding) {
            return false;
        }
        self.unsigned_div_cache.insert(key, copied);
        true
    }

    fn cache_signed_division(
        &mut self,
        key: (TermId, TermId),
        result: &(BvBits, BvBits, CnfLit, CnfLit),
    ) -> bool {
        let Some((q, r)) = self.copy_division_pair(&result.0, &result.1) else {
            return false;
        };
        if !counted::memory::map(&mut self.signed_div_cache, &self.encoding) {
            return false;
        }
        self.signed_div_cache
            .insert(key, (q, r, result.2, result.3));
        true
    }

    /// Fast path for unsigned `bvudiv`/`bvurem` by a constant power of two:
    /// `a / 2^k = a >> k` (logical) and `a % 2^k = a & (2^k - 1)` (low k bits).
    /// Returns `None` unless `b_term` is a non-zero constant power of two, so the
    /// general restoring-division circuit handles every other case (including
    /// division by zero, which must yield quotient all-ones / remainder `a`).
    /// `BvBits` is LSB-first, so the shift/mask are pure wire re-routing.
    fn try_udiv_urem_by_const_pow2(
        &mut self,
        a_term: TermId,
        b_term: TermId,
    ) -> Option<(BvBits, BvBits)> {
        if !self.encoding_complete() {
            return None;
        }

        let TermData::Const(Constant::BitVec { value, width }) = self.terms.get(b_term) else {
            return None;
        };
        let width = *width as usize;
        let bits = value.bits();
        let Some(limbs) = usize::try_from(bits.div_ceil(32))
            .ok()
            .and_then(|n| n.checked_add(1))
        else {
            counted::memory::storage(&self.encoding);
            return None;
        };
        if !self.encoding.counted_admit(limbs, 0) {
            return None;
        }
        // A positive value is a power of two exactly when its only set bit
        // is both its highest and lowest one. Read borrowed limbs; do not
        // clone a potentially very large payload just to inspect this shape.
        if value.sign() != num_bigint::Sign::Plus || value.trailing_zeros() != bits.checked_sub(1) {
            return None;
        }
        // value == 2^k.
        let Ok(k) = usize::try_from(bits - 1) else {
            counted::memory::storage(&self.encoding);
            return None;
        };
        // `TermStore::mk_bitvec` normalizes a width-w constant below 2^w, so
        // k < width. A constant that is not normalized is left to the
        // restoring circuit, which reads its low `width` bits.
        if k >= width {
            return None;
        }
        let a = self.get_bits(a_term);
        if a.len() != width {
            return None;
        }
        let f = self.fresh_false();
        // quotient = a >> k: bit i is a[i + k] while that is a bit of `a`,
        // else zero. remainder = a & (2^k - 1): the low k bits of a,
        // zero-padded to width.
        let mut q = self.counted_bits(width)?;
        let mut r = self.counted_bits(width)?;
        for i in 0..width {
            if !self.encoding_step() {
                return None;
            }
            let q_bit = i.checked_add(k).and_then(|j| a.get(j)).copied();
            q.push(q_bit.unwrap_or(f));
            let r_bit = if i < k { a.get(i).copied() } else { None };
            r.push(r_bit.unwrap_or(f));
        }
        Some((q, r))
    }

    /// Cached signed division+remainder: shares abs-value computation and
    /// the unsigned division circuit between `bvsdiv(x,y)` and `bvsrem(x,y)`
    /// (#4873). Returns (abs_quotient, abs_remainder, sign_a, sign_b).
    pub(super) fn bitblast_signed_div_rem_cached(
        &mut self,
        a_term: TermId,
        b_term: TermId,
    ) -> (BvBits, BvBits, CnfLit, CnfLit) {
        if !self.encoding_complete() || !self.encoding.counted_admit(1, 0) {
            return (Vec::new(), Vec::new(), 0, 0);
        }

        if let Some(cached) = self.signed_div_cache.get(&(a_term, b_term)) {
            let Some((q, r)) = self.copy_division_pair(&cached.0, &cached.1) else {
                return (Vec::new(), Vec::new(), 0, 0);
            };
            return (q, r, cached.2, cached.3);
        }
        let a = self.get_bits(a_term);
        let b = self.get_bits(b_term);
        if !self.encoding_complete() {
            return (Vec::new(), Vec::new(), 0, 0);
        }
        let n = a.len();
        if n == 0 {
            let dummy: CnfLit = 1;
            let result = (Vec::new(), Vec::new(), dummy, dummy);
            if !self.encoding_complete() {
                return (Vec::new(), Vec::new(), 0, 0);
            }
            if !self.cache_signed_division((a_term, b_term), &result) {
                return (Vec::new(), Vec::new(), 0, 0);
            }
            return result;
        }
        let sign_a = a[n - 1];
        let sign_b = b[n - 1];
        let abs_a = self.conditional_neg(&a, sign_a);
        let abs_b = self.conditional_neg(&b, sign_b);
        let (abs_q, abs_r) = self.bitblast_udiv_urem(&abs_a, &abs_b);
        let result = (abs_q, abs_r, sign_a, sign_b);
        if !self.encoding_complete() {
            return (Vec::new(), Vec::new(), 0, 0);
        }
        if !self.cache_signed_division((a_term, b_term), &result) {
            return (Vec::new(), Vec::new(), 0, 0);
        }
        result
    }

    /// Bit-blast unsigned remainder (used by `bitblast_smod`).
    fn bitblast_urem(&mut self, a: &BvBits, b: &BvBits) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }

        let (_q, r) = self.bitblast_udiv_urem(a, b);
        r
    }

    /// Bit-blast signed modulo.
    ///
    /// SMT-LIB semantics: sign of the result matches the divisor.
    pub(super) fn bitblast_smod(&mut self, a: &BvBits, b: &BvBits) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }

        assert_eq!(a.len(), b.len());
        let n = a.len();
        if n == 0 {
            return Vec::new();
        }

        let sign_a = a[n - 1];
        let sign_b = b[n - 1];

        let abs_a = self.conditional_neg(a, sign_a);
        let abs_b = self.conditional_neg(b, sign_b);

        // u = abs(a) mod abs(b) (also handles b=0 via bvurem semantics)
        let u = self.bitblast_urem(&abs_a, &abs_b);
        let u_is_zero = self.is_zero(&u);
        let zero = self.const_bits(0, n);

        // If u=0 then result=0, otherwise select based on signs.
        // Cases (u != 0):
        //  a >= 0, b >= 0  =>  u
        //  a <  0, b >= 0  =>  |b| - u
        //  a >= 0, b <  0  =>  u - |b|
        //  a <  0, b <  0  =>  -u
        let abs_b_minus_u = self.bitblast_sub(&abs_b, &u);
        let u_minus_abs_b = self.bitblast_sub(&u, &abs_b);
        let neg_u = self.bitblast_neg(&u);

        // When b >= 0: if a is negative, choose |b|-u else u
        let res_b_pos = self.bitwise_mux(&abs_b_minus_u, &u, sign_a);
        // When b < 0: if a is negative, choose -u else u-|b|
        let res_b_neg = self.bitwise_mux(&neg_u, &u_minus_abs_b, sign_a);
        // Select based on sign(b)
        let res = self.bitwise_mux(&res_b_neg, &res_b_pos, sign_b);

        self.bitwise_mux(&zero, &res, u_is_zero)
    }

    /// Conditionally negate a bitvector
    /// Returns: if cond then -bits else bits
    pub(super) fn conditional_neg(&mut self, bits: &BvBits, cond: CnfLit) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }

        let neg = self.bitblast_neg(bits);
        self.bitwise_mux(&neg, bits, cond)
    }
}
