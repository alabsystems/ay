// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bitvector arithmetic circuits for the floating-point bit-blasting pipeline.
//!
//! These operate on `FpSolver`'s clause store, reusing the lower-level gate
//! helpers from `gates.rs`.

use ay_core::{CnfClause, CnfLit};

use super::FpSolver;

impl FpSolver<'_> {
    /// Return a canonical false literal (always 0), creating it on first call.
    /// Subsequent calls reuse the same variable (#5870).
    pub(crate) fn const_false(&mut self) -> CnfLit {
        if let Some(lit) = self.cached_false {
            return lit;
        }
        let v = self.fresh_var();
        self.add_clause(CnfClause::unit(-v));
        self.cached_false = Some(v);
        v
    }

    /// Return a canonical true literal (always 1), creating it on first call.
    /// Subsequent calls reuse the same variable (#5870).
    pub(crate) fn const_true(&mut self) -> CnfLit {
        if let Some(lit) = self.cached_true {
            return lit;
        }
        let v = self.fresh_var();
        self.add_clause(CnfClause::unit(v));
        self.cached_true = Some(v);
        v
    }

    /// Create a constant bitvector of given width from a u64 value.
    /// Bit 0 is the LSB.
    pub(crate) fn const_bv(&mut self, value: u64, width: usize) -> Vec<CnfLit> {
        (0..width)
            .map(|i| {
                if i < 64 && (value >> i) & 1 == 1 {
                    self.const_true()
                } else {
                    self.const_false()
                }
            })
            .collect()
    }

    /// Zero-extend a bitvector by prepending `extra` zero bits at the MSB.
    pub(crate) fn zero_extend(&mut self, bits: &[CnfLit], extra: usize) -> Vec<CnfLit> {
        let mut result = bits.to_vec();
        let zero = self.const_false();
        for _ in 0..extra {
            result.push(zero);
        }
        result
    }

    /// Sign-extend a bitvector by replicating the MSB.
    pub(crate) fn sign_extend(&mut self, bits: &[CnfLit], extra: usize) -> Vec<CnfLit> {
        debug_assert!(
            !bits.is_empty(),
            "invariant: sign_extend requires non-empty input"
        );
        let msb = bits[bits.len() - 1];
        let mut result = bits.to_vec();
        for _ in 0..extra {
            result.push(msb);
        }
        result
    }

    /// Concatenate two bitvectors: result = [lo, hi] (lo bits first, hi bits at MSB).
    pub(crate) fn bv_concat(lo: &[CnfLit], hi: &[CnfLit]) -> Vec<CnfLit> {
        let mut result = lo.to_vec();
        result.extend_from_slice(hi);
        result
    }

    /// Half adder: returns (sum, carry).
    pub(crate) fn half_adder(&mut self, a: CnfLit, b: CnfLit) -> (CnfLit, CnfLit) {
        let sum = self.make_xor(a, b);
        let carry = self.make_and(a, b);
        (sum, carry)
    }

    /// Full adder: returns (sum, carry_out).
    pub(crate) fn full_adder(&mut self, a: CnfLit, b: CnfLit, cin: CnfLit) -> (CnfLit, CnfLit) {
        let (s1, c1) = self.half_adder(a, b);
        let (sum, c2) = self.half_adder(s1, cin);
        let carry = self.make_or(c1, c2);
        (sum, carry)
    }

    /// Ripple-carry addition of two bitvectors. Result has same width as inputs.
    pub(crate) fn bv_add(&mut self, a: &[CnfLit], b: &[CnfLit]) -> Vec<CnfLit> {
        debug_assert_eq!(a.len(), b.len());
        let n = a.len();
        let mut result = Vec::with_capacity(n);
        let mut carry = self.const_false();
        for i in 0..n {
            let (sum, cout) = self.full_adder(a[i], b[i], carry);
            result.push(sum);
            carry = cout;
        }
        result
    }

    /// Negate a bitvector (two's complement).
    pub(crate) fn bv_neg(&mut self, a: &[CnfLit]) -> Vec<CnfLit> {
        let inverted: Vec<CnfLit> = a.iter().map(|&lit| -lit).collect();
        let one = self.const_bv(1, a.len());
        self.bv_add(&inverted, &one)
    }

    /// Subtraction: a - b.
    pub(crate) fn bv_sub(&mut self, a: &[CnfLit], b: &[CnfLit]) -> Vec<CnfLit> {
        let neg_b = self.bv_neg(b);
        self.bv_add(a, &neg_b)
    }

    /// Bitwise OR of two bitvectors.
    pub(crate) fn bv_or(&mut self, a: &[CnfLit], b: &[CnfLit]) -> Vec<CnfLit> {
        debug_assert_eq!(a.len(), b.len());
        a.iter()
            .zip(b.iter())
            .map(|(&ai, &bi)| self.make_or(ai, bi))
            .collect()
    }

    /// Multiplication of two bitvectors. Result has same width as inputs.
    pub(crate) fn bv_mul(&mut self, a: &[CnfLit], b: &[CnfLit]) -> Vec<CnfLit> {
        debug_assert_eq!(a.len(), b.len());
        let n = a.len();
        if n == 0 {
            return vec![];
        }
        // Shift-and-add multiplier
        let zero = self.const_false();
        let mut acc = vec![zero; n];
        for (i, &b_bit) in b.iter().enumerate() {
            // partial product: a[j] & b[i], for positions where i+j < n
            let mut partial = Vec::with_capacity(n);
            for &a_bit in a.iter().take(n.saturating_sub(i)) {
                partial.push(self.make_and(a_bit, b_bit));
            }
            // Pad to n bits with leading zeros
            while partial.len() < n {
                partial.push(zero);
            }
            // Shift left by i: prepend i zeros, truncate to n bits
            let mut shifted = vec![zero; i];
            shifted.extend_from_slice(&partial[..n.saturating_sub(i)]);
            shifted.truncate(n);
            acc = self.bv_add(&acc, &shifted);
        }
        acc
    }

    /// Logical right shift by a symbolic amount (barrel shifter).
    pub(crate) fn bv_lshr(&mut self, a: &[CnfLit], b: &[CnfLit]) -> Vec<CnfLit> {
        let n = a.len();
        let zero = self.const_false();
        let mut current = a.to_vec();
        // Barrel shifter: for each bit of shift amount, conditionally shift by 2^i.
        // Only iterate ceil(log2(n))+1 stages; OR-reduce remaining high bits (#5869).
        for (i, &b_bit) in b.iter().enumerate() {
            let shift_amount = match 1usize.checked_shl(i as u32) {
                Some(v) => v,
                None => n,
            };
            if shift_amount >= n {
                // All remaining bits (including this one) cause full overflow.
                // OR-reduce them into a single overflow condition.
                let overflow = self.bv_or_reduce(&b[i..]);
                let all_zero = vec![zero; n];
                current = self.make_ite_bits(overflow, &all_zero, &current);
                break;
            }
            let mut shifted = Vec::with_capacity(n);
            for j in 0..n {
                if j + shift_amount < n {
                    shifted.push(current[j + shift_amount]);
                } else {
                    shifted.push(zero);
                }
            }
            current = self.make_ite_bits(b_bit, &shifted, &current);
        }
        current
    }

    /// Logical left shift by a symbolic amount (barrel shifter).
    pub(crate) fn bv_shl(&mut self, a: &[CnfLit], b: &[CnfLit]) -> Vec<CnfLit> {
        let n = a.len();
        let zero = self.const_false();
        let mut current = a.to_vec();
        // Barrel shifter: only iterate ceil(log2(n))+1 stages; OR-reduce rest (#5869).
        for (i, &b_bit) in b.iter().enumerate() {
            let shift_amount = match 1usize.checked_shl(i as u32) {
                Some(v) => v,
                None => n,
            };
            if shift_amount >= n {
                let overflow = self.bv_or_reduce(&b[i..]);
                let all_zero = vec![zero; n];
                current = self.make_ite_bits(overflow, &all_zero, &current);
                break;
            }
            let mut shifted = Vec::with_capacity(n);
            for j in 0..n {
                if j >= shift_amount {
                    shifted.push(current[j - shift_amount]);
                } else {
                    shifted.push(zero);
                }
            }
            current = self.make_ite_bits(b_bit, &shifted, &current);
        }
        current
    }

    /// OR-reduce: true iff any bit is set. Returns a single CnfLit.
    pub(crate) fn bv_or_reduce(&mut self, bits: &[CnfLit]) -> CnfLit {
        self.make_any_nonzero(bits)
    }

    /// Unsigned bitvector division and remainder (restoring division algorithm).
    ///
    /// Returns (quotient, remainder), both n-bit wide.
    /// Division by zero returns (all-ones, a) following SMT-LIB semantics.
    pub(crate) fn bv_udiv_urem(
        &mut self,
        a: &[CnfLit],
        b: &[CnfLit],
    ) -> (Vec<CnfLit>, Vec<CnfLit>) {
        let n = a.len();
        debug_assert_eq!(n, b.len());
        debug_assert!(n > 0);

        let zero = self.const_false();

        // Restoring division: iterate from MSB to LSB.
        // Maintain a partial remainder (n bits wide).
        // At each step i (from n-1 down to 0):
        //   1. Shift remainder left by 1, bring in a[i] at LSB
        //   2. Trial subtract: trial = shifted_rem - b
        //   3. If trial >= 0 (no borrow): quotient[i] = 1, remainder = trial
        //      Else: quotient[i] = 0, remainder unchanged
        let mut rem = vec![zero; n];
        let mut quot = vec![zero; n];

        for i in (0..n).rev() {
            // Shift remainder left by 1 and bring in dividend bit a[i]
            let mut shifted_rem = Vec::with_capacity(n);
            shifted_rem.push(a[i]); // LSB = next dividend bit
            shifted_rem.extend_from_slice(&rem[..n - 1]); // shift up

            // Trial subtraction: trial = shifted_rem - b
            let trial = self.bv_sub(&shifted_rem, b);

            // Borrow/sign: if trial MSB (sign bit in n-bit two's complement)
            // indicates a negative result, the subtraction underflowed.
            // Actually for unsigned subtraction, borrow = carry_out complement.
            // We use the unsigned comparison: shifted_rem >= b iff no borrow.
            let ge = self.make_unsigned_ge(&shifted_rem, b);

            // quotient bit
            quot[i] = ge;

            // Select remainder: ge ? trial : shifted_rem
            rem = self.make_ite_bits(ge, &trial, &shifted_rem);
        }

        (quot, rem)
    }

    /// Unsigned greater-than-or-equal comparison: a >= b.
    pub(crate) fn make_unsigned_ge(&mut self, a: &[CnfLit], b: &[CnfLit]) -> CnfLit {
        // a >= b  iff  NOT (a < b)
        let a_lt_b = self.make_unsigned_lt(a, b);
        -a_lt_b
    }

    /// Unsigned less-than comparison: a < b.
    pub(crate) fn make_unsigned_lt(&mut self, a: &[CnfLit], b: &[CnfLit]) -> CnfLit {
        debug_assert_eq!(a.len(), b.len());
        if a.is_empty() {
            let result = self.fresh_var();
            self.add_clause(CnfClause::unit(-result));
            return result;
        }

        // Iterate LSB→MSB so the MSB (highest weight) gets final priority.
        // At each bit: result = (a[i]<b[i]) || (a[i]==b[i] && prev_result).
        // The last-processed bit (MSB) overrides all lower bits.
        let not_a_lsb = -a[0];
        let mut result = self.make_and(not_a_lsb, b[0]);

        for i in 1..a.len() {
            let not_a_i = -a[i];
            let bit_lt = self.make_and(not_a_i, b[i]);
            let bit_eq = self.make_xnor(a[i], b[i]);
            let bit_eq_and_result = self.make_and(bit_eq, result);
            result = self.make_or(bit_lt, bit_eq_and_result);
        }

        result
    }

    /// Signed less-than comparison (two's complement).
    pub(crate) fn bv_slt(&mut self, a: &[CnfLit], b: &[CnfLit]) -> CnfLit {
        debug_assert_eq!(a.len(), b.len());
        let n = a.len();
        debug_assert!(n > 0);
        // a < b signed iff:
        // (a_msb=1, b_msb=0) => true (a is negative, b positive)
        // (a_msb=0, b_msb=1) => false
        // (same MSB) => unsigned(a[n-2:0]) < unsigned(b[n-2:0])
        let a_neg = a[n - 1];
        let b_pos = -b[n - 1];
        let case1 = self.make_and(a_neg, b_pos);

        let a_pos = -a[n - 1];
        let b_neg = b[n - 1];
        let case2 = self.make_and(a_pos, b_neg);

        let same_msb = self.make_xnor(a[n - 1], b[n - 1]);
        let lower_lt = self.make_unsigned_lt(&a[..n - 1], &b[..n - 1]);
        let case3 = self.make_and(same_msb, lower_lt);

        let not_case2 = -case2;
        let case1_or_3 = self.make_or(case1, case3);
        self.make_and(not_case2, case1_or_3)
    }

    /// Signed less-than-or-equal comparison (two's complement).
    pub(crate) fn bv_sle(&mut self, a: &[CnfLit], b: &[CnfLit]) -> CnfLit {
        let b_lt_a = self.bv_slt(b, a);
        -b_lt_a
    }

    /// Count leading zeros of a bitvector. Result width = result_width.
    /// Counts from MSB. For a bitvector [b0, b1, ..., bn-1] where bn-1 is MSB,
    /// returns the number of consecutive zeros starting from bn-1.
    pub(crate) fn bv_leading_zeros(&mut self, bits: &[CnfLit], result_width: usize) -> Vec<CnfLit> {
        let n = bits.len();
        if n == 0 {
            return self.const_bv(0, result_width);
        }
        // Build a priority encoder from MSB to LSB
        // lz = 0 if bits[n-1] == 1
        // lz = 1 if bits[n-1] == 0 and bits[n-2] == 1
        // etc.
        // We build this as nested ITE: starting from position 0 (all zeros case)
        let mut lz = self.const_bv(n as u64, result_width);
        for (i, &bit) in bits.iter().enumerate() {
            // If bits[i] is set, lz = (n - 1 - i)
            let count = (n - 1 - i) as u64;
            let count_bv = self.const_bv(count, result_width);
            lz = self.make_ite_bits(bit, &count_bv, &lz);
        }
        lz
    }
}
