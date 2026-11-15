// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bitvector arithmetic circuits for the floating-point bit-blasting pipeline.
//!
//! These operate on `FpSolver`'s clause store, reusing the lower-level gate
//! helpers from `gates.rs`.

use ay_core::{CnfClause, CnfLit};
use num_bigint::BigInt;

use crate::construction::control::{uninterrupted, BuildControl};
use crate::construction::FpBuildStage;

use super::gates::neg_lit;
use super::FpSolver;

impl FpSolver<'_> {
    /// Return a canonical false literal (always 0), creating it on first call.
    /// Subsequent calls reuse the same variable (#5870).
    pub(crate) fn const_false(&mut self) -> CnfLit {
        if let Some(lit) = self.cached_false {
            return lit;
        }
        let v = self.fresh_var();
        self.add_clause(CnfClause::unit(neg_lit(v)));
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
        let mut bits = Vec::new();
        // A capacity hint only: on failure `push` grows the vector as before.
        let _ = bits.try_reserve_exact(width);
        for i in 0..width {
            bits.push(if i < 64 && (value >> i) & 1 == 1 {
                self.const_true()
            } else {
                self.const_false()
            });
        }
        bits
    }

    /// Encode a signed host integer, sign-extending beyond 64 bits. Effective
    /// FP exponents have two guard bits, so a 63-bit format needs 65 bits here.
    pub(crate) fn const_bv_signed(&mut self, value: i64, width: usize) -> Vec<CnfLit> {
        let mut bits = self.const_bv(value as u64, width.min(64));
        if width > 64 {
            let sign = if value < 0 {
                self.const_true()
            } else {
                self.const_false()
            };
            bits.resize(width, sign);
        }
        bits
    }

    /// Create an exact-width constant without truncating it to a host word.
    /// As with BV literals, bit 0 is the LSB and excess high bits are omitted.
    pub(crate) fn const_bv_bigint(&mut self, value: &BigInt, width: usize) -> Vec<CnfLit> {
        let mut bits = Vec::new();
        // Match const_bv's existing capacity-hint behavior.
        let _ = bits.try_reserve_exact(width);
        for i in 0..width {
            bits.push(if value.bit(i as u64) {
                self.const_true()
            } else {
                self.const_false()
            });
        }
        bits
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

    /// Resize an UNSIGNED bitvector to `width` bits: zero-extend, or drop high
    /// bits. Dropping is exact only when the caller knows the value fits.
    pub(crate) fn resize_unsigned(&mut self, bits: &[CnfLit], width: usize) -> Vec<CnfLit> {
        if bits.len() >= width {
            bits[..width].to_vec()
        } else {
            self.zero_extend(bits, width - bits.len())
        }
    }

    /// The number of bits an unsigned `value` needs (at least 1).
    pub(crate) const fn bits_to_hold(value: u64) -> usize {
        let bits = (u64::BITS - value.leading_zeros()) as usize;
        if bits == 0 {
            1
        } else {
            bits
        }
    }

    /// Sign-extend a bitvector by replicating the MSB.
    pub(crate) fn sign_extend(&mut self, bits: &[CnfLit], extra: usize) -> Vec<CnfLit> {
        debug_assert!(
            !bits.is_empty(),
            "invariant: sign_extend requires non-empty input"
        );
        // A zero-width vector has value 0, whose extension is all zeros.
        let Some(&msb) = bits.last() else {
            return self.zero_extend(bits, extra);
        };
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
        let mut result = Vec::new();
        // A capacity hint only: on failure `push` grows the vector as before.
        let _ = result.try_reserve_exact(a.len());
        let mut carry = self.const_false();
        for (&ai, &bi) in a.iter().zip(b) {
            let (sum, cout) = self.full_adder(ai, bi, carry);
            result.push(sum);
            carry = cout;
        }
        result
    }

    /// Negate a bitvector (two's complement).
    pub(crate) fn bv_neg(&mut self, a: &[CnfLit]) -> Vec<CnfLit> {
        let inverted: Vec<CnfLit> = a.iter().map(|&lit| neg_lit(lit)).collect();
        let one = self.const_bv(1, a.len());
        self.bv_add(&inverted, &one)
    }

    /// Subtraction: a - b.
    pub(crate) fn bv_sub(&mut self, a: &[CnfLit], b: &[CnfLit]) -> Vec<CnfLit> {
        let neg_b = self.bv_neg(b);
        self.bv_add(a, &neg_b)
    }

    /// Subtraction with borrow indication: returns `(a - b, a >= b)`.
    ///
    /// One adder pass (`a + ~b + 1`): the final carry-out is 1 exactly
    /// when `a >= b` unsigned. Functionally identical difference bits
    /// to [`Self::bv_sub`]; used by the restoring divider, where the
    /// previous form rebuilt `bv_neg(b)` (a full-width incrementer)
    /// and a separate full-width comparator on every one of the `n`
    /// iterations — measured at width 161 (one double `fp.div`):
    /// 227k SAT vars before this change. (#fp-div-borrow)
    pub(crate) fn bv_sub_with_ge(&mut self, a: &[CnfLit], b: &[CnfLit]) -> (Vec<CnfLit>, CnfLit) {
        debug_assert_eq!(a.len(), b.len());
        let mut result = Vec::new();
        let _ = result.try_reserve_exact(a.len());
        let mut carry = self.const_true();
        for (&ai, &bi) in a.iter().zip(b) {
            let (sum, cout) = self.full_adder(ai, neg_lit(bi), carry);
            result.push(sum);
            carry = cout;
        }
        (result, carry)
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
        uninterrupted(|control| self.bv_mul_with_control(a, b, control))
    }

    /// The shared multiplier, with refusal before allocating each row.
    pub(crate) fn bv_mul_with_control<C: BuildControl>(
        &mut self,
        a: &[CnfLit],
        b: &[CnfLit],
        control: &mut C,
    ) -> Result<Vec<CnfLit>, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::MultiplyRow))?;
        debug_assert_eq!(a.len(), b.len());
        let n = a.len();
        if n == 0 {
            control.checkpoint(self.construction_progress(FpBuildStage::MultiplyRow))?;
            return Ok(vec![]);
        }
        // Shift-and-add multiplier
        let zero = self.const_false();
        let mut acc = vec![zero; n];
        for (i, &b_bit) in b.iter().enumerate() {
            control.checkpoint(self.construction_progress(FpBuildStage::MultiplyRow))?;
            // partial product: a[j] & b[i], for positions where i+j < n
            let mut partial = Vec::new();
            // A capacity hint only: on failure `push` grows the vector as before.
            let _ = partial.try_reserve_exact(n);
            for &a_bit in a.iter().take(n.saturating_sub(i)) {
                partial.push(self.make_and(a_bit, b_bit));
            }
            // Pad to n bits with leading zeros
            while partial.len() < n {
                partial.push(zero);
            }
            // Shift left by i: prepend i zeros, truncate to n bits
            let mut shifted = vec![zero; i];
            shifted.extend(partial.iter().take(n.saturating_sub(i)));
            shifted.truncate(n);
            acc = self.bv_add(&acc, &shifted);
        }
        control.checkpoint(self.construction_progress(FpBuildStage::MultiplyRow))?;
        Ok(acc)
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
            let mut shifted = Vec::new();
            // A capacity hint only: on failure `push` grows the vector as before.
            let _ = shifted.try_reserve_exact(n);
            for j in 0..n {
                // `current` is n bits wide, so the source bit exists iff
                // `j + shift_amount < n`.
                match j.checked_add(shift_amount).and_then(|k| current.get(k)) {
                    Some(&bit) => shifted.push(bit),
                    None => shifted.push(zero),
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
            let mut shifted = Vec::new();
            // A capacity hint only: on failure `push` grows the vector as before.
            let _ = shifted.try_reserve_exact(n);
            for j in 0..n {
                // The source bit exists iff `j >= shift_amount`.
                match j.checked_sub(shift_amount).and_then(|k| current.get(k)) {
                    Some(&bit) => shifted.push(bit),
                    None => shifted.push(zero),
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
        uninterrupted(|control| self.bv_udiv_urem_with_control(a, b, control))
    }

    /// The shared restoring divider, with refusal before allocating each row.
    pub(crate) fn bv_udiv_urem_with_control<C: BuildControl>(
        &mut self,
        a: &[CnfLit],
        b: &[CnfLit],
        control: &mut C,
    ) -> Result<(Vec<CnfLit>, Vec<CnfLit>), C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::DivideRow))?;
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
            control.checkpoint(self.construction_progress(FpBuildStage::DivideRow))?;
            // Shift remainder left by 1 and bring in dividend bit a[i]
            let mut shifted_rem = Vec::new();
            // A capacity hint only: on failure `push` grows the vector as before.
            let _ = shifted_rem.try_reserve_exact(n);
            shifted_rem.push(a[i]); // LSB = next dividend bit
            if let Some((_, below_msb)) = rem.split_last() {
                // Shift up: every bit of the n-bit remainder but its MSB.
                shifted_rem.extend_from_slice(below_msb);
            }

            // Trial subtraction: trial = shifted_rem - b, with the
            // carry-out giving `shifted_rem >= b` directly (#fp-div-borrow).
            let (trial, ge) = self.bv_sub_with_ge(&shifted_rem, b);

            // quotient bit
            quot[i] = ge;

            // Select remainder: ge ? trial : shifted_rem
            rem = self.make_ite_bits(ge, &trial, &shifted_rem);
        }

        control.checkpoint(self.construction_progress(FpBuildStage::DivideRow))?;
        Ok((quot, rem))
    }

    /// Unsigned greater-than-or-equal comparison: a >= b.
    pub(crate) fn make_unsigned_ge(&mut self, a: &[CnfLit], b: &[CnfLit]) -> CnfLit {
        // a >= b  iff  NOT (a < b)
        let a_lt_b = self.make_unsigned_lt(a, b);
        neg_lit(a_lt_b)
    }

    /// Unsigned less-than comparison: a < b.
    pub(crate) fn make_unsigned_lt(&mut self, a: &[CnfLit], b: &[CnfLit]) -> CnfLit {
        debug_assert_eq!(a.len(), b.len());
        let mut pairs = a.iter().zip(b);
        let Some((&a_lsb, &b_lsb)) = pairs.next() else {
            let result = self.fresh_var();
            self.add_clause(CnfClause::unit(neg_lit(result)));
            return result;
        };

        // Iterate LSB→MSB so the MSB (highest weight) gets final priority.
        // At each bit: result = (a[i]<b[i]) || (a[i]==b[i] && prev_result).
        // The last-processed bit (MSB) overrides all lower bits.
        let not_a_lsb = neg_lit(a_lsb);
        let mut result = self.make_and(not_a_lsb, b_lsb);

        for (&a_i, &b_i) in pairs {
            let not_a_i = neg_lit(a_i);
            let bit_lt = self.make_and(not_a_i, b_i);
            let bit_eq = self.make_xnor(a_i, b_i);
            let bit_eq_and_result = self.make_and(bit_eq, result);
            result = self.make_or(bit_lt, bit_eq_and_result);
        }

        result
    }

    /// Signed less-than comparison (two's complement).
    pub(crate) fn bv_slt(&mut self, a: &[CnfLit], b: &[CnfLit]) -> CnfLit {
        debug_assert_eq!(a.len(), b.len());
        debug_assert!(!a.is_empty());
        // a < b signed iff:
        // (a_msb=1, b_msb=0) => true (a is negative, b positive)
        // (a_msb=0, b_msb=1) => false
        // (same MSB) => unsigned(a[n-2:0]) < unsigned(b[n-2:0])
        let (Some((&a_msb, a_low)), Some((&b_msb, b_low))) = (a.split_last(), b.split_last())
        else {
            // Zero-width vectors both have value 0, and 0 < 0 is false.
            return self.const_false();
        };
        let a_neg = a_msb;
        let b_pos = neg_lit(b_msb);
        let case1 = self.make_and(a_neg, b_pos);

        let a_pos = neg_lit(a_msb);
        let b_neg = b_msb;
        let case2 = self.make_and(a_pos, b_neg);

        let same_msb = self.make_xnor(a_msb, b_msb);
        let lower_lt = self.make_unsigned_lt(a_low, b_low);
        let case3 = self.make_and(same_msb, lower_lt);

        let not_case2 = neg_lit(case2);
        let case1_or_3 = self.make_or(case1, case3);
        self.make_and(not_case2, case1_or_3)
    }

    /// Signed less-than-or-equal comparison (two's complement).
    pub(crate) fn bv_sle(&mut self, a: &[CnfLit], b: &[CnfLit]) -> CnfLit {
        let b_lt_a = self.bv_slt(b, a);
        neg_lit(b_lt_a)
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
        // Pair bits[i] with n - 1 - i: the counts run n-1 down to 0.
        for (&bit, count) in bits.iter().zip((0..n).rev()) {
            // If bits[i] is set, lz = (n - 1 - i)
            let count_bv = self.const_bv(count as u64, result_width);
            lz = self.make_ite_bits(bit, &count_bv, &lz);
        }
        lz
    }
}

impl FpSolver<'_> {
    /// Logical left shift under the caller's original construction controller.
    pub(crate) fn bv_shl_with_control<C: BuildControl>(
        &mut self,
        a: &[CnfLit],
        b: &[CnfLit],
        control: &mut C,
    ) -> Result<Vec<CnfLit>, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let n = a.len();
        let zero = self.const_false();
        let mut current = a.to_vec();
        for i in 0..b.len() {
            control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
            let b_bit = b[i];
            let shift_amount = match 1usize.checked_shl(i as u32) {
                Some(v) => v,
                None => n,
            };
            if shift_amount >= n {
                let overflow = self.bv_or_reduce(&b[i..]);
                let all_zero = vec![zero; n];
                current = self.make_ite_bits(overflow, &all_zero, &current);
                drop(all_zero);
                control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
                break;
            }
            let mut shifted = Vec::new();
            let _ = shifted.try_reserve_exact(n);
            for j in 0..n {
                match j.checked_sub(shift_amount).and_then(|k| current.get(k)) {
                    Some(&bit) => shifted.push(bit),
                    None => shifted.push(zero),
                }
            }
            current = self.make_ite_bits(b_bit, &shifted, &current);
            drop(shifted);
            control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        }
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        Ok(current)
    }
}
