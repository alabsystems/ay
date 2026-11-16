// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV arithmetic, bitwise, shift, and division bit-blasting primitives.
//!
//! Adder circuits, multiplication (shift-add + const-case), bitwise
//! operations (AND, OR, XOR, NOT, NAND, NOR, XNOR). The dispatch
//! function that routes BV operations is in `arithmetic`.

use super::*;

#[cfg(test)]
mod full_adder_tests;

/// Largest number of result bits a bit-blasting primitive reserves up front.
///
/// The reservation only pre-sizes the result vector: every primitive pushes
/// exactly one literal per result bit, so a word wider than this grows on push
/// as an unreserved `Vec` does and the literals are identical.
const MAX_PRESIZED_BITS: usize = 1 << 24;

/// Complement of a CNF literal: `neg_lit(lit) == -lit` for every literal.
///
/// CNF literals are DIMACS `±var` with `var` in `1..=i32::MAX`, a domain on
/// which negation never overflows, so `wrapping_neg` is total and identical to
/// `-lit` there (the same form as gates.rs and ay-core's `Tseitin::negate`).
/// `i32::MIN` is not a literal of any variable; it is the one value
/// `wrapping_neg` maps to itself.
#[inline]
const fn neg_lit(lit: CnfLit) -> CnfLit {
    lit.wrapping_neg()
}

impl BvSolver<'_> {
    /// Keep the ordinary pre-sizing hint; counted storage covers the whole word.
    fn arithmetic_bits(&self, n: usize) -> Option<BvBits> {
        if self.encoding.is_counted() {
            self.counted_bits(n)
        } else {
            Some(Vec::with_capacity(n.min(MAX_PRESIZED_BITS)))
        }
    }

    // =========================================================================
    // Bit-blasting for arithmetic operations
    // =========================================================================

    /// Create a half adder: (sum, carry) = a + b
    fn half_adder(&mut self, a: CnfLit, b: CnfLit) -> (CnfLit, CnfLit) {
        let sum = self.mk_xor(a, b);
        let carry = self.mk_and(a, b);
        (sum, carry)
    }

    /// Create a full adder: (sum, carry) = a + b + cin
    fn full_adder(&mut self, a: CnfLit, b: CnfLit, cin: CnfLit) -> (CnfLit, CnfLit) {
        // Preserve the existing constant-input simplifications and gate order.
        if self.is_known_const(a) || self.is_known_const(b) || self.is_known_const(cin) {
            let (s1, c1) = self.half_adder(a, b);
            let (sum, c2) = self.half_adder(s1, cin);
            let carry = self.mk_or(c1, c2);
            return (sum, carry);
        }

        // Canonical signed-literal order also makes the MUX cache reusable
        // when the two addends are exchanged.
        let (a, b) = if a <= b { (a, b) } else { (b, a) };
        let p = self.mk_xor(a, b);
        let sum = self.mk_xor(p, cin);
        // If p is false, a = b and carry = a. Otherwise exactly one addend
        // is true and carry = cin: carry = ite(a XOR b, cin, a).
        let carry = self.mk_mux(cin, a, p);
        (sum, carry)
    }

    /// Create a 3-input XOR: a ^ b ^ c (sum without carry, for MSB optimization)
    fn xor3(&mut self, a: CnfLit, b: CnfLit, c: CnfLit) -> CnfLit {
        let ab = self.mk_xor(a, b);
        self.mk_xor(ab, c)
    }

    /// Bit-blast addition using ripple-carry adder
    ///
    /// Optimization (#1812): MSB uses xor3 instead of full adder since
    /// the final carry is discarded. This matches Z3's mk_adder.
    #[allow(clippy::many_single_char_names)]
    pub(super) fn bitblast_add(&mut self, a: &BvBits, b: &BvBits) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }

        assert_eq!(a.len(), b.len());
        let n = a.len();
        let Some(mut result) = self.arithmetic_bits(n) else {
            return Vec::new();
        };

        if n == 0 {
            return result;
        }

        // Single-bit case: just XOR (no carry needed)
        if n == 1 {
            let s = self.mk_xor(a[0], b[0]);
            result.push(s);
            return result;
        }

        // First bit: half adder
        let (s, mut carry) = self.half_adder(a[0], b[0]);
        result.push(s);

        // Middle bits (1..n-1): full adder
        for i in 1..n - 1 {
            if !self.encoding_step() {
                return Vec::new();
            }
            let (s, c) = self.full_adder(a[i], b[i], carry);
            result.push(s);
            carry = c;
        }

        // MSB: xor3 only (no carry output needed, matches Z3 mk_adder)
        let msb_sum = self.xor3(a[n - 1], b[n - 1], carry);
        result.push(msb_sum);

        result
    }

    /// Bit-blast addition with carry-in using ripple-carry adder.
    ///
    /// Computes a + b + carry_in (mod 2^n). Used by subtraction and negation
    /// to avoid a redundant second addition: a - b = a + ~b + 1 is computed
    /// as a single add(a, ~b, carry_in=true) instead of two adds.
    #[allow(clippy::many_single_char_names)]
    pub(super) fn bitblast_add_with_carry(
        &mut self,
        a: &BvBits,
        b: &BvBits,
        carry_in: CnfLit,
    ) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }

        assert_eq!(a.len(), b.len());
        let n = a.len();
        let Some(mut result) = self.arithmetic_bits(n) else {
            return Vec::new();
        };

        if n == 0 {
            return result;
        }

        if n == 1 {
            let s = self.xor3(a[0], b[0], carry_in);
            result.push(s);
            return result;
        }

        // First bit: full adder with carry_in
        let (s, mut carry) = self.full_adder(a[0], b[0], carry_in);
        result.push(s);

        // Middle bits (1..n-1): full adder
        for i in 1..n - 1 {
            if !self.encoding_step() {
                return Vec::new();
            }
            let (s, c) = self.full_adder(a[i], b[i], carry);
            result.push(s);
            carry = c;
        }

        // MSB: xor3 only (no carry output needed)
        let msb_sum = self.xor3(a[n - 1], b[n - 1], carry);
        result.push(msb_sum);

        result
    }

    /// Bit-blast subtraction: a - b = a + ~b + 1
    ///
    /// Uses a single add-with-carry instead of two additions. The carry-in of 1
    /// replaces the `+ 1` in two's complement negation, halving the gate count.
    pub(super) fn bitblast_sub(&mut self, a: &BvBits, b: &BvBits) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }

        let not_b = self.bitblast_not(b);
        let cin = self.fresh_true();
        self.bitblast_add_with_carry(a, &not_b, cin)
    }

    /// Subtract while retaining the unsigned no-borrow bit: `(a - b, a >= b)`.
    ///
    /// The final carry of `a + !b + 1` is true exactly when `a >= b`.
    /// Keeping it lets restoring division share comparison and subtraction.
    /// For empty words this returns an empty difference and true (`0 >= 0`).
    ///
    /// Reference: Z3's `mk_subtracter`, consumed by `mk_udiv_urem`:
    /// <https://github.com/Z3Prover/z3/blob/z3-4.13.0/src/ast/rewriter/bit_blaster/bit_blaster_tpl_def.h#L159-L179>.
    pub(super) fn bitblast_sub_with_carry(&mut self, a: &BvBits, b: &BvBits) -> (BvBits, CnfLit) {
        if !self.encoding_complete() {
            return (Vec::new(), 0);
        }

        assert_eq!(a.len(), b.len());
        let n = a.len();
        let Some(mut result) = self.arithmetic_bits(n) else {
            return (Vec::new(), 0);
        };
        let mut carry = self.fresh_true();
        for (&ai, &bi) in a.iter().zip(b.iter()) {
            if !self.encoding_step() {
                return (Vec::new(), 0);
            }
            let (sum, next_carry) = self.full_adder(ai, neg_lit(bi), carry);
            result.push(sum);
            carry = next_carry;
        }
        (result, carry)
    }

    /// Bit-blast negation: -a = ~a + 1
    ///
    /// Uses a half-adder chain (increment) instead of full addition.
    /// Each bit: sum_i = ~a_i XOR carry, carry = ~a_i AND carry.
    /// MSB: sum only (no carry output needed).
    pub(super) fn bitblast_neg(&mut self, a: &BvBits) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }

        let not_a = self.bitblast_not(a);
        let n = not_a.len();
        let Some(mut result) = self.arithmetic_bits(n) else {
            return Vec::new();
        };

        if n == 0 {
            return result;
        }
        if n == 1 {
            // ~a + 1 for 1-bit = ~a XOR 1 = a (since ~(~a) = a)
            // But we should just negate: for 1-bit, -a = ~a XOR 1 = a
            // More precisely: result = NOT(a[0]) XOR true = a[0]
            // The XOR with known_true will give NOT(NOT(a[0])) = a[0]
            result.push(a[0]);
            return result;
        }

        // Increment ~a by 1 using half-adder chain with carry-in = 1
        // For bit 0: sum = ~a[0] XOR 1 = a[0], carry = ~a[0] AND 1 = ~a[0]
        // (constant propagation in mk_xor/mk_and handles these)
        let cin = self.fresh_true();
        let (s, mut carry) = self.half_adder(not_a[0], cin);
        result.push(s);

        // The middle bits `1..n - 1` (here `n >= 2`).
        for na_bit in not_a.iter().take(n - 1).skip(1) {
            if !self.encoding_step() {
                return Vec::new();
            }
            let (s, c) = self.half_adder(*na_bit, carry);
            result.push(s);
            carry = c;
        }

        // MSB: just XOR (discard carry)
        let msb = self.mk_xor(not_a[n - 1], carry);
        result.push(msb);

        result
    }

    /// Attempt const-case multiplier optimization (Z3's mk_const_case_multiplier).
    ///
    /// When operands have many known-constant bits, case-splitting on the non-constant
    /// bits is cheaper than building the full shift-and-add multiplier circuit.
    ///
    /// Returns Some(result) if case-splitting was used, None if standard multiplication
    /// should be used instead.
    ///
    /// Ported from Z3: `reference/z3/src/ast/rewriter/bit_blaster/bit_blaster_tpl_def.h:1117-1174`
    fn try_const_case_mul(&mut self, a: &BvBits, b: &BvBits) -> Option<BvBits> {
        if !self.encoding_complete() {
            return None;
        }

        let n = a.len();
        if n == 0 || n >= 100 {
            // Z3 has a hard cap at 100 bits (bit_blaster_tpl_def.h:1128-1129)
            return None;
        }

        // Count non-constant bits in both operands
        let mut case_size: usize = 1;
        let circuit_size = n * n * 5; // Z3's cost heuristic for shift-and-add circuit

        for i in 0..n {
            if !self.encoding_step() {
                return None;
            }
            if case_size >= circuit_size {
                break;
            }
            if !self.is_known_const(a[i]) {
                case_size = case_size.saturating_mul(2);
            }
            if !self.is_known_const(b[i]) {
                case_size = case_size.saturating_mul(2);
            }
        }

        if case_size >= circuit_size {
            // Case-splitting is not cheaper than the circuit
            return None;
        }

        // Case-splitting is cheaper - build ITE tree
        let mut a_bits = self.counted_copy_bits(a)?;
        let mut b_bits = self.counted_copy_bits(b)?;
        Some(self.const_case_mul_recurse(true, 0, &mut a_bits, &mut b_bits))
    }

    /// Recursive implementation of const-case multiplier.
    ///
    /// Finds the next non-constant bit, splits on it (true/false cases),
    /// and combines results with ITE. At leaves, computes the product numerically.
    ///
    /// Algorithm from Z3 bit_blaster_tpl_def.h:1140-1174:
    /// 1. Find next non-constant bit in a (then b)
    /// 2. If found, split: set bit to true, recurse for out1; set to false, recurse for out2
    /// 3. Combine: result[j] = ite(original_bit, out1[j], out2[j])
    /// 4. At leaf (all bits constant): compute a*b numerically
    fn const_case_mul_recurse(
        &mut self,
        is_a: bool,
        start_idx: usize,
        a_bits: &mut Vec<CnfLit>,
        b_bits: &mut Vec<CnfLit>,
    ) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }

        let n = a_bits.len();

        // Find next non-constant bit in current operand, skipping constant
        // bits from `start_idx` on.
        let operand: &[CnfLit] = if is_a { a_bits } else { b_bits };
        if !self
            .encoding
            .counted_admit(operand.len().saturating_sub(start_idx), 0)
        {
            return Vec::new();
        }
        let next_open = operand
            .iter()
            .enumerate()
            .skip(start_idx)
            .find(|&(_, &lit)| !self.is_known_const(lit))
            .map(|(i, _)| i);

        if is_a && next_open.is_none() {
            // Done with a, switch to b starting from 0
            return self.const_case_mul_recurse(false, 0, a_bits, b_bits);
        }

        if let Some(i) = next_open {
            // The split bit is an operand position, so `i < n` and the
            // following search starts at `i + 1 <= n` (an empty search at `n`).
            let next_start = i.checked_add(1).unwrap_or(n);
            // Found non-constant bit at position i in current operand
            // Split: compute result for bit=true and bit=false, combine with ITE
            let orig_lit = if is_a { a_bits[i] } else { b_bits[i] };

            // Case 1: bit = true
            let true_lit = self.fresh_true();
            if is_a {
                a_bits[i] = true_lit;
            } else {
                b_bits[i] = true_lit;
            }
            let out1 = self.const_case_mul_recurse(is_a, next_start, a_bits, b_bits);

            // Case 2: bit = false
            let false_lit = self.fresh_false();
            if is_a {
                a_bits[i] = false_lit;
            } else {
                b_bits[i] = false_lit;
            }
            let out2 = self.const_case_mul_recurse(is_a, next_start, a_bits, b_bits);

            // Restore original literal
            if is_a {
                a_bits[i] = orig_lit;
            } else {
                b_bits[i] = orig_lit;
            }

            if !self.encoding_complete() {
                return Vec::new();
            }

            // Combine with ITE: result[j] = ite(orig_lit, out1[j], out2[j])
            let Some(mut result) = self.arithmetic_bits(n) else {
                return Vec::new();
            };
            for j in 0..n {
                if !self.encoding_step() {
                    return Vec::new();
                }
                let bit = self.mk_mux(out1[j], out2[j], orig_lit);
                result.push(bit);
            }
            result
        } else {
            // All bits are constant - compute product numerically
            self.const_case_mul_leaf(a_bits, b_bits)
        }
    }

    /// Compute product at leaf when all bits are known constants.
    fn const_case_mul_leaf(&mut self, a_bits: &[CnfLit], b_bits: &[CnfLit]) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }

        let n = a_bits.len();

        // Extract numeric values from known-constant bits
        let mut a_val: u128 = 0;
        let mut b_val: u128 = 0;

        // Leaves are reached only below the 100-bit cap of
        // `try_const_case_mul`, so every bit position fits the `u128` value
        // and `checked_shl` is `<<` on each of them.
        for (i, &lit) in a_bits.iter().enumerate() {
            if !self.encoding_step() {
                return Vec::new();
            }
            if self.is_known_true(lit) {
                if let Some(bit) = u32::try_from(i).ok().and_then(|s| 1u128.checked_shl(s)) {
                    a_val |= bit;
                }
            }
            // is_known_false: bit stays 0
        }

        for (i, &lit) in b_bits.iter().enumerate() {
            if !self.encoding_step() {
                return Vec::new();
            }
            if self.is_known_true(lit) {
                if let Some(bit) = u32::try_from(i).ok().and_then(|s| 1u128.checked_shl(s)) {
                    b_val |= bit;
                }
            }
        }

        // Compute product (truncated to n bits)
        let product = a_val.wrapping_mul(b_val);

        // Convert to const bits
        let Some(mut result) = self.arithmetic_bits(n) else {
            return Vec::new();
        };
        for i in 0..n {
            if !self.encoding_step() {
                return Vec::new();
            }
            // Positions past the `u128` product are zero bits of it.
            let bit_set = u32::try_from(i)
                .ok()
                .and_then(|s| product.checked_shr(s))
                .is_some_and(|shifted| shifted & 1 == 1);
            let lit = if bit_set {
                self.fresh_true()
            } else {
                self.fresh_false()
            };
            result.push(lit);
        }
        result
    }

    /// Bit-blast multiplication.
    ///
    /// Optimization #0: Power-of-2 shortcut (#8111) - when one operand is a
    /// known power of 2, replace the multiplier with a simple left shift (wiring).
    /// This eliminates the entire multiplier circuit for constants like 2, 4, 8, etc.
    ///
    /// Optimization #1: Const-case multiplier (#1828) - when operands have many
    /// known-constant bits, case-splitting on non-constant bits is cheaper than
    /// building the full shift-and-add circuit.
    ///
    /// Optimization #2: Skip iterations where b[i] is known-false (#1720).
    /// For `concat(0^48, x) * concat(0^48, y)`, this reduces 96 iterations to 48.
    pub(super) fn bitblast_mul(&mut self, a: &BvBits, b: &BvBits) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }

        assert_eq!(a.len(), b.len());
        let n = a.len();

        // Power-of-2 shortcut (#8111): x * 2^k = x << k (just wiring)
        if let Some(k) = self.try_bits_power_of_2(b) {
            if k >= n {
                return self.const_bits(0, n);
            }
            return self.shift_left_const(a, k);
        }
        if let Some(k) = self.try_bits_power_of_2(a) {
            if k >= n {
                return self.const_bits(0, n);
            }
            return self.shift_left_const(b, k);
        }

        // The circuit is asymmetric even
        // though multiplication is commutative: only selector zero-bits skip
        // an addition, and unknown selector bits also need an n-bit mask.
        // Orient the cheaper word as selector, breaking equal-cost ties by
        // signed literal order. Both a*b and b*a then use the same circuit
        // and existing gate caches, rather than asking SAT to rediscover
        // modular multiplication commutativity. Apply this to case splitting
        // too: its first operand otherwise changes its decision-tree shape.
        let a_score = self.mul_selector_score(a);
        let b_score = self.mul_selector_score(b);
        let mut a_is_selector = a_score < b_score;
        if a_score == b_score {
            for (&a_bit, &b_bit) in a.iter().zip(b) {
                if !self.encoding_step() {
                    return Vec::new();
                }
                if a_bit != b_bit {
                    a_is_selector = a_bit < b_bit;
                    break;
                }
            }
        }
        let (a, b) = if a_is_selector { (b, a) } else { (a, b) };

        // Try const-case multiplier optimization first (#1828).
        if let Some(result) = self.try_const_case_mul(a, b) {
            return result;
        }

        self.bitblast_mul_shift_add(a, b)
    }

    /// Cost key for the selector side of shift-and-add multiplication.
    pub(super) fn mul_selector_score(&self, bits: &BvBits) -> (usize, usize) {
        if !self.encoding_complete() {
            return (0, 0);
        }

        let mut non_false: usize = 0;
        let mut unknown: usize = 0;
        for &bit in bits {
            if !self.encoding_step() {
                return (0, 0);
            }
            if !self.is_known_false(bit) {
                non_false = non_false.saturating_add(1);
                if !self.is_known_true(bit) {
                    unknown = unknown.saturating_add(1);
                }
            }
        }
        (non_false, unknown)
    }

    /// Bit-blast multiplication using shift-and-add (fallback when const-case
    /// optimization doesn't apply).
    ///
    /// Optimization (#1720): Skip iterations where b[i] is known-false.
    fn bitblast_mul_shift_add(&mut self, a: &BvBits, b: &BvBits) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }

        let n = a.len();

        if n == 0 {
            return Vec::new();
        }

        // Initialize with zero
        let mut result = self.const_bits(0, n);

        for (i, &bi) in b.iter().enumerate().take(n) {
            if !self.encoding_step() {
                return Vec::new();
            }
            // Optimization: Skip if b[i] is known to be false (#1720)
            // When b[i] = 0, a << i masked by b[i] is all zeros, contributing nothing.
            if self.is_known_false(bi) {
                continue;
            }

            // If b[i] is set, add a << i to result
            let shifted = self.shift_left_const(a, i);
            let masked: BvBits = if self.is_known_true(bi) {
                shifted
            } else {
                let Some(mut masked) = self.counted_bits(shifted.len()) else {
                    return Vec::new();
                };
                for &bit in &shifted {
                    if !self.encoding_step() {
                        return Vec::new();
                    }
                    masked.push(self.mk_and(bit, bi));
                }
                masked
            };
            result = self.bitblast_add(&result, &masked);
        }

        result
    }

    // =========================================================================
    // Bit-blasting for bitwise operations
    // =========================================================================

    /// Bit-blast bitwise AND
    pub(crate) fn bitblast_and(&mut self, a: &BvBits, b: &BvBits) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }
        assert_eq!(a.len(), b.len());
        let Some(mut result) = self.counted_bits(a.len()) else {
            return Vec::new();
        };
        for (&ai, &bi) in a.iter().zip(b.iter()) {
            if !self.encoding_step() {
                return Vec::new();
            }
            let lit = self.mk_and(ai, bi);
            result.push(lit);
        }
        result
    }

    /// Bit-blast bitwise OR
    pub(super) fn bitblast_or(&mut self, a: &BvBits, b: &BvBits) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }
        assert_eq!(a.len(), b.len());
        let Some(mut result) = self.counted_bits(a.len()) else {
            return Vec::new();
        };
        for (&ai, &bi) in a.iter().zip(b.iter()) {
            if !self.encoding_step() {
                return Vec::new();
            }
            let lit = self.mk_or(ai, bi);
            result.push(lit);
        }
        result
    }

    /// Bit-blast bitwise XOR
    pub(super) fn bitblast_xor(&mut self, a: &BvBits, b: &BvBits) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }
        assert_eq!(a.len(), b.len());
        let Some(mut result) = self.counted_bits(a.len()) else {
            return Vec::new();
        };
        for (&ai, &bi) in a.iter().zip(b.iter()) {
            if !self.encoding_step() {
                return Vec::new();
            }
            let lit = self.mk_xor(ai, bi);
            result.push(lit);
        }
        result
    }

    /// Bit-blast bitwise NAND
    pub(super) fn bitblast_nand(&mut self, a: &BvBits, b: &BvBits) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }
        assert_eq!(a.len(), b.len());
        let Some(mut result) = self.counted_bits(a.len()) else {
            return Vec::new();
        };
        for (&ai, &bi) in a.iter().zip(b.iter()) {
            if !self.encoding_step() {
                return Vec::new();
            }
            let lit = self.mk_and(ai, bi);
            result.push(neg_lit(lit));
        }
        result
    }

    /// Bit-blast bitwise NOR
    pub(super) fn bitblast_nor(&mut self, a: &BvBits, b: &BvBits) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }
        assert_eq!(a.len(), b.len());
        let Some(mut result) = self.counted_bits(a.len()) else {
            return Vec::new();
        };
        for (&ai, &bi) in a.iter().zip(b.iter()) {
            if !self.encoding_step() {
                return Vec::new();
            }
            let lit = self.mk_or(ai, bi);
            result.push(neg_lit(lit));
        }
        result
    }

    /// Bit-blast bitwise XNOR
    pub(super) fn bitblast_xnor(&mut self, a: &BvBits, b: &BvBits) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }
        assert_eq!(a.len(), b.len());
        let Some(mut result) = self.counted_bits(a.len()) else {
            return Vec::new();
        };
        for (&ai, &bi) in a.iter().zip(b.iter()) {
            if !self.encoding_step() {
                return Vec::new();
            }
            let lit = self.mk_xnor(ai, bi);
            result.push(lit);
        }
        result
    }

    /// Bit-blast bitwise NOT
    pub(super) fn bitblast_not(&mut self, a: &BvBits) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }
        let Some(mut result) = self.counted_bits(a.len()) else {
            return Vec::new();
        };
        for &bit in a {
            if !self.encoding_step() {
                return Vec::new();
            }
            result.push(neg_lit(bit));
        }
        result
    }
}
