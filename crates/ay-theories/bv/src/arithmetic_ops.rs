// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV arithmetic, bitwise, shift, and division bit-blasting primitives.
//!
//! Adder circuits, multiplication (shift-add + const-case), bitwise
//! operations (AND, OR, XOR, NOT, NAND, NOR, XNOR). The dispatch
//! function that routes BV operations is in `arithmetic`.

use super::*;

impl BvSolver<'_> {
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
        let (s1, c1) = self.half_adder(a, b);
        let (sum, c2) = self.half_adder(s1, cin);
        let carry = self.mk_or(c1, c2);
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
        assert_eq!(a.len(), b.len());
        let n = a.len();
        let mut result = Vec::with_capacity(n);

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
        assert_eq!(a.len(), b.len());
        let n = a.len();
        let mut result = Vec::with_capacity(n);

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
        let not_b = Self::bitblast_not(b);
        let cin = self.fresh_true();
        self.bitblast_add_with_carry(a, &not_b, cin)
    }

    /// Bit-blast negation: -a = ~a + 1
    ///
    /// Uses a half-adder chain (increment) instead of full addition.
    /// Each bit: sum_i = ~a_i XOR carry, carry = ~a_i AND carry.
    /// MSB: sum only (no carry output needed).
    pub(super) fn bitblast_neg(&mut self, a: &BvBits) -> BvBits {
        let not_a = Self::bitblast_not(a);
        let n = not_a.len();
        let mut result = Vec::with_capacity(n);

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

        for na_bit in &not_a[1..n - 1] {
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
        let n = a.len();
        if n == 0 || n >= 100 {
            // Z3 has a hard cap at 100 bits (bit_blaster_tpl_def.h:1128-1129)
            return None;
        }

        // Count non-constant bits in both operands
        let mut case_size: usize = 1;
        let circuit_size = n * n * 5; // Z3's cost heuristic for shift-and-add circuit

        for i in 0..n {
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
        let mut a_bits = a.clone();
        let mut b_bits = b.clone();
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
        let n = a_bits.len();

        // Find next non-constant bit in current operand
        let mut i = start_idx;

        if is_a {
            // Skip constant bits in a
            while i < n && self.is_known_const(a_bits[i]) {
                i += 1;
            }
            if i == n {
                // Done with a, switch to b starting from 0
                return self.const_case_mul_recurse(false, 0, a_bits, b_bits);
            }
        } else {
            // Skip constant bits in b
            while i < n && self.is_known_const(b_bits[i]) {
                i += 1;
            }
        }

        if i < n {
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
            let out1 = self.const_case_mul_recurse(is_a, i + 1, a_bits, b_bits);

            // Case 2: bit = false
            let false_lit = self.fresh_false();
            if is_a {
                a_bits[i] = false_lit;
            } else {
                b_bits[i] = false_lit;
            }
            let out2 = self.const_case_mul_recurse(is_a, i + 1, a_bits, b_bits);

            // Restore original literal
            if is_a {
                a_bits[i] = orig_lit;
            } else {
                b_bits[i] = orig_lit;
            }

            // Combine with ITE: result[j] = ite(orig_lit, out1[j], out2[j])
            let mut result = Vec::with_capacity(n);
            for j in 0..n {
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
        let n = a_bits.len();

        // Extract numeric values from known-constant bits
        let mut a_val: u128 = 0;
        let mut b_val: u128 = 0;

        for (i, &lit) in a_bits.iter().enumerate() {
            if self.is_known_true(lit) {
                a_val |= 1u128 << i;
            }
            // is_known_false: bit stays 0
        }

        for (i, &lit) in b_bits.iter().enumerate() {
            if self.is_known_true(lit) {
                b_val |= 1u128 << i;
            }
        }

        // Compute product (truncated to n bits)
        let product = a_val.wrapping_mul(b_val);

        // Convert to const bits
        let mut result = Vec::with_capacity(n);
        for i in 0..n {
            let bit_set = (product >> i) & 1 == 1;
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

        // Try const-case multiplier optimization first (#1828)
        if let Some(result) = self.try_const_case_mul(a, b) {
            return result;
        }

        // Fall back to standard shift-and-add. The circuit is asymmetric even
        // though multiplication is commutative: only selector zero-bits skip
        // an addition, and unknown selector bits also need an n-bit mask.
        // Orient the cheaper word as selector so raw bvmul performance cannot
        // depend on operand order.
        if self.mul_selector_score(a) < self.mul_selector_score(b) {
            self.bitblast_mul_shift_add(b, a)
        } else {
            self.bitblast_mul_shift_add(a, b)
        }
    }

    /// Cost key for the selector side of shift-and-add multiplication.
    pub(super) fn mul_selector_score(&self, bits: &BvBits) -> (usize, usize) {
        let mut non_false = 0;
        let mut unknown = 0;
        for &bit in bits {
            if !self.is_known_false(bit) {
                non_false += 1;
                if !self.is_known_true(bit) {
                    unknown += 1;
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
        let n = a.len();

        if n == 0 {
            return Vec::new();
        }

        // Initialize with zero
        let mut result = self.const_bits(0, n);

        for (i, &bi) in b.iter().enumerate().take(n) {
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
                shifted.iter().map(|&s| self.mk_and(s, bi)).collect()
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
        assert_eq!(a.len(), b.len());
        a.iter()
            .zip(b.iter())
            .map(|(&ai, &bi)| self.mk_and(ai, bi))
            .collect()
    }

    /// Bit-blast bitwise OR
    pub(super) fn bitblast_or(&mut self, a: &BvBits, b: &BvBits) -> BvBits {
        assert_eq!(a.len(), b.len());
        a.iter()
            .zip(b.iter())
            .map(|(&ai, &bi)| self.mk_or(ai, bi))
            .collect()
    }

    /// Bit-blast bitwise XOR
    pub(super) fn bitblast_xor(&mut self, a: &BvBits, b: &BvBits) -> BvBits {
        assert_eq!(a.len(), b.len());
        a.iter()
            .zip(b.iter())
            .map(|(&ai, &bi)| self.mk_xor(ai, bi))
            .collect()
    }

    /// Bit-blast bitwise NAND
    pub(super) fn bitblast_nand(&mut self, a: &BvBits, b: &BvBits) -> BvBits {
        assert_eq!(a.len(), b.len());
        a.iter()
            .zip(b.iter())
            .map(|(&ai, &bi)| {
                let and = self.mk_and(ai, bi);
                -and
            })
            .collect()
    }

    /// Bit-blast bitwise NOR
    pub(super) fn bitblast_nor(&mut self, a: &BvBits, b: &BvBits) -> BvBits {
        assert_eq!(a.len(), b.len());
        a.iter()
            .zip(b.iter())
            .map(|(&ai, &bi)| {
                let or = self.mk_or(ai, bi);
                -or
            })
            .collect()
    }

    /// Bit-blast bitwise XNOR
    pub(super) fn bitblast_xnor(&mut self, a: &BvBits, b: &BvBits) -> BvBits {
        assert_eq!(a.len(), b.len());
        a.iter()
            .zip(b.iter())
            .map(|(&ai, &bi)| self.mk_xnor(ai, bi))
            .collect()
    }

    /// Bit-blast bitwise NOT
    pub(super) fn bitblast_not(a: &BvBits) -> BvBits {
        a.iter().map(|&ai| -ai).collect()
    }
}
