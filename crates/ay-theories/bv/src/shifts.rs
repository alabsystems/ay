// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV shift and barrel-shifter bit-blasting operations.

use super::*;

impl BvSolver<'_> {
    /// Shift left by a constant amount.
    ///
    /// Zero bits use `fresh_false` for multiplication optimization (#1720).
    pub(super) fn shift_left_const(&mut self, a: &BvBits, amt: usize) -> BvBits {
        let n = a.len();
        let mut result = Vec::with_capacity(n);

        // Low bits become zero
        for _ in 0..amt.min(n) {
            result.push(self.fresh_false());
        }

        // Shift in the original bits
        for &bit in a.iter().take(n - amt.min(n)) {
            result.push(bit);
        }

        result
    }

    /// Logical shift right by a constant amount.
    ///
    /// Zero bits use `fresh_false` for multiplication optimization (#1720).
    pub(super) fn shift_right_const(&mut self, a: &BvBits, amt: usize) -> BvBits {
        let n = a.len();
        let mut result = Vec::with_capacity(n);

        // Shift in the original bits
        for &bit in a.iter().skip(amt.min(n)) {
            result.push(bit);
        }

        // High bits become zero
        for _ in 0..amt.min(n) {
            result.push(self.fresh_false());
        }

        result
    }

    /// Bit-blast left shift (variable amount)
    ///
    /// Shortcut (#8111): When the shift amount is a known constant at the bit
    /// level, bypass the barrel-shifter MUX tree and just wire bits directly.
    /// This eliminates ~log2(n) layers of n MUX gates per constant shift.
    pub(super) fn bitblast_shl(&mut self, a: &BvBits, b: &BvBits) -> BvBits {
        let n = a.len();
        if n == 0 {
            return Vec::new();
        }

        // Constant-shift shortcut: if all shift-amount bits are known constants,
        // just wire the bits directly without building a barrel-shifter circuit.
        if let Some(shift_amt) = self.try_bits_to_usize(b) {
            if shift_amt >= n {
                return self.const_bits(0, n);
            }
            return self.shift_left_const(a, shift_amt);
        }

        // Use barrel shifter approach for bits 0..log2(n)
        let mut current = a.clone();

        // How many bits of shift amount can we handle before overflow?
        // For n-bit value, shifts 0..n-1 are valid. That requires ceil(log2(n)) bits.
        let log2_n = if n.is_power_of_two() {
            n.trailing_zeros() as usize // exact log2
        } else {
            (usize::BITS - n.leading_zeros()) as usize // ceil(log2)
        };

        for (i, &bi) in b.iter().enumerate().take(log2_n) {
            let shift_amt = 1 << i;
            if shift_amt >= n {
                break;
            }

            let shifted = self.shift_left_const(&current, shift_amt);
            // MUX: if bi then shifted else current
            current = self.bitwise_mux(&shifted, &current, bi);
        }

        // Handle overflow: if any high bit (>= log2_n) is set, shift >= n => result = 0
        let high_bits: Vec<CnfLit> = b.iter().skip(log2_n).copied().collect();
        if !high_bits.is_empty() {
            let overflow = self.mk_or_many(&high_bits);
            let zero = self.const_bits(0, n);
            current = self.bitwise_mux(&zero, &current, overflow);
        }

        current
    }

    /// Bit-blast logical right shift (variable amount)
    ///
    /// Shortcut (#8111): When the shift amount is a known constant at the bit
    /// level, bypass the barrel-shifter MUX tree and just wire bits directly.
    pub(super) fn bitblast_lshr(&mut self, a: &BvBits, b: &BvBits) -> BvBits {
        let n = a.len();
        if n == 0 {
            return Vec::new();
        }

        // Constant-shift shortcut: if all shift-amount bits are known constants,
        // just wire the bits directly without building a barrel-shifter circuit.
        if let Some(shift_amt) = self.try_bits_to_usize(b) {
            if shift_amt >= n {
                return self.const_bits(0, n);
            }
            return self.shift_right_const(a, shift_amt);
        }

        let mut current = a.clone();

        // How many bits of shift amount can we handle before overflow?
        let log2_n = if n.is_power_of_two() {
            n.trailing_zeros() as usize
        } else {
            (usize::BITS - n.leading_zeros()) as usize
        };

        for (i, &bi) in b.iter().enumerate().take(log2_n) {
            let shift_amt = 1 << i;
            if shift_amt >= n {
                break;
            }

            let shifted = self.shift_right_const(&current, shift_amt);
            current = self.bitwise_mux(&shifted, &current, bi);
        }

        // Handle overflow: if any high bit (>= log2_n) is set, shift >= n => result = 0
        let high_bits: Vec<CnfLit> = b.iter().skip(log2_n).copied().collect();
        if !high_bits.is_empty() {
            let overflow = self.mk_or_many(&high_bits);
            let zero = self.const_bits(0, n);
            current = self.bitwise_mux(&zero, &current, overflow);
        }

        current
    }

    /// Bit-blast arithmetic right shift (variable amount)
    ///
    /// Shortcut (#8111): When the shift amount is a known constant at the bit
    /// level, bypass the barrel-shifter MUX tree and just wire bits directly.
    pub(super) fn bitblast_ashr(&mut self, a: &BvBits, b: &BvBits) -> BvBits {
        let n = a.len();
        if n == 0 {
            return Vec::new();
        }

        let sign_bit = a[n - 1];

        // Constant-shift shortcut: if all shift-amount bits are known constants,
        // just wire the bits directly without building a barrel-shifter circuit.
        if let Some(shift_amt) = self.try_bits_to_usize(b) {
            if shift_amt >= n {
                // All bits become the sign bit
                return vec![sign_bit; n];
            }
            // Arithmetic shift right: shift in the original bits, fill with sign bit
            let mut result = Vec::with_capacity(n);
            for &bit in a.iter().skip(shift_amt) {
                result.push(bit);
            }
            for _ in 0..shift_amt {
                result.push(sign_bit);
            }
            return result;
        }

        let mut current = a.clone();

        // How many bits of shift amount can we handle before overflow?
        let log2_n = if n.is_power_of_two() {
            n.trailing_zeros() as usize
        } else {
            (usize::BITS - n.leading_zeros()) as usize
        };

        for (i, &bi) in b.iter().enumerate().take(log2_n) {
            let shift_amt = 1 << i;
            if shift_amt >= n {
                break;
            }

            // Arithmetic shift fills with sign bit
            let mut shifted = Vec::with_capacity(n);
            for &bit in current.iter().skip(shift_amt) {
                shifted.push(bit);
            }
            for _ in 0..shift_amt.min(n) {
                shifted.push(sign_bit);
            }

            current = self.bitwise_mux(&shifted, &current, bi);
        }

        // Handle overflow: if any high bit (>= log2_n) is set, shift >= n => result = all sign bits
        let high_bits: Vec<CnfLit> = b.iter().skip(log2_n).copied().collect();
        if !high_bits.is_empty() {
            let overflow = self.mk_or_many(&high_bits);
            let all_sign = vec![sign_bit; n];
            current = self.bitwise_mux(&all_sign, &current, overflow);
        }

        current
    }
}
