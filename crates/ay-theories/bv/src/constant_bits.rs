// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Reading a constant out of a bit vector whose bits are all known: the
//! bitblaster's shift and multiply shortcuts (#8111).

use super::*;

impl BvSolver<'_> {
    /// Try to extract a constant usize value from a bit vector whose bits
    /// are all known constants. Returns `None` if any bit is non-constant
    /// or the value exceeds `usize::MAX`.
    ///
    /// Used by bitblaster shift/multiply shortcuts (#8111) to detect constant
    /// operands and bypass barrel-shifter/multiplier circuits.
    pub(crate) fn try_bits_to_usize(&self, bits: &BvBits) -> Option<usize> {
        if !self.encoding_complete() {
            return None;
        }
        let mut value: usize = 0;
        for (i, &lit) in bits.iter().enumerate() {
            if !self.encoding_step() {
                return None;
            }
            if self.is_known_true(lit) {
                // Guard against overflow for very wide bitvectors
                if i >= usize::BITS as usize {
                    return None;
                }
                value |= 1usize << i;
            } else if !self.is_known_false(lit) {
                return None; // non-constant bit
            }
        }
        Some(value)
    }

    /// Check if exactly one bit is set (power of 2) in a constant bit vector.
    /// Returns the position of the set bit, or None if not a power of 2
    /// or if any bit is non-constant.
    ///
    /// Used by bitblaster mul shortcut (#8111) to detect power-of-2 multipliers
    /// and replace the multiplier circuit with simple wiring.
    pub(crate) fn try_bits_power_of_2(&self, bits: &BvBits) -> Option<usize> {
        if !self.encoding_complete() {
            return None;
        }
        let mut set_pos = None;
        for (i, &lit) in bits.iter().enumerate() {
            if !self.encoding_step() {
                return None;
            }
            if self.is_known_true(lit) {
                if set_pos.is_some() {
                    return None; // more than one bit set
                }
                set_pos = Some(i);
            } else if !self.is_known_false(lit) {
                return None; // non-constant bit
            }
        }
        set_pos
    }
}
