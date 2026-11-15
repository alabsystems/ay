// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Remove common, known-zero high input bits before unsigned division.

use super::*;

impl BvSolver<'_> {
    pub(super) fn try_zero_padded_division(
        &mut self,
        a: &BvBits,
        b: &BvBits,
    ) -> Option<(BvBits, BvBits)> {
        let width = a.len();
        let mut live = width;
        while live > 1 {
            if !self.encoding_step() {
                return None;
            }
            if !self.is_known_false(a[live - 1]) || !self.is_known_false(b[live - 1]) {
                break;
            }
            live -= 1;
        }
        if live == width {
            return None;
        }

        let small_a = self.counted_copy_bits(&a[..live])?;
        let small_b = self.counted_copy_bits(&b[..live])?;
        // This recursive call strictly decreases the input width. Keep one
        // bit even for all-zero inputs, preserving the ordinary zero case.
        let (small_q, small_r) = self.bitblast_udiv_urem(&small_a, &small_b);
        if !self.encoding_complete() {
            return None;
        }
        // For a nonzero divisor, q and r fit in `live` bits. SMT-LIB division
        // by zero instead returns ALL ONES at the ORIGINAL width; simply
        // zero-extending the smaller quotient would be unsound. Remainder by
        // zero remains a, so its high bits are zero in both cases.
        let zero_divisor = self.is_zero(&small_b);
        let zero = self.fresh_false();
        if !self.encoding_complete() {
            return None;
        }
        let mut quotient = self.counted_bits(width)?;
        let mut remainder = self.counted_bits(width)?;
        for (&q, &r) in small_q.iter().zip(&small_r) {
            if !self.encoding_step() {
                return None;
            }
            quotient.push(q);
            if !self.encoding_step() {
                return None;
            }
            remainder.push(r);
        }
        for _ in live..width {
            if !self.encoding_step() {
                return None;
            }
            quotient.push(zero_divisor);
            if !self.encoding_step() {
                return None;
            }
            remainder.push(zero);
        }
        Some((quotient, remainder))
    }
}
