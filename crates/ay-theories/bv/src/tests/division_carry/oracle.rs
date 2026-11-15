// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

/// Frozen pre-fusion restoring loop from f22669734 division.rs. Uses the
/// independent comparison plus old carry-discarding subtraction, never the
/// fused helper. Keep this algorithm separate from the production divider.
pub(super) fn divide(solver: &mut BvSolver<'_>, a: &BvBits, b: &BvBits) -> (BvBits, BvBits) {
    assert_eq!(a.len(), b.len());
    let n = a.len();
    if n == 0 {
        return (Vec::new(), Vec::new());
    }
    let mut rem = solver.const_bits(0, n);
    let mut q_msb_first = Vec::with_capacity(n);
    for i in (0..n).rev() {
        let mut shifted = Vec::with_capacity(n);
        shifted.push(a[i]);
        shifted.extend_from_slice(&rem[..n - 1]);
        rem = shifted;
        let rem_lt_b = solver.bitblast_ult(&rem, b);
        let rem_ge_b = -rem_lt_b;
        let rem_minus_b = solver.bitblast_sub(&rem, b);
        rem = solver.bitwise_mux(&rem_minus_b, &rem, rem_ge_b);
        q_msb_first.push(rem_ge_b);
    }
    q_msb_first.reverse();
    (q_msb_first, rem)
}
