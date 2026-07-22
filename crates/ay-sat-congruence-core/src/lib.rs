// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared, pure-Rust congruence parity/merge-polarity core for `ay-sat`.
//!
//! `ay-sat` depends on this crate and the solver runs [`xor_collapse_parity`]
//! and [`xor_accumulate_parity`] directly; the development proof toolchain
//! verifies the SAME source bytes (see `proofs/`). No twin.

#![forbid(unsafe_code)]
#![no_std]

mod parity;

pub use parity::{xor_accumulate_parity, xor_collapse_parity, xor_collapse_slice};

#[cfg(test)]
mod tests {
    use super::*;

    /// Independent (non-XOR) ground truth: count set contributions, reduce mod 2.
    fn popcount_parity(bits: &[bool]) -> bool {
        let mut n: u32 = 0;
        for &b in bits {
            if b {
                n += 1;
            }
        }
        n % 2 == 1
    }

    /// The REAL `xor_collapse_parity` equals the independent popcount-parity on
    /// all 2^6 contribution patterns — the exact soundness obligation, executed.
    #[test]
    fn real_collapse_parity_matches_popcount_all_patterns() {
        for mask in 0u8..64 {
            let neg = mask & 1 != 0;
            let c0 = mask & 2 != 0;
            let c1 = mask & 4 != 0;
            let c2 = mask & 8 != 0;
            let c3 = mask & 16 != 0;
            let c4 = mask & 32 != 0;
            assert_eq!(
                xor_collapse_parity(neg, c0, c1, c2, c3, c4),
                popcount_parity(&[neg, c0, c1, c2, c3, c4]),
                "mismatch at mask={mask}"
            );
        }
    }

    /// The UNBOUNDED fold equals the independent popcount-parity for slices of
    /// many lengths (0..=12) and patterns — executing the same inductive
    /// obligation the trust proof harness states over ARBITRARY length.
    #[test]
    fn unbounded_slice_fold_matches_popcount_all_lengths() {
        let mut buf = [false; 12];
        for len in 0u32..=12 {
            for mask in 0u32..(1u32 << len) {
                for (i, slot) in buf[..len as usize].iter_mut().enumerate() {
                    *slot = mask & (1 << i) != 0;
                }
                let bits = &buf[..len as usize];
                assert_eq!(
                    xor_collapse_slice(bits),
                    popcount_parity(bits),
                    "mismatch at len={len} mask={mask}"
                );
            }
        }
    }

    /// The accumulation primitive is the GF(2) add step (a XOR b).
    #[test]
    fn accumulate_is_xor() {
        for &a in &[false, true] {
            for &b in &[false, true] {
                assert_eq!(xor_accumulate_parity(a, b), a ^ b);
            }
        }
    }

    /// Order-independence: the union-find applies eliminations in arbitrary
    /// order, so the folded parity must be permutation-invariant.
    #[test]
    fn collapse_parity_order_independent() {
        for mask in 0u8..64 {
            let neg = mask & 1 != 0;
            let c0 = mask & 2 != 0;
            let c1 = mask & 4 != 0;
            let c2 = mask & 8 != 0;
            let c3 = mask & 16 != 0;
            let c4 = mask & 32 != 0;
            let forward = xor_collapse_parity(neg, c0, c1, c2, c3, c4);
            let reverse = xor_collapse_parity(neg, c4, c3, c2, c1, c0);
            let interleaved = xor_collapse_parity(neg, c2, c0, c4, c1, c3);
            assert_eq!(forward, reverse);
            assert_eq!(forward, interleaved);
        }
    }
}
