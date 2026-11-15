// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared, pure-Rust congruence parity/merge-polarity core for `ay-sat`.
//!
//! `ay-sat` calls [`xor_accumulate_parity`] from this crate directly, and the
//! harnesses in `proofs/` submit the SAME source bytes to `offline deductive checker check`.
//! No twin. Submitted is not proved: as measured 2026-09-23 both harnesses are
//! INCONCLUSIVE and the parity obligations are UNKNOWN to the verifier (the
//! PROOF STATUS note in `parity.rs` has the rows). The tests below check them
//! by execution.

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

    /// The slice fold equals the independent popcount-parity for EVERY slice of
    /// length `0..=16` (all 2^len patterns of each length) — an executed,
    /// BOUNDED check of the property the trust harness states over arbitrary
    /// length. 16 is more than three times the solver's `XOR_ARITY_LIMIT = 5`
    /// (`ay-sat/src/gates/xor.rs`). It says nothing about a length past 16;
    /// see [`slice_fold_unbounded_by_induction`] for what is argued beyond it.
    #[test]
    fn unbounded_slice_fold_matches_popcount_all_lengths() {
        let mut buf = [false; 16];
        for len in 0u32..=16 {
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

    /// EXECUTED CORROBORATING CHECK plus a HAND-WRITTEN induction for the
    /// UNBOUNDED statement `xor_collapse_slice(bits) == popcount(bits) % 2`.
    /// This is NOT a machine-checked proof: nothing here, and no `offline deductive checker
    /// check` run (the harness the development proof harness measured
    /// INCONCLUSIVE on 2026-09-23), establishes the statement for every length.
    ///
    /// What the test EXECUTES, with `I(p)` the invariant `fold(p) == popcount(p) % 2`:
    ///
    ///   BASE  `I([])`       : `fold([]) == false == (0 % 2 == 1)`.
    ///   STEP  one fold step  : `xor_accumulate_parity(a, b) == a ^ b`, over the
    ///                          complete step state `a, b ∈ {F,T}` (all 2×2).
    ///   SHAPE fold = step    : `fold(p·b) == xor_accumulate_parity(fold(p), b)`,
    ///                          for ONE sampled prefix `p` of each length `0..20`
    ///                          (so for extended lengths `1..=20`).
    ///
    /// What is ARGUED BY HAND, not executed: that `xor_collapse_slice` is that
    /// step folded left for EVERY length (the source is a four-line loop), and
    /// structural induction over the slice. A mutant of `xor_collapse_slice`
    /// that is wrong only at length 21 or more passes this test and the
    /// `0..=16` test above; only the hand argument excludes it.
    #[test]
    fn slice_fold_unbounded_by_induction() {
        // BASE: the empty-prefix accumulator is the even-parity witness.
        assert!(!xor_collapse_slice(&[]));
        assert_eq!(xor_collapse_slice(&[]), popcount_parity(&[]));

        // STEP: complete over the finite step state. For every accumulator parity
        // `a` and next contribution `b`, the real fold step equals GF(2) addition
        // `a ^ b`, which is exactly the popcount-parity of a prefix whose parity
        // was `a`, extended by `b`. Both facts checked for all four `(a, b)`.
        for &a in &[false, true] {
            for &b in &[false, true] {
                let advanced = xor_accumulate_parity(a, b);
                assert_eq!(advanced, a ^ b, "step is not GF(2) add at a={a} b={b}");
                assert_eq!(
                    advanced,
                    (u32::from(a) + u32::from(b)) % 2 == 1,
                    "step does not advance popcount-parity by b at a={a} b={b}"
                );
            }
        }

        // Confirm the fold is literally that step iterated: extending any prefix by
        // one bit applies exactly `xor_accumulate_parity` to the running accumulator
        // (so the induction above governs the REAL function, not a twin).
        let mut acc = false;
        let mut running = [false; 20];
        for len in 0..20usize {
            for &b in &[false, true] {
                let mut extended = running;
                extended[len] = b;
                assert_eq!(
                    xor_collapse_slice(&extended[..=len]),
                    xor_accumulate_parity(xor_collapse_slice(&running[..len]), b),
                    "fold is not step-iterated at len={len} b={b}"
                );
            }
            // walk one concrete prefix forward to vary the accumulator state.
            running[len] = len % 3 == 0;
            acc = xor_accumulate_parity(acc, running[len]);
            assert_eq!(acc, xor_collapse_slice(&running[..=len]));
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
