// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Algebraic operation-chain growth measurements.

use super::*;

// ===========================================================================
// Cost: degree and coefficient growth across CHAINS of operations
// ===========================================================================

/// One step of an operation chain.
pub(crate) struct ChainRow {
    /// Degree of each base operand.
    pub(crate) base_degree: usize,
    /// How many operations have been applied so far (1 = the first).
    pub(crate) step: usize,
    /// `+` or `*`.
    pub(crate) op: &'static str,
    /// Degree of the accumulator's defining polynomial after this step.
    pub(crate) degree: usize,
    /// Bit length of the largest coefficient after this step.
    pub(crate) coeff_bits: u64,
    /// Denominator exponent of the isolating interval after this step.
    pub(crate) interval_k: u32,
    /// Wall clock for this step alone.
    pub(crate) elapsed_us: u128,
    /// The step declined (fail-closed). Nothing after it is attempted.
    pub(crate) declined: bool,
}

/// The `j`-th base operand at degree `d`: the real root of `x^d - prime_j` in
/// the dyadic interval `(1, 2)`.
///
/// `p(1) = 1 - k < 0` and `p(2) = 2^d - k > 0` whenever `1 < k < 2^d`, and
/// `x^d = k` has exactly one root in `(1, 2)`, so the interval isolates by
/// construction — and `from_poly_interval` verifies it anyway.
fn base_operand(d: usize, j: usize) -> Option<ODyadicAnum> {
    const PRIMES: [i64; 12] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
    let k = PRIMES[j % PRIMES.len()];
    if d < 2 || (1i64 << d.min(62)) <= k {
        return None;
    }
    let mut coeffs = vec![BigInt::zero(); d + 1];
    coeffs[0] = BigInt::from(-k);
    coeffs[d] = BigInt::one();
    let iv = OBqInterval::new(
        &OBq::from_int(BigInt::one()),
        &OBq::from_int(BigInt::from(2)),
    )?;
    ODyadicAnum::from_poly_interval(&coeffs, &iv)
}

/// Chain `steps` operations, alternating `+` and `*`, from a degree-`d` base.
///
/// Every step's operands are DISTINCT algebraic numbers (a different prime under
/// the radical), so no step collapses to a rational and the degree really does
/// multiply.
fn chain_at(d: usize, steps: usize, budget_ms: u128) -> Vec<ChainRow> {
    let mut rows = Vec::new();
    let Some(mut acc) = base_operand(d, 0) else {
        return rows;
    };
    for step in 1..=steps {
        let Some(next) = base_operand(d, step) else {
            break;
        };
        let is_add = step % 2 == 1;
        let t = std::time::Instant::now();
        let out = if is_add {
            acc.add(&next)
        } else {
            acc.mul(&next)
        };
        let elapsed_us = t.elapsed().as_micros();
        let op = if is_add { "+" } else { "*" };
        match out {
            Some(v) => {
                let coeffs = v.poly_coeffs().unwrap_or_default();
                let coeff_bits = coeffs.iter().map(BigInt::bits).max().unwrap_or(0);
                let interval_k = v.interval().map_or(0, |iv| iv.lo().k().max(iv.hi().k()));
                rows.push(ChainRow {
                    base_degree: d,
                    step,
                    op,
                    degree: v.degree(),
                    coeff_bits,
                    interval_k,
                    elapsed_us,
                    declined: false,
                });
                acc = v;
            }
            None => {
                rows.push(ChainRow {
                    base_degree: d,
                    step,
                    op,
                    degree: 0,
                    coeff_bits: 0,
                    interval_k: 0,
                    elapsed_us,
                    declined: true,
                });
                break;
            }
        }
        if elapsed_us / 1000 > budget_ms {
            break;
        }
    }
    rows
}

/// Sweep base degrees and chain depths.
///
/// The degrees are deliberately IRREGULAR — not powers of two — because a
/// previous lane's harness measured 8/16/.../256 and missed a capability cliff
/// at 335-512. Here the cliff is in the chain DEPTH, so every step of every
/// chain is reported rather than only its last.
pub(crate) fn measure_chain_growth(budget_ms: u128) -> Vec<ChainRow> {
    const DEGREES: [usize; 9] = [2, 3, 4, 5, 6, 7, 9, 11, 13];
    let mut out = Vec::new();
    for d in DEGREES {
        out.extend(chain_at(d, 6, budget_ms));
    }
    out
}
