// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sequential counter PB-to-CNF encoding (Sinz 2005, generalized for PB).
//!
//! For **cardinality** constraints (all coefficients = 1), this is the classic
//! Sinz 2005 encoding with O(n*k) clauses and auxiliary variables.
//!
//! For **weighted** PB constraints, we generalize: each literal contributes its
//! coefficient to a running weight counter. The counter variable `r[i][w]`
//! means "the accumulated weight from the first i+1 terms is at least w".
//!
//! # References
//! - Sinz, "Towards an Optimal CNF Encoding of Boolean Cardinality Constraints", 2005

/// Encodes a normalized `sum(coeffs[i] * lits[i]) >= rhs` into CNF using
/// the sequential (weighted) counter encoding.
///
/// All coefficients must be positive and `rhs > 0`.
/// Trivial cases (always SAT/UNSAT) should be handled by the caller.
///
/// Clauses are appended to `clauses`; new variables are allocated via `next_var`.
pub(crate) fn encode_sequential_counter(
    coeffs: &[i128],
    lits: &[i32],
    rhs: i128,
    clauses: &mut Vec<Vec<i32>>,
    next_var: &mut u32,
) {
    let n = coeffs.len();
    debug_assert!(n > 0);
    debug_assert!(rhs > 0);
    debug_assert!(coeffs.iter().all(|&c| c > 0));

    // The counter tracks weight values 1..=rhs.
    // r[i][w] for i in 0..n, w in 1..=rhs means
    // "weight accumulated from first i+1 literals is >= w".
    //
    // For cardinality (all coeffs=1), rhs = k, and this reduces to Sinz 2005.
    let k = rhs as usize; // number of distinct weight levels to track

    // Allocate auxiliary variables. r[i][j] corresponds to weight level j+1.
    // Total aux vars: n * k.
    let base = *next_var;
    *next_var += (n * k) as u32;

    // Helper to get DIMACS variable for r[i][j] (0-indexed j maps to weight j+1).
    let r = |i: usize, j: usize| -> i32 { (base + (i * k + j) as u32) as i32 };

    // Base case: i = 0, the first literal.
    let c0 = coeffs[0].min(rhs) as usize;
    // If lit[0] is true, weight levels 1..=c0 are reached.
    // lit[0] -> r[0][j] for j in 0..c0  (i.e., weight levels 1..=c0)
    for j in 0..c0.min(k) {
        clauses.push(vec![-lits[0], r(0, j)]);
    }
    // If lit[0] is false, no weight levels are reached.
    // r[0][j] -> lit[0] for j in 0..c0
    for j in 0..c0.min(k) {
        clauses.push(vec![-r(0, j), lits[0]]);
    }
    // Weight levels beyond c0 are impossible from just the first literal.
    for j in c0..k {
        clauses.push(vec![-r(0, j)]);
    }

    // Inductive case: for each subsequent literal i.
    for i in 1..n {
        let ci = coeffs[i].min(rhs) as usize;

        for j in 0..k {
            let w = j + 1; // weight level being tracked

            // r[i][j] is true if:
            //   (a) r[i-1][j] is true (already had enough weight), OR
            //   (b) lit[i] is true AND r[i-1][j - ci] is true (if j >= ci), OR
            //   (c) lit[i] is true AND w <= ci (literal alone reaches this level)

            // Forward implications (sufficient conditions -> r[i][j]):

            // (a) r[i-1][j] -> r[i][j]
            clauses.push(vec![-r(i - 1, j), r(i, j)]);

            if w <= ci {
                // (c) lit[i] alone reaches weight level w: lit[i] -> r[i][j]
                clauses.push(vec![-lits[i], r(i, j)]);
            } else if ci > 0 {
                // (b) lit[i] AND r[i-1][j - ci] -> r[i][j]
                // j - ci corresponds to weight level w - ci, index = j - ci
                let prev_idx = j - ci;
                clauses.push(vec![-lits[i], -r(i - 1, prev_idx), r(i, j)]);
            }

            // Backward implication (necessary condition: r[i][j] -> some justification):
            // r[i][j] -> r[i-1][j] OR lit[i]
            clauses.push(vec![-r(i, j), r(i - 1, j), lits[i]]);

            if w > ci && ci > 0 {
                // r[i][j] -> r[i-1][j] OR r[i-1][j - ci]
                let prev_idx = j - ci;
                clauses.push(vec![-r(i, j), r(i - 1, j), r(i - 1, prev_idx)]);
            }
        }

        // Block overflow: if adding this literal would push beyond rhs,
        // that's fine since we only track up to rhs. But we need to ensure
        // that we can't assign weight > rhs. For the sequential counter,
        // we block: lit[i] AND r[i-1][k-1] is allowed (it means >= rhs, which
        // is what we want). No overflow blocking needed since we track >= rhs.
    }

    // The constraint is satisfied iff r[n-1][k-1] is true (weight >= rhs).
    clauses.push(vec![r(n - 1, k - 1)]);
}
