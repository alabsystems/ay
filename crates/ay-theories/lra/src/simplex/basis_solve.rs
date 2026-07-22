// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact rational solve of a small square linear system `M x = r` via
//! **fraction-free Bareiss** (integer-preserving Gaussian elimination).
//!
//! This is the exact-certification kernel of the float-pivot layer
//! (`AY_LRA_FLOAT_LAYER`). The f64 shadow simplex chooses a candidate basis
//! `B*`; this module solves the ORIGINAL small-coefficient slack-definition
//! system restricted to `B*` in **one** dense elimination — cost `O(m^3)` exact
//! ops decoupled from the pivot count `P`, unlike replaying `P` exact
//! reduced-tableau pivots with compounding denominators.
//!
//! ## Why Bareiss (not plain rational Gauss)
//!
//! Plain Gaussian elimination over `BigRational` re-normalizes a fraction after
//! every operation; the denominators COMPOUND, so intermediate bignums grow
//! super-linearly in `m`. Bareiss keeps every intermediate entry an EXACT
//! INTEGER: each entry after step `k` is a `(k+1)×(k+1)` minor determinant of
//! the (row-scaled) input, whose size is Hadamard-bounded by a SINGLE
//! determinant — no denominator blow-up, no gcd normalization in the hot loop.
//! The one exact integer division per update `(a·pivot − b·c)/prev` is provably
//! remainder-free (Bareiss/Sylvester identity). We clear each row's denominators
//! up front (row scaling preserves the solution) so the elimination runs over
//! `BigInt`, and only the final back-substitution produces `BigRational`.
//!
//! ## Soundness
//!
//! Correctness of the *verdict* never depends on this solver: the caller
//! independently re-checks — for SAT, the produced assignment against every
//! tableau row equation and bound; for UNSAT, that the reduced conflict row is a
//! genuine tableau identity — in exact arithmetic before emitting a verdict. A
//! wrong result here can therefore only cause a fallback to the exact simplex,
//! never an unsound answer. As a belt-and-braces check we still verify every
//! Bareiss division is exact and return `None` (→ fallback) if it is ever not.
//!
//! Reference: Bareiss, "Sylvester's Identity and Multistep Integer-Preserving
//! Gaussian Elimination", Math. Comp. 22 (1968).

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Zero};

/// Solve the dense square system `mat * x = rhs` exactly via fraction-free
/// Bareiss elimination.
///
/// `mat` is `n` rows each of length `n` (row-major). `rhs` has length `n`.
/// Both are consumed. Returns `Some(x)` with the exact rational solution, or
/// `None` if the matrix is singular (no unique solution) — or, defensively, if
/// a Bareiss division is ever inexact (which the identity guarantees cannot
/// happen for a well-formed integer system, but we fail closed regardless).
pub(crate) fn solve_dense(
    mat: Vec<Vec<BigRational>>,
    rhs: Vec<BigRational>,
) -> Option<Vec<BigRational>> {
    let n = rhs.len();
    if mat.len() != n || mat.iter().any(|row| row.len() != n) {
        return None;
    }
    if n == 0 {
        return Some(Vec::new());
    }

    // --- Build the integer augmented matrix [A | b]. ---
    // Scale each row by the LCM of its denominators (rational entries only);
    // scaling an equation by a nonzero constant leaves the solution unchanged.
    // Column `n` holds the RHS.
    let mut a: Vec<Vec<BigInt>> = Vec::with_capacity(n);
    for i in 0..n {
        let mut denom_lcm = BigInt::one();
        for entry in &mat[i] {
            denom_lcm = denom_lcm.lcm(entry.denom());
        }
        denom_lcm = denom_lcm.lcm(rhs[i].denom());
        let mut row = Vec::with_capacity(n + 1);
        for entry in &mat[i] {
            // mat[i][j] * denom_lcm is exactly integral: numer * (lcm / denom).
            let scaled = entry.numer() * (&denom_lcm / entry.denom());
            row.push(scaled);
        }
        let rhs_scaled = rhs[i].numer() * (&denom_lcm / rhs[i].denom());
        row.push(rhs_scaled);
        a.push(row);
    }

    // --- Fraction-free forward elimination (Bareiss). ---
    let mut prev = BigInt::one();
    for k in 0..n {
        // Pivot: first row >= k with a nonzero entry in column k. Any nonzero
        // pivot keeps the Bareiss division exact; no magnitude search needed
        // (entries stay integer-bounded regardless of choice).
        let mut pivot = None;
        for (i, row) in a.iter().enumerate().skip(k) {
            if !row[k].is_zero() {
                pivot = Some(i);
                break;
            }
        }
        let pr = pivot?; // no pivot in column k → singular
        if pr != k {
            a.swap(pr, k);
        }
        let pivot_val = a[k][k].clone();
        let pivot_tail = a[k][(k + 1)..=n].to_vec();
        for row in a.iter_mut().skip(k + 1) {
            // Row i, columns k+1..=n: a[i][j] = (a[i][j]*pivot − a[i][k]*a[k][j]) / prev.
            let a_ik = row[k].clone();
            for (cell, pivot_cell) in row[(k + 1)..=n].iter_mut().zip(&pivot_tail) {
                let num = &*cell * &pivot_val - &a_ik * pivot_cell;
                let (q, r) = num.div_rem(&prev);
                if !r.is_zero() {
                    return None; // Bareiss invariant broken → fail closed.
                }
                *cell = q;
            }
            row[k] = BigInt::zero();
        }
        prev = pivot_val;
    }

    // --- Back-substitution over the rationals. ---
    // Row k is now: a[k][k]·x_k + Σ_{j>k} a[k][j]·x_j = a[k][n].
    let mut x: Vec<BigRational> = vec![BigRational::zero(); n];
    for k in (0..n).rev() {
        if a[k][k].is_zero() {
            return None; // singular
        }
        let mut acc = BigRational::from(a[k][n].clone());
        for j in (k + 1)..n {
            if !a[k][j].is_zero() && !x[j].is_zero() {
                acc -= &(BigRational::from(a[k][j].clone()) * &x[j]);
            }
        }
        x[k] = &acc / &BigRational::from(a[k][k].clone());
    }
    Some(x)
}

#[allow(dead_code)]
pub(crate) fn is_zero_row(row: &[BigRational]) -> bool {
    row.iter().all(|v| v.is_zero())
}

/// Test helper: exact residual `mat*x - rhs` is the zero vector.
#[cfg(test)]
pub(crate) fn residual_is_zero(
    mat: &[Vec<BigRational>],
    x: &[BigRational],
    rhs: &[BigRational],
) -> bool {
    for (row, r) in mat.iter().zip(rhs.iter()) {
        let mut acc = BigRational::zero();
        for (a, xi) in row.iter().zip(x.iter()) {
            acc += a * xi;
        }
        if &acc != r {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    fn r(n: i64, d: i64) -> BigRational {
        BigRational::new(BigInt::from(n), BigInt::from(d))
    }
    fn ri(n: i64) -> BigRational {
        BigRational::from(BigInt::from(n))
    }

    #[test]
    fn test_identity() {
        let mat = vec![vec![ri(1), ri(0)], vec![ri(0), ri(1)]];
        let rhs = vec![ri(3), ri(5)];
        let x = solve_dense(mat, rhs).expect("nonsingular");
        assert_eq!(x, vec![ri(3), ri(5)]);
    }

    #[test]
    fn test_2x2() {
        // 2x + y = 5 ; x - y = 1  => x=2, y=1
        let mat = vec![vec![ri(2), ri(1)], vec![ri(1), ri(-1)]];
        let rhs = vec![ri(5), ri(1)];
        let x = solve_dense(mat, rhs).expect("nonsingular");
        assert_eq!(x, vec![ri(2), ri(1)]);
    }

    #[test]
    fn test_fractional_solution() {
        // x + y = 1 ; x - y = 0 => x = y = 1/2
        let mat = vec![vec![ri(1), ri(1)], vec![ri(1), ri(-1)]];
        let rhs = vec![ri(1), ri(0)];
        let x = solve_dense(mat, rhs).expect("nonsingular");
        assert_eq!(x, vec![r(1, 2), r(1, 2)]);
    }

    #[test]
    fn test_singular() {
        // Two identical rows => singular.
        let mat = vec![vec![ri(1), ri(2)], vec![ri(2), ri(4)]];
        let rhs = vec![ri(3), ri(6)];
        assert!(solve_dense(mat, rhs).is_none());
    }

    #[test]
    fn test_fractional_input_row_scaling() {
        // Rational coefficients exercise the per-row denominator clearing before
        // integer Bareiss. (1/2)x + (1/3)y = 1 ; x − y = 0  ⇒ x = y = 6/5.
        let mat = vec![vec![r(1, 2), r(1, 3)], vec![ri(1), ri(-1)]];
        let rhs = vec![ri(1), ri(0)];
        let x = solve_dense(mat, rhs).expect("nonsingular");
        assert_eq!(x, vec![r(6, 5), r(6, 5)]);
    }

    #[test]
    fn test_3x3_bareiss_exact() {
        // A 3x3 with a nontrivial determinant; check against a hand solution.
        // 2x + y − z = 8 ; −3x − y + 2z = −11 ; −2x + y + 2z = −3
        // Known solution: x = 2, y = 3, z = −1.
        let mat = vec![
            vec![ri(2), ri(1), ri(-1)],
            vec![ri(-3), ri(-1), ri(2)],
            vec![ri(-2), ri(1), ri(2)],
        ];
        let rhs = vec![ri(8), ri(-11), ri(-3)];
        let x = solve_dense(mat.clone(), rhs.clone()).expect("nonsingular");
        assert_eq!(x, vec![ri(2), ri(3), ri(-1)]);
        assert!(residual_is_zero(&mat, &x, &rhs));
    }

    #[test]
    fn test_needs_pivot_swap() {
        // Zero in the (0,0) position forces a row swap.
        let mat = vec![vec![ri(0), ri(1)], vec![ri(1), ri(0)]];
        let rhs = vec![ri(2), ri(3)];
        let x = solve_dense(mat, rhs).expect("nonsingular");
        assert_eq!(x, vec![ri(3), ri(2)]);
    }

    #[test]
    fn test_empty() {
        assert_eq!(solve_dense(vec![], vec![]), Some(vec![]));
    }

    #[test]
    fn test_malformed_shapes_fail_closed() {
        assert!(solve_dense(vec![vec![ri(1)]], vec![ri(1), ri(2)]).is_none());
        assert!(solve_dense(vec![vec![ri(1)], vec![ri(0)]], vec![ri(1), ri(2)]).is_none());
        assert!(solve_dense(
            vec![vec![ri(1), ri(0), ri(0)], vec![ri(0), ri(1)]],
            vec![ri(1), ri(2)],
        )
        .is_none());
    }

    // Property test: random integer matrices; verify exact residual is zero
    // whenever a solution is returned, and cross-check against a fresh residual.
    #[test]
    fn test_random_residual_zero() {
        // Deterministic LCG — no external rng dependency.
        let mut state: u64 = 0x1234_5678_9abc_def0;
        let mut next = || {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            ((state >> 33) as i64) % 11 - 5 // in [-5, 5]
        };
        let mut solved = 0;
        for _ in 0..400 {
            let n = 1 + (next().unsigned_abs() as usize % 5); // 1..=5
            let mut mat = Vec::with_capacity(n);
            for _ in 0..n {
                let mut row = Vec::with_capacity(n);
                for _ in 0..n {
                    row.push(ri(next()));
                }
                mat.push(row);
            }
            let rhs: Vec<BigRational> = (0..n).map(|_| ri(next())).collect();
            if let Some(x) = solve_dense(mat.clone(), rhs.clone()) {
                assert!(
                    residual_is_zero(&mat, &x, &rhs),
                    "residual nonzero for solved system: mat={mat:?} rhs={rhs:?} x={x:?}"
                );
                solved += 1;
            }
        }
        // Most random systems are nonsingular; make sure we exercised the path.
        assert!(solved > 200, "expected many solvable systems, got {solved}");
    }
}
