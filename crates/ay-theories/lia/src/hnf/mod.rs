// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Hermite Normal Form (HNF) computation and cutting planes
//!
//! This module implements HNF-based cutting planes for Linear Integer Arithmetic.
//! Unlike Gomory cuts which work on the simplex tableau (and thus involve slack
//! variables), HNF cuts work on the original constraint matrix.
//!
//! ## Algorithm Overview
//!
//! From "Cutting the Mix" by Christ & Hoenicke:
//! 1. Collect tight equality constraints A'x = b' (active at current solution)
//! 2. Compute HNF H and unimodular U such that A'U = H
//! 3. Transform: H y = b' where y = U^{-1} x
//! 4. Pick a row i whose `y[i] = (H^{-1} b')[i]` is non-integer — a heuristic
//!    for where an integrality obstruction is likely to sit
//! 5. Form the multiplier row `f = e_i H^{-1}`, the coefficient row
//!    `c = f A'` and the forced value `v = f b'`, scale both to integers, and
//!    emit the GCD cut `c x <= gcd(c) * floor(v / gcd(c))`
//!
//! Step 5 keeps the cut sound WITHOUT relying on `H` being the exact Hermite
//! form: `c x = f (A' x) = f b' = v` holds for every `x` in the (real) solution
//! set by construction, and `c x` is a multiple of `gcd(c)` at every integer
//! point, so the emitted bound is valid over the integers whatever `f` is. The
//! cut only bites when `gcd(c)` does not divide `v`, i.e. when the equalities
//! have no integer solution at all.
//!
//! This avoids slack variables entirely since we work with original constraints.
//!
//! Submodules:
//! - `matrix`: Dense integer matrix for HNF computation.
//! - `cutter`: HNF-based cutting plane generation.

pub(crate) mod cutter;
pub(crate) mod matrix;

#[cfg(test)]
mod tests;

pub(crate) use cutter::HnfCutter;
pub(crate) use matrix::IntMatrix;

use ay_core::extended_gcd_bigint;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};

/// HNF computation result
pub(crate) struct HnfResult {
    /// The HNF matrix H (lower triangular with specific properties)
    pub h: IntMatrix,
}

/// Find pivot for lower triangular reduction
fn prepare_pivot(m: &mut IntMatrix, r: usize) -> bool {
    for i in r..m.row_count() {
        for j in r..m.col_count() {
            if !m.get(i, j).is_zero() {
                if i != r {
                    m.transpose_rows(i, r);
                }
                if j != r {
                    m.transpose_columns(j, r);
                }
                return true;
            }
        }
    }
    false
}

/// Pivot column using non-fractional Gaussian elimination (Bareiss algorithm)
fn pivot_column_non_fractional(m: &mut IntMatrix, r: usize, big_number: &BigInt) -> bool {
    assert!(
        !m.get(r, r).is_zero(),
        "BUG: zero pivot after prepare_pivot at row {r}"
    );

    for j in (r + 1)..m.col_count() {
        for i in (r + 1)..m.row_count() {
            let m_rr = m.get(r, r).clone();
            let m_ij = m.get(i, j).clone();
            let m_ir = m.get(i, r).clone();
            let m_rj = m.get(r, j).clone();

            let new_val = if r > 0 {
                let prev_pivot = m.get(r - 1, r - 1).clone();
                (&m_rr * &m_ij - &m_ir * &m_rj) / &prev_pivot
            } else {
                &m_rr * &m_ij - &m_ir * &m_rj
            };

            if new_val.abs() >= *big_number {
                return false; // Overflow
            }
            m.set(i, j, new_val);
        }
    }
    true
}

/// Transform matrix to lower triangular form, return rank
fn to_lower_triangle(m: &mut IntMatrix, big_number: &BigInt) -> Option<usize> {
    let mut rank = 0;
    for i in 0..m.row_count() {
        if !prepare_pivot(m, i) {
            return Some(rank);
        }
        if !pivot_column_non_fractional(m, i, big_number) {
            return None; // Overflow
        }
        rank = i + 1;
    }
    Some(rank)
}

/// Compute GCD of elements in row starting from diagonal
fn gcd_of_row(m: &IntMatrix, row: usize) -> BigInt {
    let mut g = BigInt::zero();
    for col in row..m.col_count() {
        let val = m.get(row, col);
        if !val.is_zero() {
            if g.is_zero() {
                g = val.abs();
            } else {
                g = g.gcd(val);
            }
        }
    }
    g
}

/// Compute determinant of rectangular matrix and identify basis rows
/// Returns (determinant, basis_rows) or None on overflow
pub(crate) fn determinant_of_rectangular_matrix(
    m: &IntMatrix,
    big_number: &BigInt,
) -> Option<(BigInt, Vec<usize>)> {
    let mut m_copy = m.clone();
    let rank = to_lower_triangle(&mut m_copy, big_number)?;

    if rank == 0 {
        return Some((BigInt::one(), vec![]));
    }

    let mut basis_rows = Vec::with_capacity(rank);
    for i in 0..rank {
        basis_rows.push(m_copy.adjust_row(i));
    }

    let det = gcd_of_row(&m_copy, rank - 1);
    Some((det, basis_rows))
}

/// Divide `r` by `wii_final`, asserting exact divisibility in debug builds.
///
/// Returns `None` in release builds if divisibility is violated, allowing callers
/// to gracefully abort HNF cut generation without compromising soundness.
fn divide_r_by_diagonal(r: &BigInt, wii_final: &BigInt, i: usize) -> Option<BigInt> {
    debug_assert!(
        !wii_final.is_zero(),
        "BUG: HNF diagonal must be non-zero at column {i}"
    );

    let remainder = r % wii_final;
    debug_assert!(
        remainder.is_zero(),
        "HNF divisibility invariant violated at column {i}: r={r}, wii={wii_final}, r%wii={remainder}"
    );
    if !remainder.is_zero() {
        return None;
    }

    Some(r / wii_final)
}

/// Compute Hermite Normal Form of matrix A
///
/// Returns H such that AU = H for some unimodular U.
/// H is lower triangular with:
/// - h[i][i] > 0 for all i
/// - h[i][j] <= 0 and |h[i][j]| < h[i][i] for j < i
///
/// Algorithm follows Z3's calculate_by_modulo() (hnf.h:575-613).
/// Key fixes from #1062:
/// 1. Don't break early when r becomes 1 (process all rows)
/// 2. Handle zero diagonal specially (set to R, use u=1)
/// 3. Verify divisibility when updating R
#[allow(clippy::many_single_char_names)]
pub(crate) fn compute_hnf(a: &IntMatrix, d: &BigInt) -> Option<HnfResult> {
    // PERFORMANCE/SOUNDNESS GUARD (#437): HNF uses extended GCD over BigInt, which can
    // become O(n^2) on huge magnitudes and hang solver hot paths. If coefficients
    // exceed this threshold, abort HNF so callers can fall back to other strategies.
    const MAX_COEFF_BITS: u64 = 256; // ~77 decimal digits

    let m = a.row_count();
    let n = a.col_count();

    if m == 0 || n == 0 || d.is_zero() {
        return Some(HnfResult { h: a.clone() });
    }

    let mut w = a.clone();
    let mut r = d.clone();
    if r.bits() > MAX_COEFF_BITS {
        return None;
    }

    // Process each row
    // NOTE (#1062): Unlike a previous version, we do NOT break early when r becomes 1.
    // Z3's calculate_by_modulo() processes all m rows. Early breaking can leave
    // the matrix in a partially-reduced state that is NOT in proper HNF form.
    // However, if r becomes 0, we must stop to avoid division by zero in mod operations.
    for i in 0..m {
        if r.is_zero() {
            // R became zero - matrix is already fully reduced for this determinant
            break;
        }
        if r.bits() > MAX_COEFF_BITS {
            return None;
        }
        let half_r = &r / 2;
        // Process columns j > i to eliminate entries
        for j in (i + 1)..n {
            let wii = w.get(i, i).clone();
            let wij = w.get(i, j).clone();

            if wij.is_zero() {
                continue;
            }
            if wii.bits() > MAX_COEFF_BITS || wij.bits() > MAX_COEFF_BITS {
                return None;
            }

            let (gcd, u, v) = extended_gcd_bigint(&wii, &wij);
            if gcd.is_zero() {
                continue;
            }
            if u.bits() > MAX_COEFF_BITS || v.bits() > MAX_COEFF_BITS {
                return None;
            }

            let wii_over_gcd = &wii / &gcd;
            let wij_over_gcd = &wij / &gcd;
            if wii_over_gcd.bits() > MAX_COEFF_BITS || wij_over_gcd.bits() > MAX_COEFF_BITS {
                return None;
            }

            // Column operations to eliminate w[i][j]
            // New col i = u * col_i + v * col_j
            // New col j = -wij/gcd * col_i + wii/gcd * col_j
            for k in i..m {
                let old_ki = w.get(k, i).clone();
                let old_kj = w.get(k, j).clone();
                if old_ki.bits() > MAX_COEFF_BITS || old_kj.bits() > MAX_COEFF_BITS {
                    return None;
                }

                let new_ki = mod_balanced(&(&u * &old_ki + &v * &old_kj), &r, &half_r);
                let new_kj = mod_balanced(
                    &(-&wij_over_gcd * &old_ki + &wii_over_gcd * &old_kj),
                    &r,
                    &half_r,
                );
                if new_ki.bits() > MAX_COEFF_BITS || new_kj.bits() > MAX_COEFF_BITS {
                    return None;
                }

                w.set(k, i, new_ki);
                w.set(k, j, new_kj);
            }
        }

        // Fix diagonal element (fix_row_under_diagonal_W_modulo in Z3)
        // Z3 reference: hnf.h:534-565
        let wii = w.get(i, i).clone();
        if wii.bits() > MAX_COEFF_BITS || r.bits() > MAX_COEFF_BITS {
            return None;
        }

        // Z3's special case (#1062): when W[i][i] == 0, set it to R and use u = 1
        let (gcd, u) = if wii.is_zero() {
            w.set(i, i, r.clone());
            (r.clone(), BigInt::one())
        } else {
            let (g, u, _v) = extended_gcd_bigint(&wii, &r);
            (g, u)
        };
        if u.bits() > MAX_COEFF_BITS {
            return None;
        }

        // Compute new diagonal: (wii * u) mod r, but if zero use gcd
        let mut new_wii = mod_r(&(&wii * &u), &r);
        if new_wii.is_zero() {
            new_wii.clone_from(&gcd);
        }
        if new_wii.bits() > MAX_COEFF_BITS {
            return None;
        }

        // Scale column i by u
        if !u.is_one() {
            for k in i..m {
                let old = w.get(k, i).clone();
                if old.bits() > MAX_COEFF_BITS {
                    return None;
                }
                let new_val = mod_balanced(&(&old * &u), &r, &half_r);
                if new_val.bits() > MAX_COEFF_BITS {
                    return None;
                }
                w.set(k, i, new_val);
            }
            w.set(i, i, new_wii.clone());
        }

        // Fix elements below diagonal in columns < i
        for j in 0..i {
            let wij = w.get(i, j).clone();
            if wij.is_zero() || (!wij.is_positive() && wij.abs() < new_wii) {
                continue;
            }
            if wij.bits() > MAX_COEFF_BITS {
                return None;
            }

            // q = ceil(wij / wii)
            let q = if wij.is_positive() {
                (&wij + &new_wii - 1) / &new_wii
            } else {
                &wij / &new_wii
            };
            if q.bits() > MAX_COEFF_BITS {
                return None;
            }

            // col_j -= q * col_i
            for k in i..m {
                let old_kj = w.get(k, j).clone();
                let old_ki = w.get(k, i).clone();
                if old_kj.bits() > MAX_COEFF_BITS || old_ki.bits() > MAX_COEFF_BITS {
                    return None;
                }
                let new_val = &old_kj - &q * &old_ki;
                if new_val.bits() > MAX_COEFF_BITS {
                    return None;
                }
                w.set(k, j, new_val);
            }
        }

        // Update R for next iteration
        // Z3 asserts this division is exact (hnf.h:579-580)
        let wii_final = w.get(i, i).clone();
        if !wii_final.is_zero() {
            // Divisibility check (#1062): if r % wii_final != 0, the modulus invariant is broken.
            // In release builds we return None so HNF can be skipped without unsoundness.
            r = divide_r_by_diagonal(&r, &wii_final, i)?;
        }
    }

    Some(HnfResult { h: w })
}

/// Modulo with balanced result in (-r/2, r/2]
fn mod_balanced(a: &BigInt, r: &BigInt, half_r: &BigInt) -> BigInt {
    let t = mod_r(a, r);
    if t > *half_r {
        t - r
    } else if t < -half_r {
        t + r
    } else {
        t
    }
}

/// Positive modulo: result in [0, r)
fn mod_r(a: &BigInt, r: &BigInt) -> BigInt {
    let t = a % r;
    if t.is_negative() {
        t + r
    } else {
        t
    }
}
