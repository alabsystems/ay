// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! GF(p) arithmetic for the one-hot linear-system probe: per-scope
//! linear-equation fitting and dense Gaussian elimination. Pure functions on
//! small `u8` matrices — no solver state, no dependencies.

use std::time::Instant;

/// `base^exp` with overflow checking, bailing above `cap`.
pub(super) fn checked_pow(base: usize, exp: usize, cap: usize) -> Option<usize> {
    let mut acc = 1usize;
    for _ in 0..exp {
        acc = acc.checked_mul(base)?;
        if acc > cap {
            return None;
        }
    }
    Some(acc)
}

/// Multiplicative inverse of `a` mod prime `d` (tiny linear scan; d <= 32).
fn inverse(a: u8, d: u8) -> Option<u8> {
    (1..d).find(|&x| (u16::from(a) * u16::from(x)) % u16::from(d) == 1)
}

/// Fit one normalized linear equation `x0 + a1*x1 + ... + a_{r-1}*x_{r-1}
/// ≡ c (mod d)` to a scope's ALLOWED tuple set (the complement of
/// `forbidden`, which the caller has verified holds exactly `d^r - d^(r-1)`
/// distinct tuples, i.e. `d^(r-1)` allowed tuples).
///
/// Normalizing `a0 = 1` is complete for all-nonzero-coefficient equations:
/// scaling by `a0^{-1}` preserves the solution set. The verification is
/// EXACT: every allowed tuple must satisfy the candidate, and because the
/// candidate's solution set also has exactly `d^(r-1)` elements, subset plus
/// equal cardinality forces set equality — every forbidden tuple therefore
/// violates the fitted equation. Returns `(coefficients, c)` with
/// `coefficients.len() == r`, or `None` when no linear equation fits.
pub(super) fn fit_scope(d: usize, r: usize, forbidden: &[bool]) -> Option<(Vec<u8>, u8)> {
    debug_assert!(d >= 2 && r >= 2);
    debug_assert_eq!(forbidden.len(), d.pow(r as u32));
    let mut coefs = vec![1u8; r];
    loop {
        if let Some(c) = fit_candidate(d, r, &coefs, forbidden) {
            return Some((coefs, c));
        }
        // Odometer over coefficient positions 1..r, each in 1..d.
        let mut pos = 1;
        loop {
            if pos == r {
                return None; // all candidates exhausted
            }
            if usize::from(coefs[pos]) < d - 1 {
                coefs[pos] += 1;
                break;
            }
            coefs[pos] = 1;
            pos += 1;
        }
    }
}

/// Residue `c` such that every allowed tuple satisfies `Σ coefs[i]*v_i ≡ c`,
/// or `None` if the residues disagree.
fn fit_candidate(d: usize, r: usize, coefs: &[u8], forbidden: &[bool]) -> Option<u8> {
    let mut c: Option<u8> = None;
    for (code, &is_forbidden) in forbidden.iter().enumerate() {
        if is_forbidden {
            continue;
        }
        let mut sum = 0usize;
        let mut rest = code;
        for &a in coefs.iter().take(r) {
            sum += usize::from(a) * (rest % d);
            rest /= d;
        }
        let residue = (sum % d) as u8;
        match c {
            None => c = Some(residue),
            Some(prev) if prev != residue => return None,
            Some(_) => {}
        }
    }
    c
}

/// Solve the fitted system by dense Gaussian elimination over GF(d)
/// (d prime). `eqs` holds `(group_ids, coefficients, c)` per equation.
/// Underdetermined systems are fine: free unknowns take value 0.
/// Returns `None` on inconsistency (the caller must NOT conclude UNSAT —
/// detection could have mis-fit) or deadline exhaustion.
pub(super) fn solve_linear_system(
    d: usize,
    n: usize,
    eqs: &[(Vec<u32>, Vec<u8>, u8)],
    deadline: Instant,
) -> Option<Vec<u8>> {
    let dp = d as u8;
    let m = eqs.len();
    let w = n + 1;
    let mut mat = vec![0u8; m.checked_mul(w)?];
    for (ri, (gs, coefs, c)) in eqs.iter().enumerate() {
        let row = &mut mat[ri * w..(ri + 1) * w];
        for (&g, &a) in gs.iter().zip(coefs.iter()) {
            let gi = g as usize;
            if gi >= n {
                return None;
            }
            row[gi] = a % dp;
        }
        row[n] = c % dp;
    }

    let mut where_col = vec![usize::MAX; n];
    let mut pivot_row = 0usize;
    for col in 0..n {
        if pivot_row >= m {
            break;
        }
        // Per-pivot deadline check: worst-case a pivot column costs O(m*n)
        // u8 operations, which bounds the check granularity at ~10ms even at
        // the structural caps.
        if Instant::now() >= deadline {
            return None;
        }
        let Some(pr) = (pivot_row..m).find(|&ri| mat[ri * w + col] != 0) else {
            continue;
        };
        mat.swap_ranges_rows(pivot_row, pr, w);
        let inv = inverse(mat[pivot_row * w + col], dp)?;
        for x in &mut mat[pivot_row * w..(pivot_row + 1) * w] {
            *x = ((u16::from(*x) * u16::from(inv)) % u16::from(dp)) as u8;
        }
        for ri in 0..m {
            let factor = mat[ri * w + col];
            if ri == pivot_row || factor == 0 {
                continue;
            }
            for k in 0..w {
                let sub = (u16::from(factor) * u16::from(mat[pivot_row * w + k])) % u16::from(dp);
                let cur = u16::from(mat[ri * w + k]);
                mat[ri * w + k] = ((cur + u16::from(dp) - sub) % u16::from(dp)) as u8;
            }
        }
        where_col[col] = pivot_row;
        pivot_row += 1;
    }

    // Unpivoted rows are zero in every coefficient column (full RREF); a
    // nonzero right-hand side there means the fitted system is inconsistent.
    for ri in pivot_row..m {
        if mat[ri * w + n] != 0 {
            return None;
        }
    }

    Some(
        (0..n)
            .map(|col| {
                if where_col[col] == usize::MAX {
                    0 // free unknown
                } else {
                    mat[where_col[col] * w + n]
                }
            })
            .collect(),
    )
}

/// Row-swap helper on a flat row-major matrix.
trait SwapRows {
    fn swap_ranges_rows(&mut self, a: usize, b: usize, w: usize);
}

impl SwapRows for Vec<u8> {
    fn swap_ranges_rows(&mut self, a: usize, b: usize, w: usize) {
        if a == b {
            return;
        }
        let (lo, hi) = (a.min(b), a.max(b));
        let (head, tail) = self.split_at_mut(hi * w);
        head[lo * w..lo * w + w].swap_with_slice(&mut tail[..w]);
    }
}
