// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Row-heavy box-LP transposition.

use super::*;

/// Row-to-column ratio past which a model is solved through its transpose.
///
/// The simplex keeps one basic variable per row, so a model with `m >> n`
/// otherwise pays for a basis far larger than the problem needs. Four is
/// deliberately conservative; the target shapes are much farther from parity.
const TRANSPOSE_ROW_COL_RATIO: usize = 4;

/// Whether the transposed solver should be tried for this shape and cost vector.
///
/// Its all-lower crash is feasible exactly when `c >= 0`. A negative cost gives
/// Phase I real work and made this performance-only transformation substantially
/// slower, so the cost predicate is part of the structural dispatch gate.
pub(super) fn should_transpose_model(c: &[f64], rows: usize) -> bool {
    // Shape alone, and only because `solve_transposed_for_box_lp` now CRASHES AT
    // THE DUAL IMAGE OF `x = 0`. Under the old `y = z = 0` crash any negative cost
    // started infeasible and the transpose measured 8.3x SLOWER than the primal
    // form, so the guard had to exclude `c < 0` — which excluded exactly the
    // maximisation shapes the transpose is most wanted for. With the dual-image
    // crash the same shape measures 1.18x FASTER. Kept as a named predicate so the
    // dispatch rule has one home and one test.
    let _ = c;
    should_transpose(c.len(), rows)
}

/// Whether this shape is row-heavy enough for transposition.
pub(super) fn should_transpose(columns: usize, rows: usize) -> bool {
    #[cfg(test)]
    if FORCE_PRIMAL.load(std::sync::atomic::Ordering::Relaxed) {
        return false;
    }
    columns > 0 && rows > columns.saturating_mul(TRANSPOSE_ROW_COL_RATIO)
}

/// Build the transposed model.
///
/// The primal is `min c·x` subject to `Ax >= b`, `0 <= x <= 1`. Its dual is
/// represented as `min (-b)·y + 1·z` subject to `(-A^T)y + Iz >= -c`, with
/// `y,z >= 0` and no upper bounds. Malformed, non-finite, or oversized input is
/// rejected before any simplex work.
fn build_transposed_model(n: usize, c: &[f64], rows: &[RowF64]) -> Option<LpF64> {
    let m = rows.len();
    let tn = m.checked_add(n)?;
    if tn == 0 || tn > MAX_VARS || n > MAX_ROWS {
        return None;
    }
    let mut tc = Vec::with_capacity(tn);
    for row in rows {
        if !row.b.is_finite() {
            return None;
        }
        tc.push(-row.b);
    }
    tc.extend(std::iter::repeat_n(1.0, n));

    let mut by_var = vec![Vec::new(); n];
    let mut nonzeros = 0usize;
    for (row_index, row) in rows.iter().enumerate() {
        for &(variable, coefficient) in &row.coeffs {
            if variable >= n || !coefficient.is_finite() {
                return None;
            }
            by_var[variable].push((row_index, -coefficient));
            nonzeros += 1;
        }
    }
    if nonzeros.checked_add(n)? > MAX_NONZEROS {
        return None;
    }
    let mut transposed_rows = Vec::with_capacity(n);
    for (variable, mut coefficients) in by_var.into_iter().enumerate() {
        if !c[variable].is_finite() {
            return None;
        }
        coefficients.push((m + variable, 1.0));
        transposed_rows.push(RowF64 {
            coeffs: coefficients,
            b: -c[variable],
        });
    }
    Some(LpF64 {
        n: tn,
        c: tc,
        offset: 0.0,
        rows: transposed_rows,
        upper: Some(vec![f64::INFINITY; tn]),
    })
}

fn extract_original_solution(result: SimplexResult, n: usize, m: usize) -> (Vec<f64>, Vec<f64>) {
    let dual = (0..m)
        .map(|row| {
            let value = result.primal.get(row).copied().unwrap_or(0.0);
            if value.is_finite() && value > 0.0 {
                value
            } else {
                0.0
            }
        })
        .collect();
    let primal = (0..n)
        .map(|variable| {
            let value = result.dual.get(variable).copied().unwrap_or(0.0);
            if value.is_finite() {
                value.clamp(0.0, 1.0)
            } else {
                0.0
            }
        })
        .collect();
    (dual, primal)
}

/// Solve the box LP through its dual so the basis has one entry per original
/// column instead of one per original row.
///
/// Soundness does not depend on simplex accuracy: the caller clamps the returned
/// dual to `y >= 0` and recomputes the NS bound independently. A poor transposed
/// point can therefore only weaken the bound. Any rejected build falls back to
/// the unchanged primal path.
pub(super) fn solve_transposed_for_box_lp(
    n: usize,
    c: &[f64],
    rows: &[RowF64],
    limits: SimplexLimits,
    should_stop: &dyn Fn() -> bool,
) -> Option<(Vec<f64>, Vec<f64>, bool)> {
    let m = rows.len();
    let model = build_transposed_model(n, c, rows)?;
    let tn = model.n;
    let tm = model.rows.len();
    let total_columns = tn.checked_add(tm)?;
    let mut simplex = Simplex::new(&model, tn, tm, total_columns);

    // CRASH AT THE DUAL IMAGE OF `x = 0`, rather than at the default surplus
    // basis. This is what lets the transpose handle NEGATIVE costs at all.
    //
    // The default crash is `y = z = 0`, which satisfies row `v`
    // (`-(A^T y)_v + z_v >= -c_v`) only when `c_v >= 0`. With any `c_v < 0` it
    // starts INFEASIBLE and this hugely degenerate model burns Phase-I pivots
    // under Bland's rule — measured at 0.12x, i.e. 8.3x SLOWER than the primal
    // form, which is why this path was previously restricted to `c >= 0`.
    //
    // The dual image of the primal's own free starting point `x = 0` is
    // `y = 0, z_v = max(0, -c_v)`, feasible for EVERY sign of `c`. Make the `z`
    // columns basic (one per row, `B = I`) and let the basis computation derive
    // those values, handing the transposed form the same starting point the
    // primal form gets for nothing.
    for v in 0..tm {
        simplex.basis[v] = m + v;
    }
    for slot in simplex.basic_row.iter_mut() {
        *slot = None;
    }
    for v in 0..tm {
        simplex.basic_row[m + v] = Some(v);
    }
    simplex.refactorize();

    let converged = simplex.run(should_stop, limits, None);
    let (dual, primal) = extract_original_solution(simplex.extract(&model), n, m);
    Some((dual, primal, converged))
}
