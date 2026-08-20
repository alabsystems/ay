// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Row-heavy box-LP transposition.

use super::*;

/// Row-to-column ratio past which a model is solved through its transpose,
/// expressed as the fraction `NUM/DEN` (fires when `rows/cols > 5/4 = 1.25`).
///
/// The simplex keeps one basic variable per row, so a model with `m > n`
/// otherwise pays for a basis larger than the problem needs.
///
/// MEASURED on real production f64-tier LPs (2026-08-17 replay harness
/// `replay_crossover`, per-model paired arms, iteration-capped, bounds
/// verified equal; models dumped from `ay pb solve` runs on the PB24/25
/// OPT-LIN corpus after the per-row dual-image crash fix below):
///
/// ```text
///   ratio  family                       transpose vs primal (median walls)
///   1.00   liu/domset base (6 models)   0.60-0.72x  — primal wins
///   1.42   count.b                      2.7-3.2x    — transpose wins
///   1.49   count.b (+cuts)              4.9x
///   2.26   domset cut-augmented         4.9x        (7.6s -> 1.5s)
///   2.3-2.8 fir04_area_delay (+cuts)    2.4-4.2x
///   3.07   single-obj-f13               4.7x        (1067ms -> 229ms; the
///          primal blows the 500ms f64-tier budget, the transpose converges)
///   5.3-6.1 edgecross14-019             LOSS on a quiet box (0.38-0.58x wall;
///           transpose does 2.8-3.5x MORE iterations, deterministic) — kept in
///           gate because production caps both arms at 500ms and the ~9 firings
///           x ~35ms are end-to-end immaterial (verdict-identical A/B)
/// ```
///
/// The measured crossover sits between 1.0 and 1.42; 5/4 splits it with
/// margin on both sides. The old integer threshold of 4 was chosen on
/// synthetic covers and missed every measured real winner (they live at
/// 1.4-3.1), while its one production firing (edgecross) is a budget-capped
/// LOSS (audited: 0.38-0.58x on a quiet machine — the earlier "parity, median
/// 0.93" reading did not reproduce).
const TRANSPOSE_RATIO_NUM: usize = 5;
/// See [`TRANSPOSE_RATIO_NUM`].
const TRANSPOSE_RATIO_DEN: usize = 4;

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
    columns > 0
        && rows.saturating_mul(TRANSPOSE_RATIO_DEN) > columns.saturating_mul(TRANSPOSE_RATIO_NUM)
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
    crash_at_dual_image_of_x0(&mut simplex, &model, m);

    let converged = simplex.run(should_stop, limits, None);
    let (dual, primal) = extract_original_solution(simplex.extract(&model), n, m);
    Some((dual, primal, converged))
}

/// CRASH AT THE DUAL IMAGE OF `x = 0`, rather than at the default surplus
/// basis, so Phase I starts feasible for EVERY sign of `c`.
///
/// Row `v` of the transposed model is `-(A^T y)_v + z_v - s_v = -c_v` with
/// `z_v, s_v >= 0` (`s_v` is the surplus the tableau appends). At the dual
/// image of the primal's own free starting point `x = 0`:
///
/// ```text
///   y = 0,  z_v = max(0, -c_v),  s_v = max(0, c_v)
/// ```
///
/// which satisfies every row with every variable inside its bounds. The basic
/// column for row `v` must therefore be CHOSEN PER ROW: the surplus for
/// `c_v > 0`, the `z` column for `c_v <= 0` (the transposed rhs is `-c_v`, so
/// the test reads off `row.b`).
///
/// Neither single-family crash is feasible for both signs — and both were
/// tried, at real cost. The default all-surplus basis solves to `s_v = c_v`,
/// infeasible whenever `c_v < 0`: Phase I burned pivots under Bland's rule and
/// the transpose measured 8.3x SLOWER than the primal form on negative-cost
/// models, which is why this path was originally restricted to `c >= 0`. The
/// first "dual-image" crash then made the `z` columns basic for EVERY row,
/// which solves to `z_v = -c_v` — infeasible whenever `c_v > 0`, i.e. for the
/// complemented pseudo-Boolean models that are this solver's ENTIRE production
/// diet. Measured on the real f64-tier LPs of `edgecross14-019` (n=328,
/// m=1746, the one instance whose shape dispatches the transpose): Phase I
/// spent ~314 iterations (≈ the positive-cost column count) clawing back
/// feasibility and the transposed solve ran 4-5x SLOWER than the primal form;
/// with this per-row crash Phase I exits at its first feasibility check.
fn crash_at_dual_image_of_x0(simplex: &mut Simplex, model: &LpF64, m: usize) {
    let tn = model.n;
    for slot in simplex.basic_row.iter_mut() {
        *slot = None;
    }
    for (v, row) in model.rows.iter().enumerate() {
        // `row.b == -c_v`: non-negative rhs means `c_v <= 0` (z basic at
        // `-c_v >= 0`); negative rhs means `c_v > 0` (surplus basic at `c_v`).
        let basic = if row.b >= 0.0 { m + v } else { tn + v };
        simplex.basis[v] = basic;
        simplex.basic_row[basic] = Some(v);
    }
    simplex.refactorize();
}

/// Test-only instrumented twin of [`solve_transposed_for_box_lp`]: same build,
/// same crash, but returns the per-phase effort counters so the replay
/// crossover harness can report work, not just wall clock.
#[cfg(test)]
pub(super) fn solve_transposed_for_box_lp_instrumented(
    n: usize,
    c: &[f64],
    rows: &[RowF64],
    limits: SimplexLimits,
    should_stop: &dyn Fn() -> bool,
) -> Option<(Vec<f64>, Vec<f64>, RunStats)> {
    let m = rows.len();
    let model = build_transposed_model(n, c, rows)?;
    let tn = model.n;
    let tm = model.rows.len();
    let total_columns = tn.checked_add(tm)?;
    let mut simplex = Simplex::new(&model, tn, tm, total_columns);
    crash_at_dual_image_of_x0(&mut simplex, &model, m);

    let stats = simplex.run_instrumented(should_stop, limits, None);
    let (dual, primal) = extract_original_solution(simplex.extract(&model), n, m);
    Some((dual, primal, stats))
}
