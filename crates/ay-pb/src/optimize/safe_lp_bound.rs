// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fast, **sound** floating-point LP-relaxation lower bound via the
//! Neumaier–Shcherbina (NS) "safe bounding" technique.
//!
//! # The contract
//!
//! For a PBO minimization instance
//!
//! ```text
//! minimize   offset + sum_v c_v * x_v          (x_v in {0,1})
//! subject to sum_v a_{r,v} * x_v  >=  b_r       (constraints, after >= normalization)
//! ```
//!
//! [`safe_lp_lower_bound`] returns `Some(lb)` with the **guarantee**
//! `lb <= LP* <= IntOpt`, or `None` when it declines. The returned bound is a
//! sound integer lower bound on the objective: it is `floor(.)` of a real number
//! that is provably `<= ` the true LP optimum, *even though every arithmetic step
//! uses `f64`*. The bound may be looser than the exact-rational bound (that only
//! costs quality), but it is **never** higher than the true optimum (that would be
//! catastrophic).
//!
//! # Why NS is sound regardless of LP-solver accuracy
//!
//! The keystone is **LP weak duality**, which holds for *any* non-negative dual
//! multiplier vector — not just the optimal one. Consider the LP relaxation
//! `min c·x  s.t.  Ax >= b, 0 <= x <= 1`. Pick **any** `y >= 0` (one entry per
//! `>=` row). For every primal-feasible `x` (i.e. `Ax >= b` and `0 <= x <= 1`):
//!
//! ```text
//!   c·x  =  y·(Ax)            + (c - A^T y)·x
//!        >= y·b               + (c - A^T y)·x          [y >= 0, Ax >= b]
//!        >= y·b + sum_j min( d_j·0 , d_j·1 )           [0 <= x_j <= 1, d = c - A^T y]
//!         = y·b + sum_j min( 0, d_j ).
//! ```
//!
//! The last inequality holds term-by-term: `d_j x_j` over `x_j in [0,1]` is
//! minimized at an endpoint, value `min(0, d_j)`. So
//!
//! ```text
//!   NS(y)  :=  offset + y·b + sum_j min(0, d_j)        ( d = c - A^T y )
//! ```
//!
//! is a valid lower bound on the objective for **every** `y >= 0`. Crucially this
//! needs *no* assumption that `y` is dual-feasible or LP-optimal: an approximate /
//! even infeasible `y` (after clamping to `y >= 0`) still yields a valid bound. The
//! LP solver only affects *how tight* `NS(y)` is, never its validity. That is the
//! whole power of NS: we get the speed of f64 with the safety of exact reasoning,
//! because the *only* property we rely on (`y >= 0` term-wise weak duality) is
//! re-established at the end from the clamped `y`, not trusted from the solver.
//!
//! # Making `NS(y)` sound under f64 rounding
//!
//! `NS(y)` above is the *real-number* value. We compute it in `f64`, which rounds.
//! To stay sound we compute an **upper bound `E` on the total rounding error** and
//! return `floor( NS_computed - E )`. Then
//!
//! ```text
//!   floor( NS_computed - E )  <=  NS_computed - E  <=  NS_real  <=  IntOpt,
//! ```
//!
//! the middle step holding because `|NS_computed - NS_real| <= E`. We never trust a
//! single f64 op; we bound them all. See [`ns_safe_bound`] for the derivation of
//! `E`, which follows the standard floating-point dot-product error model
//! (Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., §3.1).
//!
//! ## The standard error model (used throughout)
//!
//! With `u = 2^-53` the unit roundoff for IEEE-754 binary64 round-to-nearest, the
//! error of a single op is `fl(a∘b) = (a∘b)(1+δ)`, `|δ| <= u`. For a sum or
//! dot-product of `n` terms accumulated in any order, the classic bound is
//!
//! ```text
//!   | computed - exact |  <=  gamma_n * sum_i |partial term_i|,
//!   gamma_n = n*u / (1 - n*u)          (valid while n*u < 1).
//! ```
//!
//! We use a deliberately **generous** form: `gamma_n <= 1.01 * n * u` whenever
//! `n*u <= 0.01` (because `1/(1-x) <= 1.01` for `x <= 0.01`); here
//! `n <= MAX_NONZEROS = 2e5`, so `n*u ~ 2e-11 << 0.01`. We also bound the
//! magnitude term by an over-estimate computed from `|.|` running sums (themselves
//! rounded — so we inflate that running sum too). Every approximation is in the
//! direction that makes `E` *larger*, hence the returned bound *smaller*, hence
//! safe.
//!
//! # When we return `None`
//!
//! Too many vars/rows/non-zeros, a non-linear or empty objective, a coefficient
//! that does not produce a finite f64, an overflow in the integer mapping, or a
//! non-finite intermediate. On any doubt: `None`. A `None` is always safe; a
//! too-high bound is not.

use crate::types::{PbConstraint, PbLit, PbObjective, PbRel};

/// Environment variable that opts INTO the fast NS safe LP bound. Default OFF:
/// the existing exact-rational [`crate::optimize::lp_bound::lp_lower_bound`] path
/// is byte-for-byte unchanged unless this is set. Mirrors the `AY_PB_CG_CUTS`
/// gate in [`crate::optimize::cutting_planes`].
const SAFE_LP_ENV: &str = "AY_PB_SAFE_LP";

/// Whether the NS safe LP bound is enabled (opt-in; default OFF). Accepts
/// `1|true|yes|on` (case-insensitive, trimmed); anything else (or unset) is OFF.
#[allow(dead_code)] // wired into the solver by the parent during integration.
pub(crate) fn safe_lp_enabled() -> bool {
    fn enabled(value: &std::ffi::OsStr) -> bool {
        value.to_str().is_some_and(|value| {
            matches!(
                value.trim().to_ascii_lowercase().as_str(),
                "1" | "true" | "yes" | "on"
            )
        })
    }
    std::env::var_os(SAFE_LP_ENV)
        .as_deref()
        .is_some_and(enabled)
}

/// IEEE-754 binary64 unit roundoff `u = 2^-53`.
const UNIT_ROUNDOFF: f64 = 1.110_223_024_625_157e-16; // 2^-53.

/// Size guards. These bound work, never soundness. `MAX_VARS` is generous enough
/// to admit the multi-thousand-variable competition instances (e.g. the 6.4k-var
/// kidney-exchange family) that the bounded-variable simplex below handles fast;
/// the iteration cap + `should_stop` deadline keep it from ever hanging.
const MAX_VARS: usize = 50_000;
const MAX_ROWS: usize = 50_000;
const MAX_NONZEROS: usize = 2_000_000;
/// Hard cap on simplex iterations; hitting it just yields a (still valid) bound
/// from whatever `y >= 0` we have — NS is valid for any clamped `y`.
const MAX_SIMPLEX_ITERS: usize = 100_000;
/// How often (in basis-changing pivots) the eta-file product-form inverse is
/// rebuilt from the current basis to bound its length / fill-in and damp round-off.
/// Refactorization (with surplus-first, Markowitz-style pivot ordering) is cheap and
/// resets the eta-file to a SPARSE product form; doing it often keeps every BTRAN /
/// FTRAN fast on high-row instances where between-refactor fill would otherwise
/// blow up. Bounds work, never soundness.
const REFACTOR_EVERY: usize = 50;
/// Periodic exact recompute of the basic-variable values to damp accumulated
/// round-off drift between refactorizations.
const REFRESH_EVERY: usize = 200;
/// Upper cap (independent of the row count `m`) on how many consecutive
/// non-improving simplex iterations we tolerate before falling back from Dantzig
/// pricing to Bland's anti-cycling rule. The actual threshold is `min(m, this) +
/// 50`: on small/medium instances it tracks `m + 50` (the classic generous
/// allowance, which Dantzig rarely reaches because it keeps making progress), but on
/// instances with tens of thousands of rows it is CAPPED here so the anti-cycling
/// rule still engages well before any deadline — without this cap a 200-var / 17k-row
/// LP would stall through ~17k degenerate Dantzig pivots and never anti-cycle.
/// Bounds work, never soundness.
const STALL_BEFORE_BLAND: usize = 8000;
/// Internal wall-clock budget for one simplex solve. On timeout we return the best
/// dual found so far (sound via NS), never `None`. The external `should_stop` is the
/// real deadline in the solver; this is a backstop so a single solve cannot run away
/// when `should_stop` never fires (e.g. tests / unbounded-budget calls). The sparse
/// revised simplex converges on the vast majority of instances in well under this;
/// it only bites on pathological inputs whose `B^{-1}` densifies (e.g. a few-hundred
/// variable LP spread over tens of thousands of constraints), where the product-form
/// inverse cannot stay sparse — there we still return a sound (looser) bound promptly
/// instead of grinding indefinitely. Bounds work, never soundness.
const SIMPLEX_TIME_BUDGET: std::time::Duration = std::time::Duration::from_secs(10);

/// Computes a **sound** NS lower bound for `min objective` subject to
/// `constraints`, all variables Boolean. Returns `Some(lb)` with `lb <= IntOpt`
/// guaranteed, or `None` (always safe) when it declines.
///
/// `should_stop` is polled inside the simplex; on abort we still return a valid
/// NS bound from the current (clamped) dual point — never `None` purely due to a
/// timeout, because the partial dual is just as sound as a converged one.
#[allow(dead_code)] // gated standalone fn; wired into the solver by the parent.
pub(crate) fn safe_lp_lower_bound(
    objective: &PbObjective,
    constraints: &[PbConstraint],
    num_vars: u32,
    should_stop: &dyn Fn() -> bool,
) -> Option<i128> {
    safe_lp_bound_and_point(objective, constraints, num_vars, should_stop).0
}

/// Like [`safe_lp_lower_bound`] but ALSO returns the LP relaxation's primal
/// optimum point `x in [0,1]^n` (one entry per variable, index `v` = PB var
/// `v + 1`) for **advisory** use by branch-and-bound (branching / incumbent
/// rounding). The bound half is exactly as sound as [`safe_lp_lower_bound`]: it
/// is the NS bound from the clamped dual, unaffected by the primal point.
///
/// Returns `(Some(lb), Some(point))` on a successful solve, `(Some(lb), None)`
/// when a bound was derivable but the primal point is unavailable/unusable, or
/// `(None, None)` when the LP declined (oversized / non-linear / non-finite).
///
/// The point is **never** load-bearing for soundness: the caller must re-verify
/// any rounded assignment and re-derive bounds independently. A wrong/None point
/// only costs branching quality.
#[allow(dead_code)] // gated standalone fn; wired into the solver by the parent.
pub(crate) fn safe_lp_bound_and_point(
    objective: &PbObjective,
    constraints: &[PbConstraint],
    num_vars: u32,
    should_stop: &dyn Fn() -> bool,
) -> (Option<i128>, Option<Vec<f64>>) {
    let Some(model) = LpF64::build(objective, constraints, num_vars) else {
        return (None, None);
    };
    // Approximate optimal dual `y >= 0` (one per row) AND the primal point.
    // Accuracy only affects tightness/branching; we clamp `y` to `>= 0` before
    // using it so NS validity holds regardless of the simplex's accuracy.
    let solved = model.solve(should_stop);
    let y = match &solved {
        Some(SimplexResult { dual, .. }) if dual.len() == model.rows.len() => clamp_dual(dual),
        _ => vec![0.0; model.rows.len()],
    };
    let bound = ns_safe_bound(&model, &y);
    // Sanitize the primal point: keep it only if it has the right shape and is
    // finite; clamp into [0,1] (advisory rounding/branching tolerates this).
    let point = solved.and_then(|r| {
        if r.primal.len() != model.n {
            return None;
        }
        let mut p = r.primal;
        for v in &mut p {
            if !v.is_finite() {
                return None;
            }
            *v = v.clamp(0.0, 1.0);
        }
        Some(p)
    });
    (bound, point)
}

/// Like [`safe_lp_bound_and_point`] but returns the **clamped dual vector**
/// `y >= 0` (one entry per LP row; for all-`Ge` constraint slices the rows are
/// 1:1, in order, with the input constraints — `Eq` rows contribute two entries).
///
/// Purpose: a caller can maintain its own *incremental* NS bounds from `y`
/// (weak duality holds for ANY `y >= 0`, so a stale or rounded copy of these
/// duals still yields a sound bound). The bound half is exactly as sound as
/// [`safe_lp_lower_bound`]. Returns `(None, None)` when the LP declined;
/// `(Some(lb), Some(y))` otherwise — including on timeout, where the partial
/// dual is just as valid as a converged one.
#[allow(dead_code)] // gated standalone fn; wired into the solver by the parent.
pub(crate) fn safe_lp_bound_and_dual(
    objective: &PbObjective,
    constraints: &[PbConstraint],
    num_vars: u32,
    should_stop: &dyn Fn() -> bool,
) -> (Option<i128>, Option<Vec<f64>>) {
    let Some(model) = LpF64::build(objective, constraints, num_vars) else {
        return (None, None);
    };
    let solved = model.solve(should_stop);
    let y = match &solved {
        Some(SimplexResult { dual, .. }) if dual.len() == model.rows.len() => clamp_dual(dual),
        _ => vec![0.0; model.rows.len()],
    };
    let bound = ns_safe_bound(&model, &y);
    (bound, Some(y))
}

/// Raw-rows fast path for callers that already hold the LP in numeric form:
/// solves `min c·x  s.t.  rows[i].0 · x >= rows[i].1, 0 <= x <= 1` and returns
/// the **clamped dual vector** `y >= 0` (one entry per row, in order), or
/// `None` when the model exceeds the solver's size limits or the solve yielded
/// no usable dual. Skips the PB-constraint translation layer entirely (no
/// per-term allocations, no BTreeMap dedup) — the caller must supply
/// 0-based in-range var indices with **sorted, deduplicated, non-zero**
/// coefficients per row, exactly the `RowF64` contract.
///
/// Soundness note: the caller is expected to use the duals via its own exact
/// arithmetic (weak duality holds for ANY `y >= 0`); accuracy of the solve
/// affects only bound tightness, never validity.
pub(crate) fn safe_lp_duals_from_raw(
    num_vars: usize,
    c: Vec<f64>,
    rows_raw: Vec<(Vec<(usize, f64)>, f64)>,
    target: Option<f64>,
    should_stop: &dyn Fn() -> bool,
) -> Option<Vec<f64>> {
    if num_vars == 0 || num_vars > MAX_VARS || rows_raw.len() > MAX_ROWS || c.len() != num_vars {
        return None;
    }
    let mut nonzeros = 0usize;
    let mut rows = Vec::with_capacity(rows_raw.len());
    for (coeffs, b) in rows_raw {
        debug_assert!(coeffs.iter().all(|&(v, x)| v < num_vars && x != 0.0));
        debug_assert!(coeffs.windows(2).all(|w| w[0].0 < w[1].0));
        nonzeros += coeffs.len();
        if nonzeros > MAX_NONZEROS {
            return None;
        }
        rows.push(RowF64 { coeffs, b });
    }
    let model = LpF64 {
        n: num_vars,
        c,
        offset: 0.0,
        rows,
    };
    match model.solve_target(should_stop, target) {
        Some(SimplexResult { dual, .. }) if dual.len() == model.rows.len() => {
            Some(clamp_dual(&dual))
        }
        _ => None,
    }
}

/// Clamps a dual vector to `y >= 0` and replaces non-finite entries with 0; the
/// NS bound requires `y >= 0`, and any clamped/zeroed `y` is still sound.
fn clamp_dual(dual: &[f64]) -> Vec<f64> {
    dual.iter()
        .map(|&yi| if yi.is_finite() && yi > 0.0 { yi } else { 0.0 })
        .collect()
}

/// The LP relaxation in **f64**, original variable space (no complementation —
/// NS handles arbitrary objective signs and the `[0,1]` box directly).
///
/// Rows encode `A x >= b` for each PB constraint (`=` split into two `>=`). The
/// box `0 <= x <= 1` is *not* stored as rows for the NS expression; it is handled
/// analytically by the NS reduced-cost term `sum_j min(0, d_j)`.
struct LpF64 {
    /// Number of variables `n`.
    n: usize,
    /// Objective coefficient per variable (may be negative). Plus `offset`.
    c: Vec<f64>,
    /// Constant added to the objective after literal-negation folding.
    offset: f64,
    /// Sparse `>=` rows.
    rows: Vec<RowF64>,
}

/// A sparse `>=` row: `coeffs · x >= b`, in **original** variable space.
struct RowF64 {
    /// `(var_index_0based, coefficient)` entries, deduplicated, non-zero.
    coeffs: Vec<(usize, f64)>,
    /// Right-hand side `b`.
    b: f64,
}

impl LpF64 {
    fn build(objective: &PbObjective, constraints: &[PbConstraint], num_vars: u32) -> Option<Self> {
        let n = usize::try_from(num_vars).ok()?;
        if n == 0 || n > MAX_VARS {
            return None;
        }
        if constraints.len() > MAX_ROWS {
            return None;
        }

        // --- Objective: each term must be a single literal (linear). ---
        let mut c = vec![0.0f64; n];
        let mut offset = 0.0f64;
        let mut any_obj = false;
        for term in &objective.terms {
            if term.coeff == 0 {
                continue;
            }
            let [lit] = term.lits.as_slice() else {
                return None; // non-linear objective term.
            };
            let v = var_index(*lit, n)?;
            let coeff = coeff_to_f64(term.coeff)?;
            if lit.negated {
                // coeff * (1 - x_v) = coeff - coeff * x_v
                offset += coeff;
                c[v] -= coeff;
            } else {
                c[v] += coeff;
            }
            any_obj = true;
        }
        if !any_obj {
            return None;
        }

        // --- Rows (no complementation). ---
        let mut rows: Vec<RowF64> = Vec::new();
        let mut nonzeros = 0usize;
        for constraint in constraints {
            match constraint.rel {
                PbRel::Ge => {
                    let row = build_row_f64(constraint, n, 1)?;
                    nonzeros += row.coeffs.len();
                    rows.push(row);
                }
                PbRel::Eq => {
                    let pos = build_row_f64(constraint, n, 1)?;
                    let neg = build_row_f64(constraint, n, -1)?;
                    nonzeros += pos.coeffs.len() + neg.coeffs.len();
                    rows.push(pos);
                    rows.push(neg);
                }
            }
            if rows.len() > MAX_ROWS || nonzeros > MAX_NONZEROS {
                return None;
            }
        }

        Some(Self { n, c, offset, rows })
    }

    /// Solves the LP relaxation `min c·x s.t. Ax >= b, 0 <= x <= 1` with the
    /// bounded-variable primal simplex, returning BOTH an (approximate) optimal
    /// dual `y` (one per `Ax>=b` row) and the primal optimum `x in [0,1]^n`.
    ///
    /// Soundness does NOT depend on either output being optimal or even feasible:
    /// NS re-derives a valid bound from the clamped `y`, and the primal point is
    /// purely advisory. On no rows we return `y = []` and `x = 0` (the trivial
    /// optimum of an unconstrained `min c·x` with `c` mapped through the box).
    fn solve(&self, should_stop: &dyn Fn() -> bool) -> Option<SimplexResult> {
        bounded_simplex_solve(self, should_stop, None)
    }

    /// [`Self::solve`] with an early-exit threshold: the Phase-II loop returns
    /// as soon as its quick-NS bound reaches `target` (see `quick_ns_bound`).
    fn solve_target(
        &self,
        should_stop: &dyn Fn() -> bool,
        target: Option<f64>,
    ) -> Option<SimplexResult> {
        bounded_simplex_solve(self, should_stop, target)
    }
}

/// Builds one `>=` f64 row for `constraint` scaled by `sign` (1 or -1), folding
/// literal negation into the rhs. No complementation (NS keeps original space).
fn build_row_f64(constraint: &PbConstraint, n: usize, sign: i128) -> Option<RowF64> {
    use std::collections::BTreeMap;
    let mut coeff_by_var: BTreeMap<usize, f64> = BTreeMap::new();
    let mut rhs = coeff_to_f64(constraint.rhs.checked_mul(sign)?)?;
    for term in &constraint.terms {
        let [lit] = term.lits.as_slice() else {
            return None; // non-linear constraint term.
        };
        let v = var_index(*lit, n)?;
        let base = coeff_to_f64(term.coeff.checked_mul(sign)?)?;
        if lit.negated {
            // base * (1 - x_v) = base - base * x_v ; constant moves to rhs.
            *coeff_by_var.entry(v).or_insert(0.0) -= base;
            rhs -= base;
        } else {
            *coeff_by_var.entry(v).or_insert(0.0) += base;
        }
    }
    let coeffs: Vec<(usize, f64)> = coeff_by_var
        .into_iter()
        .filter(|(_, c)| *c != 0.0)
        .collect();
    Some(RowF64 { coeffs, b: rhs })
}

/// Maps a 1-indexed PB literal to a 0-indexed variable column, bounds-checked.
fn var_index(lit: PbLit, n: usize) -> Option<usize> {
    if lit.var == 0 {
        return None;
    }
    let idx = usize::try_from(lit.var - 1).ok()?;
    if idx >= n {
        return None;
    }
    Some(idx)
}

/// Converts an i128 coefficient to f64, declining (`None`) only if the result is
/// non-finite (cannot happen for i128, but checked defensively). The conversion
/// may *round* for magnitudes `> 2^53`; that representation error is itself
/// accounted for in the NS error term (we bound the error of using `fl(coeff)`
/// rather than `coeff`), so a rounded coefficient never threatens soundness.
fn coeff_to_f64(coeff: i128) -> Option<f64> {
    let f = coeff as f64;
    if f.is_finite() {
        Some(f)
    } else {
        None
    }
}

/// Computes the sound NS bound `floor( NS(y) - E )`, where `E` upper-bounds the
/// total f64 rounding + coefficient-representation error of the NS expression.
///
/// # The expression and its error budget
///
/// `NS(y) = offset + y·b + sum_j min(0, d_j)`, `d_j = c_j - (A^T y)_j`.
///
/// We compute, in f64:
///   `S1 = offset + y·b`                                   (sum over m rows)
///   `aty_j = (A^T y)_j`                                   (sparse accumulation)
///   `d_j = c_j - aty_j`
///   `S2 = sum_j min(0, d_j)`                              (sum over n terms)
///   `NS_hat = S1 + S2`
///
/// ## Error of `S1 = offset + sum_r b_r y_r`
///
/// A sum of `m+1` terms (offset plus `m` products). By the standard model the
/// summation error is `<= gamma_{m+2} * T1`, where `T1 = |offset| + sum_r |b_r y_r|`
/// over-estimates the accumulated magnitudes (and the extra `+1` in the gamma
/// index covers the per-product rounding `u*|b_r y_r|`). We add the representation
/// error of each integer `b_r`, weighted by `|y_r|`: `sum_r |y_r| * (u*|b_r|)`.
///
/// ## Error of each `aty_j` and `d_j`
///
/// `aty_j = sum_{r: a_{r,j} != 0} a_{r,j} y_r` is a dot of `k_j <= m` terms; its
/// error is `<= gamma_{k_j+1} * sum_r |a_{r,j} y_r|` (the `+1` covers per-product
/// rounding) plus representation error `sum_r |y_r| * (u*|a_{r,j}|)`. Then
/// `d_j = c_j - aty_j` adds one more rounding `<= u*|d_j|` and the representation
/// error of integer `c_j` (`u*|c_j|`).
///
/// ## Error of `S2 = sum_j min(0, d_j)` and `NS_hat = S1 + S2`
///
/// `min(0, .)` is exact (compare/select, no rounding). Summing `n` terms adds
/// `gamma_n * sum_j |min(0,d_j)|`. `min(0,.)` is 1-Lipschitz, so a `d_j` error of
/// `e_dj` perturbs `min(0,d_j)` by at most `e_dj`; we add `sum_j e_dj`. Finally
/// `NS_hat = S1 + S2` adds one rounding `<= u*|NS_hat|`.
///
/// Every bound above is summed into `E`; we return `floor(NS_hat - E)`. Because
/// `|NS_hat - NS_real| <= E`, `NS_hat - E <= NS_real <= IntOpt`, so the floor is a
/// sound integer lower bound. We use `gamma_k <= 1.01 * k * u` and inflate every
/// magnitude term — all in the safe (error-increasing) direction.
fn ns_safe_bound(model: &LpF64, y: &[f64]) -> Option<i128> {
    let n = model.n;
    let m = model.rows.len();
    debug_assert_eq!(y.len(), m);

    // `gamma_k` (generous): 1.01 * k * u, valid because k*u <= MAX_NONZEROS*u << 0.01.
    let gamma = |k: usize| -> f64 { 1.01 * (k as f64) * UNIT_ROUNDOFF };

    // --- S1 = offset + sum_r b_r * y_r, with magnitude accumulator T1. ---
    let mut s1 = model.offset;
    let mut t1 = model.offset.abs(); // accumulated |partial| magnitude.
    let mut rep_err_b = 0.0f64; // sum_r |y_r| * repError(b_r).
    for (r, row) in model.rows.iter().enumerate() {
        let yr = y[r];
        if yr == 0.0 {
            continue;
        }
        let prod = row.b * yr;
        s1 += prod;
        t1 += prod.abs();
        // |y_r| * (representation error of integer b_r): u*|row.b| upper-bounds it.
        rep_err_b += yr.abs() * (UNIT_ROUNDOFF * row.b.abs());
    }
    if !s1.is_finite() || !t1.is_finite() || !rep_err_b.is_finite() {
        return None;
    }
    let e_s1 = gamma(m + 2) * t1 + rep_err_b;

    // --- aty_j accumulation (sparse by row), tracking per-j magnitude & error. ---
    let mut aty = vec![0.0f64; n];
    let mut aty_mag = vec![0.0f64; n]; // sum_r |a_rj y_r| per column.
    let mut aty_terms = vec![0usize; n]; // k_j = number of accumulated terms.
    let mut aty_rep = vec![0.0f64; n]; // sum_r |y_r| * repError(a_rj) per column.
    for (r, row) in model.rows.iter().enumerate() {
        let yr = y[r];
        if yr == 0.0 {
            continue;
        }
        let ayr = yr.abs();
        for &(v, a) in &row.coeffs {
            let prod = a * yr;
            aty[v] += prod;
            aty_mag[v] += prod.abs();
            aty_terms[v] += 1;
            aty_rep[v] += ayr * (UNIT_ROUNDOFF * a.abs());
        }
    }

    // --- d_j = c_j - aty_j, S2 = sum_j min(0, d_j), with full error budget. ---
    let mut s2 = 0.0f64;
    let mut t2 = 0.0f64; // sum_j |min(0,d_j)| for the S2 sum rounding.
    let mut prop_err = 0.0f64; // sum_j e_dj (propagated error in each d_j).
    for v in 0..n {
        let cj = model.c[v];
        let dj = cj - aty[v];
        if !dj.is_finite() {
            return None;
        }
        // Error in aty_j: dot of k_j terms -> gamma_{k_j+1} * magnitude, plus the
        // per-row representation error already weighted by |y_r|.
        let e_aty = gamma(aty_terms[v].saturating_add(1)) * aty_mag[v] + aty_rep[v];
        // Error in d_j: one subtraction rounding (u*|d_j|), the aty error, and the
        // representation error of integer c_j (u*|c_j|).
        let e_dj = UNIT_ROUNDOFF * dj.abs() + e_aty + UNIT_ROUNDOFF * cj.abs();

        let contrib = dj.min(0.0); // exact (compare/select; no rounding).
        s2 += contrib;
        t2 += contrib.abs();
        prop_err += e_dj; // min(0,.) is 1-Lipschitz in d_j.
    }
    if !s2.is_finite() || !t2.is_finite() || !prop_err.is_finite() {
        return None;
    }
    let e_s2 = gamma(n) * t2 + prop_err;

    // --- NS_hat = S1 + S2 and final assembly. ---
    let ns_hat = s1 + s2;
    if !ns_hat.is_finite() {
        return None;
    }
    let e_final_add = UNIT_ROUNDOFF * ns_hat.abs();
    let total_error = e_s1 + e_s2 + e_final_add;
    if !total_error.is_finite() || total_error < 0.0 {
        return None;
    }

    // Safe real lower bound on NS(y): subtract the whole error budget.
    let safe_value = ns_hat - total_error;
    if !safe_value.is_finite() {
        return None;
    }

    floor_to_i128(safe_value)
}

/// Floors an f64 to i128, returning `None` on non-finite or out-of-range. The
/// floor of a value `<= NS_real` is `<= floor(NS_real) <= IntOpt` (the integer
/// optimum is an integer), so flooring keeps soundness. `f.floor()` is *exact*
/// for any finite f64 (IEEE-754), so no extra margin is needed here.
fn floor_to_i128(value: f64) -> Option<i128> {
    if !value.is_finite() {
        return None;
    }
    let floored = value.floor();
    // i128 range as f64. f64 cannot represent i128::MAX (= 2^63 - 1) exactly; use a
    // conservative power-of-two strictly inside the range so the cast is safe.
    const LIMIT: f64 = 9.223_372_036_854_776e18; // 2^63 as f64.
    if floored >= LIMIT || floored <= -LIMIT {
        return None;
    }
    Some(floored as i128)
}

// ===========================================================================
//  A bounded-variable primal simplex (no Big-M) producing dual prices AND the
//  primal optimum.
//
//  This solver is **advisory** for the bound's tightness/branching only: NS
//  re-derives a valid bound from the clamped `y` regardless of what this returns,
//  and the primal point is never trusted for soundness. We use a *bounded-variable*
//  method so the box `0 <= x <= 1` is handled natively (no Big-M, which is what
//  caused the numerical blow-ups in the old solver). Anti-cycling uses Dantzig
//  pricing with a Bland's-rule fallback whenever progress stalls. On any
//  difficulty (size cap, deadline, non-convergence) we still return the BEST dual
//  found so far — never `None` purely for time — so the caller gets a sound (if
//  looser) bound rather than the trivial `y = 0`.
// ===========================================================================

/// Result of the bounded-variable simplex: a dual price per `Ax>=b` row and the
/// primal optimum point in `[0,1]^n`.
struct SimplexResult {
    /// Dual multiplier `y_r` for each `>=` row. Sign-unconstrained here; the NS
    /// layer clamps to `>= 0` before use, so any value is sound.
    dual: Vec<f64>,
    /// Primal optimum `x` (one entry per variable). Advisory only.
    primal: Vec<f64>,
}

/// Standard form used internally. We introduce one **surplus** `s_r >= 0` per
/// `>=` row, giving equalities `A_r x - s_r = b_r`, i.e. `M [x; s] = b` with
/// `M = [A | -I]`. Variable layout:
///
/// ```text
///   columns 0..n          : structural x_j,  bounds [0, 1]
///   columns n..n+m        : surplus   s_r,   bounds [0, +inf)
/// ```
///
/// In a bounded-variable simplex each NON-basic variable rests at its lower or
/// upper bound; basic variables are `x_B = B^{-1} (b - sum_{j nonbasic} M_j
/// val(j))`. Rather than a dense tableau `B^{-1} M` (which is `O(m·cols)` per pivot
/// and far too slow on the thousands-of-rows competition instances) we use a
/// **sparse revised simplex**: the constraint matrix `A` is held column-major
/// (CSC) and `B^{-1}` is kept as a **product-form inverse (eta file)**
/// `B^{-1} = E_k ··· E_1 B_0^{-1}`. Each iteration does ONE `BTRAN` (`y = c_B^T
/// B^{-1}`) to price all columns by sparse dot-products against their `A`-columns,
/// then ONE `FTRAN` (`alpha = B^{-1} a_q`) of the entering column for the ratio
/// test. Per-iteration cost scales with the number of non-zeros plus the eta-file
/// length, not `m·cols`. The eta file is periodically **refactorized** (rebuilt
/// from the current basis columns) to cap its growth and damp round-off.
///
/// We start from the surplus crash basis (`B = -I`, so `B_0^{-1} = -I`). With all
/// structural vars at lower bound 0 the basic surplus values are `s_r = -b_r` —
/// generally infeasible (negative) when `b_r > 0`, so we run a **Phase I** that
/// drives the basic variables back inside their bounds by minimizing total bound
/// infeasibility, then **Phase II** minimizes `c·x`. Both phases share the same
/// bounded-variable pivot machinery.
///
/// Dual prices: with the surplus column of `M` equal to `-e_r`, the reduced cost of
/// surplus `s_r` is `0 - y·(-e_r) = y_r` where `y = c_B^T B^{-1}`, so we read `y_r`
/// directly off `y`. NS clamps `y` to `>= 0`, so we stay sound for ANY `y` — the
/// revised-simplex accuracy affects only the bound's tightness, never its validity.
fn bounded_simplex_solve(
    model: &LpF64,
    should_stop: &dyn Fn() -> bool,
    target: Option<f64>,
) -> Option<SimplexResult> {
    let n = model.n;
    let m = model.rows.len();
    if n == 0 {
        return None;
    }
    // No constraints: the LP is `min c·x, 0<=x<=1`, separable; optimum picks
    // x_j = 1 where c_j < 0 else 0. No duals.
    if m == 0 {
        let primal: Vec<f64> = model
            .c
            .iter()
            .map(|&c| if c < 0.0 { 1.0 } else { 0.0 })
            .collect();
        return Some(SimplexResult {
            dual: Vec::new(),
            primal,
        });
    }

    let total_cols = n.checked_add(m)?; // structural + surplus.

    let mut s = Simplex::new(model, n, m, total_cols);
    // Internal wall-clock budget so a large dense solve never hangs: on timeout we
    // return the best dual found so far, which NS turns into a sound (looser) bound.
    // `should_stop` (the external deadline) is honored too and usually fires first.
    let deadline = std::time::Instant::now() + SIMPLEX_TIME_BUDGET;
    // Convergence status is irrelevant here: NS derives a sound bound from any
    // clamped dual, converged or not.
    let _ = s.run(should_stop, deadline, target);
    Some(s.extract(model))
}

/// Approximately solves `min c·x  s.t.  coeffs_r · x >= b_r  (each row),
/// 0 <= x <= 1` with the bounded-variable revised f64 simplex, under a caller
/// wall-clock `budget`, returning `(dual, primal)`: one dual price per row and
/// the primal point (one entry per variable).
///
/// **ADVISORY ONLY** — both outputs are floating point and carry NO soundness
/// guarantee whatsoever. The intended consumer is
/// [`crate::optimize::lp_bound`]'s certified f64 tier, which re-verifies dual
/// feasibility and the bound value in EXACT arithmetic before trusting anything
/// (a wrong dual there only costs a fallback to the exact simplex, never a
/// wrong bound). Rows/columns are in whatever space the caller models; this
/// function attaches no meaning beyond the `[0,1]` box.
///
/// Declines (`None`) on an empty/oversized model, mirroring [`LpF64::build`]'s
/// size guards. On timeout (budget or `should_stop`) the best dual found so far
/// is returned rather than `None` — the caller's exact verification decides
/// whether it is usable. The returned `bool` is `true` iff BOTH simplex phases
/// ended at optimality (no eligible entering column) rather than on the
/// budget/iteration caps — an advisory convergence signal: measured on the
/// i128-overflow corpus, non-converged duals only get WORSE with more budget
/// (the domset family drifts for 20s+), so callers should treat a `false` as
/// "this dual is not worth verifying" rather than retry with more time.
pub(crate) fn approx_dual_for_box_lp(
    n: usize,
    c: Vec<f64>,
    rows: Vec<(Vec<(usize, f64)>, f64)>,
    budget: std::time::Duration,
    should_stop: &dyn Fn() -> bool,
) -> Option<(Vec<f64>, Vec<f64>, bool)> {
    if n == 0 || n > MAX_VARS || rows.len() > MAX_ROWS {
        return None;
    }
    let nonzeros: usize = rows.iter().map(|(coeffs, _)| coeffs.len()).sum();
    if nonzeros > MAX_NONZEROS {
        return None;
    }
    let rows: Vec<RowF64> = rows
        .into_iter()
        .map(|(coeffs, b)| RowF64 { coeffs, b })
        .collect();
    let model = LpF64 {
        n,
        c,
        offset: 0.0, // unused by the simplex; the caller owns the offset.
        rows,
    };
    let m = model.rows.len();
    if m == 0 {
        // Separable optimum of `min c·x` over the box: x_j = 1 iff c_j < 0.
        let primal: Vec<f64> = model
            .c
            .iter()
            .map(|&cj| if cj < 0.0 { 1.0 } else { 0.0 })
            .collect();
        return Some((Vec::new(), primal, true));
    }
    let total_cols = n.checked_add(m)?;
    let mut s = Simplex::new(&model, n, m, total_cols);
    let deadline = std::time::Instant::now() + budget;
    let converged = s.run(should_stop, deadline, None);
    let result = s.extract(&model);
    Some((result.dual, result.primal, converged))
}

/// Why a [`Simplex::simplex_loop`] phase ended. Advisory only — every exit
/// leaves the solver state usable (NS re-derives soundness from the clamped
/// dual regardless); `Optimal` in both phases is the convergence signal
/// surfaced by [`approx_dual_for_box_lp`].
#[derive(Clone, Copy, PartialEq, Eq)]
enum LoopExit {
    /// The phase reached its own optimality (Phase I: bound-feasible; Phase II:
    /// no eligible entering column).
    Optimal,
    /// Deadline / `should_stop` / iteration cap / unbounded-movement guard.
    Stopped,
}

/// Variable bound kind for a non-basic column.
#[derive(Clone, Copy, PartialEq, Eq)]
enum AtBound {
    Lower,
    Upper,
}

/// One column transform of the product-form inverse (an "eta"). `B^{-1}` is the
/// product `E_k ··· E_1 B_0^{-1}` with `B_0^{-1} = -I`. Each eta is identity except
/// in column `p` (the pivot ROW slot, `0..m`), which holds the eta vector
/// `eta[p] = 1/alpha[p]`, `eta[i] = -alpha[i]/alpha[p]` for `i != p`, where
/// `alpha = B^{-1} a_q` is the FTRAN'd entering column at pivot time.
struct Eta {
    /// Pivot ROW slot (index into `basis` / `xb_val`), the column the eta replaces.
    p: usize,
    /// `eta[p] = 1/alpha[p]` (the pivot reciprocal).
    diag: f64,
    /// `(row i, eta[i])` for `i != p`, only the non-zeros.
    vec: Vec<(usize, f64)>,
}

/// Sparse bounded-variable revised-simplex state. `B^{-1}` is held as an eta-file
/// product-form inverse (see [`Eta`]); the constraint matrix `A` is column-major
/// (CSC). Per-iteration work is a `BTRAN` + a column `FTRAN` + a sparse pricing
/// sweep, all scaling with non-zeros and eta-file length rather than `m·cols`.
struct Simplex {
    n: usize,
    m: usize,
    cols: usize,
    /// CSC of `A`: structural column `j` is entries `col_idx/col_val[col_ptr[j]..col_ptr[j+1]]`.
    col_ptr: Vec<usize>,
    /// Row index of each structural non-zero.
    col_idx: Vec<usize>,
    /// Coefficient of each structural non-zero.
    col_val: Vec<f64>,
    /// Right-hand side `b_r` per row.
    rhs: Vec<f64>,
    /// Product-form inverse `B^{-1} = E_k ··· E_1 (-I)`, applied in order for FTRAN
    /// and in reverse for BTRAN. The trailing `-I` is `B_0^{-1}`.
    etas: Vec<Eta>,
    /// Current value of the basic variable in each row slot, maintained
    /// incrementally (recomputed exactly at phase boundaries, after each
    /// refactorization, and periodically to damp drift).
    xb_val: Vec<f64>,
    /// Column index of the basic variable in each row slot.
    basis: Vec<usize>,
    /// For every column: the row slot it is basic in, else `None` (non-basic).
    basic_row: Vec<Option<usize>>,
    /// For non-basic columns: which bound they currently rest at.
    at: Vec<AtBound>,
    /// Lower / upper bound of each column (`upper` may be +inf for surpluses).
    lower: Vec<f64>,
    upper: Vec<f64>,
    /// Phase-II objective cost of each column (structural `c_j`; surplus 0).
    cost: Vec<f64>,
    /// Data scale (max |coeff|), for tolerances. Advisory only.
    scale: f64,
    /// Reusable scratch: length-`m` working vector for FTRAN/BTRAN.
    work: Vec<f64>,
    /// Reusable scratch: basic costs by row slot (BTRAN input / dual output).
    cb: Vec<f64>,
    /// Reusable scratch: dual `y = c_B^T B^{-1}` by row slot.
    y: Vec<f64>,
    /// Reusable scratch: residual right-hand side for `recompute_xb` (avoids a
    /// per-call allocation/clone of `rhs`).
    xb_scratch: Vec<f64>,
    /// Reusable scratch buffers for the refactorization (avoid per-refactor allocs).
    rf_new_basis: Vec<usize>,
    rf_row_used: Vec<bool>,
    rf_cols: Vec<usize>,
    /// Basis-changing pivots since the last refactorization.
    since_refactor: usize,
    /// Total non-zeros across the current eta-file. Tracked incrementally so we can
    /// refactor early (capping FTRAN/BTRAN cost) when between-refactor FILL grows
    /// large — the decisive lever on instances whose `B^{-1}` densifies quickly.
    eta_nnz: usize,
    /// Eta-nnz ceiling that forces an early refactor. Sized relative to the
    /// constraint-matrix nnz so sparse instances never trip it but dense-`B^{-1}`
    /// high-row instances refactor before a single BTRAN gets expensive.
    eta_nnz_cap: usize,
}

impl Simplex {
    fn new(model: &LpF64, n: usize, m: usize, cols: usize) -> Self {
        let mut scale = 1.0f64;
        for &cj in &model.c {
            scale = scale.max(cj.abs());
        }
        for row in &model.rows {
            scale = scale.max(row.b.abs());
            for &(_, a) in &row.coeffs {
                scale = scale.max(a.abs());
            }
        }

        // --- CSC of A (transpose the row-major model.rows). ---
        let mut counts = vec![0usize; n];
        for row in &model.rows {
            for &(v, _) in &row.coeffs {
                counts[v] += 1;
            }
        }
        let mut col_ptr = vec![0usize; n + 1];
        for j in 0..n {
            col_ptr[j + 1] = col_ptr[j] + counts[j];
        }
        let nnz = col_ptr[n];
        let mut col_idx = vec![0usize; nnz];
        let mut col_val = vec![0.0f64; nnz];
        let mut cursor = col_ptr.clone();
        let mut rhs = vec![0.0f64; m];
        for (r, row) in model.rows.iter().enumerate() {
            rhs[r] = row.b;
            for &(v, a) in &row.coeffs {
                let p = cursor[v];
                col_idx[p] = r;
                col_val[p] = a;
                cursor[v] = p + 1;
            }
        }

        // Bounds: structural [0,1], surplus [0, +inf).
        let mut lower = vec![0.0f64; cols];
        let mut upper = vec![0.0f64; cols];
        for j in 0..n {
            lower[j] = 0.0;
            upper[j] = 1.0;
        }
        for j in n..cols {
            lower[j] = 0.0;
            upper[j] = f64::INFINITY;
        }

        // Phase-II objective: structural costs c_j; surpluses cost 0.
        let mut cost = vec![0.0f64; cols];
        cost[..n].copy_from_slice(&model.c);

        // Surplus crash basis: B = -I (surplus column of M is -e_r), B^{-1} = -I.
        // Surplus s_r is basic in row slot r; the eta file starts empty.
        let basis: Vec<usize> = (0..m).map(|i| n + i).collect();
        let mut basic_row: Vec<Option<usize>> = vec![None; cols];
        for (i, &b) in basis.iter().enumerate() {
            basic_row[b] = Some(i);
        }
        // All non-basic columns start at their lower bound (0).
        let at = vec![AtBound::Lower; cols];

        Self {
            n,
            m,
            cols,
            col_ptr,
            col_idx,
            col_val,
            rhs,
            etas: Vec::new(),
            xb_val: vec![0.0; m],
            basis,
            basic_row,
            at,
            lower,
            upper,
            cost,
            scale,
            work: vec![0.0; m],
            cb: vec![0.0; m],
            y: vec![0.0; m],
            xb_scratch: vec![0.0; m],
            rf_new_basis: vec![usize::MAX; m],
            rf_row_used: vec![false; m],
            rf_cols: Vec::with_capacity(m),
            since_refactor: 0,
            eta_nnz: 0,
            // Force a refactor once the eta-file's fill reaches a few times the
            // constraint-matrix nnz (with a floor so tiny instances are unaffected).
            // This keeps each FTRAN/BTRAN's cost bounded on instances where `B^{-1}`
            // fills in fast, trading a few extra (cheap, sparse) refactorizations for
            // a much cheaper per-iteration linear solve.
            eta_nnz_cap: (8 * nnz).max(200_000),
        }
    }

    /// Pivot tolerance, scaled to the data. Bounds work, never soundness.
    fn pivot_tol(&self) -> f64 {
        1e-9 * (1.0 + self.scale)
    }
    /// Reduced-cost entering tolerance.
    fn cost_tol(&self) -> f64 {
        1e-7 * (1.0 + self.scale)
    }
    /// Bound-feasibility tolerance for a basic variable.
    fn feas_tol(&self) -> f64 {
        1e-7 * (1.0 + self.scale)
    }

    /// Value of a non-basic column = its current bound.
    fn nonbasic_value(&self, j: usize) -> f64 {
        match self.at[j] {
            AtBound::Lower => self.lower[j],
            AtBound::Upper => self.upper[j],
        }
    }

    /// Applies `B^{-1}` to a dense vector `w` IN PLACE: first `B_0^{-1} = -I`
    /// (negate), then each eta in forward order. Cost is `O(m + sum eta nnz)`.
    fn apply_inverse(&self, w: &mut [f64]) {
        for wi in w.iter_mut() {
            *wi = -*wi; // B_0^{-1} = -I.
        }
        for e in &self.etas {
            let t = w[e.p];
            if t == 0.0 {
                continue;
            }
            for &(i, val) in &e.vec {
                w[i] += val * t;
            }
            w[e.p] = e.diag * t;
        }
    }

    /// Sparse FTRAN: computes `alpha = B^{-1} M_q` into `out`, gathering the indices
    /// of the result's non-zeros into `nz`. `out` MUST be all-zero on entry (the
    /// caller sparse-resets it via `nz` afterward) and `nz` is cleared here. Cost is
    /// `O(nnz(M_q) + sum_{fired eta} nnz(eta))` rather than `O(m)`, which is the key
    /// speed-up on high-row instances (the entering column is sparse).
    ///
    /// Folds in `B_0^{-1} = -I` by scattering the NEGATED column, then applies each
    /// eta in forward order, registering any newly non-zero row in `nz` exactly once.
    /// `marked` is a per-row "already in `nz`" flag (MUST be all-false on entry and
    /// is left all-false on exit): it prevents a row whose value transiently cancels
    /// to zero and is later re-touched from being pushed twice (a duplicate would
    /// double-apply that row when the resulting eta is built — corrupting `B^{-1}`).
    fn ftran_sparse(&self, q: usize, out: &mut [f64], nz: &mut Vec<usize>, marked: &mut [bool]) {
        nz.clear();
        if q < self.n {
            for p in self.col_ptr[q]..self.col_ptr[q + 1] {
                let r = self.col_idx[p];
                if !marked[r] {
                    marked[r] = true;
                    nz.push(r);
                }
                out[r] -= self.col_val[p]; // (-I) folded in.
            }
        } else {
            let r = q - self.n;
            if !marked[r] {
                marked[r] = true;
                nz.push(r);
            }
            out[r] += 1.0; // -(-1) from -I on surplus -e_r.
        }
        for e in &self.etas {
            let t = out[e.p];
            if t == 0.0 {
                continue;
            }
            for &(i, val) in &e.vec {
                if !marked[i] {
                    marked[i] = true;
                    nz.push(i);
                }
                out[i] += val * t;
            }
            out[e.p] = e.diag * t;
        }
        // Clear the markers for the touched rows (leaving `marked` all-false).
        for &r in nz.iter() {
            marked[r] = false;
        }
    }

    /// BTRAN of `self.y` (a row vector initially `c_B` by row slot) into `y^T
    /// B^{-1}` IN PLACE: applies each eta in REVERSE order, then `B_0^{-1} = -I`.
    /// One eta's row action sets `y[p] = diag*y[p] + sum_{i != p} eta[i]*y[i]`.
    /// Operates on the `self.y` field directly (indexing rather than a borrowed
    /// slice) so it composes with the per-iteration pricing without borrow clashes.
    fn btran_y(&mut self) {
        for idx in (0..self.etas.len()).rev() {
            let e = &self.etas[idx];
            let mut acc = e.diag * self.y[e.p];
            for &(i, val) in &e.vec {
                acc += val * self.y[i];
            }
            self.y[e.p] = acc;
        }
        for zi in self.y.iter_mut() {
            *zi = -*zi; // B_0^{-1} = -I (applied last for the row product).
        }
    }

    /// Recomputes the basic value of every row slot exactly:
    ///   `xb = B^{-1} (b - sum_{j nonbasic} M_j val(j))`.
    /// One FTRAN of the residual right-hand side. Used at phase boundaries, after
    /// each refactorization, and periodically to damp round-off drift.
    fn recompute_xb(&mut self) {
        // Reuse the `xb_scratch` buffer (swapped out so `apply_inverse(&self, ..)`
        // can borrow `self` immutably without aliasing the field).
        let mut v = std::mem::take(&mut self.xb_scratch);
        v.copy_from_slice(&self.rhs);
        for j in 0..self.cols {
            if self.basic_row[j].is_some() {
                continue;
            }
            let xv = self.nonbasic_value(j);
            if xv == 0.0 || !xv.is_finite() {
                continue;
            }
            // v -= M_j * xv.
            if j < self.n {
                for p in self.col_ptr[j]..self.col_ptr[j + 1] {
                    v[self.col_idx[p]] -= self.col_val[p] * xv;
                }
            } else {
                // surplus column is -e_r: v[r] -= (-1)*xv = v[r] += xv.
                v[j - self.n] += xv;
            }
        }
        self.apply_inverse(&mut v);
        self.xb_val.copy_from_slice(&v);
        self.xb_scratch = v;
    }

    /// Rebuilds the eta-file `B^{-1}` from scratch from the current basis columns,
    /// bounding the eta-file length and damping round-off. This is Gaussian
    /// elimination in product form with **partial (row) pivoting**: each basis
    /// column is FTRAN'd through the etas built so far, then pivoted at the
    /// largest-magnitude available row, which is then assigned that column. The
    /// resulting `basis` (row slot -> basic column) is consistent with the new
    /// eta-file: `B^{-1} M_{basis[p]} = e_p`. `xb_val` is refreshed by the caller's
    /// `recompute_xb` immediately afterward (it depends only on `B^{-1}`, `b`, and
    /// the nonbasic values, all consistent here).
    ///
    /// Surplus columns still basic in their crash slot contribute the identity and
    /// are assigned directly without an eta. If a column has no acceptable pivot
    /// (numerically singular — should not happen for a true basis, but round-off can
    /// make it so) we KEEP the previous eta-file and basis (the simplex is advisory:
    /// a stale but consistent inverse only costs tightness, never soundness).
    fn refactorize(&mut self) {
        let saved_etas = std::mem::take(&mut self.etas);
        let pivot_tol = self.pivot_tol();

        // Reset the reusable refactor scratch (no per-call allocation).
        for v in self.rf_new_basis.iter_mut() {
            *v = usize::MAX;
        }
        for v in self.rf_row_used.iter_mut() {
            *v = false;
        }
        // Order the basis columns so surplus columns are factored FIRST and
        // structurals last. A basic surplus `s_r` is `-e_r` (one non-zero): factored
        // first (through an empty eta-file) it FTRANs to `e_r`, pivots at its own row
        // `r`, and contributes the IDENTITY eta (skipped). Only the few structural
        // columns then create etas, and they fill only among the rows not already
        // claimed by surpluses — which keeps the eta-file short and SPARSE (a
        // Markowitz-style sparsest-first order). This is the key win for high-row,
        // few-column instances (e.g. ~17k rows / 200 vars), where factoring
        // structurals first instead causes heavy fill and a slow BTRAN per iteration.
        self.rf_cols.clear();
        self.rf_cols.extend_from_slice(&self.basis);
        self.rf_cols
            .sort_unstable_by_key(|&q| if q >= self.n { 0 } else { 1 });
        // Move the column list out so we can borrow `self` mutably in the loop.
        let cols = std::mem::take(&mut self.rf_cols);

        // `touched` collects the row indices that became non-zero in `work` during
        // this column's FTRAN, so we can (a) scan only those for the pivot and (b)
        // reset `work` sparsely afterward — turning the dense `O(m)` per column into
        // `O(nnz(work))`, which is tiny for the surplus-heavy high-row bases.
        let mut touched: Vec<usize> = Vec::with_capacity(64);

        let mut ok = true;
        for &q in &cols {
            touched.clear();
            // Scatter column q of M = [A | -I] and apply B_0^{-1} = -I (negate).
            if q < self.n {
                for p in self.col_ptr[q]..self.col_ptr[q + 1] {
                    let r = self.col_idx[p];
                    if self.work[r] == 0.0 {
                        touched.push(r);
                    }
                    self.work[r] -= self.col_val[p]; // (-I) folded in.
                }
            } else {
                let r = q - self.n;
                if self.work[r] == 0.0 {
                    touched.push(r);
                }
                self.work[r] += 1.0; // -(-1) from -I.
            }
            // Apply the etas built so far, tracking newly non-zero rows.
            for e in &self.etas {
                let t = self.work[e.p];
                if t == 0.0 {
                    continue;
                }
                for &(i, val) in &e.vec {
                    if self.work[i] == 0.0 {
                        touched.push(i);
                    }
                    self.work[i] += val * t;
                }
                self.work[e.p] = e.diag * t;
            }
            // Partial pivoting over the (few) touched rows that are still free.
            let mut prow = usize::MAX;
            let mut best = pivot_tol;
            for &i in &touched {
                if self.rf_row_used[i] {
                    continue;
                }
                let a = self.work[i].abs();
                if a > best {
                    best = a;
                    prow = i;
                }
            }
            if prow == usize::MAX {
                ok = false;
                // Sparse-reset work before bailing.
                for &i in &touched {
                    self.work[i] = 0.0;
                }
                break; // no acceptable pivot: singular under round-off; abort.
            }
            let piv = self.work[prow];
            // Build the eta from the touched non-zeros (sparse), then sparse-reset.
            let inv = 1.0 / piv;
            let mut vec = Vec::new();
            for &i in &touched {
                if i != prow && self.work[i] != 0.0 {
                    vec.push((i, -self.work[i] * inv));
                }
                self.work[i] = 0.0; // sparse reset for the next column.
            }
            // Skip a pure-identity eta (diag==1, empty vec): its action is identity.
            if !(vec.is_empty() && (inv - 1.0).abs() <= 1e-15) {
                self.etas.push(Eta {
                    p: prow,
                    diag: inv,
                    vec,
                });
            }
            self.rf_row_used[prow] = true;
            self.rf_new_basis[prow] = q;
        }

        // Return the column-list buffer for reuse.
        self.rf_cols = cols;

        if !ok || self.rf_new_basis.contains(&usize::MAX) {
            // Refactor failed (singular / incomplete): restore the prior eta-file.
            // `basis`/`basic_row` are untouched on this path, so they stay valid.
            self.etas = saved_etas;
        } else {
            self.basis.copy_from_slice(&self.rf_new_basis);
            // Rebuild basic_row from the new basis; everything else is nonbasic.
            for slot in self.basic_row.iter_mut() {
                *slot = None;
            }
            for (i, &q) in self.basis.iter().enumerate() {
                self.basic_row[q] = Some(i);
            }
        }
        // Refresh the eta-nnz accounting from the (possibly rebuilt) eta-file.
        self.eta_nnz = self.etas.iter().map(|e| e.vec.len()).sum();
        self.since_refactor = 0;
    }

    /// Runs Phase I (restore bound feasibility) then Phase II (minimize `c·x`),
    /// both under a shared wall-clock `deadline` and the external `should_stop`. On
    /// timeout we stop with the best dual/primal so far — NS stays sound for any
    /// clamped dual, so a partial solve is a valid (if looser) bound, never `None`.
    ///
    /// Returns `true` iff BOTH phases ended at their own optimality (Phase I
    /// reached bound feasibility, Phase II ran out of eligible entering columns)
    /// rather than on the deadline/iteration caps — the advisory convergence
    /// signal surfaced by [`approx_dual_for_box_lp`]. Purely informational: no
    /// soundness anywhere depends on it.
    fn run(
        &mut self,
        should_stop: &dyn Fn() -> bool,
        deadline: std::time::Instant,
        target: Option<f64>,
    ) -> bool {
        // PHASE I: minimize the total bound infeasibility of the basic variables
        // (the surplus crash basis is infeasible whenever some `b_r > 0`).
        self.recompute_xb();
        let phase1 = self.simplex_loop(true, should_stop, deadline, None);
        // PHASE II: minimize the true objective `c·x`. If Phase I left residual
        // infeasibility (rare; degenerate / numerically hard, or a timeout), Phase II
        // still produces a point + duals; NS stays sound because it clamps `y` and
        // never trusts the primal.
        self.recompute_xb();
        let phase2 = self.simplex_loop(false, should_stop, deadline, target);
        phase1 == LoopExit::Optimal && phase2 == LoopExit::Optimal
    }

    /// Effective objective cost of a column under the current phase. Phase II uses
    /// the structural costs; Phase I uses cost 0 (the Phase-I objective lives in the
    /// basic-variable infeasibility directions encoded by `cb`).
    fn col_cost(&self, j: usize, phase1: bool) -> f64 {
        if phase1 {
            0.0
        } else {
            self.cost[j]
        }
    }

    /// One bounded-variable primal-simplex optimization loop. `phase1 == true`
    /// minimizes total bound infeasibility; otherwise minimizes `c·x`.
    ///
    /// Anti-cycling: Dantzig pricing (most-improving reduced cost) normally; if no
    /// strict objective progress is seen for a stretch of iterations we switch to
    /// Bland's rule (smallest eligible index) until progress resumes. The hard
    /// iteration cap + `should_stop` guarantee termination regardless.
    ///
    /// The returned [`LoopExit`] says WHY the loop ended (advisory only; every
    /// exit leaves the state usable for NS/extract exactly as before).
    fn simplex_loop(
        &mut self,
        phase1: bool,
        should_stop: &dyn Fn() -> bool,
        deadline: std::time::Instant,
        target: Option<f64>,
    ) -> LoopExit {
        let cost_tol = self.cost_tol();
        let pivot_tol = self.pivot_tol();
        let feas_tol = self.feas_tol();
        let mut bland = false;
        let mut stall = 0usize;
        let mut last_obj = f64::INFINITY;
        let mut alpha = vec![0.0f64; self.m]; // FTRAN'd entering column (dense store).
        let mut alpha_nz: Vec<usize> = Vec::with_capacity(64); // its non-zero rows.
        let mut marked = vec![false; self.m]; // dedup flags for sparse FTRAN gather.

        for iter in 0..MAX_SIMPLEX_ITERS {
            if iter % 64 == 0 && (should_stop() || std::time::Instant::now() >= deadline) {
                return LoopExit::Stopped; // partial solve; still NS-valid.
            }
            // Refactor on the fixed pivot cadence, OR early when the eta-file's fill
            // crosses the nnz cap — but in the latter case require a handful of pivots
            // since the last refactor so a genuinely dense `B^{-1}` (whose freshly
            // refactored eta-file already exceeds the cap) cannot make us refactor
            // every single iteration.
            let nnz_trigger = self.eta_nnz >= self.eta_nnz_cap && self.since_refactor >= 5;
            if self.since_refactor >= REFACTOR_EVERY || nnz_trigger {
                self.refactorize();
                self.recompute_xb();
            } else if iter > 0 && iter % REFRESH_EVERY == 0 {
                self.recompute_xb();
            }

            // Effective basic-variable cost vector `cb` for pricing, plus the current
            // (start-of-iteration) phase objective for stall detection — folded into
            // the same O(m) sweep instead of a second post-pivot pass.
            //   Phase I: +1 if basic var above upper, -1 if below lower, else 0,
            //            and the running total infeasibility (the Phase-I objective).
            //   Phase II: the structural cost of each basic variable.
            let mut obj = 0.0f64;
            if phase1 {
                for i in 0..self.m {
                    let b = self.basis[i];
                    let v = self.xb_val[i];
                    if v < self.lower[b] - feas_tol {
                        self.cb[i] = -1.0; // below lower: increasing it cuts infeasibility.
                        obj += self.lower[b] - v;
                    } else if v > self.upper[b] + feas_tol {
                        self.cb[i] = 1.0; // above upper.
                        obj += v - self.upper[b];
                    } else {
                        self.cb[i] = 0.0;
                    }
                }
                if obj <= feas_tol {
                    return LoopExit::Optimal; // bound-feasible: Phase I complete.
                }
            } else {
                for i in 0..self.m {
                    let b = self.basis[i];
                    self.cb[i] = self.cost[b];
                    if b < self.n {
                        obj += self.cost[b] * self.xb_val[i];
                    }
                }
            }
            // Stall detection / Bland switch from the start-of-iteration objective
            // (equivalent signal to the post-pivot value, shifted by one iteration).
            if obj < last_obj - 1e-9 * (1.0 + self.scale) {
                last_obj = obj;
                stall = 0;
                bland = false;
            } else {
                stall += 1;
                // Switch to Bland's rule after `min(m, CAP) + 50` non-improving
                // iterations. Tracking `m + 50` on small/medium instances preserves the
                // generous Dantzig allowance that converges fast there; the `CAP` keeps
                // the threshold from scaling to tens of thousands on high-row instances,
                // where it would otherwise never engage anti-cycling before the deadline
                // (the 200-var / 17k-row failure mode).
                if stall > self.m.min(STALL_BEFORE_BLAND) + 50 {
                    bland = true; // switch to Bland's rule to break cycles.
                }
            }

            // Dual `y = c_B^T B^{-1}` (BTRAN over `cb`).
            self.y.copy_from_slice(&self.cb);
            self.btran_y();

            // EARLY EXIT at a caller threshold: in Phase II the pricing dual
            // above IS the dual `extract()` would return if we stopped now, so
            // once its quick-NS bound crosses `target` the caller's (exact)
            // prune re-check will almost surely pass — further iterations only
            // polish a bound whose decision is already made. Checked every 32
            // iterations (~3% overhead); `Stopped` leaves state NS-valid.
            if !phase1 && iter & 31 == 0 {
                if let Some(t) = target {
                    if self.quick_ns_bound() >= t {
                        return LoopExit::Stopped;
                    }
                }
            }

            // --- Pricing: choose an entering column and a movement direction. ---
            // A non-basic at LOWER may enter increasing (dir = +1) if reduced < 0.
            // A non-basic at UPPER may enter decreasing (dir = -1) if reduced > 0.
            // reduced[j] = col_cost(j) - y · M_j  (sparse dot per column).
            let mut entering: Option<(usize, f64)> = None; // (col, dir)
            let mut best_score = 0.0f64;
            for j in 0..self.cols {
                if self.basic_row[j].is_some() {
                    continue;
                }
                let rc = self.reduced_cost(j, phase1);
                let dir = match self.at[j] {
                    AtBound::Lower if rc < -cost_tol => 1.0,
                    AtBound::Upper if rc > cost_tol => -1.0,
                    _ => continue,
                };
                if bland {
                    entering = Some((j, dir));
                    break; // Bland: first eligible index.
                }
                let score = rc.abs();
                if score > best_score {
                    best_score = score;
                    entering = Some((j, dir));
                }
            }

            let Some((col, dir)) = entering else {
                // No eligible entering column. In Phase II this is the phase
                // optimum. In Phase I this point is only reached with residual
                // infeasibility > feas_tol (the bound-feasible exit fired
                // earlier in the same iteration, with no pivot in between),
                // i.e. the LP is primal-infeasible or numerically stuck — NOT
                // "converged". Returning Stopped makes the certified f64 tier
                // fail closed on infeasible primals (it declines to the exact
                // tier) instead of reporting a vacuous converged floor.
                return if phase1 {
                    LoopExit::Stopped
                } else {
                    LoopExit::Optimal
                };
            };

            // FTRAN the entering column: alpha = B^{-1} M_col, gathering the indices
            // of its non-zeros so the ratio test / step / eta build touch only those
            // (the entering column is sparse; this is the key high-row speed-up).
            self.ftran_sparse(col, &mut alpha, &mut alpha_nz, &mut marked);

            // --- Ratio test (bounded-variable). In Phase I a basic variable that
            //     is currently INFEASIBLE may move toward feasibility past the
            //     bound it violates; we let it travel only to the violated bound so
            //     infeasibility never increases. ---
            let col_span = self.upper[col] - self.lower[col]; // may be +inf.
            let mut min_t = col_span; // bound flip of the entering var itself.
            let mut leave_row: Option<usize> = None;
            let mut leave_to_upper = false;
            // Pivot magnitude of the currently-chosen leaving row. Among ratio-test
            // ties we keep the LARGEST pivot (numerically stable): a bigger |pivot|
            // gives a smaller eta reciprocal `1/piv`, damping product-form blow-up
            // on degenerate covering LPs. Advisory — see `consider_leave`.
            let mut best_piv = 0.0f64;

            for &i in &alpha_nz {
                let a = alpha[i];
                if a.abs() <= pivot_tol {
                    continue;
                }
                let bvar = self.basis[i];
                let cur = self.xb_val[i];
                // d(xb_i)/dt = -a * dir.
                let slope = -a * dir;
                if slope > pivot_tol {
                    // Basic var increasing: blocked by its upper bound. If it is
                    // currently below its lower bound (Phase-I infeasible), it may
                    // first reach the lower bound — treat that as the block so we
                    // do not jump past feasibility.
                    let target = if phase1 && cur < self.lower[bvar] - feas_tol {
                        self.lower[bvar]
                    } else {
                        self.upper[bvar]
                    };
                    if target.is_finite() {
                        let t = ((target - cur) / slope).max(0.0);
                        let want_upper = !(phase1 && cur < self.lower[bvar] - feas_tol);
                        self.consider_leave(
                            t,
                            i,
                            want_upper,
                            bland,
                            a.abs(),
                            &mut min_t,
                            &mut best_piv,
                            &mut leave_row,
                            &mut leave_to_upper,
                        );
                    }
                } else if slope < -pivot_tol {
                    // Basic var decreasing: blocked by its lower bound. If currently
                    // above its upper bound (Phase-I infeasible), the upper bound is
                    // the first block.
                    let target = if phase1 && cur > self.upper[bvar] + feas_tol {
                        self.upper[bvar]
                    } else {
                        self.lower[bvar]
                    };
                    if target.is_finite() {
                        let t = ((target - cur) / slope).max(0.0);
                        let want_upper = phase1 && cur > self.upper[bvar] + feas_tol;
                        self.consider_leave(
                            t,
                            i,
                            want_upper,
                            bland,
                            a.abs(),
                            &mut min_t,
                            &mut best_piv,
                            &mut leave_row,
                            &mut leave_to_upper,
                        );
                    }
                }
            }

            if !min_t.is_finite() {
                // Unbounded movement (no basic var blocks and the entering var has
                // no finite opposite bound). Cannot happen with the [0,1] box on
                // structurals and surpluses bounded below; guard anyway and stop.
                return LoopExit::Stopped;
            }

            // --- Apply the step: move the entering variable by `dir * min_t`,
            //     update every basic value, then pivot if a variable left. ---
            let step = dir * min_t;
            if step != 0.0 {
                for &i in &alpha_nz {
                    let a = alpha[i];
                    if a != 0.0 {
                        self.xb_val[i] -= a * step;
                    }
                }
            }

            match leave_row {
                None => {
                    // Bound flip: the entering variable swaps to its other bound; no
                    // basis change. Its movement was already folded into xb_val.
                    self.at[col] = match self.at[col] {
                        AtBound::Lower => AtBound::Upper,
                        AtBound::Upper => AtBound::Lower,
                    };
                }
                Some(prow) => {
                    let piv = alpha[prow];
                    // Reject not just an exactly-zero pivot but any pivot below a
                    // relative floor: the eta reciprocal `1/piv` for a tiny `|piv|`
                    // is enormous, and appending that eta is what blows the
                    // product-form inverse up (the −2.2M dual-drift on degenerate
                    // covering LPs). Treating it as a bound flip keeps the basis
                    // and the eta-file well-conditioned. Bound work only.
                    let piv_floor = 1e-8 * (1.0 + self.scale);
                    if !piv.is_finite() || piv.abs() <= piv_floor {
                        // Degenerate pivot guard: treat as a bound flip rather than
                        // forming a blown-up eta. Bookkeeping stays consistent.
                        self.at[col] = match self.at[col] {
                            AtBound::Lower => AtBound::Upper,
                            AtBound::Upper => AtBound::Lower,
                        };
                    } else {
                        let leaving = self.basis[prow];
                        // Value the entering variable takes once basic = bound + step.
                        let entering_value = self.nonbasic_value(col) + step;
                        // Append the eta from the FTRAN'd column's non-zeros (sparse).
                        let inv = 1.0 / piv;
                        let mut evec = Vec::with_capacity(alpha_nz.len());
                        for &i in &alpha_nz {
                            if i != prow && alpha[i] != 0.0 {
                                evec.push((i, -alpha[i] * inv));
                            }
                        }
                        self.eta_nnz += evec.len();
                        self.etas.push(Eta {
                            p: prow,
                            diag: inv,
                            vec: evec,
                        });
                        self.since_refactor += 1;
                        // Basis bookkeeping.
                        self.basic_row[leaving] = None;
                        self.at[leaving] = if leave_to_upper {
                            AtBound::Upper
                        } else {
                            AtBound::Lower
                        };
                        self.basis[prow] = col;
                        self.basic_row[col] = Some(prow);
                        // The pivot row's basic value is now the entering variable's.
                        self.xb_val[prow] = entering_value;
                    }
                }
            }

            // Sparse-reset `alpha` (only the entries the FTRAN touched) so the next
            // iteration starts from a clean zero vector without an O(m) wipe.
            for &i in &alpha_nz {
                alpha[i] = 0.0;
            }
        }
        LoopExit::Stopped // iteration cap.
    }

    /// Reduced cost of column `j` under the current phase: `col_cost(j) - y · M_j`,
    /// using the sparse `A`-column for structurals and the implicit `-e_r` for
    /// surplus `n+r` (so `y · M_{n+r} = -y_r`, giving reduced cost `col_cost - (-y_r)`;
    /// surplus cost is 0 in both phases, so this is just `y_r`).
    fn reduced_cost(&self, j: usize, phase1: bool) -> f64 {
        if j < self.n {
            let mut dot = 0.0f64;
            for p in self.col_ptr[j]..self.col_ptr[j + 1] {
                dot += self.y[self.col_idx[p]] * self.col_val[p];
            }
            self.col_cost(j, phase1) - dot
        } else {
            // surplus n+r: col_cost 0; y·M = -y_r; reduced = 0 - (-y_r) = y_r.
            self.y[j - self.n]
        }
    }

    /// Records a candidate leaving row in the ratio test, honoring the Bland
    /// tie-break (smaller leaving basis index) when `bland` is set.
    #[allow(clippy::too_many_arguments)]
    fn consider_leave(
        &self,
        t: f64,
        i: usize,
        to_upper: bool,
        bland: bool,
        piv_mag: f64,
        min_t: &mut f64,
        best_piv: &mut f64,
        leave_row: &mut Option<usize>,
        leave_to_upper: &mut bool,
    ) {
        // Relative tie window (Harris-style): ratios within `tie_tol` of the
        // current minimum are treated as tied. Among tied candidates we pick a
        // LEAVING row for numerical stability — the largest pivot magnitude —
        // unless Bland anti-cycling is engaged, which needs its own strict
        // smallest-index rule to guarantee termination. Choosing a tied (not
        // strictly-smaller) ratio can nudge the true blocker past its bound by at
        // most `tie_tol * |slope|` << feas_tol; that residual is absorbed by the
        // feasibility tolerance and periodic exact recompute, and NS re-derives a
        // SOUND bound from the clamped dual regardless — so this is bound work
        // only, never soundness.
        let tie_tol = 1e-9 * (1.0 + min_t.abs());
        let take = if t < *min_t - tie_tol {
            true
        } else if (t - *min_t).abs() <= tie_tol {
            if bland {
                self.bland_pref(i, *leave_row)
            } else {
                leave_row.is_none() || piv_mag > *best_piv
            }
        } else {
            false
        };
        if take {
            *min_t = t;
            *best_piv = piv_mag;
            *leave_row = Some(i);
            *leave_to_upper = to_upper;
        }
    }

    /// Bland tie-break helper: prefer the candidate leaving row whose basic
    /// variable has the smaller column index (classic Bland anti-cycling rule).
    fn bland_pref(&self, candidate_row: usize, current: Option<usize>) -> bool {
        match current {
            None => true,
            Some(cur) => self.basis[candidate_row] < self.basis[cur],
        }
    }

    /// Reads out the dual vector and primal point from the final basis.
    /// Quick (non-rigorous) NS bound from the CURRENT pricing dual `self.y`,
    /// clamped to `y⁺ ≥ 0`: `Σ_r y⁺_r·b_r + Σ_{j<n} min(0, c_j − y⁺·A_j)`
    /// (surplus columns contribute exactly 0 because their reduced cost under
    /// `y⁺ ≥ 0` is `y⁺_r ≥ 0`). Used ONLY to decide when an early stop is
    /// safe-and-useful — the caller re-derives every prune decision in exact
    /// integer arithmetic from the extracted duals, so accuracy here affects
    /// timing, never soundness.
    fn quick_ns_bound(&self) -> f64 {
        let mut bound = 0.0f64;
        for r in 0..self.m {
            let yr = self.y[r];
            if yr.is_finite() && yr > 0.0 {
                bound += yr * self.rhs[r];
            }
        }
        for j in 0..self.n {
            let mut dot = 0.0f64;
            for p in self.col_ptr[j]..self.col_ptr[j + 1] {
                let yr = self.y[self.col_idx[p]];
                if yr.is_finite() && yr > 0.0 {
                    dot += yr * self.col_val[p];
                }
            }
            let d = self.cost[j] - dot;
            if d < 0.0 {
                bound += d;
            }
        }
        bound
    }

    fn extract(&mut self, model: &LpF64) -> SimplexResult {
        // Dual `y = c_B^T B^{-1}` under the Phase-II costs (one BTRAN). The reduced
        // cost of surplus column `n+r` is `0 - y·(-e_r) = y_r`, the LP shadow price
        // of row r (>= 0 for a binding `>=` row). NS clamps `y` to `>= 0` anyway, so
        // any value here is sound.
        for i in 0..self.m {
            self.cb[i] = self.cost[self.basis[i]];
        }
        self.y.copy_from_slice(&self.cb);
        self.btran_y();
        let mut dual = vec![0.0f64; self.m];
        for r in 0..self.m {
            let yr = self.y[r];
            dual[r] = if yr.is_finite() { yr } else { 0.0 };
        }

        // Primal point: structural variable value (basic -> maintained `xb_val`,
        // else its current bound), clamped into [0,1] by the caller. Surpluses are
        // dropped (NS handles the box via its reduced-cost term).
        let mut primal = vec![0.0f64; self.n];
        for (j, slot) in primal.iter_mut().enumerate() {
            *slot = match self.basic_row[j] {
                Some(i) => self.xb_val[i],
                None => self.nonbasic_value(j),
            };
        }
        let _ = model;
        SimplexResult { dual, primal }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{PbConstraint, PbLit, PbObjective, PbRel, PbTerm};

    fn lit(var: u32) -> PbLit {
        PbLit {
            var,
            negated: false,
        }
    }
    fn neg(var: u32) -> PbLit {
        PbLit { var, negated: true }
    }
    fn term(coeff: i128, l: PbLit) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![l],
        }
    }
    fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs,
        }
    }
    fn never_stop() -> bool {
        false
    }

    // --- Brute-force oracle. Uses i128 internally so large i128 coefficients
    //     summed over up to 12 variables never overflow the oracle. ---

    fn constraint_holds(c: &PbConstraint, x: &[bool]) -> bool {
        let mut lhs: i128 = 0;
        for t in &c.terms {
            let l = t.lits[0];
            let val = if l.negated {
                !x[(l.var - 1) as usize]
            } else {
                x[(l.var - 1) as usize]
            };
            if val {
                lhs += i128::from(t.coeff);
            }
        }
        match c.rel {
            PbRel::Ge => lhs >= i128::from(c.rhs),
            PbRel::Eq => lhs == i128::from(c.rhs),
        }
    }

    fn objective_value(obj: &PbObjective, x: &[bool]) -> i128 {
        let mut total: i128 = 0;
        for t in &obj.terms {
            let l = t.lits[0];
            let val = if l.negated {
                !x[(l.var - 1) as usize]
            } else {
                x[(l.var - 1) as usize]
            };
            if val {
                total += i128::from(t.coeff);
            }
        }
        total
    }

    /// Brute-force integer optimum over all 2^n assignments (as i128, exact), or
    /// `None` if infeasible.
    fn brute_force_optimum(
        obj: &PbObjective,
        constraints: &[PbConstraint],
        n: u32,
    ) -> Option<i128> {
        let mut best: Option<i128> = None;
        for mask in 0u32..(1u32 << n) {
            let x: Vec<bool> = (0..n).map(|b| (mask >> b) & 1 == 1).collect();
            if constraints.iter().all(|c| constraint_holds(c, &x)) {
                let v = objective_value(obj, &x);
                best = Some(best.map_or(v, |b| b.min(v)));
            }
        }
        best
    }

    /// Tiny deterministic xorshift PRNG (no dev-deps).
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
        fn range(&mut self, lo: i128, hi: i128) -> i128 {
            let span = (hi - lo + 1) as u64;
            lo + (self.next() % span) as i128
        }
    }

    // --- Basic correctness / shape tests. ---

    #[test]
    fn env_gate_reads_var() {
        // The function itself works regardless of the env var; the gate only
        // governs integration. Just exercise the helper (no process-env mutation
        // to avoid cross-test races).
        let _ = safe_lp_enabled();
    }

    #[test]
    fn empty_objective_returns_none() {
        let obj = PbObjective { terms: vec![] };
        assert_eq!(safe_lp_lower_bound(&obj, &[], 3, &never_stop), None);
    }

    #[test]
    fn unconstrained_nonneg_objective_bound_is_at_most_zero() {
        // min x1 + x2, no constraints. LP optimum 0; NS must be <= 0.
        let obj = PbObjective {
            terms: vec![term(1, lit(1)), term(1, lit(2))],
        };
        let b = safe_lp_lower_bound(&obj, &[], 2, &never_stop).expect("bound");
        assert!(b <= 0, "bound {b} must be <= optimum 0");
    }

    #[test]
    fn covering_constraint_bound_sound() {
        // min x1+x2+x3 s.t. x1+x2+x3 >= 1. LP optimum 1; NS must be <= 1.
        let obj = PbObjective {
            terms: vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))],
        };
        let c = ge(vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))], 1);
        let b = safe_lp_lower_bound(&obj, &[c.clone()], 3, &never_stop).expect("bound");
        let opt = brute_force_optimum(&obj, &[c], 3).unwrap();
        assert!(i128::from(b) <= opt, "bound {b} must be <= optimum {opt}");
    }

    #[test]
    fn negated_objective_literal_handled() {
        // min ~x1 s.t. ~x1 >= 1 (x1 must be 0); optimum 1. NS must be <= 1.
        let obj = PbObjective {
            terms: vec![term(1, neg(1))],
        };
        let c = ge(vec![term(1, neg(1))], 1);
        let b = safe_lp_lower_bound(&obj, &[c], 1, &never_stop).expect("bound");
        assert!(b <= 1, "bound {b} must be <= optimum 1");
    }

    // ============================================================
    //  MANDATORY SOUNDNESS GATES
    // ============================================================

    /// Builds a random instance: returns (obj, constraints, n).
    fn random_instance(
        rng: &mut Rng,
        max_vars: u32,
        coeff_lo: i128,
        coeff_hi: i128,
    ) -> (PbObjective, Vec<PbConstraint>, u32) {
        let n: u32 = rng.range(1, i128::from(max_vars)) as u32;
        let mut obj_terms = Vec::new();
        for v in 1..=n {
            let coeff = rng.range(coeff_lo, coeff_hi);
            if coeff != 0 {
                let negated = rng.next() & 1 == 1;
                obj_terms.push(PbTerm {
                    coeff,
                    lits: vec![PbLit { var: v, negated }],
                });
            }
        }
        if obj_terms.is_empty() {
            obj_terms.push(term(1, lit(1)));
        }
        let obj = PbObjective { terms: obj_terms };

        let num_c = rng.range(0, 4);
        let mut constraints = Vec::new();
        for _ in 0..num_c {
            let mut terms = Vec::new();
            for v in 1..=n {
                let coeff = rng.range(coeff_lo, coeff_hi);
                if coeff != 0 {
                    let negated = rng.next() & 1 == 1;
                    terms.push(PbTerm {
                        coeff,
                        lits: vec![PbLit { var: v, negated }],
                    });
                }
            }
            if terms.is_empty() {
                terms.push(term(1, lit(1)));
            }
            let rhs = rng.range(coeff_lo, coeff_hi);
            let rel = if rng.next() % 4 == 0 {
                PbRel::Eq
            } else {
                PbRel::Ge
            };
            constraints.push(PbConstraint { terms, rel, rhs });
        }
        (obj, constraints, n)
    }

    /// CORE GATE 1: thousands of small random instances; NS bound NEVER exceeds the
    /// true integer optimum, and is a finite reasonable value.
    #[test]
    fn safe_lp_never_overshoots_bruteforce() {
        let mut rng = Rng(0xA11C_E555_EED1_2340);
        let mut checked = 0usize;
        let mut produced = 0usize;
        for _ in 0..3000 {
            let (obj, constraints, n) = random_instance(&mut rng, 12, -3, 4);
            let Some(opt) = brute_force_optimum(&obj, &constraints, n) else {
                continue; // infeasible: skip.
            };
            checked += 1;
            if let Some(b) = safe_lp_lower_bound(&obj, &constraints, n, &never_stop) {
                produced += 1;
                assert!(
                    i128::from(b) <= opt,
                    "SOUNDNESS VIOLATION: NS bound {b} > integer optimum {opt}\n\
                     objective={obj:?}\nconstraints={constraints:?}"
                );
                // Reasonableness: not absurdly loose like i128::MIN.
                assert!(
                    b > i128::MIN / 2,
                    "NS bound {b} is absurdly loose (near i128::MIN)"
                );
            }
        }
        assert!(
            checked > 1000,
            "expected many feasible instances, got {checked}"
        );
        assert!(
            produced > 500,
            "expected the NS bound to be produced often, got {produced}"
        );
        eprintln!("safe_lp_never_overshoots_bruteforce: checked={checked} produced={produced}");
    }

    /// CORE GATE 2: LARGE coefficients — where f64 error is largest. NS bound must
    /// still NEVER exceed the true integer optimum. Mixes near-int-range and ~1e6+
    /// magnitudes (including values not exactly f64-representable) plus near-tight
    /// rows. Magnitudes are kept so the i128 oracle and i128 API never overflow:
    /// per-coeff <= 5e16, n <= 9, so the objective sum stays well within i128.
    #[test]
    fn safe_lp_adversarial_large_coeffs() {
        let mut rng = Rng(0xDEAD_BEEF_CAFE_F00D);
        let mut checked = 0usize;
        let mut produced = 0usize;
        // Magnitude regimes. The largest exceeds 2^53 so coefficients are NOT
        // exactly representable in f64 — the worst case for representation error.
        let regimes: &[(i128, i128)] = &[
            (-1_000_000, 1_000_000),
            (-1_000_000_000, 1_000_000_000),
            (-9_007_199_254_740_993, 9_007_199_254_740_993), // > 2^53: not f64-exact.
            (-50_000_000_000_000_000, 50_000_000_000_000_000), // 5e16.
        ];
        for _ in 0..2500 {
            let (lo, hi) = regimes[(rng.next() as usize) % regimes.len()];
            // n <= 9: the i128 objective sum (<= 9 * 5e16 = 4.5e17) stays in range,
            // and the 2^n brute force is cheap.
            let (obj, constraints, n) = random_instance(&mut rng, 9, lo, hi);
            let Some(opt) = brute_force_optimum(&obj, &constraints, n) else {
                continue;
            };
            checked += 1;
            if let Some(b) = safe_lp_lower_bound(&obj, &constraints, n, &never_stop) {
                produced += 1;
                assert!(
                    i128::from(b) <= opt,
                    "SOUNDNESS VIOLATION (large coeffs): NS bound {b} > integer optimum {opt}\n\
                     objective={obj:?}\nconstraints={constraints:?}"
                );
            }
        }
        assert!(
            checked > 800,
            "expected many feasible instances, got {checked}"
        );
        assert!(
            produced > 300,
            "expected the NS bound produced often, got {produced}"
        );
        eprintln!("safe_lp_adversarial_large_coeffs: checked={checked} produced={produced}");
    }

    /// Degenerate / pathological shapes: equality-heavy near-tight LPs, odd
    /// (non-f64-exact) coefficient multipliers, forced rows.
    #[test]
    fn safe_lp_degenerate_cases() {
        let mut rng = Rng(0x0123_4567_89AB_CDEF);
        let mut checked = 0usize;
        for _ in 0..1500 {
            let n: u32 = rng.range(1, 8) as u32;
            let mut obj_terms = Vec::new();
            for v in 1..=n {
                let coeff = rng.range(-5, 6) * 1_000_003; // odd multiplier: not f64-exact.
                if coeff != 0 {
                    obj_terms.push(term(coeff, lit(v)));
                }
            }
            if obj_terms.is_empty() {
                obj_terms.push(term(1_000_003, lit(1)));
            }
            let obj = PbObjective { terms: obj_terms };
            let mut constraints = Vec::new();
            // An equality forcing a near-tight LP.
            let mut eq_terms = Vec::new();
            for v in 1..=n {
                eq_terms.push(term(rng.range(1, 4), lit(v)));
            }
            let eq_rhs = rng.range(0, i128::from(n) * 3);
            constraints.push(PbConstraint {
                terms: eq_terms,
                rel: PbRel::Eq,
                rhs: eq_rhs,
            });
            let Some(opt) = brute_force_optimum(&obj, &constraints, n) else {
                continue;
            };
            checked += 1;
            if let Some(b) = safe_lp_lower_bound(&obj, &constraints, n, &never_stop) {
                assert!(
                    i128::from(b) <= opt,
                    "SOUNDNESS VIOLATION (degenerate): NS bound {b} > optimum {opt}\n\
                     objective={obj:?}\nconstraints={constraints:?}"
                );
            }
        }
        assert!(checked > 200, "expected feasible instances, got {checked}");
        eprintln!("safe_lp_degenerate_cases: checked={checked}");
    }

    /// CORE GATE 3: vs the EXACT rational LP bound. The hard property is still
    /// `safe_bound <= true_integer_optimum`. We additionally assert the safe bound
    /// never EXCEEDS the exact LP bound (exact returns ceil(LP*); safe floors
    /// NS <= LP* <= ceil(LP*)); a safe bound above exact is a red flag.
    #[test]
    fn safe_lp_vs_exact() {
        use crate::optimize::lp_bound::lp_lower_bound;
        let mut rng = Rng(0xFACE_FEED_0000_9999);
        let mut compared = 0usize;
        let mut both = 0usize;
        for _ in 0..2000 {
            let (obj, constraints, n) = random_instance(&mut rng, 10, -4, 5);
            let Some(opt) = brute_force_optimum(&obj, &constraints, n) else {
                continue;
            };
            compared += 1;
            let safe = safe_lp_lower_bound(&obj, &constraints, n, &never_stop);
            let exact = lp_lower_bound(&obj, &constraints, n, &never_stop);
            if let Some(safe) = safe {
                assert!(
                    i128::from(safe) <= opt,
                    "SOUNDNESS VIOLATION: safe {safe} > optimum {opt}\nobj={obj:?}\ncons={constraints:?}"
                );
                if let Some(exact) = exact {
                    both += 1;
                    assert!(
                        safe <= exact,
                        "RED FLAG: safe bound {safe} exceeds exact LP bound {exact} \
                         (safe floors NS <= LP* <= ceil(LP*) = exact)\n\
                         obj={obj:?}\ncons={constraints:?}"
                    );
                }
            }
        }
        assert!(
            compared > 500,
            "expected feasible instances, got {compared}"
        );
        assert!(both > 200, "expected exact+safe overlap often, got {both}");
        eprintln!("safe_lp_vs_exact: compared={compared} both_produced={both}");
    }

    /// The safe bound must be non-trivially tight on an easy instance.
    #[test]
    fn safe_lp_is_reasonably_tight() {
        // min 3x1 + 5x2 s.t. x1 + x2 >= 1. LP optimum picks x1=1 -> 3.
        let obj = PbObjective {
            terms: vec![term(3, lit(1)), term(5, lit(2))],
        };
        let c = ge(vec![term(1, lit(1)), term(1, lit(2))], 1);
        let b = safe_lp_lower_bound(&obj, &[c], 2, &never_stop).expect("bound");
        assert!(b <= 3, "bound {b} must be <= optimum 3");
        assert!(b >= 2, "bound {b} should be tight (close to LP optimum 3)");
    }

    /// Fractional relaxation: min x1+x2 s.t. 2x1+2x2>=3. LP* = 3/2, integer opt 2.
    #[test]
    fn safe_lp_fractional_relaxation_floor() {
        let obj = PbObjective {
            terms: vec![term(1, lit(1)), term(1, lit(2))],
        };
        let c = ge(vec![term(2, lit(1)), term(2, lit(2))], 3);
        let b = safe_lp_lower_bound(&obj, &[c], 2, &never_stop).expect("bound");
        assert!(b <= 2, "bound {b} must be <= integer optimum 2");
    }

    /// Speed sanity (not a hard timing assertion): a moderately sized synthetic
    /// instance should be solved by the f64 path in well under a second.
    #[test]
    fn safe_lp_handles_moderate_instance_quickly() {
        let n = 200u32;
        let mut obj_terms = Vec::new();
        for v in 1..=n {
            obj_terms.push(term(i128::from(v % 7 + 1), lit(v)));
        }
        let obj = PbObjective { terms: obj_terms };
        // A handful of covering rows over disjoint windows.
        let mut constraints = Vec::new();
        let mut start = 1u32;
        while start + 9 <= n {
            let terms: Vec<PbTerm> = (start..start + 10).map(|v| term(1, lit(v))).collect();
            constraints.push(ge(terms, 3));
            start += 10;
        }
        let t = std::time::Instant::now();
        let b = safe_lp_lower_bound(&obj, &constraints, n, &never_stop);
        let elapsed = t.elapsed();
        eprintln!("safe_lp moderate instance ({n} vars): {b:?} in {elapsed:?}");
        assert!(b.is_some(), "expected a bound on the moderate instance");
        // Generous ceiling; the f64 simplex should be far faster than this.
        assert!(elapsed.as_secs() < 10, "f64 LP took too long: {elapsed:?}");
    }

    /// Rough speed comparison vs the exact-rational `lp_lower_bound` on a
    /// mid-size structured covering instance. Ignored by default (timing-only).
    #[test]
    #[ignore = "manual speed comparison (exact rational vs NS f64)"]
    fn safe_lp_vs_exact_speed() {
        use crate::optimize::lp_bound::lp_lower_bound;
        // A dense weighted knapsack/cover instance: varied coefficients across
        // many overlapping rows. Dense varied-coefficient LPs are where the
        // exact-rational simplex's big-integer numerators blow up, so this is a
        // fairer stress of the rational path's slowness.
        let n = 800u32;
        let mut obj_terms = Vec::new();
        for v in 1..=n {
            obj_terms.push(term(i128::from((v * 37) % 101 + 1), lit(v)));
        }
        let obj = PbObjective { terms: obj_terms };
        let mut constraints = Vec::new();
        // Dense rows with varied coefficients (every variable in each row).
        for r in 0..120u32 {
            let terms: Vec<PbTerm> = (1..=n)
                .map(|v| term(i128::from(((v + r) * 7) % 23 + 1), lit(v)))
                .collect();
            // rhs scaled to a fraction of the max possible -> fractional optimum.
            let rhs = i128::from(n) * 4;
            constraints.push(ge(terms, rhs));
        }
        eprintln!("speed instance: {n} vars, {} rows", constraints.len());

        let t = std::time::Instant::now();
        let exact = lp_lower_bound(&obj, &constraints, n, &never_stop);
        let t_exact = t.elapsed();

        let t = std::time::Instant::now();
        let safe = safe_lp_lower_bound(&obj, &constraints, n, &never_stop);
        let t_safe = t.elapsed();

        eprintln!("exact lp_lower_bound = {exact:?} in {t_exact:?}");
        eprintln!("safe NS bound        = {safe:?} in {t_safe:?}");
        if let (Some(e), Some(s)) = (exact, safe) {
            assert!(s <= e, "safe {s} must be <= exact {e}");
        }
    }

    /// TIGHTNESS / TIMING on real competition instances. Loads the Charlotte
    /// routing instance (true LP optimum ~4996) and the 6.4k-var kidney-exchange
    /// instance, prints the safe NS bound + primal-point time for each, and
    /// asserts the *qualitative* targets: Charlotte's bound is strongly positive
    /// (the simplex now produces good duals, not the old `-1`) and KE returns a
    /// bound (not `None`) above the old 5k-var size cap. Ignored by default
    /// because it depends on benchmark files being present on disk; run with
    /// `--ignored` to see the numbers. Skips silently if a file is absent.
    #[test]
    #[ignore = "loads on-disk competition benchmarks; run with --ignored for tightness numbers"]
    fn safe_lp_tightness_on_competition_instances() {
        use crate::parser::parse_opb;

        fn load(rel: &str) -> Option<crate::types::PbInstance> {
            // Resolve under $AY_PBCOMP_BENCH_ROOT (default: the checkout-relative
            // benchmarks/pb-comp; the corpus is not tracked in git). Prefer the
            // already-decompressed .opb; fall back to nothing (the harness
            // decompresses .xz out of band, so we just skip if missing).
            let root = std::env::var_os("AY_PBCOMP_BENCH_ROOT")
                .map(std::path::PathBuf::from)
                .unwrap_or_else(|| {
                    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                        .join("../../benchmarks/pb-comp")
                });
            let text = std::fs::read_to_string(root.join(rel)).ok()?;
            parse_opb(&text).ok()
        }

        let charlotte = "PB25/normalized-PB25/OPT-LIN/wallon/normalized-Charlotte-06-2_c24.opb";
        if let Some(inst) = load(charlotte) {
            let obj = inst.objective.expect("Charlotte has an objective");
            let t = std::time::Instant::now();
            let (bound, point) =
                safe_lp_bound_and_point(&obj, &inst.constraints, inst.num_vars, &never_stop);
            let elapsed = t.elapsed();
            eprintln!(
                "Charlotte ({} vars, {} cons): safe_lp bound = {:?}, point.is_some()={} in {:?}",
                inst.num_vars,
                inst.constraints.len(),
                bound,
                point.is_some(),
                elapsed
            );
            // The OLD Big-M simplex returned -1 here; the bounded-variable simplex
            // should now give a strongly positive bound (true LP ~4996).
            assert!(
                bound.is_some_and(|b| b > 1000),
                "Charlotte bound {bound:?} should be strongly positive (true LP ~4996)"
            );
        } else {
            eprintln!("Charlotte instance absent; skipping that leg.");
        }

        let ke = "PB24/normalized-PB24/OPT-LIN/\
                  pettersson/StableMatchings/KidneyTransplantBenchmarks/\
                  normalized-KE_230_000.opb";
        if let Some(inst) = load(ke) {
            let obj = inst.objective.expect("KE has an objective");
            let t = std::time::Instant::now();
            let (bound, point) =
                safe_lp_bound_and_point(&obj, &inst.constraints, inst.num_vars, &never_stop);
            let elapsed = t.elapsed();
            eprintln!(
                "KE_230_000 ({} vars, {} cons): safe_lp bound = {:?}, point.is_some()={} in {:?}",
                inst.num_vars,
                inst.constraints.len(),
                bound,
                point.is_some(),
                elapsed
            );
            // The old 5k-var cap returned None for this 6.4k-var instance; now we
            // should get a real bound.
            assert!(
                bound.is_some(),
                "KE_230_000 should now return a bound (was None under the old size cap)"
            );
        } else {
            eprintln!("KE_230_000 instance absent; skipping that leg.");
        }

        // High-ROW stress: ~17k sparse constraints over only 200 variables. This is
        // the regime the sparse revised simplex targets (few columns, many rows): the
        // old dense tableau was hopeless here. Should now return a bound quickly.
        let twoclub = "PB24/normalized-PB24/\
                       OPT-LIN/nordstrom/MIPLIB01/opt/miplib2017/\
                       normalized-2club200v15p5scn.opb";
        if let Some(inst) = load(twoclub) {
            let obj = inst.objective.expect("2club has an objective");
            let t = std::time::Instant::now();
            let (bound, point) =
                safe_lp_bound_and_point(&obj, &inst.constraints, inst.num_vars, &never_stop);
            let elapsed = t.elapsed();
            eprintln!(
                "2club ({} vars, {} cons): safe_lp bound = {:?}, point.is_some()={} in {:?}",
                inst.num_vars,
                inst.constraints.len(),
                bound,
                point.is_some(),
                elapsed
            );
            assert!(
                bound.is_some(),
                "2club (~17k rows) should now return a bound in reasonable time"
            );
        } else {
            eprintln!("2club instance absent; skipping that leg.");
        }
    }
}
