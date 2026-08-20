// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! **Single-row closure (SRC) cuts** — separation over the EXACT integer hull of
//! one constraint at a time.
//!
//! # What this family is
//!
//! The cut families in [`crate::optimize::cutting_planes`] each emit one
//! *structured* inequality per row (a minimal cover, a lifted cover, a CG
//! rounding). This module instead separates over `conv(Z_r)` itself, where
//!
//! ```text
//! Z_r = { z in {0,1}^{S_r} : a·z >= b }
//! ```
//!
//! is the feasible set of a single row written in non-negative `>=` (covering)
//! form. Anything a cover/lifted-cover/CG generator can produce from row `r` is
//! a valid inequality for `conv(Z_r)`, so separating over `conv(Z_r)` directly
//! dominates all of them *for that row*. The intersection over all rows is the
//! **single-row closure** of the instance.
//!
//! # The structure that makes it tractable
//!
//! `Z_r` is UP-MONOTONE: coefficients are non-negative, so flipping a `0` to a
//! `1` never leaves the set. Two consequences:
//!
//! * every non-trivial facet of `conv(Z_r)` normalizes to `alpha·z >= 1` with
//!   `alpha >= 0` (a facet with a negative coefficient would be violated by
//!   raising that coordinate, and the right-hand side can be scaled to 1 because
//!   `0 notin Z_r` whenever `b > 0`);
//! * `alpha·z >= 1` is valid for `Z_r` **iff** it holds on the MINIMAL points of
//!   `Z_r` (a point where zeroing any selected coordinate breaks the row) — every
//!   other feasible point dominates a minimal one coordinate-wise.
//!
//! So separation of a fractional `x*` reduces to the tiny covering LP
//!
//! ```text
//! min alpha·x*_{S_r}   s.t.   alpha·p >= 1 for every minimal p,   alpha >= 0
//! ```
//!
//! whose optimum is `< 1` exactly when some valid `alpha·z >= 1` cuts off `x*`.
//!
//! # Soundness: a heuristic separator that cannot emit an invalid cut
//!
//! The LP above is solved in `f64` by the small dense simplex in this module, and
//! `f64` is never trusted. Two mechanical guards stand between it and an emitted
//! row:
//!
//! 1. **Round UP, never down.** The float `alpha` is scaled to integers by
//!    `ceil(alpha_j * D)`. Raising a non-negative coefficient can only raise
//!    `alpha·p`, so rounding up moves *towards* validity. (Rounding down would be
//!    unsound — see `src_cut_validity_fails_when_rounding_down` in the tests,
//!    which is the negative control for exactly this.)
//! 2. **Re-prove from scratch.** Every emitted cut is re-verified in exact `i128`
//!    arithmetic against *every* minimal point of its parent row before it
//!    leaves this module. A cut that fails is DROPPED.
//!
//! A bad `alpha` therefore yields a weak cut or no cut, never an invalid one —
//! which is what licenses using floating point to *choose* the cut at all. The
//! downstream exact-rational consumers in [`crate::optimize::lp_bound`] — the
//! Lagrangian subgradient cut loop, the simplex cut loop behind
//! `lp_lower_bound`, and the reduced-cost-fixing loop — then certify the bound
//! over originals-plus-cuts with no changes.
//!
//! # Cost control
//!
//! Minimal-point enumeration is exponential in the row's support, so it is
//! computed ONCE per row at [`SingleRowClosure::build`] time and reused across
//! every separation round. Rows wider than [`MAX_SRC_SUPPORT`] are skipped
//! outright, and the enumeration additionally fails closed on a node budget and a
//! minimal-point cap, so a pathological row costs a bounded amount and yields no
//! cut rather than blowing the time budget.

use std::collections::{BTreeMap, HashSet};

use crate::optimize::cutting_planes::{cut_key, lit_value, CutKey, FractionalPoint};
use crate::types::{PbConstraint, PbLit, PbRel, PbTerm};

/// Maximum support size of a row we will build a minimal-point set for.
///
/// Enumeration is `O(2^|S_r|)` in the worst case, so this is the knob that keeps
/// a wide row from costing an unbounded amount. 20 admits every row of the
/// covering families this was built for (the `liu/domset` rows top out at 15);
/// beyond support 18 the per-row node budget below is what actually decides, and
/// a row that trips it simply produces no SRC cut — the other cut families still
/// see it.
const MAX_SRC_SUPPORT: usize = 20;
/// Maximum number of minimal points we will store for one row. A row that
/// exceeds this is skipped (its separation LP would be large and its cut weak).
const MAX_SRC_MINIMAL_POINTS: usize = 4_096;
/// Node budget for one row's minimal-point DFS. Exceeding it abandons the row.
///
/// The DFS visits only subsets whose every proper prefix is infeasible, but the
/// worst case (unit coefficients with a large rhs) really is `2^|S_r|`, so this
/// has to be a hard cap and not an estimate. `2^18` runs the enumeration to
/// completion for every row up to support 18 and fails closed above that.
const MAX_SRC_ENUM_NODES: u64 = 1 << 18;
/// Node budget for the WHOLE build across all rows. Without it, an instance made
/// of thousands of wide rows could spend the caller's entire deadline enumerating
/// (the per-row cap bounds one row, not their sum). ~16M nodes is a few hundred
/// milliseconds; past it the remaining rows are simply not indexed.
const MAX_SRC_TOTAL_ENUM_NODES: u64 = 1 << 24;
/// Cap on minimal points retained across ALL rows. Bounds the separator's memory
/// (one `u32` each) independently of the per-row cap.
const MAX_SRC_TOTAL_MINIMAL_POINTS: usize = 2_000_000;
/// Maximum number of rows we index. Bounds the one-time build cost.
const MAX_SRC_ROWS: usize = 20_000;
/// Maximum number of SRC cuts emitted in one separation round.
const MAX_SRC_CUTS_PER_ROUND: usize = 512;
/// Relative tolerance for "is this cut violated at `x*`". Purely a quality knob:
/// a missed violation costs tightness, never soundness.
const SRC_VIOLATION_TOL: f64 = 1e-6;
/// Pivot / reduced-cost tolerance of the dense separation simplex.
const SIMPLEX_EPS: f64 = 1e-9;
/// Iteration cap of the dense separation simplex. Hitting it yields no cut.
const MAX_SIMPLEX_ITERS: usize = 20_000;
/// Denominators tried, in order, when turning the float `alpha` into integer cut
/// coefficients. The first one that yields an exactly-valid AND violated cut
/// wins, so a cut whose true coefficients are `1/2`s or `1/3`s comes out with
/// small integer coefficients instead of a `10^6`-scaled approximation. The
/// `1_000_000` tail is the reference implementation's fixed scale and acts as the
/// catch-all.
const SRC_DENOMINATORS: &[i128] = &[
    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 16, 20, 24, 30, 60, 120, 720, 1_000_000,
];

/// One indexed row: its literal support in normalized covering form, plus the
/// bitmasks of the MINIMAL feasible points of that row.
struct SrcRow {
    /// Literals `z_j` of the covering view, in a stable order. `lits.len() <=
    /// MAX_SRC_SUPPORT`, so a `u32` bitmask indexes them.
    lits: Vec<PbLit>,
    /// Minimal feasible points as bitmasks over `0..lits.len()`. Never empty and
    /// never contains the empty mask.
    minimal: Vec<u32>,
}

/// A row in normalized covering form `sum coeffs_j * lits_j >= rhs` with every
/// `coeffs_j >= 1` and `rhs >= 1`.
struct GeView {
    lits: Vec<PbLit>,
    coeffs: Vec<i128>,
    rhs: i128,
}

/// Separator over the single-row closure. Built once (the expensive part) and
/// then queried each cut round.
pub(crate) struct SingleRowClosure {
    rows: Vec<SrcRow>,
    /// Cuts already handed out, so repeated rounds on a slow-moving fractional
    /// point do not spend the cut budget on duplicates.
    seen: HashSet<CutKey>,
}

impl SingleRowClosure {
    /// Indexes every row whose covering view is small enough to enumerate.
    /// Returns `None` when no row qualifies (nothing to separate).
    pub(crate) fn build(
        constraints: &[PbConstraint],
        num_vars: u32,
        should_stop: &dyn Fn() -> bool,
    ) -> Option<Self> {
        let mut rows: Vec<SrcRow> = Vec::new();
        let mut nodes_left = MAX_SRC_TOTAL_ENUM_NODES;
        let mut points_left = MAX_SRC_TOTAL_MINIMAL_POINTS;
        for (i, c) in constraints.iter().enumerate() {
            if rows.len() >= MAX_SRC_ROWS || nodes_left == 0 || points_left == 0 {
                break;
            }
            if i.is_multiple_of(16) && should_stop() {
                break;
            }
            for view in ge_views(c, num_vars) {
                let budget = nodes_left.min(MAX_SRC_ENUM_NODES);
                let mut spent = 0u64;
                let minimal = minimal_points(&view.coeffs, view.rhs, budget, &mut spent);
                nodes_left = nodes_left.saturating_sub(spent);
                let Some(minimal) = minimal else {
                    continue;
                };
                if minimal.len() > points_left {
                    points_left = 0;
                    break;
                }
                points_left -= minimal.len();
                rows.push(SrcRow {
                    lits: view.lits,
                    minimal,
                });
            }
        }
        if rows.is_empty() {
            None
        } else {
            Some(Self {
                rows,
                seen: HashSet::new(),
            })
        }
    }

    /// Number of indexed rows (diagnostics / tests).
    #[cfg(test)]
    pub(crate) fn indexed_rows(&self) -> usize {
        self.rows.len()
    }

    /// Appends SRC cuts violated by `x` to `out`. Every appended cut has been
    /// re-proved valid in exact integer arithmetic against its parent row.
    pub(crate) fn separate(
        &mut self,
        x: &FractionalPoint,
        should_stop: &dyn Fn() -> bool,
        out: &mut Vec<PbConstraint>,
    ) {
        // Split the borrow so the dedup set can be mutated while iterating rows.
        let Self { rows, seen } = self;
        let mut added = 0usize;
        for (i, row) in rows.iter().enumerate() {
            if added >= MAX_SRC_CUTS_PER_ROUND {
                break;
            }
            if i.is_multiple_of(32) && should_stop() {
                break;
            }
            let Some(xs) = row_values(&row.lits, x) else {
                continue;
            };
            let Some((value, alpha)) = solve_covering_lp(&row.minimal, row.lits.len(), &xs) else {
                continue;
            };
            if value >= 1.0 - SRC_VIOLATION_TOL {
                continue;
            }
            let Some(cut) = build_cut(row, &alpha, &xs) else {
                continue;
            };
            if !seen.insert(cut_key(&cut)) {
                continue;
            }
            out.push(cut);
            added += 1;
        }
    }
}

/// Fractional values of a row's literals, as `f64` in `[0, 1]`.
fn row_values(lits: &[PbLit], x: &FractionalPoint) -> Option<Vec<f64>> {
    use num_traits::ToPrimitive;
    let mut out = Vec::with_capacity(lits.len());
    for &lit in lits {
        let v = lit_value(lit, x)?.to_f64()?;
        if !v.is_finite() {
            return None;
        }
        out.push(v.clamp(0.0, 1.0));
    }
    Some(out)
}

// ===================================================================== //
//  Covering-form normalization                                          //
// ===================================================================== //

/// Covering (`>=`, non-negative-coefficient) views of one constraint. A `Ge`
/// constraint yields one; an `Eq` yields both directions, each of which is a
/// relaxation of the equality and so a sound source of valid inequalities.
fn ge_views(c: &PbConstraint, num_vars: u32) -> Vec<GeView> {
    // EXHAUSTIVE ON PURPOSE. The forward `>=` view below is only sound for
    // relations that IMPLY `sum t >= rhs`. That holds for `Ge` trivially and for
    // `Eq`, and those are today's only variants — but writing this as
    // `if c.rel == PbRel::Eq` would let a future `Le` variant fall through to the
    // forward push and derive cuts from a false premise, silently OVERSTATING the
    // bound. Matching exhaustively makes that a compile error instead.
    let derive_forward = match c.rel {
        PbRel::Ge | PbRel::Eq => true,
    };
    let mut out = Vec::new();
    if derive_forward {
        if let Some(view) = normalize_ge_nonneg(&c.terms, c.rhs, num_vars) {
            out.push(view);
        }
    }
    if c.rel == PbRel::Eq {
        if let Some((neg_terms, neg_rhs)) = negate_terms_rhs(&c.terms, c.rhs) {
            if let Some(view) = normalize_ge_nonneg(&neg_terms, neg_rhs, num_vars) {
                out.push(view);
            }
        }
    }
    out
}

/// `sum t >= rhs` becomes `sum (-t) >= -rhs` (used for the second direction of an
/// equality). `None` on overflow or a non-linear term.
fn negate_terms_rhs(terms: &[PbTerm], rhs: i128) -> Option<(Vec<PbTerm>, i128)> {
    let mut neg = Vec::with_capacity(terms.len());
    for t in terms {
        let [lit] = t.lits.as_slice() else {
            return None;
        };
        neg.push(PbTerm {
            coeff: t.coeff.checked_neg()?,
            lits: vec![*lit],
        });
    }
    Some((neg, rhs.checked_neg()?))
}

/// Normalizes `sum coeff_i * lit_i >= rhs` into `sum a_j z_j >= b` with every
/// `a_j >= 1` and `b >= 1`, saturating `a_j` at `b`.
///
/// Saturation (`a_j -> min(a_j, b)`) leaves the 0/1 feasible set EXACTLY
/// unchanged for a non-negative `>=` row: if `z_j = 0` both forms agree, and if
/// `z_j = 1` both forms are satisfied outright (the saturated form contributes
/// `b`, the original contributes `a_j > b`). It keeps the enumerated weights
/// small.
///
/// `None` when the row is not a usable covering source: non-linear, out-of-range,
/// overflowing, wider than [`MAX_SRC_SUPPORT`], trivially satisfied (`b <= 0`),
/// or infeasible on its own (`b > sum a_j`).
fn normalize_ge_nonneg(terms: &[PbTerm], rhs: i128, num_vars: u32) -> Option<GeView> {
    let mut by_var: BTreeMap<u32, i128> = BTreeMap::new();
    let mut b = rhs;
    for t in terms {
        if t.coeff == 0 {
            continue;
        }
        let [lit] = t.lits.as_slice() else {
            return None;
        };
        if lit.var == 0 || lit.var > num_vars {
            return None;
        }
        // `coeff * ~x_v = coeff - coeff * x_v`: the constant moves to the rhs.
        let (pos_delta, rhs_delta) = if lit.negated {
            (t.coeff.checked_neg()?, t.coeff)
        } else {
            (t.coeff, 0)
        };
        b = b.checked_sub(rhs_delta)?;
        let e = by_var.entry(lit.var).or_insert(0);
        *e = e.checked_add(pos_delta)?;
    }

    let mut lits: Vec<PbLit> = Vec::new();
    let mut coeffs: Vec<i128> = Vec::new();
    for (var, coeff) in by_var {
        if coeff == 0 {
            continue;
        }
        if coeff > 0 {
            lits.push(PbLit {
                var,
                negated: false,
            });
            coeffs.push(coeff);
        } else {
            // `c * x_v = c + (-c) * ~x_v` with `c < 0`: the constant raises `b`.
            b = b.checked_sub(coeff)?;
            lits.push(PbLit { var, negated: true });
            coeffs.push(coeff.checked_neg()?);
        }
    }
    if lits.is_empty() || lits.len() > MAX_SRC_SUPPORT {
        return None;
    }
    if b <= 0 {
        return None;
    }
    let total = coeffs
        .iter()
        .try_fold(0i128, |acc, &c| acc.checked_add(c))?;
    if b > total {
        return None;
    }
    for c in coeffs.iter_mut() {
        if *c > b {
            *c = b;
        }
    }
    Some(GeView {
        lits,
        coeffs,
        rhs: b,
    })
}

// ===================================================================== //
//  Minimal-point enumeration                                            //
// ===================================================================== //

/// Bitmasks of the MINIMAL feasible points of `sum a_j z_j >= b`.
///
/// A set `T` is minimal iff `sum_{j in T} a_j >= b` and removing ANY member
/// breaks it, i.e. `sum(T) - min_{j in T} a_j < b`. The DFS below stops
/// extending as soon as a prefix becomes feasible, which is exactly right: every
/// minimal `T` has all its proper subsets infeasible, so the DFS reaches it, and
/// no superset of a feasible set can be minimal.
///
/// `budget` caps the DFS nodes this call may visit; `spent` is incremented by the
/// number actually visited so the caller can bound the TOTAL build cost.
///
/// `None` on an empty result (nothing to separate) or when a budget trips.
fn minimal_points(a: &[i128], b: i128, budget: u64, spent: &mut u64) -> Option<Vec<u32>> {
    let k = a.len();
    if k == 0 || k > MAX_SRC_SUPPORT || b <= 0 {
        return None;
    }
    let mut suffix = vec![0i128; k + 1];
    for j in (0..k).rev() {
        suffix[j] = suffix[j + 1].checked_add(a[j])?;
    }
    if suffix[0] < b {
        return None;
    }

    let mut out: Vec<u32> = Vec::new();
    let mut nodes: u64 = 0;
    let mut stack: Vec<(usize, i128, u32)> = vec![(0, 0, 0)];
    while let Some((j, sum, mask)) = stack.pop() {
        nodes += 1;
        if nodes > budget {
            *spent += nodes;
            return None;
        }
        if sum >= b {
            let mut min_a = i128::MAX;
            for (i, &ai) in a.iter().enumerate() {
                if mask >> i & 1 == 1 && ai < min_a {
                    min_a = ai;
                }
            }
            if min_a != i128::MAX && sum - min_a < b {
                if out.len() >= MAX_SRC_MINIMAL_POINTS {
                    *spent += nodes;
                    return None;
                }
                out.push(mask);
            }
            continue;
        }
        if j >= k || sum + suffix[j] < b {
            continue;
        }
        stack.push((j + 1, sum, mask));
        stack.push((j + 1, sum + a[j], mask | (1u32 << j)));
    }
    *spent += nodes;
    if out.is_empty() {
        None
    } else {
        Some(out)
    }
}

// ===================================================================== //
//  Separation LP (dense simplex, self-contained)                        //
// ===================================================================== //

/// Solves the separation LP
///
/// ```text
/// min c·alpha   s.t.   M alpha >= 1,  alpha >= 0
/// ```
///
/// where `M` is the 0/1 incidence matrix of `masks` (rows) against `0..k`
/// (columns) and `c >= 0`. Returns `(optimum, alpha)`.
///
/// # Why the dual is solved instead
///
/// The covering primal has no obvious feasible basis (it needs a phase 1), while
/// its dual
///
/// ```text
/// max 1·u   s.t.   M^T u <= c,  u >= 0
/// ```
///
/// is feasible at the origin, so the all-slack basis starts a plain primal
/// simplex. The primal is feasible (`alpha = 1` is), hence the dual is bounded
/// and the method terminates at an optimum. At that optimum the reduced cost of
/// slack `j` is exactly `alpha_j`, and the objective value is the covering
/// optimum. Bland's rule takes over after a warm-up so a degenerate instance
/// (very common here: `c_j = 0` whenever `x*_j = 0`) cannot cycle.
///
/// `None` on any anomaly (negative `c`, unbounded ratio test, iteration cap,
/// non-finite readout) — a missing cut is always acceptable.
fn solve_covering_lp(masks: &[u32], k: usize, c: &[f64]) -> Option<(f64, Vec<f64>)> {
    let p = masks.len();
    if p == 0 || k == 0 || k > MAX_SRC_SUPPORT || c.len() != k {
        return None;
    }
    let ncols = p.checked_add(k)?;
    let width = ncols.checked_add(1)?;
    let cells = width.checked_mul(k.checked_add(1)?)?;
    let mut tab = vec![0.0f64; cells];
    for (j, &cj) in c.iter().enumerate() {
        if cj.is_nan() || cj < 0.0 {
            return None;
        }
        let base = j * width;
        for (i, &m) in masks.iter().enumerate() {
            if m >> j & 1 == 1 {
                tab[base + i] = 1.0;
            }
        }
        tab[base + p + j] = 1.0;
        tab[base + ncols] = cj;
    }
    let obj = k * width;
    for i in 0..p {
        tab[obj + i] = -1.0;
    }

    let mut basis: Vec<usize> = (0..k).map(|j| p + j).collect();
    let warmup = 4 * width;
    let mut optimal = false;
    for iter in 0..MAX_SIMPLEX_ITERS {
        // Entering column: Dantzig while making progress, Bland once we might be
        // cycling (Bland's rule guarantees termination).
        let bland = iter >= warmup;
        let mut enter: Option<usize> = None;
        let mut best = -SIMPLEX_EPS;
        for col in 0..ncols {
            let d = tab[obj + col];
            if d < -SIMPLEX_EPS {
                if bland {
                    enter = Some(col);
                    break;
                }
                if d < best {
                    best = d;
                    enter = Some(col);
                }
            }
        }
        let Some(e) = enter else {
            optimal = true;
            break;
        };

        // Ratio test, tie-broken on the smallest leaving basis index (Bland).
        let mut leave: Option<usize> = None;
        let mut best_ratio = f64::INFINITY;
        for j in 0..k {
            let aij = tab[j * width + e];
            if aij <= SIMPLEX_EPS {
                continue;
            }
            let ratio = tab[j * width + ncols] / aij;
            let better = match leave {
                None => true,
                Some(r) => {
                    ratio < best_ratio - 1e-12
                        || (ratio <= best_ratio + 1e-12 && basis[j] < basis[r])
                }
            };
            if better {
                best_ratio = ratio.min(best_ratio);
                leave = Some(j);
            }
        }
        let Some(r) = leave else {
            return None; // unbounded: cannot happen for a feasible primal
        };

        let piv = tab[r * width + e];
        if !piv.is_finite() || piv.abs() <= SIMPLEX_EPS {
            return None;
        }
        for col in 0..width {
            tab[r * width + col] /= piv;
        }
        for j in 0..=k {
            if j == r {
                continue;
            }
            let f = tab[j * width + e];
            if f == 0.0 {
                continue;
            }
            for col in 0..width {
                let v = tab[r * width + col];
                tab[j * width + col] -= f * v;
            }
        }
        basis[r] = e;
    }
    if !optimal {
        return None;
    }

    let value = tab[obj + ncols];
    if !value.is_finite() {
        return None;
    }
    let mut alpha = Vec::with_capacity(k);
    for j in 0..k {
        let a = tab[obj + p + j];
        if !a.is_finite() {
            return None;
        }
        alpha.push(a.max(0.0));
    }
    Some((value, alpha))
}

// ===================================================================== //
//  Rounding and exact re-proof                                          //
// ===================================================================== //

/// Turns a float `alpha` into an integer cut, trying the denominators in
/// [`SRC_DENOMINATORS`] in increasing order and returning the first that is BOTH
/// exactly valid for the parent row and violated at `x*`.
fn build_cut(row: &SrcRow, alpha: &[f64], xs: &[f64]) -> Option<PbConstraint> {
    SRC_DENOMINATORS
        .iter()
        .find_map(|&den| cut_at_denominator(row, alpha, xs, den, Rounding::Up))
}

/// Direction used to turn the float `alpha` into integers. Only [`Rounding::Up`]
/// is sound; [`Rounding::Down`] exists solely as the negative control that proves
/// the exact re-proof below is actually load-bearing.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Rounding {
    Up,
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "negative control for the validity test")
    )]
    Down,
}

/// Builds, strengthens and EXACTLY re-proves one candidate cut at scale `den`.
///
/// Steps, in order:
/// 1. scale `alpha` to integers (rounding per `mode`) and saturate at `den`;
/// 2. divide through by the coefficient gcd, taking `ceil` on the rhs — a
///    Chvátal-Gomory division that is valid because the lhs is integral, and that
///    keeps the emitted coefficients small;
/// 3. **re-prove validity in exact `i128` against every minimal point** of the
///    parent row, dropping the cut on any failure;
/// 4. require an actual violation at `x*` so the cut budget buys tightening.
fn cut_at_denominator(
    row: &SrcRow,
    alpha: &[f64],
    xs: &[f64],
    den: i128,
    mode: Rounding,
) -> Option<PbConstraint> {
    let k = row.lits.len();
    if alpha.len() != k || xs.len() != k || den <= 0 {
        return None;
    }
    let denf = den as f64;
    let mut coeffs = vec![0i128; k];
    for (j, &aj) in alpha.iter().enumerate() {
        if !aj.is_finite() || aj < 0.0 {
            return None;
        }
        let scaled = match mode {
            Rounding::Up => (aj * denf).ceil(),
            Rounding::Down => (aj * denf).floor(),
        };
        if !scaled.is_finite() {
            return None;
        }
        coeffs[j] = if scaled >= denf {
            den
        } else if scaled <= 0.0 {
            0
        } else {
            scaled as i128
        };
    }

    let mut rhs = den;
    let g = coeffs.iter().fold(0i128, |acc, &c| gcd(acc, c));
    if g == 0 {
        return None;
    }
    if g > 1 {
        for c in coeffs.iter_mut() {
            *c /= g;
        }
        rhs = rhs.checked_add(g - 1)? / g;
    }
    if rhs <= 0 {
        return None;
    }

    // EXACT re-proof. This is the guard that makes the float separator safe.
    for &mask in &row.minimal {
        let mut sum = 0i128;
        for (j, &cj) in coeffs.iter().enumerate() {
            if mask >> j & 1 == 1 {
                sum = sum.checked_add(cj)?;
            }
        }
        if sum < rhs {
            return None;
        }
    }

    let lhs: f64 = coeffs
        .iter()
        .zip(xs.iter())
        .map(|(&c, &v)| c as f64 * v)
        .sum();
    if lhs >= rhs as f64 * (1.0 - SRC_VIOLATION_TOL) {
        return None;
    }

    let terms: Vec<PbTerm> = coeffs
        .iter()
        .zip(row.lits.iter())
        .filter(|(&c, _)| c != 0)
        .map(|(&c, &lit)| PbTerm {
            coeff: c,
            lits: vec![lit],
        })
        .collect();
    if terms.is_empty() {
        return None;
    }
    Some(PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs,
    })
}

fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_rational::BigRational;
    use num_traits::{One, Zero};

    fn never_stop() -> bool {
        false
    }

    /// Test shim: run the enumeration with a full budget and discard the count.
    fn mins(a: &[i128], b: i128) -> Option<Vec<u32>> {
        let mut spent = 0u64;
        minimal_points(a, b, MAX_SRC_ENUM_NODES, &mut spent)
    }

    fn frac(num: i64, den: i64) -> BigRational {
        BigRational::new(num.into(), den.into())
    }

    fn ge(coeffs: &[(u32, i128)], rhs: i128) -> PbConstraint {
        PbConstraint {
            terms: coeffs
                .iter()
                .map(|&(var, coeff)| PbTerm {
                    coeff,
                    lits: vec![PbLit {
                        var,
                        negated: false,
                    }],
                })
                .collect(),
            rel: PbRel::Ge,
            rhs,
        }
    }

    /// Evaluates `sum coeff * lit` of a `>=` constraint at a 0/1 assignment.
    fn eval(c: &PbConstraint, assign: &[bool]) -> i128 {
        let mut sum = 0i128;
        for t in &c.terms {
            let lit = t.lits[0];
            let v = assign[(lit.var - 1) as usize] != lit.negated;
            if v {
                sum += t.coeff;
            }
        }
        sum
    }

    #[test]
    fn minimal_points_of_a_unit_covering_row_are_the_singletons() {
        // x1 + x2 + x3 >= 1: minimal points are exactly the three singletons.
        let mins = mins(&[1, 1, 1], 1).expect("minimal points");
        let mut got: Vec<u32> = mins;
        got.sort_unstable();
        assert_eq!(got, vec![0b001, 0b010, 0b100]);
    }

    #[test]
    fn minimal_points_of_a_weighted_row_match_brute_force() {
        let a = [3i128, 5, 2, 4];
        let b = 6i128;
        let mut expected: Vec<u32> = Vec::new();
        for mask in 0u32..(1 << 4) {
            let sum: i128 = (0..4).filter(|j| mask >> j & 1 == 1).map(|j| a[j]).sum();
            if sum < b {
                continue;
            }
            let minimal = (0..4)
                .filter(|j| mask >> j & 1 == 1)
                .all(|j| sum - a[j] < b);
            if minimal {
                expected.push(mask);
            }
        }
        expected.sort_unstable();
        let mut got = mins(&a, b).expect("minimal points");
        got.sort_unstable();
        assert_eq!(got, expected);
    }

    #[test]
    fn separation_lp_matches_the_covering_optimum_on_a_known_row() {
        // x1 + x2 + x3 >= 2 has minimal points = the three pairs. The covering
        // LP at x* = (1/2, 1/2, 1/2) is min sum alpha_j / 2 s.t. every pair sums
        // to >= 1, whose optimum is alpha = (1/2, 1/2, 1/2), value 3/4 < 1.
        let masks = [0b011u32, 0b101, 0b110];
        let (value, alpha) = solve_covering_lp(&masks, 3, &[0.5, 0.5, 0.5]).expect("lp");
        assert!((value - 0.75).abs() < 1e-9, "value = {value}");
        for a in alpha {
            assert!((a - 0.5).abs() < 1e-9);
        }
    }

    #[test]
    fn separation_finds_no_cut_when_the_point_is_in_the_integer_hull() {
        // x* = (1, 1, 0) satisfies x1 + x2 + x3 >= 2 integrally: no violated cut.
        let masks = [0b011u32, 0b101, 0b110];
        let (value, _) = solve_covering_lp(&masks, 3, &[1.0, 1.0, 0.0]).expect("lp");
        assert!(value >= 1.0 - 1e-9, "value = {value}");
    }

    #[test]
    fn src_cuts_off_the_half_point_of_a_weighted_covering_row() {
        // 2 x1 + 2 x2 + 2 x3 >= 3 is integrally "at least two of three", so the
        // facet x1 + x2 + x3 >= 2 cuts off x* = (1/2, 1/2, 1/2).
        let c = ge(&[(1, 2), (2, 2), (3, 2)], 3);
        let mut src = SingleRowClosure::build(&[c], 3, &never_stop).expect("build");
        let x = vec![frac(1, 2), frac(1, 2), frac(1, 2)];
        let mut cuts = Vec::new();
        src.separate(&x, &never_stop, &mut cuts);
        assert_eq!(cuts.len(), 1, "cuts = {cuts:?}");
        let cut = &cuts[0];
        assert_eq!(cut.rhs, 2);
        assert_eq!(cut.terms.len(), 3);
        assert!(cut.terms.iter().all(|t| t.coeff == 1));
    }

    #[test]
    fn enumeration_reports_its_node_spend_and_fails_closed_on_a_tight_budget() {
        // `sum_{j<12} x_j >= 6` is the shape that makes the DFS expensive: every
        // 6-subset is minimal, so there are C(12,6) = 924 of them and the search
        // has to walk all the infeasible prefixes to find them.
        let a = vec![1i128; 12];
        let mut spent = 0u64;
        let full = minimal_points(&a, 6, MAX_SRC_ENUM_NODES, &mut spent).expect("minimal");
        assert_eq!(full.len(), 924);
        assert!(spent > 900, "expected a large node count, got {spent}");

        let mut tight = 0u64;
        assert!(
            minimal_points(&a, 6, 100, &mut tight).is_none(),
            "a 100-node budget must fail closed on a 3431-node enumeration"
        );
        assert!(tight >= 100, "the spend must be reported even on failure");

        // And a row whose minimal-point set exceeds the per-row cap is skipped
        // rather than stored: `sum_{j<16} x_j >= 8` has C(16,8) = 12870 > 4096.
        let mut wide = 0u64;
        assert!(minimal_points(&vec![1i128; 16], 8, MAX_SRC_ENUM_NODES, &mut wide).is_none());
    }

    #[test]
    fn src_emits_nothing_for_an_integral_point() {
        let c = ge(&[(1, 2), (2, 2), (3, 2)], 3);
        let mut src = SingleRowClosure::build(&[c], 3, &never_stop).expect("build");
        let x = vec![BigRational::one(), BigRational::one(), BigRational::zero()];
        let mut cuts = Vec::new();
        src.separate(&x, &never_stop, &mut cuts);
        assert!(cuts.is_empty(), "cuts = {cuts:?}");
    }

    #[test]
    fn src_suppresses_duplicate_cuts_across_rounds() {
        let c = ge(&[(1, 2), (2, 2), (3, 2)], 3);
        let mut src = SingleRowClosure::build(&[c], 3, &never_stop).expect("build");
        let x = vec![frac(1, 2), frac(1, 2), frac(1, 2)];
        let mut cuts = Vec::new();
        src.separate(&x, &never_stop, &mut cuts);
        let first = cuts.len();
        src.separate(&x, &never_stop, &mut cuts);
        assert_eq!(cuts.len(), first, "second round re-emitted the same cut");
    }

    #[test]
    fn wide_rows_are_skipped_rather_than_enumerated() {
        let terms: Vec<(u32, i128)> = (1..=(MAX_SRC_SUPPORT as u32 + 1)).map(|v| (v, 1)).collect();
        let c = ge(&terms, 2);
        assert!(
            SingleRowClosure::build(&[c], MAX_SRC_SUPPORT as u32 + 1, &never_stop).is_none(),
            "a row wider than the support cap must not be indexed"
        );
    }

    /// Random small covering rows: EVERY emitted cut must hold at EVERY feasible
    /// 0/1 point of its parent row, checked by brute force over the whole cube.
    ///
    /// The negative control for this test is
    /// [`src_cut_validity_fails_when_rounding_down`] below, which runs the same
    /// brute force against coefficients rounded DOWN and asserts that a violation
    /// IS found — i.e. this property test is capable of failing.
    #[test]
    fn every_emitted_cut_is_valid_by_brute_force_over_the_whole_row() {
        let mut state = 0x243f_6a88_85a3_08d3u64;
        let mut rng = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let mut total_cuts = 0usize;
        for _ in 0..400 {
            let k = 2 + (rng() % 8) as usize;
            let coeffs: Vec<i128> = (0..k).map(|_| 1 + (rng() % 9) as i128).collect();
            let total: i128 = coeffs.iter().sum();
            let rhs = 1 + (rng() % (total as u64).max(1)) as i128;
            let vars: Vec<(u32, i128)> = coeffs
                .iter()
                .enumerate()
                .map(|(i, &c)| (i as u32 + 1, c))
                .collect();
            let row = ge(&vars, rhs);
            let Some(mut src) = SingleRowClosure::build(&[row.clone()], k as u32, &never_stop)
            else {
                continue;
            };
            // A fractional point with denominators up to 8, plus a few 0/1s.
            let x: Vec<BigRational> = (0..k).map(|_| frac((rng() % 9) as i64, 8)).collect();
            let mut cuts = Vec::new();
            src.separate(&x, &never_stop, &mut cuts);
            total_cuts += cuts.len();
            for cut in &cuts {
                for mask in 0u32..(1u32 << k) {
                    let assign: Vec<bool> = (0..k).map(|j| mask >> j & 1 == 1).collect();
                    if eval(&row, &assign) < row.rhs {
                        continue; // infeasible for the parent row
                    }
                    assert!(
                        eval(cut, &assign) >= cut.rhs,
                        "invalid cut {cut:?} for row {row:?} at {assign:?}"
                    );
                }
            }
        }
        assert!(
            total_cuts >= 50,
            "property test saw only {total_cuts} cuts; it is not exercising anything"
        );
    }

    /// NEGATIVE CONTROL for the property test above.
    ///
    /// Rounds `alpha` DOWN instead of up and bypasses the exact re-proof, then
    /// runs the SAME brute-force validity check. It must find an invalid cut —
    /// which is what proves the brute force is load-bearing and that rounding UP
    /// is the direction that keeps the family sound.
    #[test]
    fn src_cut_validity_fails_when_rounding_down() {
        // x1 + x2 + x3 >= 2 at x* = (1/2, 1/2, 1/2). The separation alpha is
        // (1/2, 1/2, 1/2); rounding DOWN at denominator 1 gives all-zero
        // coefficients, and at denominator 3 gives 1 + 1 + 1 >= 3 which the
        // feasible point (1, 1, 0) violates.
        let row = ge(&[(1, 1), (2, 1), (3, 1)], 2);
        let view = normalize_ge_nonneg(&row.terms, row.rhs, 3).expect("view");
        let minimal = mins(&view.coeffs, view.rhs).expect("minimal");
        let src_row = SrcRow {
            lits: view.lits,
            minimal,
        };
        let xs = [0.5, 0.5, 0.5];
        let (value, alpha) =
            solve_covering_lp(&src_row.minimal, src_row.lits.len(), &xs).expect("lp");
        assert!(value < 1.0 - SRC_VIOLATION_TOL, "expected a violation");

        // Build the DOWN-rounded cut WITHOUT the exact re-proof, the way an
        // unsound implementation would.
        let k = src_row.lits.len();
        let den = 3i128;
        let coeffs: Vec<i128> = alpha
            .iter()
            .map(|&a| (a * den as f64).floor() as i128)
            .collect();
        let bad = PbConstraint {
            terms: coeffs
                .iter()
                .zip(src_row.lits.iter())
                .map(|(&c, &lit)| PbTerm {
                    coeff: c,
                    lits: vec![lit],
                })
                .collect(),
            rel: PbRel::Ge,
            rhs: den,
        };
        let mut found_invalid = false;
        for mask in 0u32..(1u32 << k) {
            let assign: Vec<bool> = (0..k).map(|j| mask >> j & 1 == 1).collect();
            if eval(&row, &assign) < row.rhs {
                continue;
            }
            if eval(&bad, &assign) < bad.rhs {
                found_invalid = true;
                break;
            }
        }
        assert!(
            found_invalid,
            "rounding DOWN produced {bad:?}, which the brute force accepted; \
             the validity property test would not be able to fail"
        );

        // And the real path REJECTS that same down-rounded candidate.
        assert!(
            cut_at_denominator(&src_row, &alpha, &xs, den, Rounding::Down).is_none(),
            "the exact re-proof must drop a down-rounded cut"
        );
        // While the up-rounded one at the same denominator is accepted and valid.
        let good = cut_at_denominator(&src_row, &alpha, &xs, den, Rounding::Up)
            .or_else(|| build_cut(&src_row, &alpha, &xs))
            .expect("up-rounded cut");
        for mask in 0u32..(1u32 << k) {
            let assign: Vec<bool> = (0..k).map(|j| mask >> j & 1 == 1).collect();
            if eval(&row, &assign) < row.rhs {
                continue;
            }
            assert!(eval(&good, &assign) >= good.rhs, "up-rounded cut invalid");
        }
    }

    #[test]
    fn equality_rows_yield_both_covering_directions() {
        // x1 + x2 + x3 = 2 gives `>= 2` and `~x1 + ~x2 + ~x3 >= 1`.
        let c = PbConstraint {
            terms: (1..=3)
                .map(|var| PbTerm {
                    coeff: 1,
                    lits: vec![PbLit {
                        var,
                        negated: false,
                    }],
                })
                .collect(),
            rel: PbRel::Eq,
            rhs: 2,
        };
        let src = SingleRowClosure::build(&[c], 3, &never_stop).expect("build");
        assert_eq!(src.indexed_rows(), 2);
    }

    #[test]
    fn saturation_preserves_the_feasible_set() {
        // 7 x1 + 2 x2 >= 3 saturates to 3 x1 + 2 x2 >= 3. Both forms have the
        // same 0/1 feasible set {x1 = 1}, hence the same single minimal point
        // {x1}: {x2} alone weighs 2 < 3, and {x1, x2} is not minimal.
        let view = normalize_ge_nonneg(
            &[
                PbTerm {
                    coeff: 7,
                    lits: vec![PbLit {
                        var: 1,
                        negated: false,
                    }],
                },
                PbTerm {
                    coeff: 2,
                    lits: vec![PbLit {
                        var: 2,
                        negated: false,
                    }],
                },
            ],
            3,
            2,
        )
        .expect("view");
        assert_eq!(view.coeffs, vec![3, 2]);
        assert_eq!(view.rhs, 3);
        let points = mins(&view.coeffs, view.rhs).expect("minimal");
        let mut got = points;
        got.sort_unstable();
        assert_eq!(got, vec![0b01]);
        // Same minimal points before saturation — the saturation is exact.
        let unsaturated = mins(&[7, 2], 3).expect("minimal");
        assert_eq!(unsaturated, vec![0b01]);
    }
}
