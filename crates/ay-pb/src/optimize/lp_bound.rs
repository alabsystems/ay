// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sound LP-relaxation objective lower bound for pseudo-Boolean minimization.
//!
//! # What this computes
//!
//! For a PBO minimization instance
//!
//! ```text
//! minimize   offset + sum_v c_v * x_v          (x_v in {0,1})
//! subject to sum_v a_{r,v} * x_v  >=  b_r       (constraints, after >= normalization)
//! ```
//!
//! the *LP relaxation* replaces `x_v in {0,1}` with the box `x_v in [0,1]`. Since
//! `{0,1}^n ⊆ [0,1]^n`, every integer-feasible assignment is also LP-feasible, so
//! the LP optimum `LP*` satisfies `LP* <= IntOpt`. The integer optimum is an
//! integer, hence `ceil(LP*) <= IntOpt`. Returning `ceil(LP*)` (or any value
//! `<= LP*` rounded up) is therefore a **sound** lower bound.
//!
//! # Why this implementation is sound regardless of arithmetic error
//!
//! We do **not** trust floating point. The whole computation uses exact rational
//! arithmetic ([`num_rational::BigRational`]). Concretely we solve the LP **dual**
//!
//! ```text
//! maximize   b · y     subject to   A^T y <= c,   y >= 0
//! ```
//!
//! with a single-phase rational simplex. By LP weak duality, for *any* dual-feasible
//! `y >= 0` with `A^T y <= c` and *any* primal-feasible `x in [0,1]` with `A x >= b`:
//!
//! ```text
//! b · y  <=  (A x) · y  =  x · (A^T y)  <=  x · c  =  c · x.
//! ```
//!
//! So `offset + b·y` is a valid lower bound for **every** feasible dual point — not
//! just the optimum. We start from `y = 0` (always dual-feasible because we arrange
//! `c >= 0`, giving the trivially valid bound `offset`), and every simplex pivot
//! only moves to another dual-feasible vertex, so the running bound is *always*
//! valid even if we stop early (iteration cap) or the LP is degenerate. We never
//! emit a bound from an infeasible `y`.
//!
//! Because the arithmetic is exact, the final rational bound `offset + b·y` is
//! exact, and `ceil(.)` of it is a sound integer lower bound.
//!
//! ## Variable complementation to guarantee `c >= 0`
//!
//! Objective coefficients on a PB variable can be negative once negated-literal
//! soft terms are folded in. We complement such variables (`x_v -> 1 - x'_v`),
//! which flips the sign of the objective coefficient and rewrites the constraint
//! coefficients accordingly, moving a constant into `offset`. After this every
//! `c_v >= 0`, so `y = 0` is dual-feasible and the starting bound `offset` holds.
//!
//! # When we return `None` (no bound)
//!
//! - the objective is empty or has no linear single-literal structure we can model,
//! - the instance is too large for the size/work budget,
//! - the dual simplex reports the dual is **unbounded** (primal LP infeasible) — we
//!   never assert infeasibility here, we just decline to bound,
//! - any arithmetic guard (overflow on the integer mapping) trips.
//!
//! On *any* doubt we return `None`. A `None` is always safe; a too-high bound is not.

use std::collections::BTreeMap;

use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::optimize::farkas_cert::{
    self, CertZ, Kind as CertKind, LinConZ, LpFarkasCert, QPair, SCertZ,
};
use crate::types::{PbConstraint, PbLit, PbObjective, PbRel};

/// Maximum number of PB variables we will model in the LP.
const MAX_VARS: usize = 5_000;
/// Maximum number of dual rows (primal constraints incl. upper bounds) we model.
const MAX_ROWS: usize = 12_000;
/// Maximum total non-zeros across the dual constraint matrix.
const MAX_NONZEROS: usize = 200_000;
/// Hard cap on simplex pivots. Hitting it still yields a sound (weaker) bound
/// from the last dual-feasible vertex.
const MAX_PIVOTS: usize = 20_000;
/// Poll cadence, in tableau entries, INSIDE a single Gauss-Jordan pivot. A
/// pivot rewrites up to `n * (m + n)` entries (order 1e8 on the largest
/// admitted shapes) with growing bignum numerators, so polling only BETWEEN
/// pivots leaves multi-second poll-free windows. Checked at row granularity
/// (rows are <= `m + n` entries), so the poll-free window stays well under
/// ~1e6 bignum ops. A stop mid-pivot leaves the tableau inconsistent, so the
/// solve DECLINES (no readout from a corrupted vertex) — sound, `None` = no
/// information.
const PIVOT_POLL_ENTRIES: usize = 65_536;
/// Poll cadence, in tableau rows, during the dense tableau initialization of
/// [`Model::solve_dual_big`] / [`Model::solve_dual_small`]. The init alone can
/// allocate gigabytes on admitted shapes (up to 5000 x 17000 entries), so it
/// must observe the stop/memory guard before the first pivot ever runs.
const TABLEAU_INIT_POLL_ROWS: usize = 64;
/// Maximum number of cutting-plane separation rounds around the LP solve. Each
/// round re-solves the LP after adding valid cuts, so this trades time for a
/// tighter (still sound) bound.
const MAX_CUT_ROUNDS: usize = 5;
/// Maximum number of cut rows we keep in total across all rounds. Bounds the LP
/// growth; once reached we stop separating and return the best sound bound.
const MAX_TOTAL_CUTS: usize = 1_500;
/// The exact-rational dual simplex re-solve cost scales with the augmented row
/// count *and* with the growth of big-integer numerators, so even moderate LPs can
/// be slow to re-solve several times. We only run the (expensive) cut loop when the
/// base LP is small enough that a handful of re-solves stay affordable; larger
/// instances keep the sound base bound. Measured against
/// `num_vars * (num_constraints + num_vars)` as a crude proxy for the tableau work.
/// (The wall-clock budget below is the hard backstop; this proxy avoids even
/// starting an expensive loop.)
///
/// Pegged at 2M (`~num_vars * (num_vars + num_constraints)`) so the cut loop runs
/// for the medium cardinality/injection range — e.g. the PB24 `injcomp` member at
/// ~950 vars (work proxy ~1.27M), whose base LP relaxation is off the integer
/// optimum by a single unit but whose Chvátal-Gomory closure tightens to EXACTLY the
/// integer optimum within the [`CUT_LOOP_TIME_BUDGET`]. At the old 500K threshold the
/// loop was skipped and the floor stayed loose, so native-OLL could not prove
/// optimality (the LP-floor incumbent probe needs a TIGHT floor to realize the
/// optimum). The raise is sound and bounded: the cut loop only ever *raises*
/// `best_bound` (it keeps the max across rounds, never lowers it) and every round
/// checks the wall-clock backstop. The 2M ceiling is deliberately conservative — it
/// covers the converting range while keeping the (slower) exact-rational re-solves of
/// larger LPs on the fast base bound, where a cut round cannot complete inside the
/// budget anyway (it would only return the same base bound after spending the time).
const CUT_LOOP_MAX_WORK_PROXY: u128 = 2_000_000;
/// Wall-clock budget for the whole cut loop (separation + re-solves). Exceeding it
/// stops further rounds and returns the best sound bound found so far — the cut
/// loop is *anytime*, so a partial loop is as sound as a full one, just possibly
/// less tight. Keeps a single LP-bound call from monopolizing the solver budget.
const CUT_LOOP_TIME_BUDGET: std::time::Duration = std::time::Duration::from_secs(2);
/// Wall-clock budget for the advisory f64 simplex inside the certified middle
/// tier ([`LpModel::solve_dual_f64_certified`]). Deliberately TINY: measured on
/// the i128-overflow corpus, the models this tier wins on converge almost
/// instantly (hw32, 3.2k vars / 262 rows: certifies the exact tier's floor in
/// ~20ms under heavy machine load), models at 2^30+ objective scale exit early
/// but fail certification (~75ms; f64 pricing tolerances are relative, so no
/// budget can pin a unit-precision bound there), and the degenerate-stalling
/// families (domset) only drift FURTHER from optimality with more time (their
/// NS dual estimate at 20s is worse than at 1.5s). So a small budget captures
/// every win, and its only cost is <=150ms subtracted from the exact tier's
/// root budget on models where the tier fails closed — measured (3-run A/B of
/// the exact tier at 4.85s vs 5s) to change those floors only within run-to-run
/// load jitter (±2 units, both directions). Expiry can never cause a wrong
/// bound (fail-closed on the convergence check).
const F64_TIER_SIMPLEX_BUDGET: std::time::Duration = std::time::Duration::from_millis(150);
/// Quality gate of the certified tier: reject (fall back to the exact path) when
/// the certified exact bound sits more than this RELATIVE slack below the f64
/// solve's own primal objective estimate — a converged-looking dual whose
/// certified value is still uselessly weak. Belt-and-braces on top of the
/// convergence requirement; pure quality/time trade (both accept and reject are
/// sound).
const F64_TIER_QUALITY_SLACK: f64 = 1e-6;

/// Computes a sound LP-relaxation lower bound for `min objective` subject to
/// `constraints`, where every variable is Boolean.
///
/// Returns `Some(lb)` where `lb <= IntOpt` is guaranteed, or `None` when no bound
/// could be produced soundly (see module docs). `should_stop` is polled so an
/// external timeout can abort; on abort the best sound bound so far is returned.
pub(crate) fn lp_lower_bound(
    objective: &PbObjective,
    constraints: &[PbConstraint],
    num_vars: u32,
    should_stop: &dyn Fn() -> bool,
) -> Option<i128> {
    lp_lower_bound_with_cuts(objective, constraints, num_vars, None, should_stop)
}

/// Raw dual information for building a VeriPB LP-dual floor certificate. The LP
/// model complements every variable with a negative net objective coefficient
/// (`x_v -> 1 - x'_v`) and appends one box row `-x'_v >= -1` per variable AFTER the
/// constraint rows, so `duals` is laid out as `[constraint-row duals..., box-row
/// duals...]`. The emitter un-complements this back to original space.
pub(crate) struct LpDualRaw {
    pub bound: i128,
    /// Dual-feasible `y >= 0`, one per primal row (constraint rows then box rows).
    pub duals: Vec<BigRational>,
    /// `complement[v]` = variable `v` (0-based) was replaced by `1 - x'_v`.
    pub complement: Vec<bool>,
    /// Number of constraint rows (Ge -> 1, Eq -> 2); box rows follow.
    pub num_constraint_rows: usize,
}

/// Solves the exact-rational LP dual and returns the raw multipliers for the
/// VeriPB floor-certificate emitter. `None` if the model could not be built/solved.
pub(crate) fn lp_dual_raw(
    objective: &PbObjective,
    constraints: &[PbConstraint],
    num_vars: u32,
    should_stop: &dyn Fn() -> bool,
) -> Option<LpDualRaw> {
    let model = LpModel::build(objective, constraints, num_vars)?;
    let dual = model.solve_dual(should_stop, None)?;
    let n = usize::try_from(num_vars).ok()?;
    Some(LpDualRaw {
        bound: dual.bound,
        duals: dual.duals,
        complement: model.complement.clone(),
        num_constraint_rows: model.rows.len().checked_sub(n)?,
    })
}

/// [`lp_lower_bound`] with an optional **early-exit target**: once the running
/// (already sound) bound reaches `target`, further tightening (the cutting-plane
/// loop) is skipped and the bound is returned immediately.
///
/// # Why an early exit is sound AND lossless for the caller
///
/// Every bound this function ever returns is a valid lower bound (weak duality;
/// see module docs) — the target only decides how long we keep *tightening*.
/// The intended `target` is the caller's incumbent objective value: since any
/// sound floor satisfies `floor <= IntOpt <= incumbent`, reaching
/// `floor >= incumbent` proves `incumbent == IntOpt`, and no larger floor can
/// carry any additional information for an optimality check against that (or
/// any future, necessarily smaller) incumbent. So the early exit can never turn
/// a would-be OPTIMUM into a weaker verdict; it only stops paying for cut
/// rounds whose result could not matter.
pub(crate) fn lp_lower_bound_with_target(
    objective: &PbObjective,
    constraints: &[PbConstraint],
    num_vars: u32,
    early_exit_target: Option<i128>,
    should_stop: &dyn Fn() -> bool,
) -> Option<i128> {
    lp_lower_bound_with_cuts(
        objective,
        constraints,
        num_vars,
        early_exit_target,
        should_stop,
    )
}

/// Whether the Farkas-certificate emit/check path is enabled (`AY_PB_FARKAS_CERT`).
/// Re-exported here so consumers do not depend on the `farkas_cert` module
/// directly. Default OFF, so the certificate machinery never perturbs the existing
/// (already-sound) bound path unless explicitly enabled.
pub(crate) fn cert_path_enabled() -> bool {
    farkas_cert::cert_emit_enabled()
}

/// Outcome of validating a base-LP Farkas certificate against its claimed bound.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CertOutcome {
    /// `AY_PB_FARKAS_CERT` was unset; no certificate was built.
    Disabled,
    /// The certificate `check_slack` accepted and its `claimed_bound == bound`.
    /// The bound is trusted via the checked certificate (no re-derivation needed).
    Verified,
    /// The certificate failed `check_slack` (or its claimed bound disagreed). The
    /// caller falls back to today's exact path; this is byte-for-byte as sound as
    /// before — a failed check NEVER changes the reported bound.
    Rejected,
}

/// Computes the base-LP lower bound AND, when the emit path is enabled, a
/// self-validated Farkas certificate for it.
///
/// This is the fail-closed wiring described in the design: emit the cert from the
/// data already in hand (the dual point `y`, `exact_bound`, `c`, rows, offset),
/// then immediately `check_slack` it. The returned `(bound, cert, outcome)` lets
/// callers (and tests) confirm that a REAL ay LP bound is validated by the
/// checked certificate. The bound itself is identical to [`lp_lower_bound`]'s
/// base round regardless of the certificate outcome — the certificate is an
/// internal trust accelerator, never a bound modifier.
pub(crate) fn lp_lower_bound_with_cert(
    objective: &PbObjective,
    constraints: &[PbConstraint],
    num_vars: u32,
    should_stop: &dyn Fn() -> bool,
) -> Option<(i128, Option<LpFarkasCert>, CertOutcome)> {
    let model = LpModel::build(objective, constraints, num_vars)?;
    let dual = model.solve_dual(should_stop, None)?;
    let bound = dual.bound;

    if !farkas_cert::cert_emit_enabled() {
        return Some((bound, None, CertOutcome::Disabled));
    }

    match model.build_farkas_cert(&dual) {
        Some(cert) if cert.claimed_bound == bound && farkas_cert::check_slack(&cert.cert) => {
            Some((bound, Some(cert), CertOutcome::Verified))
        }
        Some(cert) => Some((bound, Some(cert), CertOutcome::Rejected)),
        None => Some((bound, None, CertOutcome::Rejected)),
    }
}

/// Best-effort fractional LP-relaxation optimum point in **original** variable
/// space: entry `v` (0-indexed) approximates the relaxed value of PB variable
/// `v + 1` in `[0, 1]`.
///
/// This is **advisory only** — it is consumed solely by primal heuristics (LNS
/// RINS/RENS neighborhood selection) to decide *which* variables to relax. No
/// soundness property depends on its accuracy: a wrong fractional point merely
/// changes which neighborhood LNS explores, and every candidate LNS adopts is
/// independently re-verified against the original constraints. Returns `None`
/// when the base LP could not be solved or the fractional point was not
/// recovered (e.g. interrupted, too large, non-linear objective).
pub(crate) fn lp_fractional_point(
    objective: &PbObjective,
    constraints: &[PbConstraint],
    num_vars: u32,
    should_stop: &dyn Fn() -> bool,
) -> Option<Vec<f64>> {
    let model = LpModel::build(objective, constraints, num_vars)?;
    let DualSolution { primal, .. } = model.solve_dual(should_stop, None)?;
    let primal = primal?;
    let point = primal
        .iter()
        .map(|value| {
            // Advisory conversion; clamp defensively into [0, 1]. `to_f64`
            // cannot fail for a finite rational, but fall back to 0.0 if it
            // ever does rather than panicking.
            let approx = value.to_f64().unwrap_or(0.0);
            approx.clamp(0.0, 1.0)
        })
        .collect();
    Some(point)
}

/// Solves the LP relaxation, then runs a bounded cutting-plane loop: separate
/// **valid** cuts violated by the current fractional optimum, add them as new LP
/// rows, and re-solve, repeating up to [`MAX_CUT_ROUNDS`] times.
///
/// # Soundness
///
/// Every cut added is a [`PbConstraint`] satisfied by *every* 0/1 assignment that
/// satisfies the original constraints (see [`crate::optimize::cutting_planes`]),
/// so the augmented LP is still a relaxation of the **same** integer program. Its
/// optimum can therefore only rise toward — never above — the true integer
/// optimum, and the exact-rational dual bound stays a valid lower bound. We keep
/// the **largest** sound bound observed across rounds; if any round declines
/// (`None`) we keep the best previous sound bound. Cuts are extra rows only; they
/// never remove an integer-feasible point.
fn lp_lower_bound_with_cuts(
    objective: &PbObjective,
    original_constraints: &[PbConstraint],
    num_vars: u32,
    early_exit_target: Option<i128>,
    should_stop: &dyn Fn() -> bool,
) -> Option<i128> {
    // Round 0: the base LP (identical to the pre-cuts behaviour).
    let model = LpModel::build(objective, original_constraints, num_vars)?;
    let DualSolution { bound, primal, .. } = model.solve_dual(should_stop, early_exit_target)?;
    let mut best_bound = bound;

    // Early exit: the bound already certifies the caller's target (typically
    // the incumbent), so no cut round can add information — see
    // [`lp_lower_bound_with_target`]. The bound returned is sound as-is.
    if early_exit_target.is_some_and(|target| best_bound >= target) {
        return Some(best_bound);
    }

    // Gate the (expensive, exact-rational) cut loop by a crude work proxy. On
    // larger instances we keep the sound base bound rather than spend a large time
    // budget on re-solves. This only affects *quality*, never soundness.
    let work_proxy = u128::from(num_vars)
        .saturating_mul(u128::from(num_vars).saturating_add(original_constraints.len() as u128));
    if work_proxy > CUT_LOOP_MAX_WORK_PROXY {
        return Some(best_bound);
    }

    // `working` accumulates the original constraints plus every valid cut added so
    // far, so each re-solve sees all previously added cuts.
    let mut working: Vec<PbConstraint> = original_constraints.to_vec();
    let mut added_cuts = 0usize;
    let started = std::time::Instant::now();
    // Abort signal shared by separation and every re-solve: the external stop OR
    // the internal cut-loop deadline. Keeping it on *both* phases means neither a
    // dense separation pass nor a dense exact-rational re-solve can blow the budget
    // — on abort we just return the best sound bound found so far (anytime).
    let stop_or_deadline = || should_stop() || started.elapsed() >= CUT_LOOP_TIME_BUDGET;

    let mut current_primal = primal;
    for _ in 0..MAX_CUT_ROUNDS {
        if stop_or_deadline() || added_cuts >= MAX_TOTAL_CUTS {
            break;
        }
        let Some(x) = current_primal.as_ref() else {
            break; // no usable fractional point to separate against.
        };
        // Separate cuts against the ORIGINAL constraints (they alone define the
        // feasible region the cuts must be valid for; added cuts are themselves
        // already-valid consequences, so re-separating against them is harmless
        // but unnecessary). We separate over the original set for clarity.
        let cuts = crate::optimize::cutting_planes::separate_cuts(
            original_constraints,
            num_vars,
            x,
            &stop_or_deadline,
        );
        if cuts.is_empty() {
            break; // nothing violated -> LP point is cut-free for these families.
        }
        let take = cuts.len().min(MAX_TOTAL_CUTS - added_cuts);
        working.extend(cuts.into_iter().take(take));
        added_cuts += take;

        // Re-solve the augmented LP. A None here (size/overflow/infeasible-dual)
        // means we keep the best sound bound found so far. On a deadline-aborted
        // simplex the returned bound is still sound (a dual-feasible vertex) and we
        // keep the max, so `best_bound` never regresses.
        let Some(model) = LpModel::build(objective, &working, num_vars) else {
            break;
        };
        let Some(DualSolution { bound, primal, .. }) =
            model.solve_dual(&stop_or_deadline, early_exit_target)
        else {
            break;
        };
        if bound > best_bound {
            best_bound = bound;
        }
        // Same early exit inside the loop: a floor at the target ends the
        // tightening (any further cut round is paid-for but unusable work).
        if early_exit_target.is_some_and(|target| best_bound >= target) {
            return Some(best_bound);
        }
        current_primal = primal;
    }

    Some(best_bound)
}

/// A sound reduced-cost variable fixing: PB variable `var` (1-indexed) must take
/// value `value` in *every* feasible assignment strictly better than the incumbent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ReducedCostFixing {
    /// 1-indexed PB variable to fix.
    pub(crate) var: u32,
    /// The forced value (`true` = fix to 1, `false` = fix to 0).
    pub(crate) value: bool,
}

/// Output of a reduced-cost-fixing LP solve.
pub(crate) struct ReducedCostResult {
    /// Sound integer lower bound on the objective (`ceil(LP*)`), identical to what
    /// [`lp_lower_bound`] would return.
    pub(crate) lower_bound: i128,
    /// Reduced-cost fixings sound against the given incumbent. Empty when none could
    /// be certified.
    pub(crate) fixings: Vec<ReducedCostFixing>,
}

/// Solves the (cut-augmented) LP relaxation and derives **reduced-cost variable
/// fixings** that are sound against the incumbent objective `incumbent_ub`.
///
/// # The fixing rule (RoundingSat/Exact's general-OPT mechanism)
///
/// Work in the LP's *complemented* space where every objective coefficient
/// `c_v >= 0` (so increasing `x'_v` toward 1 only ever *worsens* the objective).
/// Let `y >= 0` be the dual-feasible point and define the exact-rational dual slack
/// (reduced cost) of variable v
///
/// ```text
/// d_v = c_v - (A^T y)_v   (>= 0 by dual feasibility).
/// ```
///
/// For **any** primal-feasible `x'` (i.e. `A x' >= b`, `x' >= 0`, which includes
/// the box `x'_v <= 1` rows):
///
/// ```text
/// z(x') = offset + c·x'
///       = offset + (A^T y + d)·x'                      [c = A^T y + d]
///       = offset + y·(A x') + d·x'
///       >= offset + y·b + d·x'        = LB + d·x'      [y >= 0, A x' >= b]
///       >= LB + d_v · x'_v                              [all d_u >= 0, x'_u >= 0]
/// ```
///
/// where `LB = offset + b·y` is the exact-rational LP bound. So if `x'_v = 1` then
/// `z(x') >= LB + d_v`. The objective is integer-valued, so any assignment
/// *strictly better* than the incumbent has `z(x') <= incumbent_ub - 1`. Hence if
///
/// ```text
/// LB + d_v  >  incumbent_ub - 1        (STRICT, exact rational)
/// ```
///
/// then no strictly-better assignment can have `x'_v = 1`; every such assignment
/// fixes `x'_v = 0`. We translate that back to original space:
/// `x'_v = x_v` (not complemented) → fix `x_v = 0`; `x'_v = 1 - x_v`
/// (complemented) → fix `x_v = 1`.
///
/// # Soundness
///
/// The derivation holds for the **augmented** constraint set (original `>=` rows
/// plus any added valid cuts), because every cut is satisfied by every feasible
/// 0/1 point, so the relaxation still contains every feasible assignment. The
/// fixing therefore removes only assignments that are provably *not* strictly
/// better than the incumbent — it never removes the optimum, and never removes a
/// tie unless that tie is no better than the incumbent already recorded. The
/// caller re-derives fixings whenever the incumbent improves and re-verifies any
/// claimed optimum against the ORIGINAL constraints, so a fixing is a pruning, not
/// part of the optimality certificate.
///
/// Returns `None` when no LP could be built/solved (size/work cap, non-linear
/// objective, infeasible dual). A `None` simply yields no fixings.
pub(crate) fn lp_reduced_cost_fixings(
    objective: &PbObjective,
    constraints: &[PbConstraint],
    num_vars: u32,
    incumbent_ub: i128,
    should_stop: &dyn Fn() -> bool,
) -> Option<ReducedCostResult> {
    // Reuse the cut loop to reach the tightest sound dual point: a tighter LB and
    // larger reduced costs fix more variables. We keep the FINAL model + dual point
    // (over the augmented constraint set) and compute fixings from it.
    let (model, dual) = solve_with_cuts_for_fixing(objective, constraints, num_vars, should_stop)?;

    let lower_bound = dual.bound;
    // `incumbent_ub - 1` as an exact rational is the largest objective value a
    // strictly-better assignment can take (objective is integer-valued).
    let strict_target = int(incumbent_ub.checked_sub(1)?);

    let fixings = model.reduced_cost_fixings(&dual, &strict_target);
    Some(ReducedCostResult {
        lower_bound,
        fixings,
    })
}

/// Runs the same bounded cutting-plane loop as [`lp_lower_bound_with_cuts`] but
/// returns the FINAL `(model, dual_solution)` over the cut-augmented constraint
/// set, so the caller can read per-variable reduced costs from it. The dual point
/// returned is dual-feasible for that final model (weak duality holds), which is
/// exactly what the reduced-cost fixing rule requires.
fn solve_with_cuts_for_fixing(
    objective: &PbObjective,
    original_constraints: &[PbConstraint],
    num_vars: u32,
    should_stop: &dyn Fn() -> bool,
) -> Option<(LpModel, DualSolution)> {
    let model = LpModel::build(objective, original_constraints, num_vars)?;
    let dual = model.solve_dual(should_stop, None)?;

    // Same work-proxy gate as the bound path: on larger instances keep the base LP
    // model + dual (still gives sound fixings) rather than spend the cut budget.
    let work_proxy = u128::from(num_vars)
        .saturating_mul(u128::from(num_vars).saturating_add(original_constraints.len() as u128));
    if work_proxy > CUT_LOOP_MAX_WORK_PROXY {
        return Some((model, dual));
    }

    let mut best: (LpModel, DualSolution) = (model, dual);
    let mut working: Vec<PbConstraint> = original_constraints.to_vec();
    let mut added_cuts = 0usize;
    let started = std::time::Instant::now();
    let stop_or_deadline = || should_stop() || started.elapsed() >= CUT_LOOP_TIME_BUDGET;

    for _ in 0..MAX_CUT_ROUNDS {
        if stop_or_deadline() || added_cuts >= MAX_TOTAL_CUTS {
            break;
        }
        let Some(x) = best.1.primal.as_ref() else {
            break;
        };
        let cuts = crate::optimize::cutting_planes::separate_cuts(
            original_constraints,
            num_vars,
            x,
            &stop_or_deadline,
        );
        if cuts.is_empty() {
            break;
        }
        let take = cuts.len().min(MAX_TOTAL_CUTS - added_cuts);
        working.extend(cuts.into_iter().take(take));
        added_cuts += take;

        let Some(model) = LpModel::build(objective, &working, num_vars) else {
            break;
        };
        let Some(dual) = model.solve_dual(&stop_or_deadline, None) else {
            break;
        };
        // Keep the model whose bound is at least as tight. The reduced-cost fixing
        // is sound for ANY dual-feasible point, so even if a later round's bound
        // does not strictly improve we may keep it; we prefer the tightest bound so
        // the fixing test is as strong as possible.
        if dual.bound >= best.1.bound {
            best = (model, dual);
        }
    }

    Some(best)
}

/// Test-only: the *base* LP bound with **no** cutting planes (round 0 only).
/// Used to measure how much the cut loop tightens the bound.
#[cfg(test)]
fn lp_lower_bound_no_cuts(
    objective: &PbObjective,
    constraints: &[PbConstraint],
    num_vars: u32,
    should_stop: &dyn Fn() -> bool,
) -> Option<i128> {
    let model = LpModel::build(objective, constraints, num_vars)?;
    model.solve_dual(should_stop, None).map(|s| s.bound)
}

/// The canonical LP we reason about, in *complemented* variable space.
///
/// All objective coefficients `c[v] >= 0`. Rows encode `A x >= b` (each PB
/// constraint, with `=` split into two `>=`) plus the box upper bounds
/// `-x_v >= -1`. The implicit `x >= 0` is the simplex non-negativity and needs no
/// explicit row. `offset` collects every constant produced by literal/variable
/// substitution and complementation.
struct LpModel {
    /// `c[v] >= 0`, objective coefficient on (complemented) variable `v`.
    c: Vec<BigRational>,
    /// Sparse rows: each is `(coeffs: [(var, coeff)], b)` meaning `coeffs · x >= b`.
    rows: Vec<Row>,
    /// Constant added to the objective after all substitutions.
    offset: BigRational,
    /// `complement[v]` is true when PB variable `v` was replaced by `1 - x'_v`.
    /// Used to map the complemented-space LP primal point back to original space
    /// for cut separation.
    complement: Vec<bool>,
}

/// Output of one dual LP solve: the sound objective lower bound plus a best-effort
/// fractional primal point in **original** variable space (`primal[v]` ~ value of
/// PB variable `v+1` in `[0, 1]`), used only to focus cut separation.
struct DualSolution {
    /// Sound lower bound `ceil(offset + b·y)`.
    bound: i128,
    /// The EXACT (un-ceiled) rational bound `offset + b·y`. A valid lower bound for
    /// *any* dual-feasible `y` (weak duality), hence sound even at early
    /// termination. Used by reduced-cost fixing where the un-rounded bound gives the
    /// tightest sound fixing test.
    exact_bound: BigRational,
    /// The dual-feasible point `y >= 0` (one entry per primal row), recovered from
    /// the current basis. `A^T y <= c` holds by construction, so the per-variable
    /// dual slacks `d_v = c_v - (A^T y)_v` are all `>= 0`. Used for reduced-cost
    /// variable fixing.
    duals: Vec<BigRational>,
    /// Fractional primal point, or `None` if it could not be recovered.
    primal: Option<Vec<BigRational>>,
}

struct Row {
    /// Sparse `(var_index, coefficient)` entries.
    coeffs: Vec<(usize, BigRational)>,
    /// Right-hand side `b` (row asserts `coeffs · x >= b`).
    b: BigRational,
}

fn int(v: i128) -> BigRational {
    BigRational::from_integer(v.into())
}

impl LpModel {
    fn build(objective: &PbObjective, constraints: &[PbConstraint], num_vars: u32) -> Option<Self> {
        let n = usize::try_from(num_vars).ok()?;
        if n == 0 || n > MAX_VARS {
            return None;
        }
        if constraints.len() > MAX_ROWS {
            return None;
        }

        // --- Net objective coefficient per 1-indexed PB variable. ---
        // Each objective term must be a single literal (linear). Non-linear
        // (product) terms make this a non-LP objective; decline.
        let mut g: Vec<BigRational> = vec![BigRational::zero(); n];
        let mut offset = BigRational::zero();
        let mut any_obj = false;
        for term in &objective.terms {
            if term.coeff == 0 {
                continue;
            }
            let [lit] = term.lits.as_slice() else {
                return None;
            };
            let v = var_index(*lit, n)?;
            let coeff = int(term.coeff);
            if lit.negated {
                // coeff * (1 - x_v) = coeff - coeff * x_v
                offset += &coeff;
                g[v] -= &coeff;
            } else {
                g[v] += &coeff;
            }
            any_obj = true;
        }
        if !any_obj {
            return None;
        }

        // --- Complement variables with negative net objective coefficient so
        // that the resulting objective coefficient is >= 0. `complement[v]`
        // records whether variable v was replaced by `1 - x'_v`. ---
        let mut complement = vec![false; n];
        let mut c = vec![BigRational::zero(); n];
        for v in 0..n {
            if g[v].is_negative() {
                complement[v] = true;
                // g_v * x_v with x_v = 1 - x'_v  ==>  g_v - g_v * x'_v
                offset += &g[v];
                c[v] = -(&g[v]);
            } else {
                c[v] = g[v].clone();
            }
        }

        // --- Build rows: every PB constraint as one or two `>=` rows, then box
        // upper bounds. Coefficients are rewritten into complemented space and
        // literal negation is folded into the rhs. ---
        let mut rows: Vec<Row> = Vec::new();
        let mut nonzeros = 0usize;
        for constraint in constraints {
            match constraint.rel {
                PbRel::Ge => {
                    let row = build_row(constraint, &complement, n, 1)?;
                    nonzeros += row.coeffs.len();
                    rows.push(row);
                }
                PbRel::Eq => {
                    // a·x = b  <=>  a·x >= b  AND  -a·x >= -b
                    let pos = build_row(constraint, &complement, n, 1)?;
                    let neg = build_row(constraint, &complement, n, -1)?;
                    nonzeros += pos.coeffs.len() + neg.coeffs.len();
                    rows.push(pos);
                    rows.push(neg);
                }
            }
            if rows.len() > MAX_ROWS || nonzeros > MAX_NONZEROS {
                return None;
            }
        }

        // Box upper bounds: -x_v >= -1 for every variable. (Lower bound x_v >= 0
        // is the simplex non-negativity, no row needed.)
        for v in 0..n {
            rows.push(Row {
                coeffs: vec![(v, -BigRational::one())],
                b: -BigRational::one(),
            });
        }
        nonzeros += n;
        if rows.len() > MAX_ROWS || nonzeros > MAX_NONZEROS {
            return None;
        }

        Some(Self {
            c,
            rows,
            offset,
            complement,
        })
    }

    /// Solves the dual `max b·y s.t. A^T y <= c, y >= 0` with an exact rational
    /// simplex and returns `ceil(offset + b·y_best)` as a sound lower bound, plus
    /// the recovered fractional primal point in **original** variable space.
    ///
    /// Any dual-feasible `y` gives a valid bound (weak duality), so the running
    /// bound is sound at every step including early termination. The primal point
    /// is recovered from the optimal-tableau reduced costs of the dual slack
    /// columns and is used **only** to focus cut separation — soundness never
    /// depends on it being exact (a wrong primal merely yields fewer/weaker cuts).
    ///
    /// # Three-tier dispatch (i128 → f64-certified → BigRational)
    ///
    /// The simplex is first run in **checked `i128` rational arithmetic**
    /// ([`Self::solve_dual_small`]) — exact, but 1-2 orders of magnitude faster
    /// than `num_bigint` because every entry is a pair of machine words (no heap
    /// allocation, hardware gcd/div). It mirrors the BigRational simplex
    /// operation-for-operation (same Dantzig entering rule, same ratio test,
    /// same pivot updates, all comparisons exact), so a *completed* small solve
    /// returns the **identical** `DualSolution` the BigRational path would. The
    /// moment ANY intermediate value cannot be represented (or an operation
    /// would overflow `i128`), the small tier aborts — fail-closed: on any
    /// doubt, a slower exact path decides.
    ///
    /// On an i128 overflow we do NOT go straight to the (expensive) BigRational
    /// re-solve: the **f64-certified tier** ([`Self::solve_dual_f64_certified`])
    /// runs an advisory f64 simplex for a dual point and then verifies dual
    /// feasibility and the objective **exactly** in one bigint pass. A verified
    /// dual-feasible point certifies its bound by weak duality *regardless of
    /// how it was found*, so a certified result is sound — though possibly
    /// WEAKER than the BigRational optimum (quality, never soundness). Only when
    /// certification fails (or is gated for quality) does the BigRational path
    /// ([`Self::solve_dual_big`]) re-solve from scratch. Nothing unverified is
    /// ever trusted, so a wrong f64 dual can only cost time, never correctness.
    ///
    /// # In-simplex early exit (`early_stop_bound`)
    ///
    /// When `early_stop_bound` is `Some(target)`, the pivot loop additionally
    /// stops as soon as the RUNNING bound `ceil(offset + b·y)` of the current
    /// vertex reaches `target`. This is sound for the same reason every other
    /// early termination here is sound (iteration cap, `should_stop`): the
    /// single-phase dual simplex starts dual-feasible (`y = 0`, `c >= 0`) and
    /// every pivot moves to another dual-feasible vertex, so the running bound
    /// is a valid lower bound at every step (weak duality). The caller passes
    /// its incumbent as the target: a floor at the incumbent already proves it
    /// optimal, so pivoting further is pure waste. `None` preserves the full
    /// solve-to-optimality behaviour.
    fn solve_dual(
        &self,
        should_stop: &dyn Fn() -> bool,
        early_stop_bound: Option<i128>,
    ) -> Option<DualSolution> {
        match self.solve_dual_small(should_stop, early_stop_bound) {
            SmallDualOutcome::Solved(result) => result,
            SmallDualOutcome::Overflow => {
                if let Some(certified) = self.solve_dual_f64_certified(should_stop) {
                    // Accept the certified floor only when it already satisfies
                    // the caller's target (or no target was given). A targeted
                    // caller uses `floor >= incumbent` to prove OPTIMUM at the
                    // root; the f64 tier's quality gate is RELATIVE, so at
                    // large objective magnitudes a "converged" certified floor
                    // can sit many integer units below LP*. Falling through to
                    // the exact tier (with the target still threaded for its
                    // in-simplex early exit) costs exactly what the pre-tier
                    // code paid and preserves the root OPTIMUM proof.
                    if early_stop_bound.map_or(true, |t| certified.bound >= t) {
                        return Some(certified);
                    }
                }
                self.solve_dual_big(should_stop, early_stop_bound)
            }
        }
    }

    /// The exact-rational (`num_bigint`) dual simplex — the original, always-safe
    /// tier. See [`Self::solve_dual`] for the dispatch contract.
    fn solve_dual_big(
        &self,
        should_stop: &dyn Fn() -> bool,
        early_stop_bound: Option<i128>,
    ) -> Option<DualSolution> {
        let m = self.rows.len(); // dual variables (one per primal row)
        let n = self.c.len(); // dual constraints (one per primal variable)

        // Dual standard form (maximize): A^T y + s = c, y,s >= 0.
        //   - dual variable y_r corresponds to primal row r (column r).
        //   - dual constraint v: sum_r (A^T)_{v,r} y_r <= c_v.
        // Tableau columns: m structural (y) then n slack (s). Rows: n.
        // Build A^T column-major implicitly from the sparse primal rows.
        let total_cols = m.checked_add(n)?;

        // tableau[i] is dual constraint i (i in 0..n): coefficients over columns.
        // Built row by row so the stop/memory guard is observed DURING the
        // (potentially multi-GB) initialization, not only after it.
        let mut tab: Vec<Vec<BigRational>> = Vec::with_capacity(n);
        for i in 0..n {
            if i % TABLEAU_INIT_POLL_ROWS == 0 && should_stop() {
                return None;
            }
            tab.push(vec![BigRational::zero(); total_cols]);
        }
        let mut rhs: Vec<BigRational> = vec![BigRational::zero(); n];
        // Objective row of the (max b·y) program: we store reduced costs.
        // obj[col] is current coefficient in the objective row (to maximize we
        // pick a column with positive reduced cost).
        let mut obj: Vec<BigRational> = vec![BigRational::zero(); total_cols];

        // Fill structural columns: column r (dual var y_r) has, in dual
        // constraint v, the coefficient A_{r,v} (primal row r's coeff on var v).
        for (r, row) in self.rows.iter().enumerate() {
            for &(v, ref coeff) in &row.coeffs {
                // dual constraint v, column r
                tab[v][r] = coeff.clone();
            }
            // Objective of dual is b·y -> column r gets coefficient b_r.
            obj[r] = row.b.clone();
        }
        // Slack columns: identity. rhs of dual constraint v is c_v (>= 0).
        for v in 0..n {
            tab[v][m + v] = BigRational::one();
            rhs[v] = self.c[v].clone();
        }
        // c_v >= 0 by construction, so the all-slack basis (y = 0) is feasible.
        debug_assert!(rhs.iter().all(|r| !r.is_negative()));

        // basis[i] = column index basic in row i. Start with the slacks.
        let mut basis: Vec<usize> = (0..n).map(|v| m + v).collect();

        // Whether the simplex reached optimality (no positive reduced cost). Only
        // then are the dual-slack reduced costs a valid primal point.
        let mut optimal = false;
        for _ in 0..MAX_PIVOTS {
            if should_stop() {
                break;
            }
            // Entering column: largest positive reduced cost (Dantzig). Reduced
            // costs are in `obj` after we maintain them via pivoting.
            let mut entering: Option<usize> = None;
            let mut best = BigRational::zero();
            for (col, reduced_cost) in obj.iter().enumerate() {
                if *reduced_cost > best {
                    best = reduced_cost.clone();
                    entering = Some(col);
                }
            }
            let Some(col) = entering else {
                optimal = true;
                break; // optimal: no positive reduced cost.
            };

            // Ratio test: smallest rhs[i]/tab[i][col] over tab[i][col] > 0.
            let mut leaving: Option<usize> = None;
            let mut best_ratio: Option<BigRational> = None;
            for i in 0..n {
                let a = &tab[i][col];
                if a.is_positive() {
                    let ratio = &rhs[i] / a;
                    match &best_ratio {
                        Some(br) if &ratio >= br => {}
                        _ => {
                            best_ratio = Some(ratio);
                            leaving = Some(i);
                        }
                    }
                }
            }
            let Some(prow) = leaving else {
                // Dual objective is unbounded above => primal LP infeasible.
                // We do not assert infeasibility; decline to bound.
                return None;
            };

            if !pivot(&mut tab, &mut rhs, &mut obj, prow, col, n, should_stop) {
                // Stopped mid-pivot: the tableau is inconsistent, so no sound
                // vertex readout exists — decline (`None` = no information).
                return None;
            }
            basis[prow] = col;

            // In-simplex early exit: the current vertex is dual-feasible, so
            // its running bound is already valid (see [`Self::solve_dual`]).
            // Once `ceil(offset + b·y) >= target` no further pivot can matter
            // to the caller's optimality check — stop tightening. The final
            // readout below recomputes the bound from this same vertex.
            if let Some(target) = early_stop_bound {
                let mut running = self.offset.clone();
                for i in 0..n {
                    if basis[i] < m && !rhs[i].is_zero() {
                        running += &self.rows[basis[i]].b * &rhs[i];
                    }
                }
                if rational_ceil_to_i64(&running).is_some_and(|bound| bound >= target) {
                    break;
                }
            }
        }

        // Current dual-feasible point y: read structural columns from the basis.
        let mut y: Vec<BigRational> = vec![BigRational::zero(); m];
        for i in 0..n {
            if basis[i] < m {
                y[basis[i]] = rhs[i].clone();
            }
        }
        // Sound bound = offset + b · y, computed exactly.
        let mut exact_bound = self.offset.clone();
        for (r, row) in self.rows.iter().enumerate() {
            if !y[r].is_zero() {
                exact_bound += &row.b * &y[r];
            }
        }

        let bound = rational_ceil_to_i64(&exact_bound)?;
        let primal = if optimal {
            self.recover_primal(&obj, m, n)
        } else {
            None
        };
        Some(DualSolution {
            bound,
            exact_bound,
            duals: y,
            primal,
        })
    }

    /// The `i128` fast tier of [`Self::solve_dual`]: the SAME single-phase dual
    /// simplex, in checked machine-word rational arithmetic ([`SmallRat`]).
    ///
    /// # Exactness / equivalence contract
    ///
    /// Every arithmetic step is exact (reduced `i128` rationals) and every
    /// heuristic decision (Dantzig entering column: largest positive reduced
    /// cost, first index wins ties; ratio test: smallest ratio, first row wins
    /// ties) compares exact rationals, so the pivot sequence is IDENTICAL to
    /// [`Self::solve_dual_big`]'s. A run that returns
    /// [`SmallDualOutcome::Solved`] therefore carries exactly the bound, dual
    /// point and primal point the BigRational tier would have produced
    /// (differentially pinned by `small_simplex_matches_big_on_random_instances`).
    ///
    /// # Fail-closed overflow handling
    ///
    /// Any value that does not fit an `i128` rational — in the model conversion,
    /// a pivot update, a comparison's cross-multiplication, or the bound
    /// accumulation — yields [`SmallDualOutcome::Overflow`], and the caller
    /// re-solves with BigRational from scratch. No partial small-tier state is
    /// ever reused, and no rounding exists anywhere in this tier.
    ///
    /// `early_stop_bound` mirrors [`Self::solve_dual`]'s in-simplex early exit;
    /// a checked overflow inside the (advisory) running-bound computation only
    /// skips that check, never perturbs the solve.
    fn solve_dual_small(
        &self,
        should_stop: &dyn Fn() -> bool,
        early_stop_bound: Option<i128>,
    ) -> SmallDualOutcome {
        use SmallDualOutcome::{Overflow, Solved};

        let m = self.rows.len(); // dual variables (one per primal row)
        let n = self.c.len(); // dual constraints (one per primal variable)

        // --- Convert the model into i128 rationals (decline -> BigRational). ---
        let mut c_small: Vec<SmallRat> = Vec::with_capacity(n);
        for value in &self.c {
            let Some(small) = SmallRat::from_big(value) else {
                return Overflow;
            };
            c_small.push(small);
        }
        let Some(offset) = SmallRat::from_big(&self.offset) else {
            return Overflow;
        };
        let mut rows_small: Vec<(Vec<(usize, SmallRat)>, SmallRat)> = Vec::with_capacity(m);
        for row in &self.rows {
            let Some(b) = SmallRat::from_big(&row.b) else {
                return Overflow;
            };
            let mut coeffs = Vec::with_capacity(row.coeffs.len());
            for &(v, ref coeff) in &row.coeffs {
                let Some(small) = SmallRat::from_big(coeff) else {
                    return Overflow;
                };
                coeffs.push((v, small));
            }
            rows_small.push((coeffs, b));
        }

        // Mirrors the big tier's `m.checked_add(n)?` decline.
        let Some(total_cols) = m.checked_add(n) else {
            return Solved(None);
        };

        // Tableau layout identical to the big tier: rows = dual constraints
        // (0..n), columns = m structural (y) then n slack (s). Built row by
        // row so the stop/memory guard is observed DURING the (potentially
        // multi-GB) initialization, not only after it.
        let mut tab: Vec<Vec<SmallRat>> = Vec::with_capacity(n);
        for i in 0..n {
            if i % TABLEAU_INIT_POLL_ROWS == 0 && should_stop() {
                return Solved(None);
            }
            tab.push(vec![SmallRat::ZERO; total_cols]);
        }
        let mut rhs: Vec<SmallRat> = vec![SmallRat::ZERO; n];
        let mut obj: Vec<SmallRat> = vec![SmallRat::ZERO; total_cols];
        for (r, (coeffs, b)) in rows_small.iter().enumerate() {
            for &(v, coeff) in coeffs {
                tab[v][r] = coeff;
            }
            obj[r] = *b;
        }
        for v in 0..n {
            tab[v][m + v] = SmallRat::ONE;
            rhs[v] = c_small[v];
        }
        debug_assert!(rhs.iter().all(|r| !r.is_negative()));

        let mut basis: Vec<usize> = (0..n).map(|v| m + v).collect();

        let mut optimal = false;
        for _ in 0..MAX_PIVOTS {
            if should_stop() {
                break;
            }
            // Entering column: largest positive reduced cost (Dantzig), first
            // index on ties — exactly the big tier's `*reduced_cost > best`.
            let mut entering: Option<usize> = None;
            let mut best = SmallRat::ZERO;
            for (col, reduced_cost) in obj.iter().enumerate() {
                match reduced_cost.checked_cmp(best) {
                    Some(std::cmp::Ordering::Greater) => {
                        best = *reduced_cost;
                        entering = Some(col);
                    }
                    Some(_) => {}
                    None => return Overflow,
                }
            }
            let Some(col) = entering else {
                optimal = true;
                break;
            };

            // Ratio test: smallest rhs[i]/tab[i][col] over tab[i][col] > 0, first
            // row on ties — exactly the big tier's `ratio >= br => skip`.
            let mut leaving: Option<usize> = None;
            let mut best_ratio: Option<SmallRat> = None;
            for i in 0..n {
                let a = tab[i][col];
                if !a.is_positive() {
                    continue;
                }
                let Some(ratio) = rhs[i].checked_div(a) else {
                    return Overflow;
                };
                let take = match best_ratio {
                    Some(br) => match ratio.checked_cmp(br) {
                        Some(std::cmp::Ordering::Less) => true,
                        Some(_) => false,
                        None => return Overflow,
                    },
                    None => true,
                };
                if take {
                    best_ratio = Some(ratio);
                    leaving = Some(i);
                }
            }
            let Some(prow) = leaving else {
                // Dual unbounded => primal infeasible; decline (same as big tier).
                return Solved(None);
            };

            match pivot_small(&mut tab, &mut rhs, &mut obj, prow, col, n, should_stop) {
                PivotOutcome::Done => {}
                // Mid-pivot stop: the tableau is inconsistent and the whole
                // solve declines (escalating to the BigRational tier would only
                // burn its init before declining the same way). Reported at the
                // source, so a strided memory-guard trip is never re-polled and
                // misclassified as overflow.
                PivotOutcome::Stopped => return Solved(None),
                PivotOutcome::Overflow => return Overflow,
            }
            basis[prow] = col;

            // In-simplex early exit (see [`Self::solve_dual`]): stop once the
            // current (dual-feasible) vertex's bound certifies the target. An
            // overflow inside this ADVISORY check only skips the check — the
            // solve itself continues exactly as without a target.
            if let Some(target) = early_stop_bound {
                let running = small_vertex_bound(offset, &rows_small, &basis, &rhs, m, n);
                if running
                    .and_then(SmallRat::ceil_i128)
                    .is_some_and(|bound| bound >= target)
                {
                    break;
                }
            }
        }

        // Current dual-feasible point y from the basis (identical readout).
        let mut y: Vec<SmallRat> = vec![SmallRat::ZERO; m];
        for i in 0..n {
            if basis[i] < m {
                y[basis[i]] = rhs[i];
            }
        }
        // Sound bound = offset + b · y, computed exactly in i128 rationals.
        let mut exact_bound = offset;
        for (r, (_, b)) in rows_small.iter().enumerate() {
            if y[r].is_zero() {
                continue;
            }
            let Some(product) = b.checked_mul(y[r]) else {
                return Overflow;
            };
            let Some(sum) = exact_bound.checked_add(product) else {
                return Overflow;
            };
            exact_bound = sum;
        }

        // `ceil` of the same exact rational the big tier would ceil: an i128
        // range failure here would fail there too, so a `None` bound (never a
        // different bound) is the mirrored outcome.
        let Some(bound) = exact_bound.ceil_i128() else {
            return Solved(None);
        };
        let primal = if optimal {
            let obj_big: Vec<BigRational> = obj.iter().map(SmallRat::to_big).collect();
            self.recover_primal(&obj_big, m, n)
        } else {
            None
        };
        Solved(Some(DualSolution {
            bound,
            exact_bound: exact_bound.to_big(),
            duals: y.iter().map(SmallRat::to_big).collect(),
            primal,
        }))
    }

    /// The f64-certified middle tier of [`Self::solve_dual`]: an **advisory** f64
    /// simplex finds a dual point fast, then ONE exact bigint pass turns it into a
    /// verified dual-feasible point whose bound is certified by weak duality.
    ///
    /// # Why the result is sound no matter what the f64 simplex did
    ///
    /// Weak duality needs only `y >= 0` and `A^T y <= c` — nothing about how `y`
    /// was found. The f64 dual is (a) clamped to `y >= 0` and converted
    /// **exactly** to rationals (every finite f64 IS a rational), then (b) made
    /// exactly dual-feasible by the box-row repair: for each variable `v` whose
    /// exact structural slack `d_v = c_v - (A^T_struct y)_v` is negative, the box
    /// row `-x_v >= -1` gets multiplier `-d_v > 0`, which restores
    /// `(A^T y)_v <= c_v` **with equality** and (its `b = -1`) lowers the bound by
    /// `-d_v`. The repaired point is therefore exactly dual-feasible by
    /// construction, and `offset + b·y` — accumulated in exact arithmetic — is a
    /// sound lower bound. An inaccurate f64 dual only makes the repair larger and
    /// the bound WEAKER (never higher than the true LP optimum), and the exact
    /// `duals`/`exact_bound` returned satisfy every invariant the reduced-cost
    /// fixing and Farkas-certificate consumers rely on (`d_v >= 0` exactly).
    ///
    /// # Fail-closed
    ///
    /// Declines (`None` → the caller re-solves with BigRational) when: the model
    /// does not end in the canonical box rows (build invariant violated), any
    /// coefficient has no finite f64 image, the f64 simplex declines / returns a
    /// malformed dual / did NOT converge to optimality within its (deliberately
    /// tiny) budget, an f64→rational conversion fails, the certified bound's
    /// ceiling leaves `i128`, or the quality gate rejects (the certified bound is
    /// detectably far below the f64 solve's own optimum estimate). A decline
    /// never changes any result — only which tier pays for it.
    ///
    /// The returned `primal` is the f64 point mapped back to original variable
    /// space (advisory, cut separation only), mirroring the exact tiers.
    fn solve_dual_f64_certified(&self, should_stop: &dyn Fn() -> bool) -> Option<DualSolution> {
        let m = self.rows.len();
        let n = self.c.len();
        // Structural rows are everything before the n trailing box rows that
        // `build` appends. Verify that invariant literally (fail closed).
        let m_struct = m.checked_sub(n)?;
        let minus_one = -BigRational::one();
        for v in 0..n {
            let row = &self.rows[m_struct + v];
            if row.b != minus_one || row.coeffs.len() != 1 {
                return None;
            }
            let (var, coeff) = &row.coeffs[0];
            if *var != v || *coeff != minus_one {
                return None;
            }
        }

        // --- Advisory f64 image of the complemented-space LP (rounding is fine:
        //     nothing from this block is trusted). ---
        let to_finite_f64 = |value: &BigRational| -> Option<f64> {
            let f = value.to_f64()?;
            f.is_finite().then_some(f)
        };
        let mut c_f64 = Vec::with_capacity(n);
        for value in &self.c {
            c_f64.push(to_finite_f64(value)?);
        }
        let mut rows_f64 = Vec::with_capacity(m_struct);
        for row in &self.rows[..m_struct] {
            let b = to_finite_f64(&row.b)?;
            let mut coeffs = Vec::with_capacity(row.coeffs.len());
            for &(v, ref coeff) in &row.coeffs {
                coeffs.push((v, to_finite_f64(coeff)?));
            }
            rows_f64.push((coeffs, b));
        }

        // --- Power-of-two equilibration (EXACT in f64: scaling by 2^k neither
        // rounds a value nor moves the primal optimum). The simplex's pricing
        // tolerances scale with the data magnitude, so a 2^30-coefficient model
        // solved raw stops ~1e-7*2^30 ≈ 100 objective units short of the true
        // optimum — measured to cost a full integer unit of certified floor on
        // the diagcomm family. Scaling the objective and each row to ~unit
        // magnitude makes the tolerances effectively absolute; the duals are
        // un-scaled below by the same exact powers of two. ---
        let pow2_near = |x: f64| -> f64 {
            if x > 0.0 && x.is_finite() {
                let e = x.log2().round();
                let s = e.exp2();
                if s.is_finite() && s > 0.0 {
                    s
                } else {
                    1.0
                }
            } else {
                1.0
            }
        };
        let c_max = c_f64.iter().fold(0.0f64, |acc, c| acc.max(c.abs()));
        let s_obj = pow2_near(c_max);
        let mut c_scaled = c_f64.clone();
        for c in &mut c_scaled {
            *c /= s_obj;
        }
        let mut row_scales = Vec::with_capacity(m_struct);
        let rows_scaled: Vec<(Vec<(usize, f64)>, f64)> = rows_f64
            .into_iter()
            .map(|(mut coeffs, mut b)| {
                let mag = coeffs.iter().fold(b.abs(), |acc, &(_, a)| acc.max(a.abs()));
                let s_row = pow2_near(mag);
                row_scales.push(s_row);
                for (_, a) in &mut coeffs {
                    *a /= s_row;
                }
                b /= s_row;
                (coeffs, b)
            })
            .collect();

        let (dual_f64, primal_f64, converged) =
            crate::optimize::safe_lp_bound::approx_dual_for_box_lp(
                n,
                c_scaled,
                rows_scaled,
                F64_TIER_SIMPLEX_BUDGET,
                should_stop,
            )?;
        // Convergence requirement: a dual from a stopped/capped simplex is not
        // worth the exact-verification pass — measured on the overflow corpus,
        // non-converged duals only get worse with more budget, and their
        // certified bounds are uselessly weak. Fail closed to the exact path.
        if !converged || dual_f64.len() != m_struct || primal_f64.len() != n {
            return None;
        }

        // --- Exact certification pass (the only trusted arithmetic). ---
        // Structural duals: un-scale back to the original model (row r of the
        // scaled model is `a_r/s_r · x >= b_r/s_r`, so its dual `y'_r` maps to
        // `y_r = y'_r * s_obj / s_r` — a power-of-two ratio, exact in f64 for
        // normal results; a subnormal/overflow edge only perturbs the ADVISORY
        // dual, which the exact verification below absorbs as tightness, never
        // soundness), clamp to >= 0 and convert EXACTLY to rationals.
        let mut y: Vec<BigRational> = Vec::with_capacity(m);
        for (r, &yr_scaled) in dual_f64.iter().enumerate() {
            let yr = yr_scaled * (s_obj / row_scales[r]);
            y.push(if yr.is_finite() && yr > 0.0 {
                BigRational::from_float(yr)?
            } else {
                BigRational::zero()
            });
        }
        // (A^T_struct y) per variable and the structural part of b·y, exact.
        let mut aty = vec![BigRational::zero(); n];
        let mut exact_bound = self.offset.clone();
        for (r, row) in self.rows[..m_struct].iter().enumerate() {
            let yr = &y[r];
            if yr.is_zero() {
                continue;
            }
            for &(v, ref coeff) in &row.coeffs {
                aty[v] += yr * coeff;
            }
            exact_bound += &row.b * yr;
        }
        // Box-row repair: multiplier max(0, (A^T y)_v - c_v) restores dual
        // feasibility exactly; each unit costs 1 on the bound (box b = -1).
        for v in 0..n {
            let excess = &aty[v] - &self.c[v];
            if excess.is_positive() {
                exact_bound -= &excess;
                y.push(excess);
            } else {
                y.push(BigRational::zero());
            }
        }
        debug_assert_eq!(y.len(), m);

        let bound = rational_ceil_to_i64(&exact_bound)?;

        // --- Quality gate (tightness only; never soundness). The f64 solve's own
        // primal objective estimate ~ LP*; if the certified bound is far below it
        // the simplex did not converge to a good dual, and the exact tier's tight
        // bound is worth its cost. Comparison in f64 (advisory decision). ---
        let mut objective_estimate = self.offset.to_f64().unwrap_or(0.0);
        for (v, &x) in primal_f64.iter().enumerate() {
            objective_estimate += c_f64[v] * x.clamp(0.0, 1.0);
        }
        let certified_estimate = exact_bound.to_f64().unwrap_or(f64::NEG_INFINITY);
        if !objective_estimate.is_finite()
            || objective_estimate - certified_estimate
                > F64_TIER_QUALITY_SLACK * (1.0 + objective_estimate.abs())
        {
            return None;
        }

        // Advisory primal in ORIGINAL variable space (clamp + un-complement),
        // mirroring `recover_primal`. Failure to map only drops the point.
        let one = BigRational::one();
        let mut primal = Vec::with_capacity(n);
        let mut primal_ok = true;
        for (v, &value) in primal_f64.iter().enumerate() {
            if !value.is_finite() {
                primal_ok = false;
                break;
            }
            let Some(mut rat) = BigRational::from_float(value.clamp(0.0, 1.0)) else {
                primal_ok = false;
                break;
            };
            if self.complement[v] {
                rat = &one - rat;
            }
            primal.push(rat);
        }

        Some(DualSolution {
            bound,
            exact_bound,
            duals: y,
            primal: primal_ok.then_some(primal),
        })
    }

    /// Recovers the fractional primal LP point in **original** variable space from
    /// the optimal dual tableau's objective row.
    ///
    /// For the dual `max b·y` in standard form `A^T y + s = c`, complementary
    /// slackness makes the optimal value of primal variable `x'_v` (in
    /// *complemented* LP space) equal to the negated reduced cost of the dual slack
    /// `s_v`, i.e. `x'_v = -obj[m + v]` at optimality. We then un-complement
    /// (`x_v = 1 - x'_v` where the variable was complemented) and clamp into
    /// `[0, 1]` defensively. This point is **advisory only** (cut separation);
    /// no soundness guarantee rests on it, hence the clamp rather than a hard
    /// failure on out-of-range values.
    fn recover_primal(&self, obj: &[BigRational], m: usize, n: usize) -> Option<Vec<BigRational>> {
        let zero = BigRational::zero();
        let one = BigRational::one();
        let mut x = Vec::with_capacity(n);
        for v in 0..n {
            // x'_v = -reduced_cost(slack_v).
            let mut val = -obj.get(m + v)?.clone();
            // Clamp to [0,1] (advisory point; tiny dual degeneracy can stray).
            if val < zero {
                val = zero.clone();
            } else if val > one {
                val = one.clone();
            }
            // Un-complement back to original space.
            if *self.complement.get(v)? {
                val = &one - val;
            }
            x.push(val);
        }
        Some(x)
    }

    /// Derives reduced-cost variable fixings from a dual-feasible point `dual`.
    ///
    /// For each (complemented-space) variable `v` we compute the exact dual slack
    /// `d_v = c_v - (A^T y)_v` (`>= 0` by dual feasibility) and apply the rule
    /// proven in [`lp_reduced_cost_fixings`]: if `LB + d_v > strict_target`
    /// (strict, exact rational; `strict_target = incumbent_ub - 1` and
    /// `LB = dual.exact_bound`), then every strictly-better assignment has
    /// `x'_v = 0`, which un-complements to a fix of the ORIGINAL variable `v+1`.
    ///
    /// Only `d_v > 0` can ever fix (a zero reduced cost never exceeds the
    /// non-negative gap), so we skip those cheaply. Each fixing is independently
    /// sound; we never emit a fix we cannot certify by the strict rational test.
    fn reduced_cost_fixings(
        &self,
        dual: &DualSolution,
        strict_target: &BigRational,
    ) -> Vec<ReducedCostFixing> {
        let n = self.c.len();
        let y = &dual.duals;
        let lb = &dual.exact_bound;

        // Accumulate (A^T y)_v exactly: for each row r with dual value y_r, add
        // y_r * A_{r,v} to column v. Sparse over the row's non-zeros.
        let mut aty: Vec<BigRational> = vec![BigRational::zero(); n];
        for (r, row) in self.rows.iter().enumerate() {
            let Some(yr) = y.get(r) else { continue };
            if yr.is_zero() {
                continue;
            }
            for &(v, ref coeff) in &row.coeffs {
                if v < n {
                    aty[v] += yr * coeff;
                }
            }
        }

        let mut fixings = Vec::new();
        for (v, (c_v, aty_v)) in self.c.iter().zip(aty.iter()).enumerate() {
            // Exact reduced cost d_v = c_v - (A^T y)_v. Dual feasibility guarantees
            // d_v >= 0; a tiny negative from a non-optimal/degenerate vertex would
            // only make the (strict) test fail, never produce an unsound fixing.
            let d_v = c_v - aty_v;
            if !d_v.is_positive() {
                continue;
            }
            // Sound fixing iff LB + d_v > strict_target (exact, strict).
            let lhs = lb + &d_v;
            if &lhs > strict_target {
                // x'_v = 0 is forced. Un-complement to original space.
                let Ok(var0) = u32::try_from(v) else { continue };
                let var = var0.saturating_add(1);
                // complement[v] == true => x'_v = 1 - x_v, so x'_v=0 => x_v=1.
                // complement[v] == false => x'_v = x_v, so x'_v=0 => x_v=0.
                let value = *self.complement.get(v).unwrap_or(&false);
                fixings.push(ReducedCostFixing { var, value });
            }
        }
        fixings
    }

    /// Builds a [`LpFarkasCert`] for the lower bound `dual.bound` produced by this
    /// model and dual point, in the *complemented* LP space.
    ///
    /// # The encoding (see the module doc of [`crate::optimize::farkas_cert`])
    ///
    /// The conclusion is the objective-as-a-row `c . x >= (L - offset)` (Ge). The
    /// premises are exactly the constraints the dual was solved against, all in
    /// `Ge` form, so that the multiplier-weighted combination reproduces `c`
    /// EXACTLY (the checker requires zero coefficient residual):
    ///
    /// 1. one `Ge` premise per `LpModel` row (`A x >= b`, incl. box rows), with
    ///    multiplier `y_r` (the dual point — `dual.duals`); plus
    /// 2. one `x_v >= 0` lower-bound premise per variable with multiplier the
    ///    residual reduced cost `d_v = c_v - (A^T y)_v >= 0` (dual feasibility).
    ///
    /// Then `Sum mu_r a_r = (A^T y) + d = c` exactly, so the coefficients cancel.
    /// The `Ge`-normalized combined constant is `-(b . y)` and the `Ge`-normalized
    /// conclusion constant is `-(L - offset)`, so step 8 reads
    /// `L - offset - sigma <= b . y`, i.e. `L - sigma <= offset + b . y =
    /// exact_bound`. With `sigma = L - exact_bound >= 0` this is an equality
    /// `exact_bound <= exact_bound`, which holds, and the proven quantity is
    /// exactly `exact_bound` — a sound lower bound by weak duality.
    ///
    /// Returns `None` only on the `i128`/rational conversions that can fail; a
    /// `None` simply means no certificate is offered (today's path is used).
    fn build_farkas_cert(&self, dual: &DualSolution) -> Option<LpFarkasCert> {
        let n = self.c.len();
        let y = &dual.duals;

        // Re-derive the residual reduced cost d_v = c_v - (A^T y)_v exactly, in
        // the SAME way `reduced_cost_fixings` does, but over ALL rows (structural
        // + box) since `y` covers all of them.
        let mut aty: Vec<BigRational> = vec![BigRational::zero(); n];
        for (r, row) in self.rows.iter().enumerate() {
            let Some(yr) = y.get(r) else { continue };
            if yr.is_zero() {
                continue;
            }
            for &(v, ref coeff) in &row.coeffs {
                if v < n {
                    aty[v] += yr * coeff;
                }
            }
        }

        let mut premises: Vec<LinConZ> = Vec::new();
        let mut multipliers: Vec<QPair> = Vec::new();

        // (1) One Ge premise per model row, multiplier y_r.
        for (r, row) in self.rows.iter().enumerate() {
            let coeffs = row
                .coeffs
                .iter()
                .map(|(v, c)| (var_name(*v), rational_to_qpair(c)))
                .collect();
            premises.push(LinConZ {
                coeffs,
                kind: CertKind::Ge,
                constant: rational_to_qpair(&row.b),
            });
            let yr = y.get(r).cloned().unwrap_or_else(BigRational::zero);
            multipliers.push(rational_to_qpair(&yr));
        }

        // (2) One x_v >= 0 lower-bound premise per variable, multiplier d_v.
        // d_v = c_v - aty_v (>= 0 by dual feasibility). A tiny negative from a
        // degenerate vertex would only make `check_slack` reject; never unsound.
        let one_q = QPair::from_int(&num_bigint::BigInt::one());
        let zero_q = QPair::from_int(&num_bigint::BigInt::zero());
        for v in 0..n {
            let d_v = &self.c[v] - &aty[v];
            premises.push(LinConZ {
                coeffs: vec![(var_name(v), one_q.clone())],
                kind: CertKind::Ge,
                constant: zero_q.clone(),
            });
            multipliers.push(rational_to_qpair(&d_v));
        }

        // Conclusion: c . x >= (L - offset), in complemented space.
        let concl_coeffs: Vec<(String, QPair)> = (0..n)
            .filter(|&v| !self.c[v].is_zero())
            .map(|v| (var_name(v), rational_to_qpair(&self.c[v])))
            .collect();
        let l = dual.bound;
        let concl_const_rat = int(l) - &self.offset;
        let conclusion = LinConZ {
            coeffs: concl_coeffs,
            kind: CertKind::Ge,
            constant: rational_to_qpair(&concl_const_rat),
        };

        // sigma = L - exact_bound >= 0 (L = ceil(exact_bound) >= exact_bound).
        let sigma_rat = int(l) - &dual.exact_bound;
        // margin = sigma + 1 (one integer unit of headroom).
        let margin_rat = &sigma_rat + BigRational::one();

        let cert = SCertZ {
            base: CertZ {
                premises,
                multipliers,
                conclusion,
            },
            slack: rational_to_qpair(&sigma_rat),
            margin: rational_to_qpair(&margin_rat),
        };

        let num_vars = u32::try_from(n).ok()?;
        Some(LpFarkasCert {
            cert,
            claimed_bound: l,
            num_vars,
        })
    }
}

/// Renders an LP column index as the variable name used in the certificate.
fn var_name(v: usize) -> String {
    v.to_string()
}

/// Converts a [`BigRational`] to a certificate [`QPair`] `(numer, denom)`.
///
/// `BigRational` keeps `denom > 0` and reduced form; we copy `numer`/`denom` as
/// they are. The certificate checker never assumes reduced pairs, so this is a
/// faithful (and `den > 0`) encoding.
fn rational_to_qpair(r: &BigRational) -> QPair {
    QPair::new(r.numer().clone(), r.denom().clone())
}

/// Builds one `>= ` row for `constraint` scaled by `sign` (1 for the row as
/// written, -1 for the reversed direction of an equality), rewriting literals
/// into complemented-variable space.
fn build_row(constraint: &PbConstraint, complement: &[bool], n: usize, sign: i128) -> Option<Row> {
    // Accumulate per-variable coefficient and a constant moved to the rhs.
    let mut coeff_by_var: BTreeMap<usize, BigRational> = BTreeMap::new();
    let mut rhs = int(constraint.rhs.checked_mul(sign)?);
    for term in &constraint.terms {
        let [lit] = term.lits.as_slice() else {
            return None; // non-linear term: cannot model as LP row.
        };
        let v = var_index(*lit, n)?;
        // term contributes coeff * value(lit). value(lit) = x_v (positive) or
        // 1 - x_v (negated). Combined with `sign`.
        let base = int(term.coeff.checked_mul(sign)?);
        // Resolve the literal value in ORIGINAL variable space first.
        // positive literal: + base * x_v
        // negated literal:  + base - base * x_v   (constant -> rhs side later)
        let (mut var_coeff, lit_const) = if lit.negated {
            (-(&base), base.clone())
        } else {
            (base.clone(), BigRational::zero())
        };
        // Now apply complementation: if variable v was replaced by 1 - x'_v,
        // then x_v = 1 - x'_v, so var_coeff * x_v = var_coeff - var_coeff * x'_v.
        let mut const_from_complement = BigRational::zero();
        if complement[v] {
            const_from_complement = var_coeff.clone(); // var_coeff * 1
            var_coeff = -var_coeff;
        }
        *coeff_by_var.entry(v).or_insert_with(BigRational::zero) += var_coeff;
        // Constants on the LHS move to the rhs with a sign flip:
        // LHS has (lit_const + const_from_complement); subtract from both sides.
        rhs -= lit_const;
        rhs -= const_from_complement;
    }
    let coeffs: Vec<(usize, BigRational)> = coeff_by_var
        .into_iter()
        .filter(|(_, c)| !c.is_zero())
        .collect();
    Some(Row { coeffs, b: rhs })
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

/// Outcome of a single `i128` fast-tier pivot ([`pivot_small`]).
///
/// Distinguishing a stop from an overflow AT THE SOURCE (rather than the old
/// re-poll of `should_stop` after a bare `false`) matters under memory pressure:
/// a mid-pivot memory-guard trip must decline the whole solve, NOT be
/// misclassified as an overflow that escalates to the BigRational tier — whose
/// multi-GB tableau init is exactly what the guard is trying to prevent. The
/// re-poll was also unreliable once the memory poll is strided (the guard's
/// countdown can be mid-stride on the re-check).
enum PivotOutcome {
    /// Pivot completed; the tableau is consistent.
    Done,
    /// A checked `i128` operation overflowed. The tableau is inconsistent; the
    /// caller abandons the fast tier and re-solves with BigRational.
    Overflow,
    /// `should_stop` fired mid-pivot. The tableau is inconsistent; the caller
    /// declines the whole solve (escalating would only burn the big-tier init
    /// before declining the same way).
    Stopped,
}

/// Outcome of the `i128` fast tier ([`LpModel::solve_dual_small`]).
enum SmallDualOutcome {
    /// The small tier completed without overflow. The payload is exactly what
    /// the BigRational tier would have returned (including `None` declines for
    /// dual-unbounded / out-of-`i128`-ceil, which are value-identical).
    Solved(Option<DualSolution>),
    /// Some value did not fit checked `i128` rational arithmetic. The caller
    /// must re-solve with the BigRational tier; nothing from the small run is
    /// reused.
    Overflow,
}

/// Exact rational with `i128` numerator/denominator: `den > 0`, fully reduced.
///
/// All operations are **checked**: any overflow returns `None` and the caller
/// abandons the fast tier ([`SmallDualOutcome::Overflow`]). There is no rounding
/// anywhere — a sequence of successful `SmallRat` operations computes exactly
/// the same rational a `BigRational` sequence would.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct SmallRat {
    num: i128,
    den: i128,
}

impl SmallRat {
    const ZERO: SmallRat = SmallRat { num: 0, den: 1 };
    const ONE: SmallRat = SmallRat { num: 1, den: 1 };

    /// Builds a reduced, sign-normalized rational. `None` when `den == 0` or the
    /// reduced value does not fit (only possible for `i128::MIN` magnitudes).
    fn new(num: i128, den: i128) -> Option<Self> {
        if den == 0 {
            return None;
        }
        let negative = (num < 0) != (den < 0);
        let mut un = num.unsigned_abs();
        let mut ud = den.unsigned_abs();
        let g = gcd_u128(un, ud); // >= 1 because ud >= 1.
        un /= g;
        ud /= g;
        let num = i128::try_from(un).ok()?;
        let den = i128::try_from(ud).ok()?;
        Some(Self {
            num: if negative { -num } else { num },
            den,
        })
    }

    /// Converts a (reduced, `den > 0`) [`BigRational`]; `None` when either side
    /// does not fit an `i128`.
    fn from_big(value: &BigRational) -> Option<Self> {
        let num = value.numer().to_i128()?;
        let den = value.denom().to_i128()?;
        debug_assert!(den > 0);
        Some(Self { num, den })
    }

    fn to_big(&self) -> BigRational {
        BigRational::new(self.num.into(), self.den.into())
    }

    fn is_zero(self) -> bool {
        self.num == 0
    }
    fn is_positive(self) -> bool {
        self.num > 0
    }
    fn is_negative(self) -> bool {
        self.num < 0
    }

    /// `self + rhs`, exact; `None` on overflow. Uses the common-denominator gcd
    /// trick so intermediates stay as small as possible.
    fn checked_add(self, rhs: Self) -> Option<Self> {
        // dens > 0, so the gcd fits i128.
        let g = gcd_u128(self.den.unsigned_abs(), rhs.den.unsigned_abs()) as i128;
        let l_scale = rhs.den / g;
        let r_scale = self.den / g;
        let num = self
            .num
            .checked_mul(l_scale)?
            .checked_add(rhs.num.checked_mul(r_scale)?)?;
        let den = self.den.checked_mul(l_scale)?;
        Self::new(num, den)
    }

    /// `self - rhs`, exact; `None` on overflow.
    fn checked_sub(self, rhs: Self) -> Option<Self> {
        self.checked_add(Self {
            num: rhs.num.checked_neg()?,
            den: rhs.den,
        })
    }

    /// `self * rhs`, exact; `None` on overflow. Cross-cancels gcd's first so the
    /// result is already reduced and intermediates stay small.
    fn checked_mul(self, rhs: Self) -> Option<Self> {
        if self.num == 0 || rhs.num == 0 {
            return Some(Self::ZERO);
        }
        // Both dens > 0 so both gcds fit i128 (each divides a positive den...
        // except gcd(num, den) where num may dominate: the gcd divides den > 0,
        // so it is <= den and fits).
        let g1 = gcd_u128(self.num.unsigned_abs(), rhs.den.unsigned_abs()) as i128;
        let g2 = gcd_u128(rhs.num.unsigned_abs(), self.den.unsigned_abs()) as i128;
        let a = self.num / g1;
        let d = rhs.den / g1;
        let c = rhs.num / g2;
        let b = self.den / g2;
        let num = a.checked_mul(c)?;
        let den = b.checked_mul(d)?;
        // gcd(a,b)=gcd(a,d)=gcd(c,b)=gcd(c,d)=1 => (num, den) already reduced.
        debug_assert!(den > 0);
        Some(Self { num, den })
    }

    /// `self / rhs`, exact; `None` when `rhs == 0` or on overflow.
    fn checked_div(self, rhs: Self) -> Option<Self> {
        if rhs.num == 0 {
            return None;
        }
        // Reciprocal with sign normalization (den must stay > 0).
        let recip = Self::new(rhs.den, rhs.num)?;
        self.checked_mul(recip)
    }

    /// Exact three-way comparison; `None` when the cross-multiplication
    /// overflows (treated as an i128-tier abort by callers).
    fn checked_cmp(self, rhs: Self) -> Option<std::cmp::Ordering> {
        // Sign fast path (dens are positive).
        let ls = self.num.signum();
        let rs = rhs.num.signum();
        if ls != rs {
            return Some(ls.cmp(&rs));
        }
        // a/b ? c/d  <=>  a*(d/g) ? c*(b/g)  with g = gcd(b, d) (b, d > 0).
        let g = gcd_u128(self.den.unsigned_abs(), rhs.den.unsigned_abs()) as i128;
        let lhs = self.num.checked_mul(rhs.den / g)?;
        let rhs_val = rhs.num.checked_mul(self.den / g)?;
        Some(lhs.cmp(&rhs_val))
    }

    /// Exact `ceil` as an `i128`; `None` only when the true ceiling exceeds the
    /// `i128` range (mirrors [`rational_ceil_to_i64`]'s `None`).
    fn ceil_i128(self) -> Option<i128> {
        debug_assert!(self.den > 0);
        let floor = self.num.div_euclid(self.den);
        if self.num.rem_euclid(self.den) == 0 {
            Some(floor)
        } else {
            floor.checked_add(1)
        }
    }
}

/// Binary GCD on `u128`. `gcd(x, 0) == x`, `gcd(0, 0) == 0` (callers guarantee
/// at least one argument is non-zero where a non-zero result is required).
fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    if a == 0 {
        return b;
    }
    if b == 0 {
        return a;
    }
    let shift = (a | b).trailing_zeros();
    a >>= a.trailing_zeros();
    loop {
        b >>= b.trailing_zeros();
        if a > b {
            std::mem::swap(&mut a, &mut b);
        }
        b -= a;
        if b == 0 {
            return a << shift;
        }
    }
}

/// Running bound `offset + b·y` of the small tier's CURRENT vertex, read
/// directly from the basis (`y[basis[i]] = rhs[i]`, all other `y` zero).
/// Advisory (used only by the in-simplex early exit): a `None` (overflow)
/// simply skips the check.
fn small_vertex_bound(
    offset: SmallRat,
    rows: &[(Vec<(usize, SmallRat)>, SmallRat)],
    basis: &[usize],
    rhs: &[SmallRat],
    m: usize,
    n: usize,
) -> Option<SmallRat> {
    let mut bound = offset;
    for i in 0..n {
        if basis[i] < m && !rhs[i].is_zero() {
            let b = rows[basis[i]].1;
            bound = bound.checked_add(b.checked_mul(rhs[i])?)?;
        }
    }
    Some(bound)
}

/// Gauss-Jordan pivot on `(prow, col)` in checked `i128` rational arithmetic —
/// the exact mirror of [`pivot`]. Returns a tri-state [`PivotOutcome`]:
/// `Overflow` on any checked-`i128` overflow (the caller abandons the fast
/// tier), `Stopped` when `should_stop` fires mid-pivot (polled every
/// [`PIVOT_POLL_ENTRIES`] entries at row granularity; the caller declines the
/// solve), or `Done`. Reporting the stop at the SOURCE removes the old
/// re-poll-and-guess in the caller, so a memory-guard trip can never be
/// mistaken for an overflow and escalated to the BigRational tier.
fn pivot_small(
    tab: &mut [Vec<SmallRat>],
    rhs: &mut [SmallRat],
    obj: &mut [SmallRat],
    prow: usize,
    col: usize,
    n: usize,
    should_stop: &dyn Fn() -> bool,
) -> PivotOutcome {
    let piv = tab[prow][col];
    // Normalize pivot row.
    for entry in tab[prow].iter_mut() {
        if !entry.is_zero() {
            let Some(value) = entry.checked_div(piv) else {
                return PivotOutcome::Overflow;
            };
            *entry = value;
        }
    }
    let Some(value) = rhs[prow].checked_div(piv) else {
        return PivotOutcome::Overflow;
    };
    rhs[prow] = value;
    // Snapshot the normalized pivot row (Copy elements: a cheap memcpy).
    let pivot_row: Vec<SmallRat> = tab[prow].clone();
    let pivot_rhs = rhs[prow];
    // Eliminate the entering column from all other constraint rows, polling at
    // row granularity so the poll-free window stays under PIVOT_POLL_ENTRIES.
    let mut entries_since_poll = 0usize;
    for i in 0..n {
        if i == prow {
            continue;
        }
        let factor = tab[i][col];
        if factor.is_zero() {
            continue;
        }
        entries_since_poll += pivot_row.len();
        if entries_since_poll >= PIVOT_POLL_ENTRIES {
            entries_since_poll = 0;
            if should_stop() {
                return PivotOutcome::Stopped;
            }
        }
        let target = &mut tab[i];
        for (k, pivot_val) in pivot_row.iter().enumerate() {
            if pivot_val.is_zero() {
                continue;
            }
            let Some(delta) = factor.checked_mul(*pivot_val) else {
                return PivotOutcome::Overflow;
            };
            let Some(updated) = target[k].checked_sub(delta) else {
                return PivotOutcome::Overflow;
            };
            target[k] = updated;
        }
        let Some(delta) = factor.checked_mul(pivot_rhs) else {
            return PivotOutcome::Overflow;
        };
        let Some(updated) = rhs[i].checked_sub(delta) else {
            return PivotOutcome::Overflow;
        };
        rhs[i] = updated;
    }
    // Eliminate the entering column from the objective row.
    let factor = obj[col];
    if !factor.is_zero() {
        for (obj_entry, pivot_val) in obj.iter_mut().zip(pivot_row.iter()) {
            if pivot_val.is_zero() {
                continue;
            }
            let Some(delta) = factor.checked_mul(*pivot_val) else {
                return PivotOutcome::Overflow;
            };
            let Some(updated) = obj_entry.checked_sub(delta) else {
                return PivotOutcome::Overflow;
            };
            *obj_entry = updated;
        }
    }
    PivotOutcome::Done
}

/// Gauss-Jordan pivot on `(prow, col)` maintaining the tableau, rhs and the
/// objective (reduced-cost) row. Returns `false` when `should_stop` fires
/// mid-pivot (polled every [`PIVOT_POLL_ENTRIES`] entries at row granularity);
/// the tableau is then inconsistent and the caller must decline the solve.
fn pivot(
    tab: &mut [Vec<BigRational>],
    rhs: &mut [BigRational],
    obj: &mut [BigRational],
    prow: usize,
    col: usize,
    n: usize,
    should_stop: &dyn Fn() -> bool,
) -> bool {
    let piv = tab[prow][col].clone();
    // Normalize pivot row.
    for entry in tab[prow].iter_mut() {
        if !entry.is_zero() {
            *entry /= &piv;
        }
    }
    rhs[prow] /= &piv;
    // Snapshot the normalized pivot row so the elimination loops below can read
    // it without aliasing the row being written.
    let pivot_row: Vec<BigRational> = tab[prow].clone();
    let pivot_rhs = rhs[prow].clone();
    // Eliminate the entering column from all other constraint rows, polling at
    // row granularity so the poll-free window stays under PIVOT_POLL_ENTRIES.
    let mut entries_since_poll = 0usize;
    for i in 0..n {
        if i == prow {
            continue;
        }
        let factor = tab[i][col].clone();
        if factor.is_zero() {
            continue;
        }
        entries_since_poll += pivot_row.len();
        if entries_since_poll >= PIVOT_POLL_ENTRIES {
            entries_since_poll = 0;
            if should_stop() {
                return false;
            }
        }
        let target = &mut tab[i];
        for (k, pivot_val) in pivot_row.iter().enumerate() {
            if !pivot_val.is_zero() {
                let delta = &factor * pivot_val;
                target[k] -= delta;
            }
        }
        let delta = &factor * &pivot_rhs;
        rhs[i] -= delta;
    }
    // Eliminate the entering column from the objective row.
    let factor = obj[col].clone();
    if !factor.is_zero() {
        for (obj_entry, pivot_val) in obj.iter_mut().zip(pivot_row.iter()) {
            if !pivot_val.is_zero() {
                let delta = &factor * pivot_val;
                *obj_entry -= delta;
            }
        }
    }
    true
}

/// Exact ceiling of a rational, returned as `i128`. Returns `None` on overflow.
fn rational_ceil_to_i64(value: &BigRational) -> Option<i128> {
    let ceil = value.ceil(); // BigRational with denominator 1
    let int = ceil.to_integer(); // BigInt
    i128::try_from(int).ok()
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

    #[test]
    fn empty_objective_returns_none() {
        let obj = PbObjective { terms: vec![] };
        assert_eq!(lp_lower_bound(&obj, &[], 3, &never_stop), None);
    }

    #[test]
    fn unconstrained_nonneg_objective_bound_is_zero() {
        // min x1 + x2, no constraints, x in [0,1]. LP optimum is 0.
        let obj = PbObjective {
            terms: vec![term(1, lit(1)), term(1, lit(2))],
        };
        assert_eq!(lp_lower_bound(&obj, &[], 2, &never_stop), Some(0));
    }

    #[test]
    fn covering_constraint_forces_fractional_bound_ceiled() {
        // min x1 + x2 + x3  s.t.  x1 + x2 + x3 >= 1.  LP optimum = 1.
        let obj = PbObjective {
            terms: vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))],
        };
        let c = ge(vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))], 1);
        assert_eq!(lp_lower_bound(&obj, &[c], 3, &never_stop), Some(1));
    }

    #[test]
    fn fractional_lp_optimum_ceils_up() {
        // min x1 + x2  s.t.  2 x1 + 2 x2 >= 3.  LP optimum x1=x2=3/4 -> 3/2.
        // ceil(3/2) = 2, and the true integer optimum is 2 (need both = 1 -> 2,
        // or one=1 gives 2 >= 3? 2 < 3, infeasible; so both, obj 2). LB 2 <= 2.
        let obj = PbObjective {
            terms: vec![term(1, lit(1)), term(1, lit(2))],
        };
        let c = ge(vec![term(2, lit(1)), term(2, lit(2))], 3);
        assert_eq!(lp_lower_bound(&obj, &[c], 2, &never_stop), Some(2));
    }

    #[test]
    fn negated_literal_objective_complemented() {
        // min (1 - x1) = min ~x1.  Soft pays when x1 = 0.
        // Constraint: x1 >= 0 (trivial) -> LP can set x1 = 1, objective 0.
        let obj = PbObjective {
            terms: vec![term(1, neg(1))],
        };
        let bound = lp_lower_bound(&obj, &[], 1, &never_stop).expect("bound");
        assert!(bound <= 0, "bound {bound} must be <= integer optimum 0");
    }

    #[test]
    fn negated_literal_forced_true_gives_bound_one() {
        // min ~x1  s.t.  ~x1 >= 1  (i.e. x1 must be 0). Objective forced to 1.
        let obj = PbObjective {
            terms: vec![term(1, neg(1))],
        };
        let c = ge(vec![term(1, neg(1))], 1);
        assert_eq!(lp_lower_bound(&obj, &[c], 1, &never_stop), Some(1));
    }

    #[test]
    fn equality_constraint_split_into_two_rows() {
        // min x1 + x2  s.t.  x1 + x2 = 1.  LP optimum = 1.
        let obj = PbObjective {
            terms: vec![term(1, lit(1)), term(1, lit(2))],
        };
        let c = PbConstraint {
            terms: vec![term(1, lit(1)), term(1, lit(2))],
            rel: PbRel::Eq,
            rhs: 1,
        };
        assert_eq!(lp_lower_bound(&obj, &[c], 2, &never_stop), Some(1));
    }

    #[test]
    fn weighted_objective_bound() {
        // min 3 x1 + 5 x2  s.t.  x1 + x2 >= 1. LP optimum picks cheaper x1 = 1 -> 3.
        let obj = PbObjective {
            terms: vec![term(3, lit(1)), term(5, lit(2))],
        };
        let c = ge(vec![term(1, lit(1)), term(1, lit(2))], 1);
        assert_eq!(lp_lower_bound(&obj, &[c], 2, &never_stop), Some(3));
    }

    #[test]
    fn too_many_vars_declines() {
        let obj = PbObjective {
            terms: vec![term(1, lit(1))],
        };
        assert_eq!(
            lp_lower_bound(&obj, &[], (MAX_VARS as u32) + 1, &never_stop),
            None
        );
    }

    // --- Differential soundness: LP_LB <= brute-force integer optimum. ---

    /// Evaluates a linear PB constraint under a boolean assignment (0/1 per var).
    fn constraint_holds(c: &PbConstraint, x: &[bool]) -> bool {
        let mut lhs = 0i128;
        for term in &c.terms {
            let l = term.lits[0];
            let val = if l.negated {
                !x[(l.var - 1) as usize]
            } else {
                x[(l.var - 1) as usize]
            };
            if val {
                lhs += term.coeff;
            }
        }
        match c.rel {
            PbRel::Ge => lhs >= c.rhs,
            PbRel::Eq => lhs == c.rhs,
        }
    }

    fn objective_value(obj: &PbObjective, x: &[bool]) -> i128 {
        let mut total = 0i128;
        for term in &obj.terms {
            let l = term.lits[0];
            let val = if l.negated {
                !x[(l.var - 1) as usize]
            } else {
                x[(l.var - 1) as usize]
            };
            if val {
                total += term.coeff;
            }
        }
        total
    }

    /// Brute-force integer optimum over all 2^n assignments, or `None` if no
    /// assignment satisfies the constraints (infeasible).
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

    /// Tiny deterministic xorshift PRNG so the property test needs no dev-deps.
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

    #[test]
    fn differential_lp_lb_never_exceeds_brute_force_optimum() {
        let mut rng = Rng(0x1234_5678_9abc_def0);
        let mut checked_feasible = 0usize;
        for _ in 0..2000 {
            let n: u32 = rng.range(1, 6) as u32;
            // Random objective: each var gets coeff in [-3,4] (negatives exercise the
            // maximization / variable-complementation path), maybe a negated literal.
            let mut obj_terms = Vec::new();
            for v in 1..=n {
                let coeff = rng.range(-3, 4);
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

            // Random constraints: 0..3 rows of >= or =.
            let num_c = rng.range(0, 3);
            let mut constraints = Vec::new();
            for _ in 0..num_c {
                let mut terms = Vec::new();
                for v in 1..=n {
                    let coeff = rng.range(-2, 3);
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
                let rhs = rng.range(-2, 3);
                let rel = if rng.next() & 1 == 1 {
                    PbRel::Ge
                } else {
                    PbRel::Eq
                };
                constraints.push(PbConstraint { terms, rel, rhs });
            }

            let Some(opt) = brute_force_optimum(&obj, &constraints, n) else {
                continue; // infeasible instance: LP may decline or bound below; skip.
            };
            checked_feasible += 1;

            if let Some(lp_lb) = lp_lower_bound(&obj, &constraints, n, &never_stop) {
                assert!(
                    lp_lb <= opt,
                    "SOUNDNESS VIOLATION: LP_LB {lp_lb} > brute optimum {opt}\n\
                     objective={obj:?}\nconstraints={constraints:?}"
                );
            }
        }
        assert!(
            checked_feasible > 50,
            "expected many feasible instances, got {checked_feasible}"
        );
    }

    // --- Early-exit target: sound, and lossless for the optimality check. --- //

    /// With an early-exit target the returned floor must (a) stay a sound lower
    /// bound, and (b) whenever the full bound would have reached the target, the
    /// targeted bound must reach it too (the exit never costs the caller's
    /// `floor >= incumbent` optimality check). Uses brute force as the oracle
    /// and the true optimum as the incumbent-style target.
    #[test]
    fn early_exit_target_is_sound_and_never_costs_the_optimality_check() {
        let mut rng = Rng(0x7A46_E7E5_0DD1_CE77);
        let mut checked = 0usize;
        let mut early_certified = 0usize;
        for _ in 0..1500 {
            let n: u32 = rng.range(1, 6) as u32;
            let mut obj_terms = Vec::new();
            for v in 1..=n {
                let coeff = rng.range(-3, 4);
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

            let num_c = rng.range(0, 3);
            let mut constraints = Vec::new();
            for _ in 0..num_c {
                let mut terms = Vec::new();
                for v in 1..=n {
                    let coeff = rng.range(-2, 3);
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
                let rhs = rng.range(-2, 3);
                let rel = if rng.next() & 1 == 1 {
                    PbRel::Ge
                } else {
                    PbRel::Eq
                };
                constraints.push(PbConstraint { terms, rel, rhs });
            }

            let Some(opt) = brute_force_optimum(&obj, &constraints, n) else {
                continue;
            };
            checked += 1;

            let full = lp_lower_bound(&obj, &constraints, n, &never_stop);
            // The incumbent-style target: the true optimum (what the solver
            // passes once its first incumbent is optimal).
            let targeted =
                lp_lower_bound_with_target(&obj, &constraints, n, Some(opt), &never_stop);

            if let Some(t) = targeted {
                assert!(
                    t <= opt,
                    "SOUNDNESS VIOLATION: targeted LP_LB {t} > optimum {opt}\n\
                     objective={obj:?}\nconstraints={constraints:?}"
                );
            }
            match (full, targeted) {
                (Some(f), Some(t)) => {
                    // Whenever the full bound certifies the target, the targeted
                    // bound must certify it too (lossless for the caller).
                    if f >= opt {
                        assert!(
                            t >= opt,
                            "early exit LOST a certification: full {f} >= opt {opt} but \
                             targeted {t} < opt\nobjective={obj:?}\nconstraints={constraints:?}"
                        );
                        early_certified += 1;
                    }
                }
                (None, None) => {}
                (f, t) => panic!(
                    "Some/None divergence: full={f:?} targeted={t:?}\n\
                     objective={obj:?}\nconstraints={constraints:?}"
                ),
            }

            // No target: byte-identical to the plain entry point.
            assert_eq!(
                lp_lower_bound_with_target(&obj, &constraints, n, None, &never_stop),
                full,
                "target=None must be identical to lp_lower_bound"
            );
        }
        assert!(
            checked > 100,
            "expected many feasible instances, got {checked}"
        );
        assert!(
            early_certified > 50,
            "expected many instances where the floor certifies the optimum, got {early_certified}"
        );
    }

    // --- i128 fast tier: differential equivalence + overflow fallback. --- //

    /// The i128 fast tier must return EXACTLY what the BigRational tier returns
    /// whenever it completes (`Solved`), on a large randomized corpus covering
    /// negated literals, negative coefficients (complementation), equalities and
    /// infeasible duals. This is the differential pin for the two-tier dispatch:
    /// same bound, same exact rational bound, same dual point, same primal point.
    #[test]
    fn small_simplex_matches_big_on_random_instances() {
        let mut rng = Rng(0x51AC_C0DE_F00D_BEEF);
        let mut compared = 0usize;
        for _ in 0..3000 {
            let n: u32 = rng.range(1, 7) as u32;
            let mut obj_terms = Vec::new();
            for v in 1..=n {
                let coeff = rng.range(-9, 9);
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
                    let coeff = rng.range(-5, 6);
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
                let rhs = rng.range(-5, 6);
                let rel = if rng.next() & 3 == 0 {
                    PbRel::Eq
                } else {
                    PbRel::Ge
                };
                constraints.push(PbConstraint { terms, rel, rhs });
            }

            let Some(model) = LpModel::build(&obj, &constraints, n) else {
                continue;
            };
            let big = model.solve_dual_big(&never_stop, None);
            match model.solve_dual_small(&never_stop, None) {
                SmallDualOutcome::Overflow => continue, // fallback path; covered below.
                SmallDualOutcome::Solved(small) => {
                    compared += 1;
                    match (&small, &big) {
                        (None, None) => {}
                        (Some(s), Some(b)) => {
                            assert_eq!(
                                s.bound, b.bound,
                                "bound diverged\nobj={obj:?}\ncons={constraints:?}"
                            );
                            assert_eq!(
                                s.exact_bound, b.exact_bound,
                                "exact bound diverged\nobj={obj:?}\ncons={constraints:?}"
                            );
                            assert_eq!(
                                s.duals, b.duals,
                                "dual point diverged\nobj={obj:?}\ncons={constraints:?}"
                            );
                            assert_eq!(
                                s.primal, b.primal,
                                "primal point diverged\nobj={obj:?}\ncons={constraints:?}"
                            );
                        }
                        _ => panic!(
                            "Solved/None divergence: small={:?} big={:?}\nobj={obj:?}\ncons={constraints:?}",
                            small.is_some(),
                            big.is_some()
                        ),
                    }
                }
            }
        }
        assert!(
            compared > 1000,
            "expected the small tier to complete on most random instances, got {compared}"
        );
    }

    /// Coefficients near `i128::MAX` cannot be pivoted in checked i128 rationals:
    /// the small tier must report `Overflow` (never a wrong value) and the public
    /// `solve_dual` must transparently fall back to an exact-or-certified tier
    /// whose bound never exceeds the BigRational optimum (and stays sound).
    #[test]
    fn small_simplex_overflow_falls_back_to_big() {
        // min a*x1 + b*x2  s.t.  3*x1 + 5*x2 >= 7, with a, b huge (~2^126) and
        // chosen indivisible by 3/5 so no gcd cross-cancel rescues the ratio
        // test: comparing a/3 with b/5 cross-multiplies a*5 > i128::MAX.
        let a = (1i128 << 126) - 3;
        let b = (1i128 << 126) - 5;
        let obj = PbObjective {
            terms: vec![term(a, lit(1)), term(b, lit(2))],
        };
        let c = ge(vec![term(3, lit(1)), term(5, lit(2))], 7);
        let model = LpModel::build(&obj, &[c], 2).expect("model");

        assert!(
            matches!(
                model.solve_dual_small(&never_stop, None),
                SmallDualOutcome::Overflow
            ),
            "huge coefficients must trip the checked-i128 overflow guard"
        );

        // Only x1=x2=1 satisfies 3x1+5x2 >= 7 over {0,1}^2 -> integer optimum.
        let int_opt = a + b;
        let via_dispatch = model.solve_dual(&never_stop, None).expect("dispatch bound");
        let via_big = model.solve_dual_big(&never_stop, None).expect("big bound");
        // The dispatcher may resolve via the f64-certified tier, whose bound can
        // sit (slightly) below the BigRational LP optimum but NEVER above it —
        // THE soundness ordering of the middle tier.
        assert!(
            via_dispatch.bound <= via_big.bound,
            "dispatched bound {} above the exact-tier bound {}",
            via_dispatch.bound,
            via_big.bound
        );
        assert!(via_dispatch.bound <= int_opt, "dispatched bound unsound");
        assert!(via_big.bound <= int_opt, "big-tier bound unsound");
        // The exact tier itself is unchanged: byte-identical on a direct call.
        let big_again = model.solve_dual_big(&never_stop, None).expect("big bound");
        assert_eq!(big_again.bound, via_big.bound);
        assert_eq!(big_again.exact_bound, via_big.exact_bound);
        assert_eq!(big_again.duals, via_big.duals);
    }

    /// Randomized huge-coefficient instances: wherever the small tier completes it
    /// must agree with big; wherever it overflows, the public dispatcher must
    /// return a bound that never exceeds the big tier's exact result (equality
    /// when the big tier decides, `<=` when the f64-certified tier does). Also
    /// counts that overflow REALLY engages on this regime (the fallback is
    /// exercised, not vacuous).
    #[test]
    fn small_simplex_huge_coeff_differential_and_fallback() {
        let mut rng = Rng(0x0B16_C0EF_F00D_1FF5);
        let mut overflows = 0usize;
        let mut agreements = 0usize;
        for _ in 0..300 {
            let n: u32 = rng.range(1, 4) as u32;
            let scale = i128::MAX / 5;
            let mut obj_terms = Vec::new();
            for v in 1..=n {
                let coeff = rng.range(-4, 4);
                if coeff != 0 {
                    obj_terms.push(term(coeff.saturating_mul(scale), lit(v)));
                }
            }
            if obj_terms.is_empty() {
                obj_terms.push(term(scale, lit(1)));
            }
            let obj = PbObjective { terms: obj_terms };
            let mut terms = Vec::new();
            for v in 1..=n {
                let coeff = rng.range(-3, 4);
                if coeff != 0 {
                    terms.push(term(coeff.saturating_mul(scale / 7), lit(v)));
                }
            }
            if terms.is_empty() {
                terms.push(term(scale / 7, lit(1)));
            }
            let rhs = rng.range(-2, 3).saturating_mul(scale / 11);
            let constraints = vec![ge(terms, rhs)];

            let Some(model) = LpModel::build(&obj, &constraints, n) else {
                continue;
            };
            let big = model.solve_dual_big(&never_stop, None);
            match model.solve_dual_small(&never_stop, None) {
                SmallDualOutcome::Overflow => {
                    overflows += 1;
                    // The public dispatcher resolves via the f64-certified tier
                    // (bound <= big, never above — THE soundness ordering) or,
                    // when certification fails closed, via big exactly. A
                    // certified Some against a big None is legal: a verified
                    // dual-feasible point is sound even where the exact tier
                    // declines (dual-unbounded/ceil-range), and vacuously so on
                    // an infeasible primal. A dispatch None against a big Some
                    // is impossible (the dispatcher falls back to big).
                    let dispatched = model.solve_dual(&never_stop, None);
                    match (&dispatched, &big) {
                        (None, None) | (Some(_), None) => {}
                        (Some(d), Some(b)) => {
                            assert!(
                                d.bound <= b.bound,
                                "dispatched bound {} above exact-tier bound {}",
                                d.bound,
                                b.bound
                            );
                        }
                        (None, Some(_)) => {
                            panic!("dispatcher declined where the big tier bounds")
                        }
                    }
                }
                SmallDualOutcome::Solved(small) => match (&small, &big) {
                    (None, None) => {}
                    (Some(s), Some(b)) => {
                        agreements += 1;
                        assert_eq!(s.bound, b.bound, "obj={obj:?} cons={constraints:?}");
                        assert_eq!(s.exact_bound, b.exact_bound);
                    }
                    _ => panic!("Solved/None divergence on huge coefficients"),
                },
            }
        }
        assert!(
            overflows > 10,
            "expected the overflow fallback to engage on huge coefficients, got {overflows}"
        );
        // Not all huge instances overflow (some solve in one pivot); both paths
        // must be exercised for the differential to be meaningful.
        let _ = agreements;
    }

    // --- f64-certified middle tier: exact-verification differential gates. --- //

    /// Independently re-verifies everything a [`DualSolution`] from the certified
    /// tier claims: `y >= 0`, EXACT componentwise dual feasibility
    /// `(A^T y)_v <= c_v`, and `exact_bound == offset + b·y` recomputed from
    /// scratch. Panics with context on any violation.
    fn assert_certified_dual_verifies(model: &LpModel, sol: &DualSolution, context: &str) {
        let n = model.c.len();
        assert_eq!(sol.duals.len(), model.rows.len(), "{context}: dual length");
        let mut aty = vec![BigRational::zero(); n];
        let mut bound = model.offset.clone();
        for (r, row) in model.rows.iter().enumerate() {
            let yr = &sol.duals[r];
            assert!(!yr.is_negative(), "{context}: y[{r}] negative");
            if yr.is_zero() {
                continue;
            }
            for &(v, ref coeff) in &row.coeffs {
                aty[v] += yr * coeff;
            }
            bound += &row.b * yr;
        }
        for v in 0..n {
            assert!(
                aty[v] <= model.c[v],
                "{context}: dual INFEASIBLE at var {v}: (A^T y)_v = {} > c_v = {}",
                aty[v],
                model.c[v]
            );
        }
        assert_eq!(
            bound, sol.exact_bound,
            "{context}: exact_bound does not match the recomputed offset + b·y"
        );
        assert_eq!(
            Some(sol.bound),
            rational_ceil_to_i64(&sol.exact_bound),
            "{context}: bound is not ceil(exact_bound)"
        );
    }

    /// THE soundness property of the certified tier, differentially over
    /// randomized instances in BOTH a small-coefficient regime and the
    /// huge-coefficient regime that actually overflows the i128 tier:
    /// whenever the tier certifies, its dual point must verify exactly
    /// (independent re-check) and its bound must never exceed the exact
    /// (BigRational) tier's bound, nor the brute-force integer optimum.
    #[test]
    fn f64_certified_tier_bound_never_above_exact_and_dual_verifies() {
        let mut rng = Rng(0xCE47_1F1E_D0_D0F00D);
        let mut certified = 0usize;
        let mut certified_huge = 0usize;
        for round in 0..1200 {
            let huge = round % 2 == 1;
            // The huge scale trips the i128 tier's pivot products while keeping
            // every brute-force objective SUM (<= 4 vars * 4 * scale) in i128.
            let scale: i128 = if huge { i128::MAX / 40 } else { 1 };
            let n: u32 = rng.range(1, 5) as u32;
            let mut obj_terms = Vec::new();
            for v in 1..=n {
                let coeff = rng.range(-4, 4);
                if coeff != 0 {
                    let negated = rng.next() & 1 == 1;
                    obj_terms.push(PbTerm {
                        coeff: coeff.saturating_mul(scale),
                        lits: vec![PbLit { var: v, negated }],
                    });
                }
            }
            if obj_terms.is_empty() {
                obj_terms.push(term(scale, lit(1)));
            }
            let obj = PbObjective { terms: obj_terms };
            let num_c = rng.range(1, 3);
            let mut constraints = Vec::new();
            for _ in 0..num_c {
                let mut terms = Vec::new();
                for v in 1..=n {
                    let coeff = rng.range(-3, 4);
                    if coeff != 0 {
                        let negated = rng.next() & 1 == 1;
                        terms.push(PbTerm {
                            coeff: coeff.saturating_mul(scale / 7),
                            lits: vec![PbLit { var: v, negated }],
                        });
                    }
                }
                if terms.is_empty() {
                    terms.push(term(scale / 7, lit(1)));
                }
                let rhs = rng.range(-2, 3).saturating_mul(scale / 11);
                constraints.push(ge(terms, rhs));
            }

            let Some(model) = LpModel::build(&obj, &constraints, n) else {
                continue;
            };
            let Some(cert) = model.solve_dual_f64_certified(&never_stop) else {
                continue; // fail-closed decline: the exact path would decide.
            };
            certified += 1;
            if huge {
                certified_huge += 1;
            }
            assert_certified_dual_verifies(&model, &cert, "randomized certified tier");

            if let Some(big) = model.solve_dual_big(&never_stop, None) {
                assert!(
                    cert.bound <= big.bound,
                    "SOUNDNESS ORDER VIOLATION: certified bound {} > exact bound {}\n\
                     obj={obj:?}\ncons={constraints:?}",
                    cert.bound,
                    big.bound
                );
            }
            // Brute-force soundness (feasible instances; small n keeps it cheap).
            if let Some(opt) = brute_force_optimum(&obj, &constraints, n) {
                assert!(
                    cert.bound <= opt,
                    "SOUNDNESS VIOLATION: certified bound {} > integer optimum {opt}\n\
                     obj={obj:?}\ncons={constraints:?}",
                    cert.bound
                );
            }
        }
        assert!(
            certified > 200,
            "expected the certified tier to certify often, got {certified}"
        );
        assert!(
            certified_huge > 50,
            "expected certifications in the i128-overflow regime, got {certified_huge}"
        );
    }

    /// End-to-end through the PUBLIC entry point on the overflow regime: with the
    /// certified tier in the dispatch, `lp_lower_bound` (cut loop included) must
    /// stay sound against brute force on huge-coefficient instances.
    #[test]
    fn dispatch_with_certified_tier_stays_sound_end_to_end_on_huge_coeffs() {
        let mut rng = Rng(0x00D1_5BA7_C4ED_5EED);
        let mut checked = 0usize;
        for _ in 0..250 {
            // Trips i128 pivot products; brute-force sums stay in range.
            let scale = i128::MAX / 40;
            let n: u32 = rng.range(1, 4) as u32;
            let mut obj_terms = Vec::new();
            for v in 1..=n {
                let coeff = rng.range(-4, 4);
                if coeff != 0 {
                    obj_terms.push(term(coeff.saturating_mul(scale), lit(v)));
                }
            }
            if obj_terms.is_empty() {
                obj_terms.push(term(scale, lit(1)));
            }
            let obj = PbObjective { terms: obj_terms };
            let mut terms = Vec::new();
            for v in 1..=n {
                let coeff = rng.range(-3, 4);
                if coeff != 0 {
                    terms.push(term(coeff.saturating_mul(scale / 7), lit(v)));
                }
            }
            if terms.is_empty() {
                terms.push(term(scale / 7, lit(1)));
            }
            let rhs = rng.range(-2, 3).saturating_mul(scale / 11);
            let constraints = vec![ge(terms, rhs)];

            let Some(opt) = brute_force_optimum(&obj, &constraints, n) else {
                continue;
            };
            checked += 1;
            if let Some(lb) = lp_lower_bound(&obj, &constraints, n, &never_stop) {
                assert!(
                    lb <= opt,
                    "SOUNDNESS VIOLATION: public LP_LB {lb} > brute optimum {opt}\n\
                     obj={obj:?}\ncons={constraints:?}"
                );
            }
        }
        assert!(checked > 50, "expected feasible instances, got {checked}");
    }

    /// Reduced-cost fixings derived from CERTIFIED-tier dual points (the one
    /// consumer where a bad dual could remove solutions) must never contradict
    /// any feasible assignment strictly better than the incumbent — on the
    /// huge-coefficient regime where the certified tier actually engages.
    #[test]
    fn certified_tier_reduced_cost_fixings_never_remove_better_solutions() {
        let mut rng = Rng(0xF1D0_C057_F1E5_0001);
        let mut checked = 0usize;
        let mut fixings_seen = 0usize;
        for _ in 0..400 {
            let scale = i128::MAX / 40;
            let n: u32 = rng.range(1, 4) as u32;
            let mut obj_terms = Vec::new();
            for v in 1..=n {
                let coeff = rng.range(-4, 4);
                if coeff != 0 {
                    let negated = rng.next() & 1 == 1;
                    obj_terms.push(PbTerm {
                        coeff: coeff.saturating_mul(scale),
                        lits: vec![PbLit { var: v, negated }],
                    });
                }
            }
            if obj_terms.is_empty() {
                obj_terms.push(term(scale, lit(1)));
            }
            let obj = PbObjective { terms: obj_terms };
            let mut terms = Vec::new();
            for v in 1..=n {
                let coeff = rng.range(-3, 4);
                if coeff != 0 {
                    terms.push(term(coeff.saturating_mul(scale / 7), lit(v)));
                }
            }
            if terms.is_empty() {
                terms.push(term(scale / 7, lit(1)));
            }
            let rhs = rng.range(-2, 3).saturating_mul(scale / 11);
            let constraints = vec![ge(terms, rhs)];

            let Some(opt) = brute_force_optimum(&obj, &constraints, n) else {
                continue;
            };
            checked += 1;
            for delta in [1i128, scale / 13] {
                let Some(incumbent_ub) = opt.checked_add(delta) else {
                    continue;
                };
                let Some(result) =
                    lp_reduced_cost_fixings(&obj, &constraints, n, incumbent_ub, &never_stop)
                else {
                    continue;
                };
                assert!(
                    result.lower_bound <= opt,
                    "SOUNDNESS: LP bound {} > optimum {opt}",
                    result.lower_bound
                );
                fixings_seen += result.fixings.len();
                let better = strictly_better_feasible(&obj, &constraints, n, incumbent_ub);
                for fix in &result.fixings {
                    let idx = (fix.var - 1) as usize;
                    for x in &better {
                        assert_eq!(
                            x[idx], fix.value,
                            "SOUNDNESS VIOLATION: certified-tier fixing var {} -> {} removes \
                             a strictly-better assignment {x:?}\nincumbent_ub={incumbent_ub} \
                             opt={opt}\nobj={obj:?}\ncons={constraints:?}",
                            fix.var, fix.value
                        );
                    }
                }
            }
        }
        assert!(checked > 80, "expected feasible instances, got {checked}");
        eprintln!("certified-tier reduced-cost: {fixings_seen} fixings across {checked} instances");
    }

    /// A Farkas certificate built from a CERTIFIED-tier dual point must validate:
    /// the tier's repaired dual is exactly dual-feasible, so `d_v >= 0` holds and
    /// `check_slack` must accept — the certificate machinery does not care how
    /// the dual point was found.
    #[test]
    fn farkas_cert_validates_certified_tier_bound() {
        let a = (1i128 << 126) - 3;
        let b = (1i128 << 126) - 5;
        let obj = PbObjective {
            terms: vec![term(a, lit(1)), term(b, lit(2))],
        };
        let c = ge(vec![term(3, lit(1)), term(5, lit(2))], 7);
        let model = LpModel::build(&obj, &[c], 2).expect("model");
        let Some(dual) = model.solve_dual_f64_certified(&never_stop) else {
            // The tier may fail closed (then the big tier decides — covered
            // elsewhere); nothing to check here in that case.
            return;
        };
        assert_certified_dual_verifies(&model, &dual, "farkas fixture");
        let cert = model.build_farkas_cert(&dual).expect("cert");
        assert_eq!(cert.claimed_bound, dual.bound);
        assert!(
            farkas_cert::check_slack(&cert.cert),
            "the checker MUST validate a certified-tier bound"
        );
    }

    /// The BIG tier's in-simplex early exit (`solve_dual_big` with a target) is
    /// the exact path big-coefficient competition instances take once an
    /// incumbent exists: the i128 tier overflows and the dispatcher re-solves
    /// via BigRational WITH the target still threaded. No other test executes
    /// that block (the targeted differential stays in the small tier; the
    /// huge-coefficient tests pass `None`), so pin it directly: the targeted
    /// bound must stay sound (`<= integer optimum`), reach the target whenever
    /// the untargeted floor does (lossless for the caller's `floor >=
    /// incumbent` optimality check), and an unreachable target must not change
    /// the result.
    #[test]
    fn big_tier_targeted_early_exit_after_overflow_is_sound_and_lossless() {
        // Same fixture as `small_simplex_overflow_falls_back_to_big`: ~2^126
        // coefficients trip the checked-i128 ratio test, forcing the big tier.
        let a = (1i128 << 126) - 3;
        let b = (1i128 << 126) - 5;
        let obj = PbObjective {
            terms: vec![term(a, lit(1)), term(b, lit(2))],
        };
        let c = ge(vec![term(3, lit(1)), term(5, lit(2))], 7);
        let model = LpModel::build(&obj, &[c], 2).expect("model");

        // Integer optimum by enumeration: only x1=x2=1 satisfies 3x1+5x2 >= 7.
        let int_opt = a + b;

        // The small tier must overflow with the target threaded too, so the
        // public targeted dispatch below really lands in the big tier.
        assert!(
            matches!(
                model.solve_dual_small(&never_stop, Some(int_opt)),
                SmallDualOutcome::Overflow
            ),
            "fixture must overflow the i128 tier in targeted mode"
        );

        // Untargeted big solve: the LP-optimal floor. Strictly below the
        // integer optimum here (LP relaxation takes x1 = 2/3), so a target of
        // `int_opt` exercises the running check on every pivot WITHOUT firing.
        let full = model
            .solve_dual_big(&never_stop, None)
            .expect("untargeted big bound");
        assert!(full.bound <= int_opt);
        assert!(full.bound < int_opt, "fixture needs an LP gap for case (1)");

        // (1) Unreachable target (incumbent above the LP floor): weak duality
        // caps every intermediate vertex at the LP optimum, so the exit never
        // fires and the completed solve is byte-identical to the untargeted one.
        let unreached = model
            .solve_dual_big(&never_stop, Some(int_opt))
            .expect("targeted big bound (unreachable target)");
        assert!(
            unreached.bound <= int_opt,
            "SOUNDNESS: big-tier targeted floor {} > integer optimum {int_opt}",
            unreached.bound
        );
        assert_eq!(unreached.bound, full.bound);
        assert_eq!(unreached.exact_bound, full.exact_bound);
        assert_eq!(unreached.duals, full.duals);

        // (2) Target exactly at the reachable floor (the OPTIMUM-termination
        // case): the exit fires at the first vertex whose ceil reaches it —
        // at latest the optimal vertex — and weak duality caps every running
        // ceil at `full.bound`, so reaching the target forces equality. The
        // exit is lossless for the caller's `floor >= incumbent` check.
        let at_floor = model
            .solve_dual_big(&never_stop, Some(full.bound))
            .expect("targeted big bound (target = floor)");
        assert_eq!(at_floor.bound, full.bound);

        // (3) Target below the floor: the exit may fire even earlier; the
        // returned bound must still certify the target and never exceed the
        // LP-optimal floor.
        let below = model
            .solve_dual_big(&never_stop, Some(full.bound - 1))
            .expect("targeted big bound (target < floor)");
        assert!(below.bound >= full.bound - 1);
        assert!(below.bound <= full.bound);

        // End-to-end: the public targeted dispatch on this instance (small
        // overflow -> f64-certified or big) stays sound and never exceeds the
        // exact-tier floor (the certified tier may land slightly below it).
        let dispatched = model
            .solve_dual(&never_stop, Some(full.bound))
            .expect("dispatched targeted bound");
        assert!(dispatched.bound <= int_opt);
        assert!(
            dispatched.bound <= full.bound,
            "dispatched bound {} above the exact-tier floor {}",
            dispatched.bound,
            full.bound
        );
    }

    /// SmallRat unit sanity: exact ceil, reduction, and checked-op overflow.
    #[test]
    fn small_rat_arithmetic_is_exact_and_checked() {
        let half = SmallRat::new(1, 2).unwrap();
        let third = SmallRat::new(-2, -6).unwrap(); // sign-normalizes + reduces to 1/3.
        assert_eq!(third, SmallRat::new(1, 3).unwrap());
        let sum = half.checked_add(third).unwrap();
        assert_eq!(sum, SmallRat::new(5, 6).unwrap());
        assert_eq!(sum.ceil_i128(), Some(1));
        assert_eq!(SmallRat::new(-5, 6).unwrap().ceil_i128(), Some(0));
        assert_eq!(SmallRat::new(-6, 3).unwrap().ceil_i128(), Some(-2));
        assert_eq!(SmallRat::new(7, 1).unwrap().ceil_i128(), Some(7));
        // gcd-based cross-cancel keeps this in range...
        let big = SmallRat::new(i128::MAX, 3).unwrap();
        assert_eq!(
            big.checked_mul(SmallRat::new(3, i128::MAX).unwrap()),
            Some(SmallRat::ONE)
        );
        // ...but a genuine overflow is caught, never wrapped.
        assert_eq!(big.checked_mul(big), None);
        assert_eq!(
            SmallRat::new(i128::MAX, 1)
                .unwrap()
                .checked_add(SmallRat::ONE),
            None
        );
        // Division by zero declines.
        assert_eq!(SmallRat::ONE.checked_div(SmallRat::ZERO), None);
        // Comparisons are exact.
        assert_eq!(half.checked_cmp(third), Some(std::cmp::Ordering::Greater));
        assert_eq!(
            SmallRat::new(10, 21)
                .unwrap()
                .checked_cmp(SmallRat::new(477, 1001).unwrap()),
            Some(std::cmp::Ordering::Less) // 10/21 ~= 0.47619 < 477/1001 ~= 0.47652.
        );
    }

    /// Corpus measurement (run explicitly): how often does the i128 fast tier
    /// overflow into the BigRational fallback on the repo's real PB instances?
    ///
    /// Run with:
    ///   cargo test -p ay-pb --release measure_small_tier_fallback_rate -- --ignored --nocapture
    #[test]
    #[ignore = "manual corpus measurement of the i128-tier fallback rate"]
    fn measure_small_tier_fallback_rate() {
        let root =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../benchmarks/pb-comp");
        let mut opb_files = Vec::new();
        let mut stack = vec![root];
        while let Some(dir) = stack.pop() {
            let Ok(entries) = std::fs::read_dir(&dir) else {
                continue;
            };
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    stack.push(path);
                } else if path.extension().is_some_and(|e| e == "opb") {
                    opb_files.push(path);
                }
            }
        }
        opb_files.sort();
        let (mut attempted, mut built, mut solved, mut overflowed) =
            (0usize, 0usize, 0usize, 0usize);
        for path in &opb_files {
            let Ok(text) = std::fs::read_to_string(path) else {
                continue;
            };
            let Ok(inst) = crate::parser::parse_opb(&text) else {
                continue;
            };
            let Some(obj) = inst.objective.as_ref() else {
                continue;
            };
            attempted += 1;
            let Some(model) = LpModel::build(obj, &inst.constraints, inst.num_vars) else {
                continue;
            };
            built += 1;
            // Small-tier only, bounded per instance so the sweep stays quick.
            let started = std::time::Instant::now();
            let stop = || started.elapsed() > std::time::Duration::from_secs(5);
            match model.solve_dual_small(&stop, None) {
                SmallDualOutcome::Solved(_) => solved += 1,
                SmallDualOutcome::Overflow => {
                    overflowed += 1;
                    eprintln!("OVERFLOW -> bigint fallback: {}", path.display());
                }
            }
        }
        eprintln!(
            "small-tier fallback rate: {overflowed}/{built} models overflowed \
             ({solved} solved small; {attempted} objective instances; {} files)",
            opb_files.len()
        );
    }

    /// Corpus root for the manual measurement sweeps: `$AY_PBCOMP_BENCH_ROOT`
    /// when set, else the checkout-relative `benchmarks/pb-comp` (the corpus is
    /// gitignored, so fresh checkouts only carry the tiny `test-instances/`
    /// subset and these sweeps skip).
    fn measurement_corpus_root() -> std::path::PathBuf {
        if let Some(root) = std::env::var_os("AY_PBCOMP_BENCH_ROOT") {
            return std::path::PathBuf::from(root);
        }
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../benchmarks/pb-comp")
    }

    /// Resolves a PB-competition corpus file under [`measurement_corpus_root`].
    /// The corpus is not tracked in git; tests skip when the file is absent.
    fn pbcomp_path(rel: &str) -> String {
        measurement_corpus_root().join(rel).display().to_string()
    }

    /// Collects every parseable objective-bearing `.opb` under `root` whose
    /// [`LpModel`] builds, sorted by path.
    fn corpus_lp_models(
        root: &std::path::Path,
    ) -> Vec<(std::path::PathBuf, PbObjective, Vec<PbConstraint>, u32)> {
        let mut opb_files = Vec::new();
        let mut stack = vec![root.to_path_buf()];
        while let Some(dir) = stack.pop() {
            let Ok(entries) = std::fs::read_dir(&dir) else {
                continue;
            };
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    stack.push(path);
                } else if path.extension().is_some_and(|e| e == "opb") {
                    opb_files.push(path);
                }
            }
        }
        opb_files.sort();
        let mut models = Vec::new();
        for path in opb_files {
            let Ok(text) = std::fs::read_to_string(&path) else {
                continue;
            };
            let Ok(inst) = crate::parser::parse_opb(&text) else {
                continue;
            };
            let Some(obj) = inst.objective else {
                continue;
            };
            if LpModel::build(&obj, &inst.constraints, inst.num_vars).is_none() {
                continue;
            }
            models.push((path, obj, inst.constraints, inst.num_vars));
        }
        models
    }

    /// MEASUREMENT (run explicitly): on every corpus model whose i128 tier
    /// overflows, compare the f64-certified tier against the BigRational tier —
    /// bound quality (certified must never exceed a COMPLETED big solve) and
    /// wall time (3-run medians for both, plus the production-realistic big run
    /// under the 5s root budget). This is the honest evidence for the certified
    /// tier: it must win on the data or not ship.
    ///
    /// Run with:
    ///   cargo test -p ay-pb --release measure_f64_certified_tier_on_overflow_corpus -- --ignored --nocapture
    #[test]
    #[ignore = "manual corpus measurement of the f64-certified tier on the i128-overflow models"]
    fn measure_f64_certified_tier_on_overflow_corpus() {
        const BIG_REFERENCE_CAP: std::time::Duration = std::time::Duration::from_secs(10);
        const BIG_PRODUCTION_BUDGET: std::time::Duration = std::time::Duration::from_secs(5);

        fn median(mut xs: Vec<f64>) -> f64 {
            xs.sort_by(|a, b| a.partial_cmp(b).unwrap());
            xs[xs.len() / 2]
        }

        let root = measurement_corpus_root();
        let models = corpus_lp_models(&root);
        eprintln!("corpus: {} LP-modelable objective instances", models.len());

        let mut overflowed = 0usize;
        let mut certified = 0usize;
        let mut bound_matches_reference = 0usize;
        let mut total_cert_ms = 0.0f64;
        let mut total_big_ref_ms = 0.0f64;
        for (path, obj, constraints, num_vars) in &models {
            let model = LpModel::build(obj, constraints, *num_vars).expect("prefiltered");
            let started = std::time::Instant::now();
            let stop = || started.elapsed() > std::time::Duration::from_secs(5);
            if !matches!(
                model.solve_dual_small(&stop, None),
                SmallDualOutcome::Overflow
            ) {
                continue;
            }
            overflowed += 1;
            let name = path.file_name().unwrap_or_default().to_string_lossy();

            // f64-certified tier: 3 timed runs.
            let mut cert_ms = Vec::new();
            let mut cert_bounds = Vec::new();
            for _ in 0..3 {
                let t = std::time::Instant::now();
                let result = model.solve_dual_f64_certified(&never_stop);
                cert_ms.push(t.elapsed().as_secs_f64() * 1e3);
                cert_bounds.push(result.map(|r| r.bound));
            }
            // BigRational tier, production-realistic budget: 3 timed runs.
            let mut big5_ms = Vec::new();
            let mut big5_bounds = Vec::new();
            for _ in 0..3 {
                let t = std::time::Instant::now();
                let stop = || t.elapsed() >= BIG_PRODUCTION_BUDGET;
                let result = model.solve_dual_big(&stop, None);
                big5_ms.push(t.elapsed().as_secs_f64() * 1e3);
                big5_bounds.push(result.map(|r| r.bound));
            }
            // Budget-theft check: when the certified tier fails closed it steals
            // its budget from the exact tier. Does the exact tier's floor at
            // (5s - F64_TIER_SIMPLEX_BUDGET) differ from its floor at 5s? (3 runs.)
            let mut theft_bounds = Vec::new();
            for _ in 0..3 {
                let t = std::time::Instant::now();
                let reduced = BIG_PRODUCTION_BUDGET.saturating_sub(F64_TIER_SIMPLEX_BUDGET);
                let stop = || t.elapsed() >= reduced;
                theft_bounds.push(model.solve_dual_big(&stop, None).map(|r| r.bound));
            }
            // BigRational reference (bound-quality yardstick): one capped run.
            let t = std::time::Instant::now();
            let stop = || t.elapsed() >= BIG_REFERENCE_CAP;
            let big_ref = model.solve_dual_big(&stop, None);
            let big_ref_ms = t.elapsed().as_secs_f64() * 1e3;
            let big_ref_completed = t.elapsed() < BIG_REFERENCE_CAP.mul_f64(0.95);

            let cert_med = median(cert_ms.clone());
            let big5_med = median(big5_ms.clone());
            total_cert_ms += cert_med;
            total_big_ref_ms += big_ref_ms;
            let cert_bound = cert_bounds[0];
            if cert_bound.is_some() {
                certified += 1;
            }
            let big_ref_bound = big_ref.as_ref().map(|r| r.bound);
            if cert_bound.is_some() && cert_bound == big_ref_bound {
                bound_matches_reference += 1;
            }
            // THE ordering gate, wherever the exact reference COMPLETED.
            if let (Some(cb), Some(rb), true) = (cert_bound, big_ref_bound, big_ref_completed) {
                assert!(
                    cb <= rb,
                    "{name}: certified bound {cb} EXCEEDS completed exact bound {rb}"
                );
            }
            eprintln!(
                "{name}: vars={num_vars} cons={} | cert bound={cert_bound:?} med={cert_med:.1}ms \
                 (runs {cert_ms:?}) | big@5s bound={:?} med={big5_med:.1}ms | big@theft \
                 bounds={theft_bounds:?} | big@{}s ref bound={big_ref_bound:?} {}ms \
                 completed={big_ref_completed}",
                constraints.len(),
                big5_bounds[0],
                BIG_REFERENCE_CAP.as_secs(),
                big_ref_ms as u64,
            );
        }
        eprintln!(
            "== summary: {overflowed} overflow models; {certified} certified; \
             {bound_matches_reference} certified bounds equal the exact reference; \
             total cert median time {total_cert_ms:.0}ms vs total big reference time \
             {total_big_ref_ms:.0}ms =="
        );
    }

    /// FOCUSED MEASUREMENT (run explicitly): the certified tier vs the exact
    /// tier's production-budget floor on the handful of corpus models the full
    /// sweep flagged as interesting — the certifying families (hw32, diagcomm)
    /// and fail-closed representatives (domset, bnatt350). Fast enough to
    /// re-run after every tier change.
    ///
    /// Run with:
    ///   cargo test -p ay-pb --release measure_f64_certified_tier_focused -- --ignored --nocapture
    #[test]
    #[ignore = "manual focused measurement of the certified tier on key overflow models"]
    fn measure_f64_certified_tier_focused() {
        let interesting = [
            "mult_diagcomm_opt_less_teq_nbits_15",
            "mult_diagcomm_opt_less_teq_nbits_17",
            "hw32-vm25p",
            "bnatt350",
            "domset_v500_e2000_w30_mw19_10",
        ];
        let root = measurement_corpus_root();
        let models = corpus_lp_models(&root);
        let mut seen = std::collections::BTreeSet::new();
        for (path, obj, constraints, num_vars) in &models {
            let name = path.file_name().unwrap_or_default().to_string_lossy();
            let Some(&tag) = interesting.iter().find(|t| name.contains(*t)) else {
                continue;
            };
            if !seen.insert(tag) {
                continue; // the corpus holds duplicates across selected dirs.
            }
            let model = LpModel::build(obj, constraints, *num_vars).expect("prefiltered");
            let mut cert_ms = Vec::new();
            let mut cert_bounds = Vec::new();
            for _ in 0..3 {
                let t = std::time::Instant::now();
                let result = model.solve_dual_f64_certified(&never_stop);
                cert_ms.push(t.elapsed().as_secs_f64() * 1e3);
                cert_bounds.push(result.map(|r| r.bound));
            }
            let t = std::time::Instant::now();
            let stop = || t.elapsed() >= std::time::Duration::from_secs(5);
            let big5 = model.solve_dual_big(&stop, None).map(|r| r.bound);
            let big5_ms = t.elapsed().as_secs_f64() * 1e3;
            eprintln!(
                "{name}: cert bounds={cert_bounds:?} times={cert_ms:?}ms | big@5s {big5:?} \
                 {big5_ms:.0}ms"
            );
        }
    }

    /// DIAGNOSIS (run explicitly): does the advisory f64 simplex CONVERGE on a
    /// domset overflow model given a long budget, or does it cycle? Prints the
    /// elapsed time (elapsed << budget means it reached optimality) and the
    /// certified bound at several budgets. Drives the certified tier's budget
    /// choice honestly.
    ///
    /// Run with:
    ///   cargo test -p ay-pb --release diagnose_f64_simplex_on_domset -- --ignored --nocapture
    #[test]
    #[ignore = "manual diagnosis of the f64 simplex on the domset overflow family"]
    fn diagnose_f64_simplex_on_domset() {
        let root = measurement_corpus_root();
        let path = root.join(
            "selected-PB24/PB24/normalized-PB06/OPT-LIN/submitted-PB06/liu/domset/\
             normalized-domset_v500_e2000_w30_mw19_10.opb.PB06.opb",
        );
        let Ok(text) = std::fs::read_to_string(&path) else {
            eprintln!("domset model absent at {}; skipping", path.display());
            return;
        };
        let inst = crate::parser::parse_opb(&text).expect("parse domset");
        let obj = inst.objective.clone().expect("objective");
        let model = LpModel::build(&obj, &inst.constraints, inst.num_vars).expect("model");

        // Rebuild the f64 image exactly as the certified tier does.
        let n = model.c.len();
        let m_struct = model.rows.len() - n;
        let c_f64: Vec<f64> = model.c.iter().map(|v| v.to_f64().unwrap()).collect();
        let rows_f64: Vec<(Vec<(usize, f64)>, f64)> = model.rows[..m_struct]
            .iter()
            .map(|row| {
                (
                    row.coeffs
                        .iter()
                        .map(|&(v, ref c)| (v, c.to_f64().unwrap()))
                        .collect(),
                    row.b.to_f64().unwrap(),
                )
            })
            .collect();

        for budget_ms in [1_500u64, 6_000, 20_000] {
            let budget = std::time::Duration::from_millis(budget_ms);
            let t = std::time::Instant::now();
            let solved = crate::optimize::safe_lp_bound::approx_dual_for_box_lp(
                n,
                c_f64.clone(),
                rows_f64.clone(),
                budget,
                &never_stop,
            );
            let elapsed = t.elapsed();
            let Some((dual, primal, converged)) = solved else {
                eprintln!("budget {budget_ms}ms: simplex declined");
                continue;
            };
            // NS-style f64 estimates of the dual bound and primal objective.
            let mut ns = model.offset.to_f64().unwrap_or(0.0);
            let mut aty = vec![0.0f64; n];
            for (r, (coeffs, b)) in rows_f64.iter().enumerate() {
                let yr = dual[r].max(0.0);
                if yr == 0.0 {
                    continue;
                }
                ns += b * yr;
                for &(v, a) in coeffs {
                    aty[v] += a * yr;
                }
            }
            for v in 0..n {
                ns += (c_f64[v] - aty[v]).min(0.0);
            }
            let mut primal_obj = model.offset.to_f64().unwrap_or(0.0);
            for (v, &x) in primal.iter().enumerate() {
                primal_obj += c_f64[v] * x.clamp(0.0, 1.0);
            }
            eprintln!(
                "budget {budget_ms}ms: elapsed {elapsed:?} (converged: {converged}), NS dual \
                 estimate {ns:.3}, primal objective estimate {primal_obj:.3}"
            );
        }
    }

    /// PROFILE (run explicitly): LP re-entry candidate `lo_14x14_007` — the
    /// class where the first incumbent sits ABOVE the LP optimum, so the root
    /// LP's early-exit target cannot fire and the call pays full tightening.
    /// Measures (a) the base and cut-tightened LP floor and their cost, (b) the
    /// cost of targeted re-solves at targets around the floor (what a re-entry
    /// would pay), and (c) a short real optimize run's incumbent trajectory
    /// (does the incumbent ever approach the floor within a sane budget?).
    /// The re-entry feature ships only if these numbers show a win.
    ///
    /// Run with:
    ///   cargo test -p ay-pb --release profile_lp_reentry_lo_14x14_007 -- --ignored --nocapture
    #[test]
    #[ignore = "manual profile for the LP re-entry decision on lo_14x14_007"]
    fn profile_lp_reentry_lo_14x14_007() {
        let path = measurement_corpus_root().join(
            "selected-PB25/PB24/normalized-PB15eval/OPT-LIN/dt-problems/\
             normalized-lo_14x14_007.opb.metafix.opb",
        );
        let Ok(text) = std::fs::read_to_string(&path) else {
            eprintln!("lo_14x14_007 absent at {}; skipping", path.display());
            return;
        };
        let inst = crate::parser::parse_opb(&text).expect("parse lo_14x14_007");
        let obj = inst.objective.clone().expect("objective");

        // (a) Base vs cut-tightened floor, timed (3 runs each, median by eye).
        for run in 0..3 {
            let t = std::time::Instant::now();
            let base = lp_lower_bound_no_cuts(&obj, &inst.constraints, inst.num_vars, &never_stop);
            let t_base = t.elapsed();
            let t = std::time::Instant::now();
            let full = lp_lower_bound(&obj, &inst.constraints, inst.num_vars, &never_stop);
            let t_full = t.elapsed();
            eprintln!(
                "run {run}: base floor {base:?} in {t_base:?}; cut floor {full:?} in {t_full:?}"
            );
        }
        let floor =
            lp_lower_bound(&obj, &inst.constraints, inst.num_vars, &never_stop).expect("cut floor");

        // (b) Targeted re-solves around the floor: what one re-entry would cost.
        for delta in [0i128, 1, 2, 5, 20] {
            let target = floor + delta;
            let t = std::time::Instant::now();
            let bound = lp_lower_bound_with_target(
                &obj,
                &inst.constraints,
                inst.num_vars,
                Some(target),
                &never_stop,
            );
            eprintln!(
                "target floor+{delta} = {target}: bound {bound:?} in {:?} (fires: {})",
                t.elapsed(),
                bound.is_some_and(|b| b >= target)
            );
        }

        // (c) Short real optimize run: incumbent trajectory vs the floor.
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(20);
        let t0 = std::time::Instant::now();
        let mut trajectory: Vec<(f64, i128)> = Vec::new();
        let mut on_improve = |value: i128, _model: &[bool]| {
            trajectory.push((t0.elapsed().as_secs_f64(), value));
        };
        let mut solver = crate::cdcl::PbCdclSolver::new(&inst);
        let result = solver.solve_optimize_interruptible(&obj, Some(&mut on_improve), || {
            std::time::Instant::now() >= deadline
        });
        let summary = match &result {
            crate::cdcl::PbCdclResult::Optimal(_, v) => format!("Optimal({v})"),
            crate::cdcl::PbCdclResult::Feasible(_, v) => format!("Feasible({v})"),
            other => format!("{other:?}"),
        };
        eprintln!("optimize (20s cap) result: {summary}");
        eprintln!("cut floor = {floor}; incumbent trajectory (t_secs, value):");
        for (t, v) in &trajectory {
            eprintln!("  {t:8.2}s  {v}");
        }
    }

    // --- Farkas certificate: build + check a REAL ay LP bound. --- //

    #[test]
    fn farkas_cert_validates_real_lp_bound() {
        // min x1 + x2 + x3  s.t.  x1 + x2 + x3 >= 1.  LP optimum = 1.
        // Build the model + dual EXACTLY as the production path does, emit the
        // Farkas certificate, and confirm the kernel-faithful checker accepts it
        // AND its claimed bound equals the simplex bound.
        let obj = PbObjective {
            terms: vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))],
        };
        let c = ge(vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))], 1);
        let model = LpModel::build(&obj, &[c], 3).expect("model");
        let dual = model.solve_dual(&never_stop, None).expect("dual");
        assert_eq!(dual.bound, 1, "the real LP bound is 1");

        let cert = model.build_farkas_cert(&dual).expect("cert");
        assert_eq!(cert.claimed_bound, dual.bound);
        assert!(
            farkas_cert::check_slack(&cert.cert),
            "the checker MUST validate the certificate for a real ay LP bound"
        );
    }

    #[test]
    fn farkas_cert_for_fractional_bound_validates() {
        // min x1 + x2  s.t.  2 x1 + 2 x2 >= 3.  exact LP optimum 3/2, ceil -> 2.
        // The slack sigma = 2 - 3/2 = 1/2 absorbs the ceil rounding; the checker
        // must accept the rounded integer floor.
        let obj = PbObjective {
            terms: vec![term(1, lit(1)), term(1, lit(2))],
        };
        let c = ge(vec![term(2, lit(1)), term(2, lit(2))], 3);
        let model = LpModel::build(&obj, &[c], 2).expect("model");
        let dual = model.solve_dual(&never_stop, None).expect("dual");
        assert_eq!(dual.bound, 2);
        let cert = model.build_farkas_cert(&dual).expect("cert");
        assert!(
            farkas_cert::check_slack(&cert.cert),
            "the checker MUST accept the ceil-rounded fractional bound via slack"
        );
    }

    #[test]
    fn farkas_cert_complemented_objective_validates() {
        // Negated-literal objective exercises the complementation path (offset != 0).
        // min ~x1  s.t.  ~x1 >= 1  (forces x1 = 0, objective 1).
        let obj = PbObjective {
            terms: vec![term(1, neg(1))],
        };
        let c = ge(vec![term(1, neg(1))], 1);
        let model = LpModel::build(&obj, &[c], 1).expect("model");
        let dual = model.solve_dual(&never_stop, None).expect("dual");
        assert_eq!(dual.bound, 1);
        let cert = model.build_farkas_cert(&dual).expect("cert");
        assert!(
            farkas_cert::check_slack(&cert.cert),
            "the checker MUST validate a bound from a complemented objective"
        );
    }

    #[test]
    fn farkas_cert_tampered_bound_rejected_on_real_instance() {
        // Take a real cert and INFLATE its claimed lower bound by 1 (a too-HIGH
        // bound = the soundness-critical failure). The checker MUST reject it: the
        // slack no longer absorbs the gap, so step 8 fails.
        let obj = PbObjective {
            terms: vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))],
        };
        let c = ge(vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))], 1);
        let model = LpModel::build(&obj, &[c], 3).expect("model");
        let dual = model.solve_dual(&never_stop, None).expect("dual");
        let mut cert = model.build_farkas_cert(&dual).expect("cert");

        // Inflate the conclusion bound: c . x >= (L - offset) + 1. Ge-normalized
        // combConst is -(b.y); conclConst becomes -((L - offset) + 1); step 8 needs
        // -(b.y) <= -((L-offset)+1) + sigma, i.e. (L-offset)+1 - sigma <= b.y,
        // i.e. exact_bound + 1 <= exact_bound, which is false.
        let one = QPair::from_int(&num_bigint::BigInt::from(1));
        cert.cert.base.conclusion.constant =
            farkas_cert_add_qpair(&cert.cert.base.conclusion.constant, &one);
        assert!(
            !farkas_cert::check_slack(&cert.cert),
            "an inflated (too-HIGH) real lower bound MUST be rejected by the checker"
        );
    }

    /// Test helper: add two QPairs the same way the checker's `addZ` does (the
    /// `farkas_cert` add is private, so we replicate the unreduced cross-add here).
    fn farkas_cert_add_qpair(a: &QPair, b: &QPair) -> QPair {
        QPair::new(&a.num * &b.den + &b.num * &a.den, &a.den * &b.den)
    }

    /// The on-disk real PB instance the kernel anchor is generated from. A genuine
    /// OPT-LIN instance shipped under `benchmarks/pb-comp/test-instances/`, NOT a
    /// constructed-in-test toy: `optimization-small.opb`
    /// (`min x1+2x2+3x3+4x4  s.t.  x1+x2+x3+x4>=2, x1+x3>=1, x2+x4>=1`). Its real
    /// exact LP relaxation bound is the integer floor 3. Both the gated production
    /// path here and the `verification/lean/FarkasAnchor.lean` literal transcribe
    /// the certificate this instance produces.
    const ANCHOR_OPB_REL: &str = "../../benchmarks/pb-comp/test-instances/optimization-small.opb";

    /// KERNEL-ANCHOR EXPORT (ignored by default; run explicitly to refresh the
    /// Lean fixtures): drive a REAL on-disk `.opb` through ay's *gated production*
    /// certificate path ([`lp_lower_bound_with_cert`] with `AY_PB_FARKAS_CERT` set),
    /// then emit the genuine emitted certificate plus a TAMPERED variant, as JSON via
    /// the existing serde, into `verification/lean/farkas_anchor/`. The companion
    /// Lean file `verification/lean/FarkasAnchor.lean` reconstructs the `SCertZ`
    /// literal from these decimal-string QPairs and re-checks `checkSlackEntailmentZ`
    /// in the Lean kernel (must agree with `check_slack`: valid -> true, tampered ->
    /// false).
    ///
    /// The instance is the real on-disk [`ANCHOR_OPB_REL`] (`optimization-small.opb`,
    /// exact LP floor 3) — the SAME bytes a user would solve.
    ///
    /// Run with:
    ///   cargo test -p ay-pb --lib emit_farkas_cert_json_for_lean_anchor -- --ignored --nocapture
    #[test]
    #[ignore = "fixture exporter for the Lean kernel anchor; run explicitly"]
    fn emit_farkas_cert_json_for_lean_anchor() {
        // Parse the REAL on-disk instance (the exact bytes shipped in the repo).
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(ANCHOR_OPB_REL);
        let text = std::fs::read_to_string(&path).expect("read anchor OPB");
        let instance = crate::parser::parse_opb(&text).expect("parse anchor OPB");
        let objective = instance
            .objective
            .clone()
            .expect("anchor instance has objective");

        // Drive ay's GATED PRODUCTION path: with AY_PB_FARKAS_CERT set, this is the
        // exact wiring `native_oll` uses — build the cert from the dual point in hand,
        // then `check_slack` it. (Env is process-global; restored below.)
        let prev = std::env::var_os("AY_PB_FARKAS_CERT");
        std::env::set_var("AY_PB_FARKAS_CERT", "1");
        let result = lp_lower_bound_with_cert(
            &objective,
            &instance.constraints,
            instance.num_vars,
            &never_stop,
        );
        match prev {
            Some(v) => std::env::set_var("AY_PB_FARKAS_CERT", v),
            None => std::env::remove_var("AY_PB_FARKAS_CERT"),
        }

        let (bound, valid, outcome) = result.expect("certified bound");
        assert_eq!(
            outcome,
            CertOutcome::Verified,
            "the gated path MUST verify the certificate for the real anchor instance"
        );
        let valid = valid.expect("a cert is present when Verified");
        assert_eq!(valid.claimed_bound, bound);
        assert!(
            farkas_cert::check_slack(&valid.cert),
            "valid real cert MUST pass check_slack (Rust)"
        );

        // A TAMPERED variant: inflate the conclusion bound by 1 (a too-HIGH lower
        // bound = the soundness-critical failure). Rust check_slack must reject it.
        let mut tampered = valid.clone();
        let one = QPair::from_int(&num_bigint::BigInt::from(1));
        tampered.cert.base.conclusion.constant =
            farkas_cert_add_qpair(&tampered.cert.base.conclusion.constant, &one);
        assert!(
            !farkas_cert::check_slack(&tampered.cert),
            "tampered real cert MUST be rejected by check_slack (Rust)"
        );

        // Emit both certs (the checkable SCertZ payload) as JSON next to the Lean
        // anchor file, using the existing serde (BigInt as decimal strings).
        let out_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../verification/lean/farkas_anchor");
        std::fs::create_dir_all(&out_dir).expect("create anchor dir");

        let valid_json = serde_json::to_string_pretty(&valid.cert).expect("serialize valid");
        let tampered_json =
            serde_json::to_string_pretty(&tampered.cert).expect("serialize tampered");
        std::fs::write(out_dir.join("valid_cert.json"), &valid_json).expect("write valid");
        std::fs::write(out_dir.join("tampered_cert.json"), &tampered_json).expect("write tampered");

        // Round-trip sanity: the persisted JSON re-checks identically (true / false),
        // confirming the bytes the Lean side reads carry the same decision.
        let valid_back: SCertZ = serde_json::from_str(&valid_json).expect("deser valid");
        let tampered_back: SCertZ = serde_json::from_str(&tampered_json).expect("deser tampered");
        assert!(farkas_cert::check_slack(&valid_back));
        assert!(!farkas_cert::check_slack(&tampered_back));

        eprintln!(
            "anchor instance: {ANCHOR_OPB_REL}  (vars={}, constraints={}, bound={bound})",
            instance.num_vars,
            instance.constraints.len()
        );
        eprintln!("wrote {}", out_dir.join("valid_cert.json").display());
        eprintln!("wrote {}", out_dir.join("tampered_cert.json").display());
        eprintln!("--- valid_cert.json ---\n{valid_json}");
        eprintln!("--- tampered_cert.json ---\n{tampered_json}");
    }

    /// CROSS-CHECKED FUSION: load the FRESH fixtures regenerated by
    /// `emit_farkas_cert_json_for_lean_anchor` and assert the Rust checker
    /// [`farkas_cert::check_slack`] ACCEPTS `valid_cert.json` and REJECTS
    /// `tampered_cert.json` — the SAME two artifacts the Lean kernel anchor
    /// (`verification/lean/FarkasAnchor.lean`) reduces by `decide`. This is the
    /// Rust<->Lean agreement on identical bytes: both checkers see the same JSON and
    /// must agree (valid -> true, tampered -> false). Runs by default (not ignored)
    /// so CI keeps the committed fixtures honest against the Rust checker.
    #[test]
    fn lean_anchor_fixtures_agree_with_rust_checker() {
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../verification/lean/farkas_anchor");

        let valid_text =
            std::fs::read_to_string(dir.join("valid_cert.json")).expect("read valid_cert.json");
        let tampered_text = std::fs::read_to_string(dir.join("tampered_cert.json"))
            .expect("read tampered_cert.json");

        let valid: SCertZ = serde_json::from_str(&valid_text).expect("deserialize valid_cert.json");
        let tampered: SCertZ =
            serde_json::from_str(&tampered_text).expect("deserialize tampered_cert.json");

        assert!(
            farkas_cert::check_slack(&valid),
            "Rust check_slack MUST ACCEPT the committed valid_cert.json (the artifact \
             the Lean kernel anchor accepts)"
        );
        assert!(
            !farkas_cert::check_slack(&tampered),
            "Rust check_slack MUST REJECT the committed tampered_cert.json (the artifact \
             the Lean kernel anchor rejects)"
        );

        // The tamper is a single-coefficient corruption: the two certs differ ONLY in
        // the conclusion constant (the lower bound), nowhere else.
        assert_eq!(
            valid.base.premises, tampered.base.premises,
            "premises must be byte-identical"
        );
        assert_eq!(
            valid.base.multipliers, tampered.base.multipliers,
            "multipliers must be byte-identical"
        );
        assert_eq!(
            valid.base.conclusion.coeffs, tampered.base.conclusion.coeffs,
            "conclusion coefficients must be byte-identical (only the constant changed)"
        );
        assert_ne!(
            valid.base.conclusion.constant, tampered.base.conclusion.constant,
            "the tampered cert MUST differ in exactly the conclusion constant"
        );
    }

    #[test]
    fn farkas_cert_validates_real_opb_instance_via_gated_path() {
        // End-to-end on a REAL OPT-LIN .opb instance through the gated emit path:
        // enable AY_PB_FARKAS_CERT, parse the instance, run lp_lower_bound_with_cert,
        // and confirm the checker VERIFIED the certificate for the real LP bound.
        // (Env vars are process-global; this is the only test that sets this flag,
        // and it restores the prior value.)
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/instances/weighted_opt.opb"
        );
        let text = std::fs::read_to_string(path).expect("read sample OPB");
        let instance = crate::parser::parse_opb(&text).expect("parse OPB");
        let objective = instance.objective.clone().expect("instance has objective");

        let prev = std::env::var_os("AY_PB_FARKAS_CERT");
        std::env::set_var("AY_PB_FARKAS_CERT", "1");

        let result = lp_lower_bound_with_cert(
            &objective,
            &instance.constraints,
            instance.num_vars,
            &never_stop,
        );

        // Restore the env regardless of the assertions below.
        match prev {
            Some(v) => std::env::set_var("AY_PB_FARKAS_CERT", v),
            None => std::env::remove_var("AY_PB_FARKAS_CERT"),
        }

        let (bound, cert, outcome) = result.expect("certified bound");
        assert_eq!(
            outcome,
            CertOutcome::Verified,
            "the checker MUST verify the certificate for a real OPB instance"
        );
        let cert = cert.expect("a cert is present when Verified");
        assert_eq!(cert.claimed_bound, bound);
        assert!(
            farkas_cert::check_slack(&cert.cert),
            "re-checking the persisted cert MUST still pass"
        );
        // The plain (cut-augmented) path returns a bound >= the certified base bound
        // (the cert is non-perturbing; the cut loop can only raise the floor).
        let plain = lp_lower_bound(
            &objective,
            &instance.constraints,
            instance.num_vars,
            &never_stop,
        )
        .expect("plain bound");
        assert!(
            plain >= bound,
            "the plain bound {plain} must be >= the certified base bound {bound}"
        );
    }

    #[test]
    fn farkas_cert_differential_validates_every_real_bound() {
        // For many random feasible instances, the emitted certificate for the REAL
        // simplex bound must ALWAYS validate (the cert is faithful), and its claimed
        // bound must equal the simplex bound. This is the differential check the
        // design calls for: (cert builds) => (check passes AND L == simplex bound).
        let mut rng = Rng(0x0bad_c0de_dead_beef);
        let mut validated = 0usize;
        for _ in 0..1500 {
            let n: u32 = rng.range(1, 5) as u32;
            let mut obj_terms = Vec::new();
            for v in 1..=n {
                let coeff = rng.range(-3, 4);
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

            let num_c = rng.range(0, 3);
            let mut constraints = Vec::new();
            for _ in 0..num_c {
                let mut terms = Vec::new();
                for v in 1..=n {
                    let coeff = rng.range(-2, 3);
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
                let rhs = rng.range(-2, 3);
                let rel = if rng.next() & 1 == 1 {
                    PbRel::Ge
                } else {
                    PbRel::Eq
                };
                constraints.push(PbConstraint { terms, rel, rhs });
            }

            let Some(model) = LpModel::build(&obj, &constraints, n) else {
                continue;
            };
            let Some(dual) = model.solve_dual(&never_stop, None) else {
                continue;
            };
            let Some(cert) = model.build_farkas_cert(&dual) else {
                continue;
            };
            assert_eq!(
                cert.claimed_bound, dual.bound,
                "cert bound must equal simplex bound"
            );
            assert!(
                farkas_cert::check_slack(&cert.cert),
                "FAITHFULNESS VIOLATION: real cert failed its own checker\n\
                 objective={obj:?}\nconstraints={constraints:?}"
            );
            validated += 1;
        }
        assert!(
            validated > 100,
            "expected many validated certs, got {validated}"
        );
    }

    // --- Reduced-cost variable fixing soundness. --- //

    /// Enumerates all feasible assignments whose objective is STRICTLY below
    /// `incumbent_ub`, returning them as 0/1 vectors. These are exactly the
    /// assignments a reduced-cost fixing is allowed to constrain.
    fn strictly_better_feasible(
        obj: &PbObjective,
        constraints: &[PbConstraint],
        n: u32,
        incumbent_ub: i128,
    ) -> Vec<Vec<bool>> {
        let mut out = Vec::new();
        for mask in 0u32..(1u32 << n) {
            let x: Vec<bool> = (0..n).map(|b| (mask >> b) & 1 == 1).collect();
            if constraints.iter().all(|c| constraint_holds(c, &x))
                && objective_value(obj, &x) < incumbent_ub
            {
                out.push(x);
            }
        }
        out
    }

    /// CORE SOUNDNESS GATE: every reduced-cost fixing emitted must be respected by
    /// EVERY feasible assignment strictly better than the incumbent. If any
    /// strictly-better assignment violates a fix, the fix would have removed a
    /// better solution -> UNSOUND. Also asserts the LP lower bound never exceeds the
    /// brute-force optimum (the fixing path's bound is the same exact-rational LP).
    #[test]
    fn differential_reduced_cost_fixings_never_remove_a_better_solution() {
        let mut rng = Rng(0x0BAD_F00D_1357_2468);
        let mut checked = 0usize;
        let mut total_fixings = 0usize;
        for _ in 0..4000 {
            let n: u32 = rng.range(1, 6) as u32;
            let mut obj_terms = Vec::new();
            for v in 1..=n {
                let coeff = rng.range(-3, 4);
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
                    let coeff = rng.range(-3, 4);
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
                let rhs = rng.range(-3, 4);
                let rel = if rng.next().is_multiple_of(3) {
                    PbRel::Eq
                } else {
                    PbRel::Ge
                };
                constraints.push(PbConstraint { terms, rel, rhs });
            }

            let Some(opt) = brute_force_optimum(&obj, &constraints, n) else {
                continue; // infeasible: no fixing test applies.
            };
            checked += 1;

            // Test a spread of incumbents: the true optimum, optimum+1, optimum+2,
            // and a loose one. Smaller gaps fix more; the optimum itself fixes only
            // vars forced in every strictly-better-than-optimum solution (none, since
            // there are none — vacuously sound).
            for delta in [0i128, 1, 2, 5] {
                let incumbent_ub = opt + delta;
                let Some(result) =
                    lp_reduced_cost_fixings(&obj, &constraints, n, incumbent_ub, &never_stop)
                else {
                    continue;
                };
                // LP bound soundness (same exact-rational LP).
                assert!(
                    result.lower_bound <= opt,
                    "SOUNDNESS: LP bound {} > optimum {opt}",
                    result.lower_bound
                );
                total_fixings += result.fixings.len();

                let better = strictly_better_feasible(&obj, &constraints, n, incumbent_ub);
                for fix in &result.fixings {
                    let idx = (fix.var - 1) as usize;
                    for x in &better {
                        assert_eq!(
                            x[idx], fix.value,
                            "SOUNDNESS VIOLATION: fixing var {} -> {} removes a \
                             strictly-better assignment {x:?}\nincumbent_ub={incumbent_ub} \
                             opt={opt}\nobjective={obj:?}\nconstraints={constraints:?}",
                            fix.var, fix.value
                        );
                    }
                }
            }
        }
        assert!(
            checked > 100,
            "expected many feasible instances, got {checked}"
        );
        eprintln!("reduced-cost: {total_fixings} total fixings across {checked} instances");
    }

    /// A concrete instance where a reduced-cost fixing IS derivable, so the test
    /// above is exercising real fixings (not vacuously passing on empty fix sets).
    #[test]
    fn reduced_cost_fixing_fixes_an_expensive_variable() {
        // min 100 x1 + x2 + x3  s.t.  x1 + x2 + x3 >= 1.
        // LP optimum picks the cheapest cover (x2 or x3) -> LB = 1. x1 has reduced
        // cost 100 (its objective coeff; the covering constraint is satisfied without
        // it). With incumbent_ub = 2 (a strictly-better solution must cost <= 1),
        // any solution with x1=1 costs >= 100 > 1, so x1 must be 0. Expect a fix
        // var1 -> false.
        let obj = PbObjective {
            terms: vec![term(100, lit(1)), term(1, lit(2)), term(1, lit(3))],
        };
        let c = ge(vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))], 1);
        let result =
            lp_reduced_cost_fixings(&obj, &[c], 3, 2, &never_stop).expect("fixings computed");
        assert!(
            result.fixings.iter().any(|f| f.var == 1 && !f.value),
            "expected x1 fixed to 0, got {:?}",
            result.fixings
        );
    }

    /// Complementation path: an expensive NEGATED-literal cost should fix the
    /// underlying variable the other way. min 100 ~x1 + x2 s.t. x2 >= 1 forces x2=1
    /// (cost 1); to stay strictly below incumbent 2 we cannot pay the 100 for ~x1,
    /// so ~x1 must be false, i.e. x1 must be TRUE.
    #[test]
    fn reduced_cost_fixing_handles_complemented_variable() {
        let obj = PbObjective {
            terms: vec![term(100, neg(1)), term(1, lit(2))],
        };
        let c = ge(vec![term(1, lit(2))], 1);
        let result =
            lp_reduced_cost_fixings(&obj, &[c], 2, 2, &never_stop).expect("fixings computed");
        assert!(
            result.fixings.iter().any(|f| f.var == 1 && f.value),
            "expected x1 fixed to 1 (since ~x1 too expensive), got {:?}",
            result.fixings
        );
    }

    /// Regression for the instance that exposed the OLL hardening/core collapse
    /// (min 4x1 + 92~x2 + 6x3 + 3x4 + 10x5 s.t. x1+x2+x3>=2, optimum 4): the
    /// reduced-cost fixings must be self-consistent with the optimum and never fix
    /// x1 to 0 (the optimum needs x1=1).
    #[test]
    fn reduced_cost_fixings_respect_optimum_on_regression_instance() {
        let obj = PbObjective {
            terms: vec![
                term(4, lit(1)),
                term(92, neg(2)),
                term(6, lit(3)),
                term(3, lit(4)),
                term(10, lit(5)),
            ],
        };
        let c = ge(vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))], 2);
        // Optimum x1=1,x2=1,x3=0,x4=0,x5=0 (value 4). Any fixing must agree with it
        // for any incumbent strictly above 4.
        let opt_vals = [true, true, false, false, false];
        for ub in [5, 6, 7, 100] {
            let r = lp_reduced_cost_fixings(&obj, &[c.clone()], 5, ub, &never_stop).expect("ok");
            assert!(r.lower_bound <= 4, "LP bound {} > optimum 4", r.lower_bound);
            for f in &r.fixings {
                assert_eq!(
                    f.value,
                    opt_vals[(f.var - 1) as usize],
                    "ub={ub}: fix var{} -> {} contradicts the optimum",
                    f.var,
                    f.value
                );
            }
        }
    }

    // --- Cut-tightening behaviour (still sound). --- //

    #[test]
    fn clique_cut_tightens_triangle_packing() {
        // Maximize x1+x2+x3 packed into an at-most-one (triangle) is, as a
        // *minimization*, min (1-x1)+(1-x2)+(1-x3) = min ~x1+~x2+~x3 subject to
        // the three pairwise exclusions x_i + x_j <= 1.
        // LP relaxation: x_i = 1/2 each is feasible (each pair sums to 1), giving
        // objective 3 - 3/2 = 3/2 -> ceil 2. The clique cut x1+x2+x3 <= 1 forces
        // sum x <= 1, so objective >= 3 - 1 = 2 ... here both ceil to 2, so use a
        // sharper objective: minimize -(x1+x2+x3) is not allowed (we need c>=0);
        // instead minimize ~x1+~x2+~x3 and check the *fractional* bound rises.
        let obj = PbObjective {
            terms: vec![term(1, neg(1)), term(1, neg(2)), term(1, neg(3))],
        };
        // Pairwise exclusions x_i + x_j <= 1 as >= rows: -x_i - x_j >= -1.
        let c12 = ge(vec![term(-1, lit(1)), term(-1, lit(2))], -1);
        let c13 = ge(vec![term(-1, lit(1)), term(-1, lit(3))], -1);
        let c23 = ge(vec![term(-1, lit(2)), term(-1, lit(3))], -1);
        let constraints = vec![c12, c13, c23];

        let base = lp_lower_bound_no_cuts(&obj, &constraints, 3, &never_stop).expect("base");
        let cut = lp_lower_bound(&obj, &constraints, 3, &never_stop).expect("cut");
        // The integer optimum: at most one x_i true, so >= 2 of the ~x_i true ->
        // objective 2. Both bounds are sound (<= 2); the cut bound is >= base.
        assert!(cut >= base, "cut bound {cut} should be >= base {base}");
        assert!(cut <= 2, "cut bound {cut} must be <= integer optimum 2");
        assert_eq!(cut, 2, "clique cut should prove the optimum 2 here");
    }

    #[test]
    fn cover_cut_tightens_knapsack_objective() {
        // min ~x1 + ~x2 + ~x3  (= 3 - (x1+x2+x3))  s.t. 2x1 + 2x2 + 2x3 <= 3.
        // Knapsack cap 3, weights 2: any two items exceed cap, so at most one is
        // chosen -> x1+x2+x3 <= 1, objective >= 2. LP relaxation lets x_i = 1/2
        // (sum 3 = cap), objective 3 - 3/2 = 3/2 -> ceil 2. The cover cut
        // {i,j}: x_i+x_j <= 1 (and the lifted triangle) tightens toward 2.
        let obj = PbObjective {
            terms: vec![term(1, neg(1)), term(1, neg(2)), term(1, neg(3))],
        };
        // 2x1+2x2+2x3 <= 3  as >= : -2x1 -2x2 -2x3 >= -3.
        let knap = ge(
            vec![term(-2, lit(1)), term(-2, lit(2)), term(-2, lit(3))],
            -3,
        );
        let constraints = vec![knap];
        let base = lp_lower_bound_no_cuts(&obj, &constraints, 3, &never_stop).expect("base");
        let cut = lp_lower_bound(&obj, &constraints, 3, &never_stop).expect("cut");
        let opt = brute_force_optimum(&obj, &constraints, 3).expect("feasible");
        assert!(cut >= base, "cut {cut} should be >= base {base}");
        assert!(cut <= opt, "cut {cut} must be <= integer optimum {opt}");
        assert_eq!(opt, 2);
        assert_eq!(cut, 2, "cover cut should prove the optimum 2 here");
    }

    /// Differential test that the *cut* bound never exceeds the brute-force
    /// optimum, and is never below the *no-cut* base bound, over many random
    /// instances. This is the soundness gate for the whole cut loop.
    #[test]
    fn differential_cut_bound_is_sound_and_monotone() {
        let mut rng = Rng(0xFEED_FACE_CAFE_BEEF);
        let mut checked = 0usize;
        let mut tightened = 0usize;
        for _ in 0..3000 {
            let n: u32 = rng.range(2, 6) as u32;
            let mut obj_terms = Vec::new();
            for v in 1..=n {
                let coeff = rng.range(-3, 4);
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

            let num_c = rng.range(1, 5);
            let mut constraints = Vec::new();
            for _ in 0..num_c {
                let mut terms = Vec::new();
                for v in 1..=n {
                    let coeff = rng.range(-3, 4);
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
                let rhs = rng.range(-3, 4);
                let rel = if rng.next().is_multiple_of(4) {
                    PbRel::Eq
                } else {
                    PbRel::Ge
                };
                constraints.push(PbConstraint { terms, rel, rhs });
            }

            let Some(opt) = brute_force_optimum(&obj, &constraints, n) else {
                continue;
            };
            checked += 1;

            let base = lp_lower_bound_no_cuts(&obj, &constraints, n, &never_stop);
            let cut = lp_lower_bound(&obj, &constraints, n, &never_stop);
            if let Some(cut) = cut {
                assert!(
                    cut <= opt,
                    "SOUNDNESS VIOLATION: cut LP_LB {cut} > brute optimum {opt}\n\
                     objective={obj:?}\nconstraints={constraints:?}"
                );
                if let Some(base) = base {
                    assert!(
                        cut >= base,
                        "cut bound {cut} regressed below base {base}\n\
                         objective={obj:?}\nconstraints={constraints:?}"
                    );
                    if cut > base {
                        tightened += 1;
                    }
                }
            }
        }
        assert!(
            checked > 100,
            "expected many feasible instances, got {checked}"
        );
        eprintln!("cut loop tightened {tightened}/{checked} feasible instances");
    }

    // --- Real-instance soundness: LP_LB <= known Exact optimum. ---

    #[test]
    #[ignore = "manual benchmark measurement against local PB25 instances"]
    fn measure_opt_lin_lp_bounds() {
        let dir = pbcomp_path("PB25/normalized-PB25/OPT-LIN/wallon");
        for name in [
            "normalized-Clique-c0125-9_c24.opb",
            "normalized-GolombRuler-a3v18-15_c18.opb",
            "normalized-FoolSolitaire-table-2-0_c24.opb",
            "normalized-Charlotte-mini-24-2_c24.opb",
            "normalized-AztecDiamondSym-mini-07_c24.opb",
        ] {
            let path = format!("{dir}/{name}");
            let Ok(text) = std::fs::read_to_string(&path) else {
                eprintln!("{name}: absent");
                continue;
            };
            let inst = match crate::parser::parse_opb(&text) {
                Ok(i) => i,
                Err(e) => {
                    eprintln!("{name}: parse error {e:?}");
                    continue;
                }
            };
            let Some(obj) = inst.objective.as_ref() else {
                eprintln!("{name}: no objective");
                continue;
            };
            let t0 = std::time::Instant::now();
            let base = lp_lower_bound_no_cuts(obj, &inst.constraints, inst.num_vars, &never_stop);
            let t_base = t0.elapsed().as_millis();
            let t1 = std::time::Instant::now();
            let lb = lp_lower_bound(obj, &inst.constraints, inst.num_vars, &never_stop);
            eprintln!(
                "{name}: vars={} cons={} LP_LB(base)={:?} ({} ms)  LP_LB(cuts)={:?} ({} ms)",
                inst.num_vars,
                inst.constraints.len(),
                base,
                t_base,
                lb,
                t1.elapsed().as_millis()
            );
        }
    }

    #[test]
    #[ignore = "manual benchmark measurement against local PB24/PB25 instances"]
    fn measure_cut_tightening_across_families() {
        // (path, optional known optimum) across families that have hard
        // clique/cover structure. Reports base vs cut LP_LB and the gap closed.
        // Instances where the exact-rational base LP itself is tractable so the
        // cut-loop overhead is visible. (Some PB instances have very large
        // exact-rational base LP solves unrelated to cuts; those are excluded by the
        // work-proxy gate and not measured here.)
        let cases: &[(&str, Option<i128>)] = &[
            (
                "PB25/normalized-PB25/OPT-LIN/wallon/normalized-Clique-c0125-9_c24.opb",
                None,
            ),
            (
                "PB24/normalized-PB24/OPT-LIN/pettersson/StableMatchings/KidneyTransplantBenchmarks/normalized-KE_60_004.opb",
                None,
            ),
        ];
        for (rel, opt) in cases {
            let path = pbcomp_path(rel);
            let Ok(text) = std::fs::read_to_string(&path) else {
                eprintln!("{path}: absent");
                continue;
            };
            let inst = match crate::parser::parse_opb(&text) {
                Ok(i) => i,
                Err(e) => {
                    eprintln!("{path}: parse error {e:?}");
                    continue;
                }
            };
            let Some(obj) = inst.objective.as_ref() else {
                eprintln!("{path}: no objective");
                continue;
            };
            let name = path.rsplit('/').next().unwrap_or(&path);
            let base = lp_lower_bound_no_cuts(obj, &inst.constraints, inst.num_vars, &never_stop);
            let t = std::time::Instant::now();
            let cut = lp_lower_bound(obj, &inst.constraints, inst.num_vars, &never_stop);
            // Soundness re-assertion against any known optimum.
            if let (Some(c), Some(o)) = (cut, opt) {
                assert!(
                    c <= *o,
                    "SOUNDNESS VIOLATION: {name} cut LP_LB {c} > opt {o}"
                );
            }
            if let (Some(b), Some(c)) = (base, cut) {
                assert!(c >= b, "{name}: cut bound {c} regressed below base {b}");
            }
            eprintln!(
                "{name}: vars={} cons={} base={base:?} cut={cut:?} opt={opt:?} ({} ms)",
                inst.num_vars,
                inst.constraints.len(),
                t.elapsed().as_millis()
            );
        }
    }

    #[test]
    fn spot5_54_lp_lb_is_sound_and_below_optimum() {
        // PB24 PARTIAL-LIN wcsp/spot5/normalized-spot5-54_wcsp.wbo, Exact opt = 37.
        // Skipped gracefully when the benchmark is not present in this checkout.
        let path = pbcomp_path("PB24/WBO/PARTIAL-LIN/wcsp/spot5/normalized-spot5-54_wcsp.wbo");
        let Ok(text) = std::fs::read_to_string(&path) else {
            eprintln!("spot5-54 benchmark absent; skipping real-instance check");
            return;
        };
        let wbo = crate::parser::parse_wbo(&text).expect("parse spot5-54 wbo");
        let pbo = crate::optimize::wbo::wbo_to_pbo(&wbo);
        let objective = pbo.objective.as_ref().expect("spot5-54 has an objective");
        let base = lp_lower_bound_no_cuts(objective, &pbo.constraints, pbo.num_vars, &never_stop);
        let lb = lp_lower_bound(objective, &pbo.constraints, pbo.num_vars, &never_stop);
        if let Some(lb) = lb {
            assert!(
                lb <= 37,
                "SOUNDNESS VIOLATION: spot5-54 LP_LB {lb} > Exact optimum 37"
            );
            if let Some(base) = base {
                assert!(lb >= base, "cut bound {lb} regressed below base {base}");
            }
            eprintln!("spot5-54 LP_LB(base) = {base:?}  LP_LB(cuts) = {lb} (Exact optimum 37)");
        } else {
            eprintln!("spot5-54 LP declined to bound (size/work cap)");
        }
    }
}
