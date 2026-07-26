// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! In-production cutting-planes OPTIMUM SELF-CHECK (the DUAL of
//! [`crate::proof::refutation_check`]).
//!
//! Where the refutation checker replays a cutting-planes derivation that must
//! terminate in the contradiction `0 >= c` (`c >= 1`), this module replays a
//! cutting-planes derivation that must terminate in a LOWER BOUND on the
//! OBJECTIVE's linear form:
//!
//! ```text
//!   sum_v obj_coeff[v] * x_v  >=  F
//! ```
//!
//! It implements the following certificate checks directly over the original
//! instance:
//!
//! * `cut_lower_bound_is_sound_floor`: if the cutting-planes algebra entails
//!   `ImpliedGe cs obj.terms F`, then `F` is a sound floor on the objective over
//!   the entire feasible region (the `hFloor` obligation behind OPTIMUM).
//! * `pb_optimum_eq_of_cut_lower_bound`: a checked cutting-planes lower bound `F`
//!   that equals a VIG-verified incumbent's objective value IS the optimality
//!   certificate (`LB == UB`) — the dual of the UNSAT empty clause.
//!
//! # Soundness model
//!
//! The derivation uses exactly the same kernel arrows as the refutation checker
//! (`add` / `scale` / `divide` / `saturate`, recomputed from scratch by
//! [`crate::proof::refutation_check::replay_derivation`]), over the ORIGINAL
//! instance's constraints PLUS the sound boolean lower-bound axioms `x_v >= 0`
//! (every `0/1` variable is non-negative — see
//! [`LinConstraint::var_geq_zero`](crate::proof::LinConstraint)). The terminal
//! check requires the derived constraint to be EXACTLY `sum obj_coeff[v] x_v >= F`
//! (coefficients identical to the normalized objective, RHS exactly the claimed
//! floor). A builder that overcounts (claims a higher `F` than the derivation
//! actually yields) or that derives a bound on the WRONG linear form is therefore
//! REJECTED — only the checker's own correctness (the kernel algebra mirrored
//! here) is trusted.
//!
//! Fail-closed policy: a verdict that cannot produce a self-checking certificate
//! must be emitted as `SATISFIABLE`, never as an unchecked `OPTIMUM`.

use std::collections::BTreeMap;

use crate::types::{PbConstraint, PbObjective, PbRel, PbTerm};

use super::refutation_check::{
    pb_eq_halves, pb_ge, replay_derivation, LinConstraint, RefError, RefStep,
};

/// A complete OPTIMUM lower-bound certificate: a cutting-planes derivation over
/// the inputs that must reduce to `sum obj_coeff[v] x_v >= claimed_floor`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObjectiveBound {
    /// Input constraints, already normalized to `>=` form. These are the AXIOMS
    /// the checker trusts as given: the instance's ORIGINAL constraints plus the
    /// sound boolean bounds `x_v >= 0`.
    pub inputs: Vec<LinConstraint>,
    /// Derivation steps, applied in order; each appends one constraint.
    pub steps: Vec<RefStep>,
    /// The objective's linear form (`min: sum objective_terms`). The derivation
    /// must reduce to exactly this linear form with RHS `claimed_floor`.
    pub objective_terms: Vec<PbTerm>,
    /// The lower bound `F` the emitter claims the derivation proves.
    pub claimed_floor: i128,
}

/// Why an OPTIMUM certificate failed to self-check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OptError {
    /// The cutting-planes derivation itself failed to replay (bad reference,
    /// rule side-condition, overflow, or empty derivation).
    Replay(RefError),
    /// The objective could not be normalized into a linear `>=` form (a
    /// non-linear/product term).
    UnmodeledObjective,
    /// The derivation completed but its linear form does not match the objective,
    /// or its RHS is not exactly `claimed_floor` (an overcounted/forged bound).
    NotObjectiveFloor,
    /// The certified floor is sound but does NOT meet the incumbent
    /// (`incumbent_value != F`), so this is only a floor — not optimality.
    NotTight,
}

impl ObjectiveBound {
    /// Replays the derivation and verifies it proves EXACTLY
    /// `sum obj_coeff[v] x_v >= claimed_floor`. On success returns the certified
    /// floor `F = claimed_floor` (a sound lower bound on the objective over the
    /// whole feasible region).
    pub fn check_floor(&self) -> Result<i128, OptError> {
        // The objective normalized as the target `>= claimed_floor` constraint.
        let target = pb_ge(&PbConstraint {
            terms: self.objective_terms.clone(),
            rel: PbRel::Ge,
            rhs: self.claimed_floor,
        })
        .ok_or(OptError::UnmodeledObjective)?;

        let derived = replay_derivation(&self.inputs, &self.steps).map_err(OptError::Replay)?;

        // The derived constraint must be IDENTICAL to the objective floor: same
        // per-variable coefficients AND the same RHS. Equality (not `>=`) is the
        // dual of the refutation checker's `0 >= c` terminal: a builder that
        // claims a floor the derivation does not actually reach is rejected.
        if derived == target {
            Ok(self.claimed_floor)
        } else {
            Err(OptError::NotObjectiveFloor)
        }
    }

    /// Sound-decline guard for the derivation replay. [`Self::check_floor`] /
    /// [`replay_derivation`] retain one `LinConstraint` (a `BTreeMap`) per input
    /// AND per step for the whole replay, so a large certificate's replay
    /// database can reach many GB — the runaway that detonated the 2026-07-11
    /// panic family once the eqagg Gauss path was capped. The certified floor is
    /// an OPTIONAL optimality upgrade, so declining an oversized certificate
    /// BEFORE replaying it is fail-closed (never a wrong verdict). Cost proxy:
    /// retained rows × the widest input row (an upper bound on the replay DB's
    /// per-row density), capped to keep the database well under ~1 GiB regardless
    /// of the harness `MEMLIMIT`.
    fn replay_within_memory_budget(&self) -> bool {
        const REPLAY_ROWS_TIMES_WIDTH_CAP: u128 = 20_000_000;
        let rows = (self.inputs.len() + self.steps.len()) as u128;
        let width = self
            .inputs
            .iter()
            .map(LinConstraint::width)
            .max()
            .unwrap_or(0)
            .max(self.objective_terms.len()) as u128;
        rows.saturating_mul(width) <= REPLAY_ROWS_TIMES_WIDTH_CAP
    }

    /// The full OPTIMUM certificate check (`LB == UB`): the derivation proves a
    /// sound floor `F` AND a VIG-verified incumbent attains objective value `F`.
    ///
    /// Mirrors `pb_optimum_eq_of_cut_lower_bound`: given `ImpliedGe cs obj F`
    /// (here, `check_floor`) and an incumbent `w` with `evalObjective w == F`, the
    /// incumbent is OPTIMAL. The caller MUST have verified the incumbent feasible
    /// via the VIG ([`crate::eval::verify_all_constraints`]); `incumbent_value` is
    /// the objective value of that VIG-verified assignment.
    pub fn certify_optimum(&self, incumbent_value: i128) -> Result<i128, OptError> {
        let floor = self.check_floor()?;
        if incumbent_value == floor {
            Ok(floor)
        } else {
            Err(OptError::NotTight)
        }
    }
}

/// Maps each objective term to a single PLAIN (non-negated) literal with a
/// strictly-positive integer coefficient, accumulated per variable. Returns
/// `None` for any objective the certificate builder cannot model exactly: a
/// non-linear term, a negated literal, or a non-positive coefficient. (This is
/// intentionally narrower than the solver's bound engine — it is the slice for
/// which an EXACT, x>=0-liftable cutting-planes certificate can be built.)
fn positive_plain_objective(objective: &PbObjective) -> Option<BTreeMap<u32, i128>> {
    if objective.terms.is_empty() {
        return None;
    }
    let mut coeffs: BTreeMap<u32, i128> = BTreeMap::new();
    for term in &objective.terms {
        let [lit] = term.lits.as_slice() else {
            return None;
        };
        if lit.negated || lit.var == 0 || term.coeff <= 0 {
            return None;
        }
        *coeffs.entry(lit.var).or_insert(0) = coeffs
            .get(&lit.var)
            .copied()
            .unwrap_or(0)
            .checked_add(term.coeff)?;
    }
    Some(coeffs)
}

/// `ceil(a / d)` for `d >= 1`, exact over `i128`.
fn ceil_div(a: i128, d: i128) -> Option<i128> {
    if d < 1 {
        return None;
    }
    let q = a.checked_div_euclid(d)?;
    let r = a.checked_rem_euclid(d)?;
    if r == 0 {
        Some(q)
    } else {
        q.checked_add(1)
    }
}

/// Builds a CHECKED cutting-planes OPTIMUM certificate for the surrogate LP-dual
/// (uniform-multiplier `1/M`) lower bound — the dual of
/// `crate::cdcl::aggregation_objective_lower_bound_from_constraints`, but emitted
/// as a replayable derivation rather than a trusted scalar.
///
/// # Construction (a Chvátal-Gomory aggregation)
///
/// Over the `>=` covering rows whose every term is a plain positive literal that
/// also appears (plain, positive) in the objective, with `colsum[v] = Σ row
/// coeffs on v`, `rhs_sum = Σ row RHS`, and `M = cs/cv = max_v colsum[v]/objc[v]`:
///
/// 1. ADD all selected rows  → `Σ colsum[v] x_v >= rhs_sum`.
/// 2. SCALE by `cv`          → `Σ cv·colsum[v] x_v >= cv·rhs_sum`.
/// 3. DIVIDE (ceil) by `cs`  → `Σ ⌈cv·colsum[v]/cs⌉ x_v >= ⌈cv·rhs_sum/cs⌉ = F`.
/// 4. LIFT each objective var with `(objc[v] - ⌈cv·colsum[v]/cs⌉)·(x_v >= 0)`,
///    raising every coefficient to `objc[v]` (the lift is `>= 0` because
///    `M >= colsum[v]/objc[v]` ⟹ `⌈cv·colsum[v]/cs⌉ <= objc[v]`).
///
/// The result is EXACTLY `Σ objc[v] x_v >= F`, the objective floor. The function
/// self-checks the certificate ([`ObjectiveBound::check_floor`]) before returning,
/// so it only ever yields a certificate that passes the kernel-mirrored checker.
#[must_use]
pub fn build_aggregation_floor_cert(
    constraints: &[PbConstraint],
    objective: &PbObjective,
) -> Option<ObjectiveBound> {
    let objc = positive_plain_objective(objective)?;

    // Select rows and accumulate the aggregate column sums / RHS. A row joins the
    // aggregate only if EVERY term is a single plain positive literal whose
    // variable is in the (plain positive) objective — the soundness guard that
    // keeps each aggregated coefficient bounded by the objective coefficient.
    let mut selected: Vec<LinConstraint> = Vec::new();
    let mut colsum: BTreeMap<u32, i128> = BTreeMap::new();
    let mut rhs_sum: i128 = 0;
    for c in constraints {
        if c.rel != PbRel::Ge || c.rhs <= 0 {
            continue;
        }
        let row_ok = c.terms.iter().all(|t| match t.lits.as_slice() {
            [lit] => !lit.negated && lit.var != 0 && t.coeff > 0 && objc.contains_key(&lit.var),
            _ => false,
        });
        if !row_ok {
            continue;
        }
        let lin = pb_ge(c)?;
        rhs_sum = rhs_sum.checked_add(c.rhs)?;
        for t in &c.terms {
            let v = t.lits[0].var;
            *colsum.entry(v).or_insert(0) =
                colsum.get(&v).copied().unwrap_or(0).checked_add(t.coeff)?;
        }
        selected.push(lin);
    }
    if selected.is_empty() || rhs_sum <= 0 || colsum.is_empty() {
        return None;
    }

    // M = cs/cv = max_v colsum[v]/objc[v], via exact cross-multiplication.
    let mut best_cs: i128 = 0;
    let mut best_cv: i128 = 1;
    for (&v, &cs) in &colsum {
        let cv = *objc.get(&v)?; // present and > 0 by construction
        if cs.checked_mul(best_cv)? > best_cs.checked_mul(cv)? {
            best_cs = cs;
            best_cv = cv;
        }
    }
    if best_cs <= 0 {
        return None;
    }

    let floor = ceil_div(rhs_sum.checked_mul(best_cv)?, best_cs)?;
    if floor <= 0 {
        return None;
    }

    // Assemble the derivation database: selected rows first, then the boolean
    // lower-bound axioms `x_v >= 0` for every objective variable (used by the
    // lifting step). Index layout: [0..n_rows) rows, then [n_rows..) axioms.
    let n_rows = selected.len();
    let obj_vars: Vec<u32> = objc.keys().copied().collect();
    let axiom_index: BTreeMap<u32, usize> = obj_vars
        .iter()
        .enumerate()
        .map(|(i, &v)| (v, n_rows + i))
        .collect();

    let mut inputs: Vec<LinConstraint> = selected;
    for &v in &obj_vars {
        inputs.push(LinConstraint::var_geq_zero(v));
    }

    let mut steps: Vec<RefStep> = Vec::new();
    // 1. ADD all rows. The running aggregate constraint's database index.
    let mut acc = 0usize; // db index of row 0
    if n_rows >= 2 {
        // First Add appends at index `inputs.len()`.
        let mut next = inputs.len();
        steps.push(RefStep::Add(0, 1));
        acc = next;
        for r in 2..n_rows {
            next += 1;
            steps.push(RefStep::Add(acc, r));
            acc = next;
        }
    }
    // 2. SCALE by cv (only meaningful when cv >= 2; Scale requires k >= 1).
    let mut cur = acc;
    if best_cv >= 2 {
        steps.push(RefStep::Scale(cur, best_cv));
        cur = inputs.len() + steps.len() - 1;
    }
    // 3. DIVIDE (ceil) by cs (only when cs >= 2; Divide requires d >= 1).
    if best_cs >= 2 {
        steps.push(RefStep::Divide(cur, best_cs));
        cur = inputs.len() + steps.len() - 1;
    }

    // The coefficient on each variable after steps 1-3.
    let coeff_after = |v: u32| -> Option<i128> {
        let cs_v = colsum.get(&v).copied().unwrap_or(0);
        ceil_div(cs_v.checked_mul(best_cv)?, best_cs)
    };

    // 4. LIFT each objective variable up to its objective coefficient.
    for &v in &obj_vars {
        let have = coeff_after(v)?;
        let want = *objc.get(&v)?;
        let lift = want.checked_sub(have)?;
        if lift < 0 {
            return None; // unsound shape (should not happen by the M bound)
        }
        if lift == 0 {
            continue;
        }
        let axiom_idx = *axiom_index.get(&v)?;
        if lift == 1 {
            steps.push(RefStep::Add(cur, axiom_idx));
        } else {
            // scale the x_v>=0 axiom by `lift`, then add.
            steps.push(RefStep::Scale(axiom_idx, lift));
            let scaled_idx = inputs.len() + steps.len() - 1;
            steps.push(RefStep::Add(cur, scaled_idx));
        }
        cur = inputs.len() + steps.len() - 1;
    }

    let cert = ObjectiveBound {
        inputs,
        steps,
        objective_terms: objective.terms.clone(),
        claimed_floor: floor,
    };
    // Self-check: only return a certificate that passes the kernel-mirrored
    // checker. A construction bug therefore yields `None` (no certificate),
    // never an accepted-but-wrong floor.
    if cert.replay_within_memory_budget() {
        cert.check_floor().ok().map(|_| cert)
    } else {
        None
    }
}

/// Builds a CHECKED cutting-planes OPTIMUM certificate for the DISJOINT-COVERING
/// (a.k.a. matching / disjoint-core) lower bound — the dual of
/// `crate::cdcl::direct_objective_lower_bound_from_constraints`, emitted as a
/// replayable derivation rather than a trusted scalar.
///
/// # Construction (a Lagrangian / disjoint-core aggregation)
///
/// Greedily select `>=` covering rows whose every term is a plain positive
/// literal in the (plain positive) objective. Maintain a per-variable *budget*
/// `remaining[v]` initialised to `objc[v]`; for each candidate row with per-
/// variable coefficients `rc[v]` take the largest integer multiplier
/// `m = min_v floor(remaining[v] / rc[v])`. If `m >= 1`, spend the budget
/// (`remaining[v] -= m * rc[v]`) and add `m * rhs` to the floor. Because every
/// spent coefficient stays within the budget, the aggregate of the scaled rows
/// has, on each variable, coefficient `objc[v] - remaining[v] <= objc[v]`, so it
/// lifts up to the exact objective form with the sound `x_v >= 0` axioms:
///
/// 1. SCALE each selected row `i` by its multiplier `m_i` (when `m_i >= 2`).
/// 2. ADD all the scaled rows  → `Σ (objc[v] - remaining[v]) x_v >= Σ m_i rhs_i`.
/// 3. LIFT each objective var by `remaining[v] * (x_v >= 0)` up to `objc[v]`.
///
/// The result is EXACTLY `Σ objc[v] x_v >= F` with `F = Σ m_i rhs_i`. This is the
/// matching bound for minimum vertex cover (disjoint unit edges each contribute
/// `1`) and the disjoint-core sum for core-guided lower bounds, expressed as a
/// kernel-checkable derivation. Self-checked before return, so a construction bug
/// yields `None`, never an accepted-but-wrong floor.
#[must_use]
pub fn build_covering_floor_cert(
    constraints: &[PbConstraint],
    objective: &PbObjective,
) -> Option<ObjectiveBound> {
    let objc = positive_plain_objective(objective)?;

    // Per-variable spend budget, drained as rows are committed.
    let mut remaining: BTreeMap<u32, i128> = objc.clone();
    // Committed rows, in selection order: (normalized row, multiplier).
    let mut selected: Vec<(LinConstraint, i128)> = Vec::new();
    let mut floor: i128 = 0;

    for c in constraints {
        if c.rel != PbRel::Ge || c.rhs <= 0 {
            continue;
        }
        // Accumulate this row's plain-positive coefficients; reject any row with a
        // term that is not a single plain positive objective literal.
        let mut rowc: BTreeMap<u32, i128> = BTreeMap::new();
        let mut row_ok = true;
        for t in &c.terms {
            match t.lits.as_slice() {
                [lit]
                    if !lit.negated
                        && lit.var != 0
                        && t.coeff > 0
                        && objc.contains_key(&lit.var) =>
                {
                    *rowc.entry(lit.var).or_insert(0) = rowc
                        .get(&lit.var)
                        .copied()
                        .unwrap_or(0)
                        .checked_add(t.coeff)?;
                }
                _ => {
                    row_ok = false;
                    break;
                }
            }
        }
        if !row_ok || rowc.is_empty() {
            continue;
        }
        // Largest integer multiplier the remaining budget admits.
        let mut mult: i128 = i128::MAX;
        for (&v, &rc) in &rowc {
            let rem = remaining.get(&v).copied().unwrap_or(0);
            if rc <= 0 || rem <= 0 {
                mult = 0;
                break;
            }
            mult = mult.min(rem / rc);
        }
        if mult < 1 {
            continue;
        }
        // Commit: spend budget and add this row's weighted degree to the floor.
        for (&v, &rc) in &rowc {
            let r = remaining.get_mut(&v)?;
            *r = r.checked_sub(rc.checked_mul(mult)?)?;
        }
        floor = floor.checked_add(c.rhs.checked_mul(mult)?)?;
        selected.push((pb_ge(c)?, mult));
    }

    if selected.is_empty() || floor <= 0 {
        return None;
    }

    // Assemble the derivation database: selected rows first, then the boolean
    // lower-bound axioms `x_v >= 0` for every objective variable (the lift step).
    let n_rows = selected.len();
    let obj_vars: Vec<u32> = objc.keys().copied().collect();
    let axiom_index: BTreeMap<u32, usize> = obj_vars
        .iter()
        .enumerate()
        .map(|(i, &v)| (v, n_rows + i))
        .collect();

    let mut inputs: Vec<LinConstraint> = selected.iter().map(|(lin, _)| lin.clone()).collect();
    for &v in &obj_vars {
        inputs.push(LinConstraint::var_geq_zero(v));
    }

    let mut steps: Vec<RefStep> = Vec::new();
    // 1. SCALE each row by its multiplier (only when m >= 2); record the database
    //    index that now holds the (scaled) row.
    let mut eff: Vec<usize> = Vec::with_capacity(n_rows);
    for (i, (_lin, mult)) in selected.iter().enumerate() {
        if *mult >= 2 {
            steps.push(RefStep::Scale(i, *mult));
            eff.push(inputs.len() + steps.len() - 1);
        } else {
            eff.push(i);
        }
    }
    // 2. ADD all (scaled) rows into a single aggregate.
    let mut cur = eff[0];
    for &idx in eff.iter().skip(1) {
        steps.push(RefStep::Add(cur, idx));
        cur = inputs.len() + steps.len() - 1;
    }
    // 3. LIFT each objective variable up to its objective coefficient. The
    //    aggregate's coefficient on `v` is `objc[v] - remaining[v]`, so the lift
    //    amount is exactly the unspent budget `remaining[v] >= 0`.
    for &v in &obj_vars {
        let lift = remaining.get(&v).copied().unwrap_or(0);
        if lift < 0 {
            return None; // unsound shape (should not happen by the budget invariant)
        }
        if lift == 0 {
            continue;
        }
        let axiom_idx = *axiom_index.get(&v)?;
        if lift == 1 {
            steps.push(RefStep::Add(cur, axiom_idx));
        } else {
            steps.push(RefStep::Scale(axiom_idx, lift));
            let scaled_idx = inputs.len() + steps.len() - 1;
            steps.push(RefStep::Add(cur, scaled_idx));
        }
        cur = inputs.len() + steps.len() - 1;
    }

    // Materialize the aggregate as an explicit derived step when no scale/add/lift
    // ran (a single already-exact covering row), so the derivation is never empty.
    if steps.is_empty() {
        steps.push(RefStep::Scale(cur, 1));
    }

    let cert = ObjectiveBound {
        inputs,
        steps,
        objective_terms: objective.terms.clone(),
        claimed_floor: floor,
    };
    if cert.replay_within_memory_budget() {
        cert.check_floor().ok().map(|_| cert)
    } else {
        None
    }
}

/// Cost caps for the equality-affine certificate's Gaussian elimination. Declining
/// above these is always sound (the builder just returns `None`).
const EQ_AFFINE_MAX_ROWS: usize = 4000;
const EQ_AFFINE_MAX_VARS: usize = 6000;
/// Work-proxy decline for the equality-affine certificate, measured in the ACTUAL
/// exact-rational elimination cost — mirroring `EQ_AGG_MAX_WORK_PROXY` in
/// [`crate::cdcl`], but sized for the WIDER augmented matrix carried here. Full
/// reduction eliminates each of the `n_eq` pivot rows against every other row,
/// and each step rewrites the whole augmented matrix: the `n_eq x (n+1)`
/// coefficient block AND the `n_eq x n_eq` combination-multiplier block, of
/// multiplicatively growing bignum entries. Total work is therefore
/// `O(n_eq * cells) = O(n_eq^2 * (n + n_eq))`, not `O(cells)`. The shape caps
/// (`EQ_AFFINE_MAX_ROWS`/`_VARS`) admit up to `4000^2 * (6001+4000) ~= 1.6e11`
/// — a multi-GiB, minutes-long detonator the per-poll stop can only abort AFTER
/// the matrix is committed. Declining upfront (before the `rows`/`comb`
/// allocation) is fail-closed: the floor gate is purely additive, so `None`
/// only forfeits an OPTIMUM upgrade, never a wrong answer. 1e8 matches the
/// `EQ_AGG` threshold, sheds the mult_diagcomm-class detonators, and still
/// admits the small structured circuits whose exact floor is useful.
const EQ_AFFINE_MAX_WORK_PROXY: u128 = 100_000_000;
/// Inner-loop poll cadence (in bignum operations) for the elimination /
/// comb-multiplier loops of the equality-affine certificate builder. 64 keeps
/// the poll overhead negligible against BigRational arithmetic while bounding
/// the poll-free window even when individual entries have grown to thousands
/// of limbs.
const EQ_AFFINE_INNER_POLL: usize = 64;

/// Folds single-literal linear `PbTerm`s into exact-rational net per-variable
/// coefficients plus the constant moved off the LHS, using the `~x = 1 - x`
/// convention that matches [`LinConstraint`] normalization (`from_ge`): a negated
/// literal `c*~x = c - c*x` lands `-c` on the variable and `+c` in the constant.
/// Returns `None` on any non-linear (multi-/zero-literal) term or `var == 0`.
fn fold_rational_terms(
    terms: &[PbTerm],
) -> Option<(
    BTreeMap<u32, num_rational::BigRational>,
    num_rational::BigRational,
)> {
    use num_bigint::BigInt;
    use num_rational::BigRational;
    use num_traits::Zero;

    let mut coeffs: BTreeMap<u32, BigRational> = BTreeMap::new();
    let mut lhs_const = BigRational::zero();
    for term in terms {
        let [lit] = term.lits.as_slice() else {
            return None;
        };
        if lit.var == 0 {
            return None;
        }
        let coeff = BigRational::from_integer(BigInt::from(term.coeff));
        let entry = coeffs.entry(lit.var).or_insert_with(BigRational::zero);
        if lit.negated {
            *entry -= &coeff;
            lhs_const += &coeff;
        } else {
            *entry += &coeff;
        }
    }
    Some((coeffs, lhs_const))
}

/// Builds a CHECKED cutting-planes OPTIMUM certificate for the EQUALITY-AFFINE
/// constant bound — the dual of
/// `crate::cdcl::equality_aggregation_objective_constant`, emitted as a replayable
/// derivation rather than a trusted scalar.
///
/// When the objective's linear form is an exact rational combination
/// `obj = Σ_k λ_k · L_k` of the instance's equality rows `L_k = b_k`, the
/// objective is the CONSTANT `c = c0 + Σ_k λ_k b_k` on the whole feasible set. We
/// recover the multipliers `λ_k` by Gaussian elimination (tracking the row
/// combination), clear denominators to integer `μ_k = D·λ_k`, and emit:
///
/// 1. SCALE the `>=` half of each `L_k` (when `μ_k > 0`) or its `<=` half
///    `-L_k >= -b_k` (when `μ_k < 0`) by `|μ_k|`.
/// 2. ADD all the scaled halves  → `D · obj_form >= D · (c - c0)`.
/// 3. DIVIDE (exact) by `D`  → `obj_form >= c - c0` (the normalized objective
///    floor with RHS `c`).
///
/// This certifies the multiplication-verification / bit-equality families
/// (`mult_diagcomm`) whose optimum is an affine constant of the `=` rows, with a
/// signed/weighted objective the positive-only covering and aggregation builders
/// cannot model. Self-checked before return (fail-closed on overflow / non-
/// integral constant / inexact combination).
#[must_use]
pub fn build_equality_affine_floor_cert(
    constraints: &[PbConstraint],
    objective: &PbObjective,
) -> Option<ObjectiveBound> {
    build_equality_affine_floor_cert_interruptible(constraints, objective, &|| false)
}

/// Interruptible variant of [`build_equality_affine_floor_cert`].
///
/// The dimension caps (`EQ_AFFINE_MAX_ROWS`/`EQ_AFFINE_MAX_VARS`) bound the
/// matrix SHAPE but not the cost of exact-rational elimination: on
/// equality-heavy circuit instances (e.g. the mult_diagcomm multipliers) the
/// BigRational coefficients blow up and a single elimination can run for
/// minutes with no cancellation point — stalling the solve past its deadline
/// and deaf to SIGTERM (measured: no `s` line, unkillable without SIGKILL).
/// `EQ_AFFINE_MAX_WORK_PROXY` therefore declines shapes whose `n_eq^2*(n+n_eq)`
/// elimination cost is unbounded BEFORE the dense `rows`/`comb` matrix is even
/// allocated (the build loop itself is also polled every `EQ_AFFINE_INNER_POLL`
/// rows). Within the admitted band, `should_stop` is polled per pivot column and
/// per eliminated row, AND
/// (counter-based, every [`EQ_AFFINE_INNER_POLL`] iterations) inside the
/// row-elimination / comb-multiplier inner loops themselves: with
/// multiplicatively growing bignum entries a SINGLE row combination can take
/// seconds, so per-row polling alone still overshoots the deadline and the
/// memory watermark. Declining (`None`) is fail-closed — the floor gate is
/// purely additive.
pub fn build_equality_affine_floor_cert_interruptible(
    constraints: &[PbConstraint],
    objective: &PbObjective,
    should_stop: &dyn Fn() -> bool,
) -> Option<ObjectiveBound> {
    use num_bigint::{BigInt, Sign};
    use num_rational::BigRational;
    use num_traits::{One, Zero};

    if objective.terms.is_empty() {
        return None;
    }

    // Collect equality rows: folded coeffs A_k and effective rhs b_k = rhs - const.
    // Keep the source constraint index so the derivation can reference its halves.
    let mut eq_src: Vec<usize> = Vec::new();
    let mut eq_coeffs: Vec<BTreeMap<u32, BigRational>> = Vec::new();
    let mut eq_rhs: Vec<BigRational> = Vec::new();
    for (i, c) in constraints.iter().enumerate() {
        if c.rel != PbRel::Eq {
            continue;
        }
        let (coeffs, lhs_const) = fold_rational_terms(&c.terms)?;
        let rhs_eff = BigRational::from_integer(BigInt::from(c.rhs)) - lhs_const;
        eq_src.push(i);
        eq_coeffs.push(coeffs);
        eq_rhs.push(rhs_eff);
        if eq_src.len() > EQ_AFFINE_MAX_ROWS {
            return None;
        }
    }
    let n_eq = eq_src.len();
    if n_eq == 0 {
        return None;
    }

    let (obj_coeffs, c0) = fold_rational_terms(&objective.terms)?;

    // Variable universe and dense column layout (final column = constant).
    let mut universe: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();
    universe.extend(obj_coeffs.keys().copied());
    for coeffs in &eq_coeffs {
        universe.extend(coeffs.keys().copied());
    }
    let n = universe.len();
    if n > EQ_AFFINE_MAX_VARS {
        return None;
    }

    // Actual exact-rational elimination cost over the WIDE augmented matrix
    // (coeff block `n_eq x (n+1)` + comb block `n_eq x n_eq`): each of the n_eq
    // pivot steps rewrites the whole matrix, so work is `n_eq * cells`, not
    // `cells`. Decline BEFORE the multi-GiB `rows`/`comb` allocation when it
    // exceeds the proxy (sound `None`: the floor gate is purely additive).
    let cells = (n_eq as u128).saturating_mul(n as u128 + 1 + n_eq as u128);
    let work = (n_eq as u128).saturating_mul(cells);
    if work > EQ_AFFINE_MAX_WORK_PROXY {
        return None;
    }

    let col_of: BTreeMap<u32, usize> = universe.iter().enumerate().map(|(i, v)| (*v, i)).collect();

    // Dense augmented rows: columns 0..n variables, column n = -b_k. Each row also
    // carries `comb`, its expansion as a combination of the ORIGINAL equality rows
    // (identity at start), so we can read off the multipliers after elimination.
    // The matrix build itself allocates and clones `n_eq * (n + 1 + n_eq)`
    // BigRational cells (up to the work-proxy cap above), so poll every
    // EQ_AFFINE_INNER_POLL rows to observe the deadline / memory guard DURING the
    // build, not only once the elimination starts.
    let mut rows: Vec<Vec<BigRational>> = Vec::with_capacity(n_eq);
    let mut comb: Vec<Vec<BigRational>> = Vec::with_capacity(n_eq);
    for k in 0..n_eq {
        if k % EQ_AFFINE_INNER_POLL == 0 && should_stop() {
            return None;
        }
        let mut row = vec![BigRational::zero(); n + 1];
        for (v, cc) in &eq_coeffs[k] {
            row[col_of[v]] = cc.clone();
        }
        row[n] = -eq_rhs[k].clone();
        rows.push(row);
        let mut cb = vec![BigRational::zero(); n_eq];
        cb[k] = BigRational::one();
        comb.push(cb);
    }

    // Objective homogeneous vector (column n = +c0) and its accumulated combination
    // of original rows (the λ vector we are solving for).
    let mut obj_vec = vec![BigRational::zero(); n + 1];
    for (v, cc) in &obj_coeffs {
        obj_vec[col_of[v]] = cc.clone();
    }
    obj_vec[n] = c0.clone();
    let mut lambda = vec![BigRational::zero(); n_eq];

    // Gaussian elimination (never pivot on the constant column n).
    let mut pivot_for_col: Vec<Option<usize>> = vec![None; n];
    let mut next_row = 0usize;
    for col in 0..n {
        if should_stop() {
            return None;
        }
        if next_row >= rows.len() {
            break;
        }
        let mut sel: Option<usize> = None;
        for (i, row) in rows.iter().enumerate().skip(next_row) {
            if !row[col].is_zero() {
                sel = Some(i);
                break;
            }
        }
        let Some(sel) = sel else { continue };
        rows.swap(next_row, sel);
        comb.swap(next_row, sel);
        let pivot = next_row;
        let inv = rows[pivot][col].clone();
        for x in rows[pivot].iter_mut() {
            *x /= &inv;
        }
        for x in comb[pivot].iter_mut() {
            *x /= &inv;
        }
        for i in 0..rows.len() {
            if i == pivot || rows[i][col].is_zero() {
                continue;
            }
            if should_stop() {
                return None;
            }
            let factor = rows[i][col].clone();
            for j in 0..=n {
                if j % EQ_AFFINE_INNER_POLL == 0 && should_stop() {
                    return None;
                }
                let term = &factor * &rows[pivot][j];
                rows[i][j] -= term;
            }
            for k in 0..n_eq {
                if k % EQ_AFFINE_INNER_POLL == 0 && should_stop() {
                    return None;
                }
                let term = &factor * &comb[pivot][k];
                comb[i][k] -= term;
            }
        }
        pivot_for_col[col] = Some(pivot);
        next_row += 1;
    }

    // Reduce the objective against the pivots, accumulating λ = Σ factor·comb_pivot.
    for col in 0..n {
        if should_stop() {
            return None;
        }
        let Some(pivot) = pivot_for_col[col] else {
            continue;
        };
        if obj_vec[col].is_zero() {
            continue;
        }
        let factor = obj_vec[col].clone();
        for j in 0..=n {
            if j % EQ_AFFINE_INNER_POLL == 0 && should_stop() {
                return None;
            }
            let term = &factor * &rows[pivot][j];
            obj_vec[j] -= term;
        }
        for k in 0..n_eq {
            if k % EQ_AFFINE_INNER_POLL == 0 && should_stop() {
                return None;
            }
            let term = &factor * &comb[pivot][k];
            lambda[k] += term;
        }
    }

    // Residual variable coefficients must vanish (objective in the row space).
    if obj_vec[0..n].iter().any(|c| !c.is_zero()) {
        return None;
    }
    // The constant must be integral to be a sound integer floor.
    let constant = &obj_vec[n];
    if !constant.denom().is_one() {
        return None;
    }
    let floor = i128::try_from(constant.numer().clone()).ok()?;

    // Clear denominators: D = lcm of all λ_k denominators (positive).
    let mut denom = BigInt::one();
    for l in &lambda {
        if l.is_zero() {
            continue;
        }
        let d = l.denom().clone();
        let d = if d.sign() == Sign::Minus { -d } else { d };
        denom = lcm_bigint(&denom, &d);
    }
    if denom.is_zero() {
        return None;
    }

    // Integer multipliers μ_k = D·λ_k. Skip zero multipliers.
    let mut used: Vec<(usize, i128)> = Vec::new(); // (eq index k, μ_k)
    for (k, l) in lambda.iter().enumerate() {
        if l.is_zero() {
            continue;
        }
        let scaled = l * BigRational::from_integer(denom.clone());
        if !scaled.denom().is_one() {
            return None; // not cleared (should not happen given lcm)
        }
        let mu = i128::try_from(scaled.numer().clone()).ok()?;
        if mu != 0 {
            used.push((k, mu));
        }
    }
    if used.is_empty() {
        return None;
    }
    let divisor = i128::try_from(denom).ok()?;
    if divisor < 1 {
        return None;
    }

    // Assemble the derivation: each used equality contributes the appropriate half
    // as an input; steps scale it by |μ_k|, add all, then divide by D.
    let mut inputs: Vec<LinConstraint> = Vec::with_capacity(used.len());
    for &(k, mu) in &used {
        let (ge_half, le_half) = pb_eq_halves(&constraints[eq_src[k]])?;
        // μ_k > 0 uses `L >= b`; μ_k < 0 uses `-L >= -b`.
        inputs.push(if mu > 0 { ge_half } else { le_half });
    }

    let mut steps: Vec<RefStep> = Vec::new();
    // 1. SCALE each half by |μ_k| (when >= 2).
    let mut eff: Vec<usize> = Vec::with_capacity(used.len());
    for (i, &(_, mu)) in used.iter().enumerate() {
        let mag = mu.checked_abs()?;
        if mag >= 2 {
            steps.push(RefStep::Scale(i, mag));
            eff.push(inputs.len() + steps.len() - 1);
        } else {
            eff.push(i);
        }
    }
    // 2. ADD all scaled halves.
    let mut cur = eff[0];
    for &idx in eff.iter().skip(1) {
        steps.push(RefStep::Add(cur, idx));
        cur = inputs.len() + steps.len() - 1;
    }
    // 3. DIVIDE (exact) by D (only when D >= 2; D == 1 leaves the aggregate as-is).
    if divisor >= 2 {
        steps.push(RefStep::Divide(cur, divisor));
    }
    // Materialize the aggregate as an explicit step when a single |μ|=1 half with
    // D=1 produced no scale/add/divide, so the derivation is never empty.
    if steps.is_empty() {
        steps.push(RefStep::Scale(cur, 1));
    }

    let cert = ObjectiveBound {
        inputs,
        steps,
        objective_terms: objective.terms.clone(),
        claimed_floor: floor,
    };
    if cert.replay_within_memory_budget() {
        cert.check_floor().ok().map(|_| cert)
    } else {
        None
    }
}

/// `lcm(a, b)` for positive `BigInt`s (`a, b >= 1`), via the Euclidean `gcd`.
fn lcm_bigint(a: &num_bigint::BigInt, b: &num_bigint::BigInt) -> num_bigint::BigInt {
    use num_traits::Zero;
    if a.is_zero() || b.is_zero() {
        return num_bigint::BigInt::zero();
    }
    let g = gcd_bigint(a.clone(), b.clone());
    (a / &g) * b
}

/// `gcd(a, b)` (Euclid) returning a non-negative `BigInt`.
fn gcd_bigint(mut a: num_bigint::BigInt, mut b: num_bigint::BigInt) -> num_bigint::BigInt {
    use num_bigint::Sign;
    use num_traits::Zero;
    if a.sign() == Sign::Minus {
        a = -a;
    }
    if b.sign() == Sign::Minus {
        b = -b;
    }
    while !b.is_zero() {
        let r = &a % &b;
        a = b;
        b = r;
    }
    a
}

/// Returns a CHECKED sound lower bound (floor) on the objective if one can be
/// certified by a self-checking cutting-planes certificate, or `None` otherwise.
///
/// This is the in-production OPTIMUM gate entry point: a verdict may be promoted
/// to `OPTIMUM` only when this returns a floor `>=` the (VIG-verified) incumbent
/// value. A `None` return must leave the verdict as `SATISFIABLE` (fail-closed).
///
/// Three independent self-checking certificate families are tried and the LARGER
/// certified floor is returned: the uniform-multiplier surrogate aggregation
/// ([`build_aggregation_floor_cert`]), the greedy disjoint-covering / matching /
/// disjoint-core bound ([`build_covering_floor_cert`]), and the equality-affine
/// constant bound ([`build_equality_affine_floor_cert`]). Each alone is sound; the
/// max only strengthens the certified floor (each is independently re-derived by
/// the kernel-mirrored checker).
#[must_use]
pub fn certified_objective_floor(
    constraints: &[PbConstraint],
    objective: &PbObjective,
) -> Option<i128> {
    certified_objective_floor_interruptible(constraints, objective, &|| false)
}

// Test-only instrumentation: per-thread count of
// `certified_objective_floor_interruptible` entries, so unit tests can
// assert a code path performs NO floor-certificate work (e.g. the lazy gate
// in `portfolio::sanitize_optimization_solution`) via a cheap observable
// instead of a timing-flaky elapsed check. Thread-local so concurrently
// running tests never perturb each other's counts (the callers under test
// invoke the certificate synchronously on the calling thread).
// (Regular comment: rustdoc ignores doc comments on macro invocations.)
#[cfg(test)]
thread_local! {
    pub(crate) static FLOOR_CERT_CALLS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Interruptible variant of [`certified_objective_floor`]: `should_stop` is
/// polled between builders and inside the equality-affine elimination (the
/// only builder whose exact-rational arithmetic can run away). Declining is
/// fail-closed — callers simply lose the additive OPTIMUM upgrade.
pub fn certified_objective_floor_interruptible(
    constraints: &[PbConstraint],
    objective: &PbObjective,
    should_stop: &dyn Fn() -> bool,
) -> Option<i128> {
    #[cfg(test)]
    FLOOR_CERT_CALLS.with(|calls| calls.set(calls.get() + 1));
    if should_stop() {
        return None;
    }
    let aggregation = build_aggregation_floor_cert(constraints, objective)
        .and_then(|cert| cert.check_floor().ok());
    if should_stop() {
        return None;
    }
    let covering =
        build_covering_floor_cert(constraints, objective).and_then(|cert| cert.check_floor().ok());
    let equality_affine =
        build_equality_affine_floor_cert_interruptible(constraints, objective, should_stop)
            .and_then(|cert| cert.check_floor().ok());
    [aggregation, covering, equality_affine]
        .into_iter()
        .flatten()
        .max()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::PbLit;

    #[test]
    fn checked_floor_matches_lp_and_integer_optimum() {
        let inst = crate::parse_opb(
            "* #variable= 2 #constraint= 1\n\
             min: +1 x1 +1 x2 ;\n\
             +2 x1 +2 x2 >= 3 ;\n",
        )
        .expect("parse fixture");
        let obj = inst.objective.as_ref().expect("objective");
        let cert = build_aggregation_floor_cert(&inst.constraints, obj).expect("floor certificate");
        assert_eq!(cert.check_floor(), Ok(2), "checker verdict");
        assert_eq!(cert.certify_optimum(2), Ok(2));
        assert_eq!(certified_objective_floor(&inst.constraints, obj), Some(2));
        assert_eq!(
            crate::optimize::lp_bound::lp_lower_bound(
                obj,
                &inst.constraints,
                inst.num_vars,
                &|| false,
            ),
            Some(2)
        );
        assert_eq!(brute_optimum(&inst), Some(2));
    }

    #[test]
    fn wbo_projection_round_trips_and_preserves_optimum() {
        let wbo = crate::parse_wbo(
            "soft: 10 ;\n\
             +1 x1 >= 1 ;\n\
             [5] +1 x2 >= 1 ;\n\
             [2] +1 ~x2 >= 1 ;\n",
        )
        .expect("parse WBO fixture");
        let pbo = crate::optimize::wbo::wbo_to_pbo(&wbo);
        let encoded = crate::instance_to_opb(&pbo);
        let round_trip = crate::parse_opb(&encoded).expect("parse projected OPB");
        assert_eq!(round_trip, pbo);
        assert_eq!(brute_optimum(&round_trip), Some(2));
    }

    #[test]
    fn nlc_linearization_round_trips_and_preserves_optimum() {
        let inst = crate::parse_opb(
            "* #variable= 2 #constraint= 1\n\
             min: +3 x1 x2 +1 x1 +1 x2 ;\n\
             +1 x1 +1 x2 >= 1 ;\n",
        )
        .expect("parse nonlinear fixture");
        let lin = crate::linearize::linearize(&inst);
        assert!(crate::linearize::is_linear(&lin));
        assert!(lin.num_vars > inst.num_vars);
        assert_eq!(brute_optimum(&inst), Some(1));
        assert_eq!(brute_optimum(&lin), Some(1));
        assert_eq!(
            crate::parse_opb(&crate::instance_to_opb(&lin)).expect("parse linear OPB"),
            lin
        );
    }

    fn plain(coeff: i128, var: u32) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![PbLit {
                var,
                negated: false,
            }],
        }
    }

    fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs,
        }
    }

    fn brute_optimum(instance: &crate::types::PbInstance) -> Option<i128> {
        assert!(instance.num_vars <= 20, "bounded test fixture");
        let objective = instance.objective.as_ref()?;
        let eval_terms = |terms: &[PbTerm], mask: u64| {
            terms
                .iter()
                .map(|term| {
                    let active = term.lits.iter().all(|lit| {
                        let value = mask & (1u64 << (lit.var - 1)) != 0;
                        value != lit.negated
                    });
                    if active {
                        term.coeff
                    } else {
                        0
                    }
                })
                .sum::<i128>()
        };
        (0..(1u64 << instance.num_vars))
            .filter(|&mask| {
                instance.constraints.iter().all(|constraint| {
                    let lhs = eval_terms(&constraint.terms, mask);
                    match constraint.rel {
                        PbRel::Ge => lhs >= constraint.rhs,
                        PbRel::Eq => lhs == constraint.rhs,
                    }
                })
            })
            .map(|mask| eval_terms(&objective.terms, mask))
            .min()
    }

    #[test]
    fn interruptible_floor_declines_immediately_when_stopped() {
        // Fail-closed: a tripped stop signal must decline (None), never stall.
        let constraints = vec![ge(vec![plain(2, 1), plain(2, 2)], 3)];
        let objective = PbObjective {
            terms: vec![plain(1, 1), plain(1, 2)],
        };
        assert_eq!(
            certified_objective_floor_interruptible(&constraints, &objective, &|| true),
            None
        );
        // And the uninterrupted wrapper still certifies.
        assert_eq!(certified_objective_floor(&constraints, &objective), Some(2));
    }

    /// The Lean end-to-end example: `min x + y` s.t. `2x + 2y >= 3`. The division
    /// cut `(2x+2y>=3)/2` gives the floor `x + y >= 2`; incumbent `x=y=1` has
    /// objective `2 == F` ⟹ OPTIMUM. Here the aggregation builder uses
    /// `M = cs/cv = 2/1`, `F = ceil(3/2) = 2`.
    #[test]
    fn aggregation_certifies_lean_division_example() {
        let constraints = vec![ge(vec![plain(2, 1), plain(2, 2)], 3)];
        let objective = PbObjective {
            terms: vec![plain(1, 1), plain(1, 2)],
        };
        let cert =
            build_aggregation_floor_cert(&constraints, &objective).expect("certificate builds");
        assert_eq!(cert.check_floor(), Ok(2));
        // LB == UB at the incumbent value 2 ⟹ OPTIMUM.
        assert_eq!(cert.certify_optimum(2), Ok(2));
    }

    /// A min-cover / perfect-code shape: every variable appears in exactly `k=2`
    /// rows, so `M = 2` and `F = ceil(rhs_sum / 2)`. Three triangle covers:
    /// `x1+x2>=1, x2+x3>=1, x1+x3>=1`; rhs_sum=3, colsum each =2, M=2,
    /// F=ceil(3/2)=2. Objective `min x1+x2+x3`: incumbent {x1=x2=1,x3=0} has
    /// value 2 == F ⟹ OPTIMUM (the classic edge-cover lower bound).
    #[test]
    fn aggregation_certifies_triangle_cover_optimum() {
        let constraints = vec![
            ge(vec![plain(1, 1), plain(1, 2)], 1),
            ge(vec![plain(1, 2), plain(1, 3)], 1),
            ge(vec![plain(1, 1), plain(1, 3)], 1),
        ];
        let objective = PbObjective {
            terms: vec![plain(1, 1), plain(1, 2), plain(1, 3)],
        };
        let cert =
            build_aggregation_floor_cert(&constraints, &objective).expect("certificate builds");
        assert_eq!(cert.check_floor(), Ok(2));
        assert_eq!(cert.certify_optimum(2), Ok(2));
        assert_eq!(certified_objective_floor(&constraints, &objective), Some(2));
    }

    // -------- NEGATIVE CONTROLS: an unsound/forged/loose certificate MUST be
    // rejected (fail-closed). --------

    /// FORGED OVERCOUNT: claim a floor (3) strictly higher than the derivation
    /// actually proves (2). The checker recomputes the derivation and rejects the
    /// mismatch — an overcounted lower bound can NEVER yield a wrong OPTIMUM.
    #[test]
    fn negative_control_overcounted_floor_is_rejected() {
        let constraints = vec![ge(vec![plain(2, 1), plain(2, 2)], 3)];
        let objective = PbObjective {
            terms: vec![plain(1, 1), plain(1, 2)],
        };
        let mut cert =
            build_aggregation_floor_cert(&constraints, &objective).expect("certificate builds");
        cert.claimed_floor = 3; // forged: derivation only yields 2
        assert_eq!(cert.check_floor(), Err(OptError::NotObjectiveFloor));
        assert_eq!(cert.certify_optimum(3), Err(OptError::NotObjectiveFloor));
    }

    /// WRONG OBJECTIVE FORM: a derivation that proves a bound on a DIFFERENT
    /// linear form than the objective claimed must be rejected (the bound, even if
    /// individually sound, says nothing about THIS objective).
    #[test]
    fn negative_control_wrong_objective_form_is_rejected() {
        let constraints = vec![ge(vec![plain(2, 1), plain(2, 2)], 3)];
        let objective = PbObjective {
            terms: vec![plain(1, 1), plain(1, 2)],
        };
        let mut cert =
            build_aggregation_floor_cert(&constraints, &objective).expect("certificate builds");
        // Tamper: claim the derivation bounds `x1 + x3` (different variable).
        cert.objective_terms = vec![plain(1, 1), plain(1, 3)];
        assert_eq!(cert.check_floor(), Err(OptError::NotObjectiveFloor));
    }

    /// NOT TIGHT (LB != UB): a sound floor that does not meet the incumbent is
    /// only a floor, never an OPTIMUM. Incumbent value 3 > floor 2 ⟹ `NotTight`.
    #[test]
    fn negative_control_floor_below_incumbent_is_not_optimum() {
        let constraints = vec![ge(vec![plain(2, 1), plain(2, 2)], 3)];
        let objective = PbObjective {
            terms: vec![plain(1, 1), plain(1, 2)],
        };
        let cert =
            build_aggregation_floor_cert(&constraints, &objective).expect("certificate builds");
        assert_eq!(cert.check_floor(), Ok(2));
        assert_eq!(cert.certify_optimum(3), Err(OptError::NotTight));
    }

    /// TAMPERED DERIVATION: replacing the divisor so the derived RHS no longer
    /// equals the claimed floor is rejected (a hand-built bad certificate).
    #[test]
    fn negative_control_tampered_divisor_is_rejected() {
        // inputs: [row0: 2x1+2x2>=3, ax: x1>=0, x2>=0]; steps scale by 1, divide
        // by 3 instead of 2 ⟹ ceil(3/3)=1 with coeffs ceil(2/3)=1, then lift
        // none; derived = x1+x2 >= 1, but claim floor 2 ⟹ reject.
        let row0 = pb_ge(&ge(vec![plain(2, 1), plain(2, 2)], 3)).unwrap();
        let ax1 = LinConstraint::var_geq_zero(1);
        let ax2 = LinConstraint::var_geq_zero(2);
        let cert = ObjectiveBound {
            inputs: vec![row0, ax1, ax2],
            steps: vec![RefStep::Divide(0, 3)], // ceil(2/3)=1, ceil(3/3)=1
            objective_terms: vec![plain(1, 1), plain(1, 2)],
            claimed_floor: 2, // forged: real derived floor is 1
        };
        assert_eq!(cert.check_floor(), Err(OptError::NotObjectiveFloor));
    }

    /// NON-CERTIFIABLE OBJECTIVE: a negated-literal / negative-coefficient
    /// objective (e.g. KidneyTransplant's `min -w·x`) is OUTSIDE the builder's
    /// exact-certificate slice, so it declines (`None`) — fail-closed, the verdict
    /// stays SATISFIABLE rather than an unchecked OPTIMUM.
    #[test]
    fn non_certifiable_negative_objective_declines() {
        let constraints = vec![ge(vec![plain(1, 1), plain(1, 2)], 1)];
        let objective = PbObjective {
            terms: vec![PbTerm {
                coeff: -5,
                lits: vec![PbLit {
                    var: 1,
                    negated: false,
                }],
            }],
        };
        assert!(build_aggregation_floor_cert(&constraints, &objective).is_none());
        assert_eq!(certified_objective_floor(&constraints, &objective), None);
    }

    // -------- DISJOINT-COVERING / MATCHING certificate --------

    /// Min vertex cover on a path `1-2-3-4` (edges `x1+x2>=1, x2+x3>=1,
    /// x3+x4>=1`). The greedy disjoint cover picks the matching `{(1,2),(3,4)}`
    /// (the middle edge shares spent vars), so `F = 2 = optimum`. The
    /// uniform-aggregation bound here is only `ceil(3/2) = 2` as well, but on
    /// longer even paths the matching bound is the tight one.
    #[test]
    fn covering_certifies_path_matching_optimum() {
        let constraints = vec![
            ge(vec![plain(1, 1), plain(1, 2)], 1),
            ge(vec![plain(1, 2), plain(1, 3)], 1),
            ge(vec![plain(1, 3), plain(1, 4)], 1),
        ];
        let objective = PbObjective {
            terms: vec![plain(1, 1), plain(1, 2), plain(1, 3), plain(1, 4)],
        };
        let cert =
            build_covering_floor_cert(&constraints, &objective).expect("covering cert builds");
        assert_eq!(cert.check_floor(), Ok(2));
        assert_eq!(cert.certify_optimum(2), Ok(2));
        assert_eq!(certified_objective_floor(&constraints, &objective), Some(2));
    }

    /// The covering bound is STRICTLY stronger than the uniform aggregation on a
    /// disjoint (perfect-matching) edge set: three vertex-disjoint edges
    /// `x1+x2>=1, x3+x4>=1, x5+x6>=1`. Matching bound `F = 3 = optimum`; the
    /// uniform-aggregation bound is `ceil(rhs_sum / M) = ceil(3 / 1) = 3` too
    /// (M=1 since every var has colsum 1), but the covering cert reaches it via
    /// the disjoint-sum route, and `certified_objective_floor` returns the max.
    #[test]
    fn covering_certifies_disjoint_edges_optimum() {
        let constraints = vec![
            ge(vec![plain(1, 1), plain(1, 2)], 1),
            ge(vec![plain(1, 3), plain(1, 4)], 1),
            ge(vec![plain(1, 5), plain(1, 6)], 1),
        ];
        let objective = PbObjective {
            terms: (1..=6).map(|v| plain(1, v)).collect(),
        };
        let cert =
            build_covering_floor_cert(&constraints, &objective).expect("covering cert builds");
        assert_eq!(cert.check_floor(), Ok(3));
        assert_eq!(certified_objective_floor(&constraints, &objective), Some(3));
    }

    /// A weighted cardinality row `2x1+2x2+2x3 >= 4` with multiplier: the greedy
    /// cover takes `m = floor(objc/rowcoeff)`; with unit objective `m=0` so it
    /// declines that row — exercises the multiplier guard (no overcount). With a
    /// matching unit covering row it certifies the unit bound instead.
    #[test]
    fn covering_multiplier_guard_no_overcount() {
        // Row coeff 2 but objective coeff 1 => floor(1/2)=0 => row skipped, and no
        // other row => no covering certificate (fail-closed, not an overcount).
        let constraints = vec![ge(vec![plain(2, 1), plain(2, 2)], 4)];
        let objective = PbObjective {
            terms: vec![plain(1, 1), plain(1, 2)],
        };
        assert!(build_covering_floor_cert(&constraints, &objective).is_none());
    }

    /// NEGATIVE CONTROL: forging a higher floor on a covering cert is rejected by
    /// the kernel-mirrored replay (the derivation only reaches the true matching
    /// bound).
    #[test]
    fn covering_negative_control_overcount_rejected() {
        let constraints = vec![
            ge(vec![plain(1, 1), plain(1, 2)], 1),
            ge(vec![plain(1, 3), plain(1, 4)], 1),
        ];
        let objective = PbObjective {
            terms: (1..=4).map(|v| plain(1, v)).collect(),
        };
        let mut cert =
            build_covering_floor_cert(&constraints, &objective).expect("covering cert builds");
        assert_eq!(cert.check_floor(), Ok(2));
        cert.claimed_floor = 3; // forged
        assert_eq!(cert.check_floor(), Err(OptError::NotObjectiveFloor));
    }

    // -------- EQUALITY-AFFINE constant certificate --------

    fn eq_c(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Eq,
            rhs,
        }
    }

    fn signed(coeff: i128, var: u32, negated: bool) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![PbLit { var, negated }],
        }
    }

    /// Bit-equality / multiplication-verification shape: `min (a - b)` where two
    /// equality rows force `a == b`, so the objective is the constant `0` on the
    /// whole feasible set. `x3 = x1`, `x4 = x2`; objective `x3 + 2 x4 - x1 - 2 x2`.
    /// The affine combination is `1·(x3 - x1) + 2·(x4 - x2)` => floor `0`.
    #[test]
    fn equality_affine_certifies_bit_difference_zero() {
        let constraints = vec![
            eq_c(vec![plain(1, 3), signed(-1, 1, false)], 0), // x3 - x1 = 0
            eq_c(vec![plain(1, 4), signed(-1, 2, false)], 0), // x4 - x2 = 0
        ];
        let objective = PbObjective {
            terms: vec![
                plain(1, 3),
                plain(2, 4),
                signed(-1, 1, false),
                signed(-2, 2, false),
            ],
        };
        let cert = build_equality_affine_floor_cert(&constraints, &objective)
            .expect("equality-affine cert builds");
        assert_eq!(cert.check_floor(), Ok(0));
        assert_eq!(certified_objective_floor(&constraints, &objective), Some(0));
    }

    /// Non-unit (rational λ) combination: `2 x1 = 3` is infeasible-shaped but the
    /// affine reduction still extracts a constant. Use `2 x1 + 2 x2 = 2` and a
    /// matching objective `x1 + x2`: λ = 1/2, D = 2, derivation scales+divides.
    #[test]
    fn equality_affine_handles_rational_multiplier() {
        let constraints = vec![eq_c(vec![plain(2, 1), plain(2, 2)], 2)];
        let objective = PbObjective {
            terms: vec![plain(1, 1), plain(1, 2)],
        };
        let cert = build_equality_affine_floor_cert(&constraints, &objective)
            .expect("rational-λ cert builds");
        // x1 + x2 = 1 on the feasible set => floor 1.
        assert_eq!(cert.check_floor(), Ok(1));
    }

    /// NEGATIVE: an objective NOT in the row space of the equalities declines
    /// (`None`, fail-closed) — the residual variable coefficient is nonzero.
    #[test]
    fn equality_affine_declines_when_not_in_row_space() {
        let constraints = vec![eq_c(vec![plain(1, 1), signed(-1, 2, false)], 0)];
        let objective = PbObjective {
            terms: vec![plain(1, 1), plain(1, 3)], // x3 not constrained
        };
        assert!(build_equality_affine_floor_cert(&constraints, &objective).is_none());
    }

    /// NEGATIVE: forging a higher floor on an equality-affine cert is rejected by
    /// the kernel-mirrored replay.
    #[test]
    fn equality_affine_overcount_rejected() {
        let constraints = vec![
            eq_c(vec![plain(1, 3), signed(-1, 1, false)], 0),
            eq_c(vec![plain(1, 4), signed(-1, 2, false)], 0),
        ];
        let objective = PbObjective {
            terms: vec![
                plain(1, 3),
                plain(2, 4),
                signed(-1, 1, false),
                signed(-2, 2, false),
            ],
        };
        let mut cert = build_equality_affine_floor_cert(&constraints, &objective).unwrap();
        cert.claimed_floor = 5; // forged
        assert_eq!(cert.check_floor(), Err(OptError::NotObjectiveFloor));
    }

    /// SATURATION rule round-trips through the shared replay (degree capping):
    /// `3x1 + 1x2 >= 1` saturates to `1x1 + 1x2 >= 1`. Used here to exercise the
    /// new `RefStep::Saturate` arm end-to-end via a certificate.
    #[test]
    fn saturation_step_round_trips() {
        // row: 3x1 + 3x2 >= 2; saturate -> 2x1 + 2x2 >= 2; then this is a sound
        // floor on objective 2x1 + 2x2 with F = 2.
        let row0 = pb_ge(&ge(vec![plain(3, 1), plain(3, 2)], 2)).unwrap();
        let cert = ObjectiveBound {
            inputs: vec![row0],
            steps: vec![RefStep::Saturate(0)],
            objective_terms: vec![plain(2, 1), plain(2, 2)],
            claimed_floor: 2,
        };
        assert_eq!(cert.check_floor(), Ok(2));
    }
}
