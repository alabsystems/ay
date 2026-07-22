// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Stronger primal neighborhoods: **local branching** (Fischetti & Lodi, 2003)
//! and the **feasibility pump** (Fischetti, Glover & Lodi, 2005).
//!
//! These complement the always-on RINS/RENS/relax-random LNS in
//! [`crate::optimize::lns`]. They are opt-in behind the `AY_PB_LNS2` env flag
//! (default OFF) so the default proof path is byte-for-byte unchanged unless the
//! caller deliberately enables them.
//!
//! # Local branching (incumbent IMPROVEMENT)
//! Around an incumbent x̄, add the *local-branching* row
//! `Δ(x, x̄) = Σ_{x̄_j=1}(1 − x_j) + Σ_{x̄_j=0} x_j ≤ k` (a Hamming ball of radius
//! k around x̄) PLUS an objective-cutoff row `obj ≤ best − 1`, then solve that
//! sub-problem with AY's FULL native PB-CDCL solver under a sub-budget. Unlike
//! RINS hard-fixing, this lets ANY ≤k variables flip simultaneously. On success
//! we re-center on the new incumbent and reset k; on failure within budget we
//! grow k; we loop until the deadline.
//!
//! # Feasibility pump (FIRST incumbent on no-incumbent instances)
//! Alternate LP-rounding and L1-projection: solve the LP relaxation → round the
//! fractional point to a 0/1 point x̃ → if x̃ is constraint-feasible, report it;
//! else solve an auxiliary LP minimizing L1 distance to x̃ subject to the original
//! constraints → round again. Cycle-break with a deterministic, iteration-seeded
//! perturbation (never system entropy). The first constraint-feasible 0/1 point
//! is returned as the first incumbent.
//!
//! # Soundness (NON-NEGOTIABLE)
//! 1. The local-branching and objective-cutoff rows are added ONLY to a CLONED
//!    sub-instance; they NEVER touch the main optimality-proof instance or the
//!    lower-bound path. They cannot cause a false OPTIMUM.
//! 2. Every candidate this module emits (from either technique) is re-verified
//!    against ALL ORIGINAL constraints with
//!    [`crate::eval::verify_all_constraints`] and its objective recomputed with
//!    [`crate::solver::eval_objective`] before it is reported. Local-branching
//!    additionally requires STRICT improvement over the prior best.
//! 3. Neither technique ever returns a "proven optimum" or "infeasible" verdict.
//!    A sub-problem UNSAT means only "no better point within the current Hamming
//!    ball / cutoff", never a global verdict.
//! 4. Every loop polls the stop signal and the deadline; on timeout we return the
//!    best verified incumbent (or `None`), never an overrun, never a false claim.

use crate::cdcl::{PbCdclResult, PbCdclSolver};
use crate::eval::verify_all_constraints;
use crate::objective_bound::strictly_better_than_incumbent_constraint;
use crate::optimize::lns::LnsImprovement;
use crate::solver::eval_objective;
use crate::types::{PbConstraint, PbInstance, PbLit, PbObjective, PbRel, PbTerm};

/// Whether the stronger LNS2 neighborhoods (local branching + feasibility pump)
/// are enabled. Default ON (the pump is a deadline-safe, re-verified FALLBACK that
/// fires only when there is no feasible incumbent and never emits a global
/// verdict). Disable explicitly via `AY_PB_LNS2` ∈ {0,false,no,off} to recover the
/// prior default-off behavior. Any other (or unset) value enables it.
pub(crate) fn lns2_enabled() -> bool {
    match std::env::var_os("AY_PB_LNS2").as_deref() {
        None => true,
        Some(v) => v.to_str().map_or(true, |v| {
            !matches!(
                v.trim().to_ascii_lowercase().as_str(),
                "0" | "false" | "no" | "off"
            )
        }),
    }
}

/// Upper bound on instance size for LNS2. Above this, cloning the instance and
/// re-solving per local-branching round costs too much to help within a slice.
/// `pub(crate)`: also the variable gate of the portfolio's `lp-round-sls-opt`
/// worker, which reuses [`pump_lp_point`] and must decline at the same sizes.
pub(crate) const MAX_LNS2_VARS: usize = 200_000;

/// Initial local-branching Hamming radius k (Fischetti & Lodi use a small ball,
/// typically 10-20; we start at 12 and adapt).
const LB_INITIAL_K: i128 = 12;
/// Multiplicative growth applied to k after a failed (in-budget) round, so larger
/// flips are eventually explored.
const LB_GROW_NUMERATOR: i128 = 3;
const LB_GROW_DENOMINATOR: i128 = 2;
/// Hard cap on k so the Hamming ball never degenerates into a free global solve.
const LB_MAX_K: i128 = 100_000;
/// Base conflict budget for a single local-branching sub-problem solve. Scales
/// with k (a larger ball needs more search). Keeps each round anytime.
const LB_BASE_CONFLICT_BUDGET: u64 = 50_000;
const LB_CONFLICT_PER_K: u64 = 2_000;
const LB_MAX_CONFLICT_BUDGET: u64 = 1_000_000;
/// Maximum number of local-branching rounds, independent of the deadline (so an
/// absent deadline still terminates — e.g. in tests).
const LB_MAX_ROUNDS: u64 = 100_000;
/// Consecutive failed rounds at the maximum k that trigger an early give-up when
/// no deadline is supplied. With a real deadline, the deadline dominates.
const LB_MAX_STALE_AT_MAX_K: u64 = 64;

/// Maximum feasibility-pump major iterations.
const FP_MAX_ITERATIONS: u64 = 10_000;
/// Number of consecutive identical rounded points that flags a cycle (we then
/// perturb).
const FP_CYCLE_WINDOW: usize = 3;

/// Conflict budget for a local-branching sub-problem with the given k.
fn lb_conflict_budget(k: i128) -> u64 {
    let k_u = u64::try_from(k.max(0)).unwrap_or(u64::MAX);
    LB_BASE_CONFLICT_BUDGET
        .saturating_add(k_u.saturating_mul(LB_CONFLICT_PER_K))
        .min(LB_MAX_CONFLICT_BUDGET)
}

/// Builds the local-branching Hamming-ball row for radius `k` around `incumbent`.
///
/// `Δ(x, x̄) = Σ_{x̄_j=1}(1 − x_j) + Σ_{x̄_j=0} x_j ≤ k`.
///
/// Expanding the constant `Σ_{x̄_j=1} 1 = n1` and moving to AY's only inequality
/// form (`Ge`):
///   `Σ_{x̄_j=1} x_j − Σ_{x̄_j=0} x_j ≥ n1 − k`.
/// Each variable contributes a single linear term, so this is a valid linear PB
/// row. Returns `None` only on a (practically impossible) i128 overflow.
fn local_branching_row(incumbent: &[bool], num_vars: usize, k: i128) -> Option<PbConstraint> {
    let mut terms: Vec<PbTerm> = Vec::with_capacity(num_vars);
    let mut n1: i128 = 0;
    for index in 0..num_vars {
        let var = u32::try_from(index + 1).ok()?;
        let set = incumbent.get(index).copied().unwrap_or(false);
        if set {
            n1 = n1.checked_add(1)?;
            terms.push(PbTerm {
                coeff: 1,
                lits: vec![PbLit {
                    var,
                    negated: false,
                }],
            });
        } else {
            terms.push(PbTerm {
                coeff: -1,
                lits: vec![PbLit {
                    var,
                    negated: false,
                }],
            });
        }
    }
    let rhs = n1.checked_sub(k)?;
    Some(PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs,
    })
}

/// Runs the local-branching primal-improvement loop around `incumbent` (a
/// feasible assignment of value `incumbent_cost`). Reports every adopted strict
/// improvement through `on_improve` and returns the best one, or `None`.
///
/// SOUNDNESS: the local-branching and objective-cutoff rows are added only to a
/// cloned sub-instance; every adopted candidate is re-verified against the
/// ORIGINAL constraints and must strictly improve. This function never claims a
/// global optimum. See the module docs.
pub(crate) fn improve_with_local_branching(
    instance: &PbInstance,
    objective: &PbObjective,
    incumbent: &[bool],
    incumbent_cost: i128,
    deadline: Option<std::time::Instant>,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
) -> Option<LnsImprovement> {
    let num_vars = usize::try_from(instance.num_vars).ok()?;
    if num_vars == 0 || num_vars > MAX_LNS2_VARS {
        return None;
    }
    if objective.terms.is_empty() {
        return None;
    }

    // Normalize + re-verify the starting incumbent: we only ever search a ball
    // around a known-feasible point.
    let mut best: Vec<bool> = incumbent.to_vec();
    best.resize(num_vars, false);
    if !verify_all_constraints(&instance.constraints, &best) {
        return None;
    }
    let mut best_cost = eval_objective(objective, &best).max(incumbent_cost);

    let stop = || should_stop() || deadline.is_some_and(|dl| std::time::Instant::now() >= dl);
    if stop() {
        return None;
    }

    let mut k = LB_INITIAL_K;
    let mut improved = false;
    let mut rounds = 0u64;
    let mut stale_at_max = 0u64;

    while rounds < LB_MAX_ROUNDS {
        rounds += 1;
        if stop() {
            break;
        }
        if stale_at_max >= LB_MAX_STALE_AT_MAX_K {
            break;
        }
        let at_max_k = k >= LB_MAX_K;

        match solve_local_branching_round(instance, objective, &best, best_cost, k, &stop) {
            LbRoundResult::Improved(candidate) => {
                let candidate_cost = eval_objective(objective, &candidate);
                // SOUNDNESS GATE: re-verify against ORIGINAL constraints and
                // require STRICT improvement before adopting.
                if candidate_cost < best_cost
                    && verify_all_constraints(&instance.constraints, &candidate)
                {
                    best = candidate;
                    best_cost = candidate_cost;
                    improved = true;
                    stale_at_max = 0;
                    on_improve(best_cost, &best);
                    // Re-center on the new incumbent and reset the ball radius
                    // (Fischetti & Lodi: intensify around the new center).
                    k = LB_INITIAL_K;
                } else {
                    // Verification failed or no real improvement: grow the ball.
                    k = grow_k(k);
                    if at_max_k {
                        stale_at_max += 1;
                    }
                }
            }
            LbRoundResult::NoBetter | LbRoundResult::Unknown => {
                // No strictly better point inside this ball+cutoff (or the round
                // was interrupted). Diversify by enlarging the ball.
                k = grow_k(k);
                if at_max_k {
                    stale_at_max += 1;
                }
            }
        }
    }

    if improved {
        Some(LnsImprovement {
            assignment: best,
            objective: best_cost,
        })
    } else {
        None
    }
}

/// Grows the Hamming radius k by the configured factor, clamped to `LB_MAX_K`.
fn grow_k(k: i128) -> i128 {
    let grown = k
        .saturating_mul(LB_GROW_NUMERATOR)
        .checked_div(LB_GROW_DENOMINATOR)
        .unwrap_or(LB_MAX_K);
    // Always advance by at least 1 so a tiny k still moves.
    grown.max(k + 1).min(LB_MAX_K)
}

/// Outcome of a single local-branching round.
enum LbRoundResult {
    /// A candidate (subject to the caller's re-verification) was found.
    Improved(Vec<bool>),
    /// The ball+cutoff sub-problem is UNSAT: no strictly-better point here.
    NoBetter,
    /// Interrupted / could not encode the round.
    Unknown,
}

/// Solves one local-branching round: original constraints + the Hamming-ball row
/// (radius k around the incumbent) + the objective-cutoff row (`obj ≤ best − 1`),
/// solved with the FULL native PB-CDCL solver under a conflict sub-budget.
///
/// This is strictly richer than RINS hard-fixing: NO variable is fixed by an
/// assumption — any subset of up to k variables may flip, as long as the result
/// is feasible AND strictly cheaper.
fn solve_local_branching_round(
    instance: &PbInstance,
    objective: &PbObjective,
    incumbent: &[bool],
    best_cost: i128,
    k: i128,
    should_stop: &dyn Fn() -> bool,
) -> LbRoundResult {
    let num_vars = match usize::try_from(instance.num_vars) {
        Ok(n) => n,
        Err(_) => return LbRoundResult::Unknown,
    };
    let Ok(cutoff_row) = strictly_better_than_incumbent_constraint(objective, best_cost) else {
        return LbRoundResult::Unknown;
    };
    let Some(ball_row) = local_branching_row(incumbent, num_vars, k) else {
        return LbRoundResult::Unknown;
    };

    let mut constraints: Vec<PbConstraint> = Vec::with_capacity(instance.constraints.len() + 2);
    constraints.extend_from_slice(&instance.constraints);
    constraints.push(cutoff_row);
    constraints.push(ball_row);

    let sub_instance = PbInstance {
        num_vars: instance.num_vars,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: None,
    };

    if should_stop() {
        return LbRoundResult::Unknown;
    }

    let budget = lb_conflict_budget(k);
    let mut conflicts = 0u64;
    let slice_stop = || {
        if should_stop() {
            return true;
        }
        conflicts += 1;
        conflicts > budget
    };

    let mut solver = PbCdclSolver::new_interruptible(&sub_instance, should_stop);
    match solver.solve_interruptible(slice_stop) {
        PbCdclResult::Satisfiable(model) => {
            let mut candidate = model;
            candidate.resize(num_vars, false);
            candidate.truncate(num_vars);
            LbRoundResult::Improved(candidate)
        }
        PbCdclResult::Optimal(model, _) | PbCdclResult::Feasible(model, _) => {
            let mut candidate = model;
            candidate.resize(num_vars, false);
            candidate.truncate(num_vars);
            LbRoundResult::Improved(candidate)
        }
        PbCdclResult::Unsatisfiable => LbRoundResult::NoBetter,
        PbCdclResult::Unknown => LbRoundResult::Unknown,
    }
}

// ---------------------------------------------------------------------------
// Feasibility pump
// ---------------------------------------------------------------------------

/// Deterministic SplitMix64 (Steele, Lea & Flood, 2014), seeded from the
/// instance structure and the iteration counter. Used ONLY to break feasibility
/// pump cycles by perturbing the rounding; nothing about soundness depends on it,
/// and it never reads system entropy.
struct FpRng {
    state: u64,
}

impl FpRng {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

/// Structure-only seed for the feasibility pump RNG (no instance identity / file
/// content): variable and constraint counts plus a bounded coefficient fold.
fn fp_seed(instance: &PbInstance) -> u64 {
    let mut seed: u64 = 0x51ED_C0DE_F00D_BA11;
    seed ^= u64::from(instance.num_vars).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    seed = seed.rotate_left(13);
    seed ^= (instance.constraints.len() as u64).wrapping_mul(0xC2B2_AE3D_27D4_EB4F);
    let mut acc: u64 = 0;
    for (i, c) in instance.constraints.iter().enumerate().take(4096) {
        let rhs = c.rhs.unsigned_abs();
        acc = acc
            .wrapping_mul(31)
            .wrapping_add((rhs as u64) ^ ((rhs >> 64) as u64))
            .wrapping_add(c.terms.len() as u64)
            .wrapping_add(i as u64);
    }
    seed ^= acc;
    if seed == 0 {
        seed = 0x1234_5678_9ABC_DEF0;
    }
    seed
}

/// Rounds a fractional LP point to a 0/1 assignment: value ≥ 0.5 → true.
/// `pub(crate)`: shared with the portfolio's `lp-round-sls-opt` worker.
pub(crate) fn round_point(point: &[f64], num_vars: usize) -> Vec<bool> {
    (0..num_vars)
        .map(|i| point.get(i).copied().unwrap_or(0.0) >= 0.5)
        .collect()
}

/// Builds the L1-distance objective `min Σ_j |x_j − x̃_j|` for a target rounded
/// point `target`. For a 0/1 variable: if `target_j = 0` the distance is `x_j`
/// (coeff +1 on x_j); if `target_j = 1` the distance is `1 − x_j` (coeff −1 on
/// x_j, with the constant dropped — constants do not affect the argmin). This is
/// a valid linear PB objective the LP layer can minimize.
fn l1_distance_objective(target: &[bool], num_vars: usize) -> PbObjective {
    let mut terms = Vec::with_capacity(num_vars);
    for index in 0..num_vars {
        let Ok(var) = u32::try_from(index + 1) else {
            continue;
        };
        let coeff = if target.get(index).copied().unwrap_or(false) {
            -1
        } else {
            1
        };
        terms.push(PbTerm {
            coeff,
            lits: vec![PbLit {
                var,
                negated: false,
            }],
        });
    }
    PbObjective { terms }
}

/// Result of a feasibility-pump run: a verified-feasible first incumbent and its
/// objective value, or `None`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FpIncumbent {
    pub(crate) assignment: Vec<bool>,
    pub(crate) objective: i128,
}

/// Maximum constraint count the feasibility pump will attempt. The fast f64
/// simplex (`safe_lp_bound_and_point`) handles up to 50k rows; we cap a bit below
/// that so a pathological instance cannot dominate the budget. `pub(crate)`:
/// also the row gate of the portfolio's `lp-round-sls-opt` worker.
pub(crate) const FP_MAX_CONSTRAINTS: usize = 50_000;

/// Best-effort advisory LP fractional point for the pump, for an arbitrary
/// objective over the original constraints. Prefers the FAST f64 NS simplex
/// (`safe_lp_bound_and_point`), which reaches tens of thousands of variables, and
/// falls back to the exact-rational LP (`lp_fractional_point`, capped near 5k
/// vars) when the f64 point is unavailable. The point is ADVISORY ONLY — it is
/// merely rounded; soundness comes from re-verifying the rounded 0/1 point.
/// `pub(crate)`: shared with the portfolio's `lp-round-sls-opt` worker.
pub(crate) fn pump_lp_point(
    objective: &PbObjective,
    instance: &PbInstance,
    num_vars: usize,
    should_stop: &dyn Fn() -> bool,
) -> Option<Vec<f64>> {
    let (_bound, point) = crate::optimize::safe_lp_bound::safe_lp_bound_and_point(
        objective,
        &instance.constraints,
        instance.num_vars,
        should_stop,
    );
    if let Some(p) = point {
        if p.len() == num_vars {
            return Some(p);
        }
    }
    // Fallback: exact-rational LP (smaller reach, but exact).
    let p = crate::optimize::lp_bound::lp_fractional_point(
        objective,
        &instance.constraints,
        instance.num_vars,
        should_stop,
    )?;
    if p.len() == num_vars {
        Some(p)
    } else {
        None
    }
}

/// Runs the feasibility pump to find a FIRST constraint-feasible 0/1 incumbent
/// for an instance AY otherwise leaves with no incumbent. Returns the verified
/// incumbent (and its true objective value), or `None`.
///
/// SOUNDNESS: every returned point is re-verified against ALL original
/// constraints; an unverified rounded point is never reported. The pump never
/// emits a verdict (SAT/UNSAT/OPTIMUM). The auxiliary LPs are advisory only.
pub(crate) fn feasibility_pump(
    instance: &PbInstance,
    objective: &PbObjective,
    deadline: Option<std::time::Instant>,
    should_stop: &dyn Fn() -> bool,
) -> Option<FpIncumbent> {
    let num_vars = usize::try_from(instance.num_vars).ok()?;
    if num_vars == 0 || num_vars > MAX_LNS2_VARS {
        return None;
    }
    // Row-count guard for the LP solve. The fast f64 simplex handles up to ~50k
    // rows; above that, decline rather than risk dominating the budget.
    if instance.constraints.len() > FP_MAX_CONSTRAINTS {
        return None;
    }

    let stop = || should_stop() || deadline.is_some_and(|dl| std::time::Instant::now() >= dl);
    if stop() {
        return None;
    }

    // Initial LP: minimize the TRUE objective to start from a good fractional
    // point (Fischetti-Glover-Lodi's stage-1 LP).
    let initial_point = pump_lp_point(objective, instance, num_vars, &stop)?;

    let mut rng = FpRng::new(fp_seed(instance));
    let mut current = round_point(&initial_point, num_vars);

    // If the very first rounding is already feasible, accept it immediately.
    if let Some(found) = verify_and_wrap(instance, objective, &current) {
        return Some(found);
    }

    // Track recent rounded points to detect cycles.
    let mut recent: Vec<Vec<bool>> = Vec::with_capacity(FP_CYCLE_WINDOW);

    let mut iterations = 0u64;
    while iterations < FP_MAX_ITERATIONS {
        iterations += 1;
        if stop() {
            break;
        }

        // Auxiliary LP: minimize L1 distance to the current rounded point,
        // subject to the ORIGINAL constraints. Its fractional optimum is the
        // closest LP-feasible point to x̃.
        let l1_obj = l1_distance_objective(&current, num_vars);
        let Some(lp_point) = pump_lp_point(&l1_obj, instance, num_vars, &stop) else {
            break;
        };

        let mut next = round_point(&lp_point, num_vars);

        // Feasible? Report it (after re-verification).
        if let Some(found) = verify_and_wrap(instance, objective, &next) {
            return Some(found);
        }

        // Cycle detection: if the new rounded point equals the current one (or a
        // recently-seen one), perturb deterministically to escape the cycle.
        let cycled = next == current || recent.iter().any(|p| p == &next);
        if cycled {
            perturb(&mut next, &lp_point, iterations, num_vars, &mut rng);
            // A perturbed point may itself be feasible.
            if let Some(found) = verify_and_wrap(instance, objective, &next) {
                return Some(found);
            }
        }

        // Slide the recent-window.
        recent.push(current.clone());
        if recent.len() > FP_CYCLE_WINDOW {
            recent.remove(0);
        }
        current = next;
    }

    None
}

/// Re-verifies a 0/1 point against ALL original constraints and, if feasible,
/// wraps it with its recomputed objective. Returns `None` if infeasible.
fn verify_and_wrap(
    instance: &PbInstance,
    objective: &PbObjective,
    point: &[bool],
) -> Option<FpIncumbent> {
    if verify_all_constraints(&instance.constraints, point) {
        Some(FpIncumbent {
            assignment: point.to_vec(),
            objective: eval_objective(objective, point),
        })
    } else {
        None
    }
}

/// Deterministic cycle-breaking perturbation (Fischetti-Glover-Lodi restart): flip
/// a handful of the variables whose LP value is closest to 0.5 (the most
/// "undecided"). The count and which vars are chosen are derived from the
/// iteration counter and the structure-seeded RNG — never from system entropy.
fn perturb(point: &mut [bool], lp_point: &[f64], iteration: u64, num_vars: usize, rng: &mut FpRng) {
    if num_vars == 0 {
        return;
    }
    // Number of flips grows mildly with the iteration (more aggressive escapes
    // the longer we stall), capped at a small fraction of the variables.
    let base = 1 + (iteration % 7) as usize;
    let cap = (num_vars / 10).max(1);
    let flips = base.min(cap);

    // Rank variables by closeness to 0.5 (most fractional first).
    let mut order: Vec<usize> = (0..num_vars).collect();
    order.sort_by(|&a, &b| {
        let da = (lp_point.get(a).copied().unwrap_or(0.0) - 0.5).abs();
        let db = (lp_point.get(b).copied().unwrap_or(0.0) - 0.5).abs();
        da.partial_cmp(&db).unwrap_or(std::cmp::Ordering::Equal)
    });

    // From a small candidate prefix of the most-fractional vars, flip `flips` of
    // them chosen by the RNG (deterministic).
    let prefix = (flips * 4).min(num_vars).max(flips);
    for _ in 0..flips {
        let pick = (rng.next_u64() as usize) % prefix;
        if let Some(idx) = order.get(pick) {
            if let Some(slot) = point.get_mut(*idx) {
                *slot = !*slot;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::PbRel;

    fn lit(var: u32) -> PbLit {
        PbLit {
            var,
            negated: false,
        }
    }

    fn term(coeff: i128, var: u32) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![lit(var)],
        }
    }

    fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs,
        }
    }

    fn vertex_cover_instance(num_vertices: u32, edges: &[(u32, u32)]) -> (PbInstance, PbObjective) {
        let constraints: Vec<PbConstraint> = edges
            .iter()
            .map(|&(u, v)| ge(vec![term(1, u), term(1, v)], 1))
            .collect();
        let objective = PbObjective {
            terms: (1..=num_vertices).map(|v| term(1, v)).collect(),
        };
        let instance = PbInstance {
            num_vars: num_vertices,
            num_constraints: constraints.len() as u32,
            constraints,
            objective: Some(objective.clone()),
        };
        (instance, objective)
    }

    fn no_stop() -> impl Fn() -> bool {
        || false
    }

    /// Exhaustive 0/1 search for the true optimum of a small linear instance.
    /// Returns `(optimum_value, num_feasible)`.
    fn brute_force_optimum(
        instance: &PbInstance,
        objective: &PbObjective,
    ) -> (Option<i128>, usize) {
        let n = instance.num_vars as usize;
        assert!(n <= 16, "brute force only for tiny instances");
        let mut best: Option<i128> = None;
        let mut feasible = 0usize;
        for mask in 0u32..(1u32 << n) {
            let assign: Vec<bool> = (0..n).map(|i| (mask >> i) & 1 == 1).collect();
            if verify_all_constraints(&instance.constraints, &assign) {
                feasible += 1;
                let v = eval_objective(objective, &assign);
                best = Some(best.map_or(v, |b| b.min(v)));
            }
        }
        (best, feasible)
    }

    #[test]
    fn local_branching_row_encodes_hamming_ball() {
        // Incumbent (true, false, true) with k = 1.
        // Δ = (1 - x1) + x2 + (1 - x3) ≤ 1
        //   => x1 - x2 + x3 ≥ n1 - k = 2 - 1 = 1.
        let incumbent = vec![true, false, true];
        let row = local_branching_row(&incumbent, 3, 1).expect("encodes");
        assert_eq!(row.rel, PbRel::Ge);
        assert_eq!(row.rhs, 1);
        assert_eq!(row.terms, vec![term(1, 1), term(-1, 2), term(1, 3)]);

        // Spot-check Δ values against the row: the incumbent itself has Δ = 0,
        // so x1 - x2 + x3 = 1 + 0 + 1 = 2 ≥ 1 (inside the ball, as expected).
        let inc_lhs = 1 - 0 + 1;
        assert!(inc_lhs >= row.rhs);
        // A point at Hamming distance 2 (flip x1 and x3 -> false,false,false):
        // x1 - x2 + x3 = 0 - 0 + 0 = 0 < 1, correctly OUTSIDE the radius-1 ball.
        let far_lhs = 0 - 0 + 0;
        assert!(far_lhs < row.rhs);
    }

    #[test]
    fn local_branching_improves_poor_vertex_cover() {
        // Path 1-2-3-4-5-6: optimum cover size 3, all-true start cost 6.
        let (instance, objective) =
            vertex_cover_instance(6, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 6)]);
        let incumbent = vec![true; 6];
        let incumbent_cost = eval_objective(&objective, &incumbent);
        assert_eq!(incumbent_cost, 6);

        let stop = no_stop();
        let mut on_improve = |_o: i128, _m: &[bool]| {};
        let result = improve_with_local_branching(
            &instance,
            &objective,
            &incumbent,
            incumbent_cost,
            Some(std::time::Instant::now() + std::time::Duration::from_secs(5)),
            &stop,
            &mut on_improve,
        )
        .expect("local branching should improve the trivial cover");
        assert!(verify_all_constraints(
            &instance.constraints,
            &result.assignment
        ));
        assert!(result.objective < incumbent_cost);
        // The (brute-force) optimum is 3; local branching reaches it on this tiny path.
        let (opt, _) = brute_force_optimum(&instance, &objective);
        assert_eq!(opt, Some(3));
        assert!(result.objective >= opt.unwrap());
        assert_eq!(result.objective, 3);
    }

    #[test]
    fn local_branching_never_reports_below_optimum_fuzz() {
        // Across many random small covers and starting incumbents, every reported
        // and returned incumbent MUST be feasible, strictly better than the start,
        // and never below the brute-force optimum.
        let mut rng = FpRng::new(0xABCD_1234_5678_9F00);
        for _ in 0..40 {
            let nv = 4 + (rng.next_u64() % 8) as u32; // 4..=11
            let ec = 3 + (rng.next_u64() % 10) as usize;
            let mut edges = Vec::new();
            for _ in 0..ec {
                let u = 1 + (rng.next_u64() % nv as u64) as u32;
                let mut v = 1 + (rng.next_u64() % nv as u64) as u32;
                if v == u {
                    v = 1 + (v % nv);
                }
                edges.push((u, v));
            }
            let (instance, objective) = vertex_cover_instance(nv, &edges);
            let (brute_opt, _) = brute_force_optimum(&instance, &objective);
            let brute_opt = brute_opt.expect("all-true cover is always feasible");

            let incumbent = vec![true; nv as usize];
            let incumbent_cost = eval_objective(&objective, &incumbent);

            let stop = no_stop();
            let mut violations = 0usize;
            let mut prev = incumbent_cost;
            let mut on_improve = |obj: i128, model: &[bool]| {
                if !verify_all_constraints(&instance.constraints, model) {
                    violations += 1; // infeasible incumbent reported
                }
                if obj >= prev {
                    violations += 1; // not strictly improving
                }
                if obj < brute_opt {
                    violations += 1; // below the true optimum -> catastrophic
                }
                if eval_objective(&objective, model) != obj {
                    violations += 1;
                }
                prev = obj;
            };

            let result = improve_with_local_branching(
                &instance,
                &objective,
                &incumbent,
                incumbent_cost,
                Some(std::time::Instant::now() + std::time::Duration::from_millis(150)),
                &stop,
                &mut on_improve,
            );

            assert_eq!(
                violations, 0,
                "local branching emitted an unsound incumbent"
            );

            if let Some(imp) = result {
                assert!(verify_all_constraints(
                    &instance.constraints,
                    &imp.assignment
                ));
                assert!(imp.objective < incumbent_cost);
                assert!(
                    imp.objective >= brute_opt,
                    "returned {} below brute-force optimum {}",
                    imp.objective,
                    brute_opt
                );
                assert_eq!(eval_objective(&objective, &imp.assignment), imp.objective);
            }
        }
    }

    #[test]
    fn local_branching_no_improvement_on_optimal_incumbent() {
        // Already-optimal cover {2,4,6} on the path: nothing to report.
        let (instance, objective) =
            vertex_cover_instance(6, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 6)]);
        let incumbent = vec![false, true, false, true, false, true];
        let incumbent_cost = eval_objective(&objective, &incumbent);
        assert_eq!(incumbent_cost, 3);

        let stop = no_stop();
        let mut reports = 0usize;
        let mut on_improve = |_o: i128, _m: &[bool]| reports += 1;
        let result = improve_with_local_branching(
            &instance,
            &objective,
            &incumbent,
            incumbent_cost,
            Some(std::time::Instant::now() + std::time::Duration::from_millis(500)),
            &stop,
            &mut on_improve,
        );
        assert!(result.is_none());
        assert_eq!(reports, 0);
    }

    #[test]
    fn local_branching_respects_should_stop() {
        let (instance, objective) =
            vertex_cover_instance(6, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 6)]);
        let incumbent = vec![true; 6];
        let incumbent_cost = eval_objective(&objective, &incumbent);
        let stop = || true;
        let mut called = false;
        let mut on_improve = |_o: i128, _m: &[bool]| called = true;
        let result = improve_with_local_branching(
            &instance,
            &objective,
            &incumbent,
            incumbent_cost,
            None,
            &stop,
            &mut on_improve,
        );
        assert!(result.is_none());
        assert!(!called);
    }

    #[test]
    fn local_branching_rejects_infeasible_start() {
        let objective = PbObjective {
            terms: vec![term(1, 1), term(1, 2)],
        };
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vec![ge(vec![term(1, 1), term(1, 2)], 2)],
            objective: Some(objective.clone()),
        };
        let incumbent = vec![false, false];
        let stop = no_stop();
        let mut on_improve = |_o: i128, _m: &[bool]| {};
        let result = improve_with_local_branching(
            &instance,
            &objective,
            &incumbent,
            0,
            None,
            &stop,
            &mut on_improve,
        );
        assert!(result.is_none());
    }

    #[test]
    fn feasibility_pump_finds_feasible_first_incumbent() {
        // Set-cover style: each constraint forces at least one of two vars on.
        // Optimum is 3, but we only require the pump to return ANY feasible point.
        let (instance, objective) =
            vertex_cover_instance(6, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 6)]);
        let stop = no_stop();
        let result = feasibility_pump(
            &instance,
            &objective,
            Some(std::time::Instant::now() + std::time::Duration::from_secs(5)),
            &stop,
        )
        .expect("pump should find a feasible cover");
        // SOUNDNESS: returned incumbent must be feasible and its objective correct.
        assert!(verify_all_constraints(
            &instance.constraints,
            &result.assignment
        ));
        assert_eq!(
            eval_objective(&objective, &result.assignment),
            result.objective
        );
        // Never below the true optimum.
        let (opt, _) = brute_force_optimum(&instance, &objective);
        assert!(result.objective >= opt.unwrap());
    }

    #[test]
    fn feasibility_pump_output_always_feasible_fuzz() {
        // Across random small covers, ANY incumbent the pump reports must be a
        // genuinely feasible 0/1 point with a correct objective, never below the
        // brute-force optimum.
        let mut rng = FpRng::new(0x0FACE_0FF1CE_u64);
        for _ in 0..30 {
            let nv = 4 + (rng.next_u64() % 8) as u32;
            let ec = 3 + (rng.next_u64() % 10) as usize;
            let mut edges = Vec::new();
            for _ in 0..ec {
                let u = 1 + (rng.next_u64() % nv as u64) as u32;
                let mut v = 1 + (rng.next_u64() % nv as u64) as u32;
                if v == u {
                    v = 1 + (v % nv);
                }
                edges.push((u, v));
            }
            let (instance, objective) = vertex_cover_instance(nv, &edges);
            let (brute_opt, _) = brute_force_optimum(&instance, &objective);
            let brute_opt = brute_opt.expect("always feasible");

            let stop = no_stop();
            if let Some(found) = feasibility_pump(
                &instance,
                &objective,
                Some(std::time::Instant::now() + std::time::Duration::from_millis(200)),
                &stop,
            ) {
                assert!(
                    verify_all_constraints(&instance.constraints, &found.assignment),
                    "pump returned an INFEASIBLE incumbent"
                );
                assert_eq!(
                    eval_objective(&objective, &found.assignment),
                    found.objective
                );
                assert!(
                    found.objective >= brute_opt,
                    "pump returned {} below brute-force optimum {}",
                    found.objective,
                    brute_opt
                );
            }
        }
    }

    #[test]
    fn feasibility_pump_respects_should_stop() {
        let (instance, objective) =
            vertex_cover_instance(6, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 6)]);
        let stop = || true;
        let result = feasibility_pump(&instance, &objective, None, &stop);
        assert!(result.is_none());
    }

    #[test]
    fn l1_distance_objective_signs() {
        // target = (true, false): coeff -1 on x1 (1 - x1), coeff +1 on x2 (x2).
        let obj = l1_distance_objective(&[true, false], 2);
        assert_eq!(obj.terms, vec![term(-1, 1), term(1, 2)]);
    }
}
