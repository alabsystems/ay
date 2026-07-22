// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! General Large-Neighborhood-Search (LNS) primal-improvement worker.
//!
//! Given a feasible incumbent, LNS repeatedly re-optimizes a *neighborhood* — a
//! random subset of variables left FREE while every other variable is FIXED to
//! its incumbent value — under an objective-improvement constraint, adopting any
//! strictly better feasible solution it finds. This is the portable primal
//! strength that lifts AY off poor incumbents on weighted/optimization instances
//! (WBO / OPT / PARTIAL / SOFT), in the spirit of OR-Tools CP-SAT and SCIP LNS.
//!
//! # Neighborhoods
//! - **relax-random**: free a random subset of variables (the always-available
//!   baseline neighborhood).
//! - **RINS**: free the variables where the incumbent disagrees with the rounded
//!   LP-relaxation optimum (Danna et al., 2005). Available only when the LP
//!   fractional point could be recovered.
//! - **RENS**: free the variables that are fractional in the LP optimum (Berthold,
//!   2014). Available only when the LP fractional point could be recovered.
//!
//! The neighborhood size is **adaptive**: it shrinks after an improving move
//! (intensify) and grows after a stuck move (diversify), clamped to a structural
//! band.
//!
//! # Soundness
//! This module can only ever PROPOSE feasible incumbents; it can never claim a
//! global OPTIMUM or UNSAT. The argument:
//!
//! 1. Every candidate returned by a sub-problem solve is re-verified against ALL
//!    original constraints with [`crate::eval::verify_all_constraints`], and its
//!    objective is recomputed with [`eval_objective`]; only a strictly-better,
//!    fully-feasible candidate is adopted. An infeasible or non-improving
//!    candidate is discarded.
//! 2. The function returns at most an improved feasible assignment (and its
//!    value). It NEVER returns a "proven optimum" or "infeasible" verdict; the
//!    caller treats the result as `Satisfiable` only.
//! 3. Each sub-problem FIXES variables only to the *current incumbent's* values
//!    (a known feasible point) and merely adds an objective-improvement row, so
//!    the sub-problem can be UNSAT (no better neighbor) but never *falsely* UNSAT
//!    in a way that could be mistaken for global infeasibility — and we never
//!    interpret a sub-problem UNSAT as a global verdict.
//! 4. The PRNG is seeded deterministically from the instance *structure* (sizes
//!    and coefficient shape), never from system entropy and never from any
//!    instance identity, so runs are reproducible without any instance-specific
//!    recognition.

use crate::cdcl::{PbCdclAssumptionResult, PbCdclSolver};
use crate::eval::verify_all_constraints;
use crate::objective_bound::strictly_better_than_incumbent_constraint;
use crate::solver::eval_objective;
use crate::types::{PbConstraint, PbInstance, PbLit, PbObjective};

/// Maximum number of variables an LNS-managed instance may have. Above this the
/// per-neighborhood solves become too coarse to help within a time slice, and
/// building per-iteration sub-instances would dominate the budget; decline.
const MAX_LNS_VARS: usize = 200_000;

/// Hard cap on neighborhood iterations per call, independent of the deadline.
/// Prevents an unbounded loop if `should_stop`/deadline are both absent.
const MAX_ITERATIONS: u64 = 100_000;

/// Number of consecutive non-improving iterations *after the neighborhood has
/// already grown to its maximum size* that triggers an early give-up. This makes
/// LNS terminate promptly even when no deadline is supplied: once the largest
/// neighborhood repeatedly fails to find a better solution, further search is
/// very unlikely to help. The deadline / `should_stop` still bound everything;
/// this is the convergence cutoff that dominates only when no deadline is given
/// (e.g. unit tests). It is set high enough that, with a real time budget, the
/// deadline is the effective bound and many diverse large neighborhoods are tried
/// before giving up.
const MAX_STALE_AT_MAX_SIZE: u64 = 400;

/// Base conflict budget granted to a single sub-problem solve. The effective
/// budget scales with the number of freed variables (see
/// [`subproblem_conflict_budget`]) so larger neighborhoods get proportionally
/// more search. Small slices keep LNS anytime: many quick neighborhoods beat one
/// slow global solve.
const SUBPROBLEM_CONFLICT_BUDGET: u64 = 20_000;
/// Per-freed-variable conflict allowance added on top of the base budget, capped
/// by [`SUBPROBLEM_CONFLICT_BUDGET_MAX`]. Lets a large relaxation actually be
/// optimized rather than abandoned after a fixed small slice.
const SUBPROBLEM_CONFLICT_PER_FREE_VAR: u64 = 400;
/// Hard cap on a single sub-problem's conflict budget so one neighborhood cannot
/// monopolize the time budget.
const SUBPROBLEM_CONFLICT_BUDGET_MAX: u64 = 200_000;

/// Initial fraction of free variables in a relax-random neighborhood.
const INITIAL_FREE_FRACTION: f64 = 0.20;
/// Lower / upper clamps on the free fraction as it adapts.
const MIN_FREE_FRACTION: f64 = 0.02;
const MAX_FREE_FRACTION: f64 = 0.80;
/// Multiplicative shrink applied after an improving move (intensify).
const SHRINK_FACTOR: f64 = 0.80;
/// Multiplicative growth applied after a stuck move (diversify).
const GROW_FACTOR: f64 = 1.30;
/// Always free at least this many variables, regardless of fraction, so a
/// neighborhood is never trivially empty on small instances.
const MIN_FREE_VARS: usize = 4;

/// Outcome of an LNS run: the best feasible incumbent it produced (only ever
/// returned when strictly better than the starting incumbent), or `None` if it
/// could not improve.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LnsImprovement {
    pub(crate) assignment: Vec<bool>,
    pub(crate) objective: i128,
}

/// Which neighborhood-construction strategy a given iteration uses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Neighborhood {
    RelaxRandom,
    Rins,
    Rens,
}

/// Deterministic 64-bit PRNG (SplitMix64). Seeded from instance *structure*
/// only — never from system entropy and never from the `rand` crate — so an LNS
/// run is bit-for-bit reproducible for a given instance. This is a standard,
/// well-distributed generator (Steele, Lea & Flood, 2014) used here purely to
/// pick neighborhoods; nothing about soundness depends on its statistical
/// quality.
pub(crate) struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    pub(crate) fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    pub(crate) fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Uniformly returns a value in `0..bound` (bound > 0). Uses Lemire's
    /// multiply-shift reduction; the slight modulo bias is irrelevant for a
    /// heuristic neighborhood pick.
    pub(crate) fn below(&mut self, bound: usize) -> usize {
        if bound <= 1 {
            return 0;
        }
        let r = self.next_u64();
        ((u128::from(r) * (bound as u128)) >> 64) as usize
    }
}

/// Derives a deterministic PRNG seed from the *structure* of the instance and
/// objective: variable/constraint/term counts and a coefficient-shape mix. This
/// is intentionally structure-only (no file content, no instance name, no
/// content hash) so it cannot encode any instance-specific recognition.
pub(crate) fn structural_seed(instance: &PbInstance, objective: &PbObjective) -> u64 {
    let mut seed: u64 = 0xA5A5_5A5A_C3C3_3C3C;
    let mix = |value: u64, seed: &mut u64| {
        *seed ^= value.wrapping_add(0x9E37_79B9_7F4A_7C15);
        *seed = seed.rotate_left(17).wrapping_mul(0x2545_F491_4F6C_DD1D);
    };

    mix(u64::from(instance.num_vars), &mut seed);
    mix(instance.constraints.len() as u64, &mut seed);
    mix(objective.terms.len() as u64, &mut seed);

    // Fold a bounded coefficient-shape summary so two structurally-different
    // instances of the same size still get distinct seeds. Bounded work.
    let mut acc: u64 = 0;
    for (index, term) in objective.terms.iter().enumerate().take(4096) {
        let coeff_mag = term.coeff.unsigned_abs();
        let coeff_fold = (coeff_mag as u64) ^ ((coeff_mag >> 64) as u64);
        acc = acc
            .wrapping_mul(31)
            .wrapping_add(coeff_fold)
            .wrapping_add(term.lits.len() as u64)
            .wrapping_add(index as u64);
    }
    mix(acc, &mut seed);

    let mut crow: u64 = 0;
    for (index, constraint) in instance.constraints.iter().enumerate().take(4096) {
        let rhs_mag = constraint.rhs.unsigned_abs();
        let rhs_fold = (rhs_mag as u64) ^ ((rhs_mag >> 64) as u64);
        crow = crow
            .wrapping_mul(37)
            .wrapping_add(constraint.terms.len() as u64)
            .wrapping_add(rhs_fold)
            .wrapping_add(index as u64);
    }
    mix(crow, &mut seed);

    // Never seed with 0 (SplitMix64 still works, but a nonzero seed is tidier).
    if seed == 0 {
        seed = 0x1234_5678_9ABC_DEF0;
    }
    seed
}

/// The set of variables that actually appear in the objective (0-indexed). These
/// are the only variables whose flip can change the objective value, so they are
/// the most valuable to relax. Returns `None` if any objective variable is out
/// of range for `num_vars`.
fn objective_variable_indices(objective: &PbObjective, num_vars: usize) -> Vec<usize> {
    let mut seen = vec![false; num_vars];
    let mut out = Vec::new();
    for term in &objective.terms {
        for lit in &term.lits {
            let Some(index) = (lit.var as usize).checked_sub(1) else {
                continue;
            };
            if index < num_vars && !seen[index] {
                seen[index] = true;
                out.push(index);
            }
        }
    }
    out
}

/// Runs LNS to try to improve `incumbent` (a feasible assignment with objective
/// value `incumbent_cost`). Reports every adopted improvement through
/// `on_improve` and returns the best improvement found, or `None` if it could
/// not improve. See the module docs for the soundness argument.
///
/// `should_stop` is polled frequently; LNS stops promptly on `true`, on
/// `deadline` expiry, or after [`MAX_ITERATIONS`] neighborhoods.
pub(crate) fn improve_with_lns(
    instance: &PbInstance,
    objective: &PbObjective,
    incumbent: &[bool],
    incumbent_cost: i128,
    deadline: Option<std::time::Instant>,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
) -> Option<LnsImprovement> {
    let num_vars = usize::try_from(instance.num_vars).ok()?;
    if num_vars == 0 || num_vars > MAX_LNS_VARS {
        return None;
    }
    if objective.terms.is_empty() {
        return None;
    }

    // Normalize the incoming incumbent to the instance width and re-verify it.
    // We only ever fix to a *feasible* point, so a malformed/infeasible starting
    // incumbent must be rejected (otherwise the sub-problem could be UNSAT for a
    // reason unrelated to "no better neighbor").
    let mut best: Vec<bool> = incumbent.to_vec();
    best.resize(num_vars, false);
    if !verify_all_constraints(&instance.constraints, &best) {
        return None;
    }
    // Trust the recomputed objective over the caller's claimed value.
    let mut best_cost = eval_objective(objective, &best);
    if best_cost > incumbent_cost {
        // Caller's incumbent evaluates worse than claimed; still proceed from the
        // true value (we never adopt anything not strictly better than this).
        best_cost = best_cost.max(incumbent_cost);
    }

    // Fail-closed on the process-memory guard: each LNS round builds a
    // sub-instance and sub-solver, and on dense instances the accumulated
    // relaxation/solve footprint can run past MEMLIMIT while the caller's stop
    // is only deadline/term. Declining (returning the best incumbent) is sound.
    //
    // This `stop` is threaded through `solve_neighborhood` into the sub-solver's
    // per-decision search loop, so its memory component MUST stay off the
    // syscall path: it uses the syscall-free live-heap signal
    // (`live_bytes_exceeded_at_percent`, a single relaxed atomic load). The full
    // footprint/RSS poll (`process_memory_exceeded`, a `task_info`/`getrusage`
    // syscall) is applied only at the one-time entry and the per-round loop
    // top (see below) — O(rounds), never per decision. The sub-solver's own
    // construction/optimize loops additionally run the full poll internally, so
    // the footprint backstop is not lost.
    let stop = || {
        should_stop()
            || deadline.is_some_and(|dl| std::time::Instant::now() >= dl)
            || ay_sys::live_bytes_exceeded_at_percent(95)
    };
    if stop() || ay_sys::process_memory_exceeded() {
        return None;
    }

    let obj_vars = objective_variable_indices(objective, num_vars);
    if obj_vars.is_empty() {
        return None;
    }
    // The relaxation universe is ALL variables, not just objective variables. On
    // WBO-derived instances the objective is over relaxation/selector variables,
    // and reducing the objective requires changing the ORIGINAL problem variables
    // those selectors depend on. Freeing only objective variables would fix every
    // original variable to the incumbent and make every sub-problem trivially
    // UNSAT (no cheaper neighbor), so we relax across the whole variable space.
    // Objective variables are still given selection preference via RINS/RENS and a
    // guaranteed share in relax-random.
    let all_vars: Vec<usize> = (0..num_vars).collect();

    // Advisory LP fractional point for RINS/RENS. Best-effort: a `None` simply
    // disables those neighborhoods (relax-random always remains available).
    let lp_point = if instance.constraints.len() <= 4096 {
        crate::optimize::lp_bound::lp_fractional_point(
            objective,
            &instance.constraints,
            instance.num_vars,
            &stop,
        )
    } else {
        None
    };
    let lp_available = lp_point.as_ref().is_some_and(|p| p.len() == num_vars);

    let mut rng = SplitMix64::new(structural_seed(instance, objective));
    let mut free_fraction = INITIAL_FREE_FRACTION;
    let mut improved = false;

    let mut free_flags = vec![false; num_vars];
    let mut iterations = 0u64;
    // Consecutive non-improving iterations while the neighborhood is already at
    // its maximum size. Used as a convergence cutoff so LNS terminates promptly
    // even without a deadline once the largest neighborhood stops helping.
    let mut stale_at_max = 0u64;

    while iterations < MAX_ITERATIONS {
        iterations += 1;
        // Per-round cadence (O(rounds), off the per-decision hot path): the
        // cheap `stop()` plus the full footprint/RSS syscall backstop.
        if stop() || ay_sys::process_memory_exceeded() {
            break;
        }
        if stale_at_max >= MAX_STALE_AT_MAX_SIZE {
            break;
        }

        let neighborhood = pick_neighborhood(&mut rng, lp_available);
        let target_free = free_count(free_fraction, all_vars.len());
        let at_max_size = free_fraction >= MAX_FREE_FRACTION - f64::EPSILON;

        select_free_variables(
            &mut free_flags,
            neighborhood,
            &all_vars,
            &obj_vars,
            &best,
            lp_point.as_deref(),
            target_free,
            &mut rng,
        );

        // A neighborhood that frees nothing cannot improve; grow and retry.
        if !free_flags.iter().any(|&f| f) {
            free_fraction = (free_fraction * GROW_FACTOR).min(MAX_FREE_FRACTION);
            if at_max_size {
                stale_at_max += 1;
            }
            continue;
        }

        match solve_neighborhood(instance, objective, &best, best_cost, &free_flags, &stop) {
            NeighborhoodResult::Improved(candidate) => {
                let candidate_cost = eval_objective(objective, &candidate);
                // SOUNDNESS GATE: re-verify feasibility and strict improvement
                // against the ORIGINAL constraints before adopting.
                if candidate_cost < best_cost
                    && verify_all_constraints(&instance.constraints, &candidate)
                {
                    best = candidate;
                    best_cost = candidate_cost;
                    improved = true;
                    stale_at_max = 0;
                    on_improve(best_cost, &best);
                    // Intensify around the new, better incumbent.
                    free_fraction = (free_fraction * SHRINK_FACTOR).max(MIN_FREE_FRACTION);
                } else {
                    // Verification failed or no real improvement: treat as stuck.
                    free_fraction = (free_fraction * GROW_FACTOR).min(MAX_FREE_FRACTION);
                    if at_max_size {
                        stale_at_max += 1;
                    }
                }
            }
            NeighborhoodResult::NoImprovement | NeighborhoodResult::Unknown => {
                // No better neighbor in this region: diversify by enlarging the
                // next neighborhood. A NoImprovement at the maximum size means
                // the whole-incumbent neighborhood has no better solution under
                // the time slice; count it toward the convergence cutoff.
                free_fraction = (free_fraction * GROW_FACTOR).min(MAX_FREE_FRACTION);
                if at_max_size {
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

/// Chooses a neighborhood strategy for this iteration. RINS/RENS are only
/// eligible when an LP fractional point is available; otherwise relax-random.
fn pick_neighborhood(rng: &mut SplitMix64, lp_available: bool) -> Neighborhood {
    if !lp_available {
        return Neighborhood::RelaxRandom;
    }
    match rng.below(3) {
        0 => Neighborhood::Rins,
        1 => Neighborhood::Rens,
        _ => Neighborhood::RelaxRandom,
    }
}

/// Number of variables to free this iteration, from the adaptive fraction.
fn free_count(free_fraction: f64, candidate_count: usize) -> usize {
    let raw = (free_fraction * candidate_count as f64).round() as usize;
    raw.clamp(MIN_FREE_VARS.min(candidate_count), candidate_count)
}

/// Populates `free_flags` (length `num_vars`) marking which variables are FREE
/// this iteration. Every variable not flagged free is FIXED to its incumbent
/// value by the caller.
///
/// The relaxation universe is `all_vars` (the whole variable space), because on
/// WBO-derived instances reducing the objective requires changing original
/// problem variables, not just the objective/selector variables. `obj_vars` is
/// used only to GUARANTEE that some objective variables are freed in every
/// relax-random neighborhood (so the objective can actually change), and as the
/// RINS/RENS preference set when the LP point is unavailable.
fn select_free_variables(
    free_flags: &mut [bool],
    neighborhood: Neighborhood,
    all_vars: &[usize],
    obj_vars: &[usize],
    incumbent: &[bool],
    lp_point: Option<&[f64]>,
    target_free: usize,
    rng: &mut SplitMix64,
) {
    for flag in free_flags.iter_mut() {
        *flag = false;
    }
    if all_vars.is_empty() {
        return;
    }

    match neighborhood {
        Neighborhood::Rins => {
            // Free variables where the incumbent disagrees with the rounded LP
            // optimum. These are the "contested" variables most likely to be
            // flippable toward the LP optimum. Considered over ALL variables.
            if let Some(lp) = lp_point {
                let mut disagree: Vec<usize> = all_vars
                    .iter()
                    .copied()
                    .filter(|&v| {
                        let lp_round = lp.get(v).copied().unwrap_or(0.0) >= 0.5;
                        let inc = incumbent.get(v).copied().unwrap_or(false);
                        lp_round != inc
                    })
                    .collect();
                if disagree.is_empty() {
                    relax_random(free_flags, all_vars, obj_vars, target_free, rng);
                } else {
                    cap_and_mark(free_flags, &mut disagree, target_free, rng);
                }
            } else {
                relax_random(free_flags, all_vars, obj_vars, target_free, rng);
            }
        }
        Neighborhood::Rens => {
            // Free variables that are fractional in the LP optimum. Over ALL vars.
            if let Some(lp) = lp_point {
                let mut fractional: Vec<usize> = all_vars
                    .iter()
                    .copied()
                    .filter(|&v| {
                        let value = lp.get(v).copied().unwrap_or(0.0);
                        value > 1e-6 && value < 1.0 - 1e-6
                    })
                    .collect();
                if fractional.is_empty() {
                    relax_random(free_flags, all_vars, obj_vars, target_free, rng);
                } else {
                    cap_and_mark(free_flags, &mut fractional, target_free, rng);
                }
            } else {
                relax_random(free_flags, all_vars, obj_vars, target_free, rng);
            }
        }
        Neighborhood::RelaxRandom => {
            relax_random(free_flags, all_vars, obj_vars, target_free, rng);
        }
    }
}

/// Relax-random over the whole variable space, but guaranteeing that at least a
/// share of objective variables are freed so the objective can change. Roughly
/// half of `target_free` is drawn from objective variables (when available) and
/// the rest from all variables; both draws are uniform random subsets.
fn relax_random(
    free_flags: &mut [bool],
    all_vars: &[usize],
    obj_vars: &[usize],
    target_free: usize,
    rng: &mut SplitMix64,
) {
    if !obj_vars.is_empty() {
        let obj_share = (target_free / 2).clamp(1, obj_vars.len());
        let mut obj_pool: Vec<usize> = obj_vars.to_vec();
        cap_and_mark(free_flags, &mut obj_pool, obj_share, rng);
    }
    // Fill the remainder from the whole variable space (overlap with already-freed
    // objective vars is fine; cap_and_mark just re-marks them and we still reach
    // roughly target_free distinct freed variables on average).
    let mut all_pool: Vec<usize> = all_vars.to_vec();
    cap_and_mark(free_flags, &mut all_pool, target_free, rng);
}

/// Partial Fisher-Yates: shuffles the first `min(target_free, pool.len())`
/// elements of `pool` to the front and marks them free in `free_flags`.
fn cap_and_mark(
    free_flags: &mut [bool],
    pool: &mut [usize],
    target_free: usize,
    rng: &mut SplitMix64,
) {
    let take = target_free.min(pool.len());
    for i in 0..take {
        let j = i + rng.below(pool.len() - i);
        pool.swap(i, j);
        if let Some(flag) = free_flags.get_mut(pool[i]) {
            *flag = true;
        }
    }
}

/// Result of solving one neighborhood sub-problem.
enum NeighborhoodResult {
    /// A candidate assignment was found (still subject to the caller's soundness
    /// re-verification before adoption).
    Improved(Vec<bool>),
    /// The sub-problem is UNSAT: no strictly-better neighbor exists in this
    /// region. NOT a global verdict.
    NoImprovement,
    /// Interrupted / unsupported sub-problem.
    Unknown,
}

/// Conflict budget for a sub-problem that frees `free_count` variables: a base
/// budget plus a per-freed-variable allowance, capped. Larger relaxations get
/// proportionally more search so they can be solved rather than abandoned.
fn subproblem_conflict_budget(free_count: usize) -> u64 {
    let scaled = (free_count as u64).saturating_mul(SUBPROBLEM_CONFLICT_PER_FREE_VAR);
    SUBPROBLEM_CONFLICT_BUDGET
        .saturating_add(scaled)
        .min(SUBPROBLEM_CONFLICT_BUDGET_MAX)
}

/// Builds and solves the sub-problem for the current neighborhood: original
/// constraints + an objective-improvement row (`objective <= best_cost - 1`),
/// with every NON-free variable fixed to its incumbent value via assumptions.
///
/// Fixing only to incumbent values means the incumbent itself satisfies every
/// assumption; the only thing that can make the sub-problem UNSAT is the
/// objective-improvement row (i.e. genuinely no better neighbor here), which is
/// exactly the signal we want and never a false global infeasibility.
fn solve_neighborhood(
    instance: &PbInstance,
    objective: &PbObjective,
    incumbent: &[bool],
    best_cost: i128,
    free_flags: &[bool],
    should_stop: &dyn Fn() -> bool,
) -> NeighborhoodResult {
    // Objective-improvement row: `objective <= best_cost - 1`. If it can't be
    // encoded (overflow), there is nothing useful to do.
    let Ok(improve_row) = strictly_better_than_incumbent_constraint(objective, best_cost) else {
        return NeighborhoodResult::Unknown;
    };

    let mut constraints: Vec<PbConstraint> = Vec::with_capacity(instance.constraints.len() + 1);
    constraints.extend_from_slice(&instance.constraints);
    constraints.push(improve_row);

    let sub_instance = PbInstance {
        num_vars: instance.num_vars,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: None,
    };

    // Assumptions: fix every non-free variable to its incumbent value.
    let mut assumptions: Vec<PbLit> = Vec::new();
    for (index, &free) in free_flags.iter().enumerate() {
        if free {
            continue;
        }
        let Ok(var) = u32::try_from(index + 1) else {
            continue;
        };
        let value = incumbent.get(index).copied().unwrap_or(false);
        assumptions.push(PbLit {
            var,
            // To FIX x = true we assume the positive literal; to FIX x = false we
            // assume the negated literal (so that the literal is forced true).
            negated: !value,
        });
    }

    let free_count = free_flags.iter().filter(|&&f| f).count();
    let budget = subproblem_conflict_budget(free_count);

    let mut conflicts = 0u64;
    let mut solver = PbCdclSolver::new_interruptible(&sub_instance, should_stop);
    if should_stop() {
        return NeighborhoodResult::Unknown;
    }

    // Per-neighborhood time/conflict slice on top of the global stop. The budget
    // scales with the neighborhood size so a large relaxation is actually given
    // enough search to be optimized rather than abandoned.
    let slice_stop = || {
        if should_stop() {
            return true;
        }
        conflicts += 1;
        conflicts > budget
    };

    match solver.solve_with_assumptions_interruptible(&assumptions, slice_stop) {
        PbCdclAssumptionResult::Satisfiable(model) => {
            let mut candidate = model;
            let target = usize::try_from(instance.num_vars).unwrap_or(candidate.len());
            candidate.resize(target, false);
            candidate.truncate(target);
            NeighborhoodResult::Improved(candidate)
        }
        PbCdclAssumptionResult::Unsatisfiable { .. } => NeighborhoodResult::NoImprovement,
        PbCdclAssumptionResult::Unknown | PbCdclAssumptionResult::Unsupported => {
            NeighborhoodResult::Unknown
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{PbRel, PbTerm};

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

    /// Build a minimum vertex-cover instance over a path/graph: for each edge
    /// (u, v) we require `x_u + x_v >= 1`; the objective minimizes the number of
    /// chosen vertices (`sum x_i`). The trivial "all-true" cover is feasible but
    /// far from optimal.
    fn vertex_cover_instance(num_vertices: u32, edges: &[(u32, u32)]) -> (PbInstance, PbObjective) {
        let constraints: Vec<PbConstraint> = edges
            .iter()
            .map(|&(u, v)| ge(vec![term(1, lit(u)), term(1, lit(v))], 1))
            .collect();
        let objective = PbObjective {
            terms: (1..=num_vertices).map(|v| term(1, lit(v))).collect(),
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

    #[test]
    fn splitmix64_is_deterministic() {
        let mut a = SplitMix64::new(12345);
        let mut b = SplitMix64::new(12345);
        for _ in 0..1000 {
            assert_eq!(a.next_u64(), b.next_u64());
        }
    }

    #[test]
    fn splitmix64_below_in_range() {
        let mut rng = SplitMix64::new(999);
        for bound in 1..50usize {
            for _ in 0..200 {
                assert!(rng.below(bound) < bound);
            }
        }
    }

    #[test]
    fn structural_seed_is_stable_for_same_structure() {
        let (instance, objective) = vertex_cover_instance(4, &[(1, 2), (2, 3), (3, 4)]);
        let s1 = structural_seed(&instance, &objective);
        let s2 = structural_seed(&instance, &objective);
        assert_eq!(s1, s2);
        assert_ne!(s1, 0);
    }

    #[test]
    fn structural_seed_differs_for_different_structure() {
        let (a_instance, a_objective) = vertex_cover_instance(4, &[(1, 2), (2, 3), (3, 4)]);
        let (b_instance, b_objective) = vertex_cover_instance(5, &[(1, 2), (2, 3), (3, 4), (4, 5)]);
        assert_ne!(
            structural_seed(&a_instance, &a_objective),
            structural_seed(&b_instance, &b_objective)
        );
    }

    #[test]
    fn lns_improves_poor_vertex_cover_incumbent() {
        // Path 1-2-3-4-5-6 (edges between consecutive vertices). Optimum cover is
        // {2, 4, 6} (or {1,3,5}) of size 3. The trivial all-true incumbent has
        // cost 6; LNS should drive it down toward 3.
        let (instance, objective) =
            vertex_cover_instance(6, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 6)]);
        let incumbent = vec![true; 6];
        let incumbent_cost = eval_objective(&objective, &incumbent);
        assert_eq!(incumbent_cost, 6);

        let stop = no_stop();
        let mut reported = Vec::new();
        let mut on_improve = |obj: i128, _model: &[bool]| reported.push(obj);
        let result = improve_with_lns(
            &instance,
            &objective,
            &incumbent,
            incumbent_cost,
            None,
            &stop,
            &mut on_improve,
        );

        let improvement = result.expect("LNS should improve the trivial cover");
        // Re-verify the returned incumbent is genuinely feasible.
        assert!(verify_all_constraints(
            &instance.constraints,
            &improvement.assignment
        ));
        assert_eq!(
            eval_objective(&objective, &improvement.assignment),
            improvement.objective
        );
        // Strictly better than the start, and at the known optimum of 3 (LNS on
        // this tiny path readily reaches it).
        assert!(improvement.objective < incumbent_cost);
        assert_eq!(improvement.objective, 3);
        // Every reported value must be a real improvement on the previous best.
        for window in reported.windows(2) {
            assert!(window[1] < window[0]);
        }
    }

    #[test]
    fn lns_improves_star_vertex_cover() {
        // Star: center 1 connected to leaves 2..=8. Optimum cover is {1} (size 1)
        // since covering all edges only needs the center. All-true cost is 8.
        let edges: Vec<(u32, u32)> = (2..=8).map(|leaf| (1, leaf)).collect();
        let (instance, objective) = vertex_cover_instance(8, &edges);
        let incumbent = vec![true; 8];
        let incumbent_cost = eval_objective(&objective, &incumbent);
        assert_eq!(incumbent_cost, 8);

        let stop = no_stop();
        let mut on_improve = |_obj: i128, _model: &[bool]| {};
        let result = improve_with_lns(
            &instance,
            &objective,
            &incumbent,
            incumbent_cost,
            None,
            &stop,
            &mut on_improve,
        )
        .expect("LNS should improve the star cover");

        assert!(verify_all_constraints(
            &instance.constraints,
            &result.assignment
        ));
        assert!(result.objective < incumbent_cost);
        assert_eq!(result.objective, 1);
    }

    #[test]
    fn lns_never_reports_infeasible_incumbent_fuzz() {
        // Fuzz: across many pseudo-random vertex-cover instances and starting
        // incumbents, EVERY improvement LNS reports (both via on_improve and the
        // returned value) must be feasible against all original constraints and
        // strictly better than the start. LNS must never emit an infeasible or
        // non-improving "improvement".
        let mut rng = SplitMix64::new(0xDEAD_BEEF_CAFE_F00D);

        for _ in 0..40 {
            let num_vertices = 4 + rng.below(9) as u32; // 4..=12
            let edge_count = 3 + rng.below(12); // a handful of edges
            let mut edges = Vec::new();
            for _ in 0..edge_count {
                let u = 1 + rng.below(num_vertices as usize) as u32;
                let mut v = 1 + rng.below(num_vertices as usize) as u32;
                if v == u {
                    v = 1 + (v % num_vertices);
                }
                edges.push((u, v));
            }
            let (instance, objective) = vertex_cover_instance(num_vertices, &edges);

            // Start from the trivial all-true cover (always feasible for these
            // covering constraints).
            let incumbent = vec![true; num_vertices as usize];
            let incumbent_cost = eval_objective(&objective, &incumbent);

            let stop = no_stop();
            let mut violations = 0usize;
            let mut prev = incumbent_cost;
            let mut on_improve = |obj: i128, model: &[bool]| {
                if !verify_all_constraints(&instance.constraints, model) {
                    violations += 1;
                }
                if obj >= prev {
                    violations += 1;
                }
                if eval_objective(&objective, model) != obj {
                    violations += 1;
                }
                prev = obj;
            };

            let result = improve_with_lns(
                &instance,
                &objective,
                &incumbent,
                incumbent_cost,
                // Bound each fuzz instance so the whole test stays fast; the
                // soundness invariant we check holds regardless of how long LNS
                // runs.
                Some(std::time::Instant::now() + std::time::Duration::from_millis(150)),
                &stop,
                &mut on_improve,
            );

            assert_eq!(
                violations, 0,
                "LNS reported an infeasible/non-improving incumbent"
            );

            if let Some(improvement) = result {
                assert!(
                    verify_all_constraints(&instance.constraints, &improvement.assignment),
                    "returned LNS incumbent must be feasible"
                );
                assert!(
                    improvement.objective < incumbent_cost,
                    "returned LNS incumbent must strictly improve"
                );
                assert_eq!(
                    eval_objective(&objective, &improvement.assignment),
                    improvement.objective
                );
            }
        }
    }

    #[test]
    fn lns_respects_should_stop() {
        let (instance, objective) =
            vertex_cover_instance(6, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 6)]);
        let incumbent = vec![true; 6];
        let incumbent_cost = eval_objective(&objective, &incumbent);

        // should_stop is always true: LNS must return immediately with no
        // improvement and never adopt anything.
        let stop = || true;
        let mut called = false;
        let mut on_improve = |_obj: i128, _model: &[bool]| called = true;
        let result = improve_with_lns(
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
    fn lns_rejects_infeasible_starting_incumbent() {
        // Constraint x1 + x2 >= 2 cannot be satisfied by an all-false start.
        let objective = PbObjective {
            terms: vec![term(1, lit(1)), term(1, lit(2))],
        };
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vec![ge(vec![term(1, lit(1)), term(1, lit(2))], 2)],
            objective: Some(objective.clone()),
        };
        let incumbent = vec![false, false]; // infeasible
        let stop = no_stop();
        let mut on_improve = |_obj: i128, _model: &[bool]| {};
        let result = improve_with_lns(
            &instance,
            &objective,
            &incumbent,
            0,
            None,
            &stop,
            &mut on_improve,
        );
        // Must refuse to operate from an infeasible point.
        assert!(result.is_none());
    }

    #[test]
    fn lns_improves_wbo_style_relaxation_objective() {
        // WBO-style structure: the objective is over RELAXATION/selector variables,
        // and the only way to reduce it is to change ORIGINAL problem variables
        // (exactly the WBO-to-PBO shape). This is the case that fails if LNS only
        // frees objective variables: with the originals fixed, the relaxation
        // variables cannot be turned off. The all-variables relaxation must handle
        // it.
        //
        // Originals: x1, x2. Relaxations: r1 (var 3), r2 (var 4).
        //   Soft "x1 is true": x1 + r1 >= 1   (pay r1=1 if x1 is false)
        //   Soft "x2 is true": x2 + r2 >= 1   (pay r2=1 if x2 is false)
        //   Hard: x1 + x2 >= 1                (at least one original true)
        //   Objective: min r1 + r2
        //
        // Optimal: set x1 = x2 = true, r1 = r2 = 0 -> objective 0. A poor incumbent
        // sets x1=false (paying r1), x2=true: objective 1. LNS must free x1 (an
        // ORIGINAL variable) to flip it true and drop r1 to 0.
        let constraints = vec![
            ge(vec![term(1, lit(1)), term(1, lit(3))], 1), // x1 + r1 >= 1
            ge(vec![term(1, lit(2)), term(1, lit(4))], 1), // x2 + r2 >= 1
            ge(vec![term(1, lit(1)), term(1, lit(2))], 1), // x1 + x2 >= 1
        ];
        let objective = PbObjective {
            terms: vec![term(1, lit(3)), term(1, lit(4))], // min r1 + r2
        };
        let instance = PbInstance {
            num_vars: 4,
            num_constraints: constraints.len() as u32,
            constraints,
            objective: Some(objective.clone()),
        };
        // Poor incumbent: x1=false, x2=true, r1=true (paid), r2=false. Feasible,
        // objective = 1.
        let incumbent = vec![false, true, true, false];
        let incumbent_cost = eval_objective(&objective, &incumbent);
        assert_eq!(incumbent_cost, 1);
        assert!(verify_all_constraints(&instance.constraints, &incumbent));

        let stop = no_stop();
        let mut on_improve = |_obj: i128, _model: &[bool]| {};
        let result = improve_with_lns(
            &instance,
            &objective,
            &incumbent,
            incumbent_cost,
            None,
            &stop,
            &mut on_improve,
        )
        .expect("LNS must escape the relaxation-only local optimum by freeing originals");
        assert!(verify_all_constraints(
            &instance.constraints,
            &result.assignment
        ));
        assert_eq!(
            result.objective, 0,
            "optimum is 0 (turn off both relaxations)"
        );
    }

    #[test]
    fn lns_no_improvement_on_optimal_incumbent() {
        // Already-optimal cover {2, 4, 6} on the 1-2-3-4-5-6 path: LNS cannot
        // improve and must return None without reporting anything.
        let (instance, objective) =
            vertex_cover_instance(6, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 6)]);
        // {2,4,6} (indices 1,3,5) -> cost 3, optimal.
        let incumbent = vec![false, true, false, true, false, true];
        let incumbent_cost = eval_objective(&objective, &incumbent);
        assert_eq!(incumbent_cost, 3);
        assert!(verify_all_constraints(&instance.constraints, &incumbent));

        let stop = no_stop();
        let mut reports = 0usize;
        let mut on_improve = |_obj: i128, _model: &[bool]| reports += 1;
        let result = improve_with_lns(
            &instance,
            &objective,
            &incumbent,
            incumbent_cost,
            // Bound the search so the test is quick even though it can't improve.
            Some(std::time::Instant::now() + std::time::Duration::from_millis(500)),
            &stop,
            &mut on_improve,
        );
        assert!(result.is_none());
        assert_eq!(reports, 0);
    }

    #[test]
    fn lns_uses_weighted_objective() {
        // Weighted vertex cover: vertex 1 is very expensive (weight 100), the
        // rest cheap (weight 1). Path edges 1-2, 2-3, 3-4. Starting all-true cost
        // is 100 + 3 = 103; the cheap optimum avoids vertex 1: cover {2, 4} ...
        // but edge (1,2) needs 1 or 2, edge (3,4) needs 3 or 4. {2,3} covers
        // (1,2),(2,3),(3,4) -> cost 2. LNS should drop vertex 1.
        let constraints = vec![
            ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
            ge(vec![term(1, lit(2)), term(1, lit(3))], 1),
            ge(vec![term(1, lit(3)), term(1, lit(4))], 1),
        ];
        let objective = PbObjective {
            terms: vec![
                term(100, lit(1)),
                term(1, lit(2)),
                term(1, lit(3)),
                term(1, lit(4)),
            ],
        };
        let instance = PbInstance {
            num_vars: 4,
            num_constraints: constraints.len() as u32,
            constraints,
            objective: Some(objective.clone()),
        };
        let incumbent = vec![true; 4];
        let incumbent_cost = eval_objective(&objective, &incumbent);
        assert_eq!(incumbent_cost, 103);

        let stop = no_stop();
        let mut on_improve = |_obj: i128, _model: &[bool]| {};
        let result = improve_with_lns(
            &instance,
            &objective,
            &incumbent,
            incumbent_cost,
            None,
            &stop,
            &mut on_improve,
        )
        .expect("LNS should drop the expensive vertex");
        assert!(verify_all_constraints(
            &instance.constraints,
            &result.assignment
        ));
        // The expensive vertex 1 must be dropped (cost falls well below 100).
        assert!(result.objective < 100);
        assert!(!result.assignment[0]);
    }

    #[test]
    fn objective_variable_indices_dedups_and_bounds() {
        let objective = PbObjective {
            terms: vec![term(1, lit(1)), term(1, lit(1)), term(1, neg(3))],
        };
        let indices = objective_variable_indices(&objective, 5);
        assert_eq!(indices, vec![0, 2]);
    }
}
