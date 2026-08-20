// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fixed-cardinality violation descent for UNICOST COVERING optimization
//! instances (NuMVC / RWLS shaped) — the primal move that
//! [`crate::optimize::sls`] structurally cannot make.
//!
//! # Why this exists
//! `sls.rs` minimizes a PENALTY BLEND of objective and violation, so a
//! feasible point of value `k+1` and an infeasible point of value `k` are
//! COMPARABLE and the search wanders between them. On unicost covering
//! families (dominating set, set cover, vertex cover) the last unit of the
//! objective is exactly where that blend stalls. This module inverts the
//! decomposition:
//!
//! * the cardinality `|S|` is HELD FIXED at `k = best_known - 1` and the
//!   objective is not in the cost function at all;
//! * the only move is a remove+add SWAP, so `|S| = k` is invariant
//!   ([`state::Descent::swap_step`]);
//! * the cost is total row violation, with DYNAMIC ROW WEIGHTS bumped on the
//!   rows that stay violated (the RWLS plateau escape), so the landscape tilts
//!   away from the plateau instead of flattening on it;
//! * reaching violation zero yields a feasible solution of size `k`; record
//!   it, set `k <- k-1`, and repeat.
//!
//! Shrinking `k` always goes through [`state::Descent::set_selection`], which
//! RE-DERIVES the whole violation structure from scratch — patching it in
//! place silently corrupts the search.
//!
//! # Applicability (the gate — [`cover::build_cover_view`])
//! The instance must be a UNICOST COVERING program:
//! 1. every constraint is linear (one literal per term) and `>=`;
//! 2. after normalizing each row to `sum_v c_v x_v >= d` (expanding `~x` as
//!    `1 - x`), every `c_v >= 0` — i.e. every row is MONOTONE NON-DECREASING
//!    in the selection. This is what makes "search at exactly `|S| = k`"
//!    lossless: a feasible set of size `< k` extends to a feasible set of
//!    size `k`;
//! 3. the objective is `min c * sum_{v in V} x_v` for ONE positive `c` shared
//!    by every term, each term a distinct non-negated variable, and every
//!    variable occurring in a (non-trivial) row is one of them — so the
//!    objective value is exactly `c * |S|` and shrinking `|S|` is exactly
//!    shrinking the objective.
//!
//! Anything else — an `=` row, a negative normalized coefficient, mixed
//! objective weights, a variable constrained but unpriced — DECLINES (returns
//! `None`, does nothing, costs one O(nonzeros) pass). A negative coefficient
//! rejects EVEN when the row's rhs normalizes to `d <= 0`: an at-most-one or
//! implication row is not trivially true, and dropping it would leave the
//! advisory view a strict relaxation whose candidates only die later in
//! `record` (see `cover::collect_normalized`). Only rows that are monotone
//! AND have `d <= 0` are trivially true and dropped; a row whose coefficients
//! cannot reach its own rhs makes the instance infeasible, which this
//! heuristic cannot help with, so it declines too.
//!
//! # Soundness (NON-NEGOTIABLE, identical posture to [`crate::optimize::sls`])
//! This module can only ever PROPOSE feasible incumbents; it can NEVER claim a
//! global OPTIMUM or UNSAT. The normalized `CoverView` is ADVISORY: it steers
//! the search and nothing else. Every candidate is re-verified here against
//! ALL ORIGINAL constraints with [`verify_all_constraints`] and its objective
//! recomputed with [`eval_objective`] before `on_improve` is called, and the
//! caller re-verifies independently through `sanitize_optimization_incumbent`.
//! A normalization bug can therefore only lose a solution, never emit a wrong
//! one. The PRNG is seeded from instance STRUCTURE only, so runs are
//! bit-for-bit reproducible.

use crate::eval::verify_all_constraints;
use crate::optimize::lns::structural_seed;
use crate::solver::eval_objective;
use crate::types::{PbInstance, PbObjective};

mod cover;
mod state;
#[cfg(test)]
mod tests;

use cover::build_cover_view;
use state::Descent;

/// How often (in swaps) the deadline / stop signal is polled.
const STOP_POLL_INTERVAL: u64 = 1024;

/// Swaps without a new best total shortfall at the current `k` after which the
/// search re-seeds from the incumbent minus a random member.
const STALL_LIMIT: u64 = 400_000;

/// Hard cap on swaps per call, independent of the deadline, so an absent
/// deadline still terminates (mirrors `sls::MAX_FLIPS`). Without it the
/// descent would spin forever at the first `k` it cannot reach — which is the
/// NORMAL end state, since the last `k` tried is by definition the one that
/// does not close.
const MAX_SWAPS: u64 = 2_000_000_000;

/// Seed diversifier so this arm's trajectory differs from every `sls` arm's on
/// the same instance. Arbitrary fixed nonzero constant.
const CARD_DESCENT_SEED_XOR: u64 = 0x5CA1_AB1E_5EED_000E;

/// Runs the fixed-cardinality descent, streaming every strictly-improving
/// VERIFIED feasible incumbent through `on_improve` — assignment included, so
/// the caller never has to reconstruct one.
///
/// Returns the EXACT objective of the best feasible point found (recomputed by
/// [`eval_objective`], never inferred from `|S|`), or `None` when the instance
/// is outside the applicability gate or nothing feasible was reached.
pub(crate) fn search(
    instance: &PbInstance,
    objective: &PbObjective,
    deadline: Option<std::time::Instant>,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
) -> Option<i128> {
    search_with_budget(
        instance,
        objective,
        deadline,
        should_stop,
        on_improve,
        MAX_SWAPS,
    )
}

/// As [`search`], but with an explicit swap budget. Tests use a small budget
/// so the loop runs fully deterministically with no wall-clock deadline.
pub(crate) fn search_with_budget(
    instance: &PbInstance,
    objective: &PbObjective,
    deadline: Option<std::time::Instant>,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
    max_swaps: u64,
) -> Option<i128> {
    let view = build_cover_view(instance, objective)?;
    let stop = || should_stop() || deadline.is_some_and(|dl| std::time::Instant::now() >= dl);
    if stop() {
        return None;
    }
    let seed = structural_seed(instance, objective) ^ CARD_DESCENT_SEED_XOR;
    let mut descent = Descent::new(&view, seed);
    if !descent.greedy_complete(&stop) {
        return None;
    }

    let mut best: Option<i128> = None;
    let mut incumbent: Vec<u32> = descent.selection().to_vec();
    if !record(instance, objective, &incumbent, &mut best, on_improve) {
        return None;
    }
    // `incumbent.len() == 1` would shrink to the EMPTY set, which is infeasible
    // by construction (every kept row has `rhs > 0` and `lhs(empty) == 0`), so
    // stop rather than spin on a swap-less state.
    let mut budget = max_swaps;
    while incumbent.len() > 1 && budget > 0 && !stop() {
        descent.set_selection(&incumbent);
        let Some(drop_at) = least_damaging(&descent) else {
            break;
        };
        let mut shrunk = incumbent.clone();
        shrunk.swap_remove(drop_at);
        // Re-derive the WHOLE violation structure for the smaller set.
        descent.set_selection(&shrunk);
        if !descend_to_feasible(&mut descent, &incumbent, &stop, &mut budget) {
            break;
        }
        incumbent = descent.selection().to_vec();
        if !record(instance, objective, &incumbent, &mut best, on_improve) {
            break;
        }
    }
    best
}

/// Index in `descent.selection()` of the member whose removal costs least.
fn least_damaging(descent: &Descent<'_>) -> Option<usize> {
    descent
        .selection()
        .iter()
        .enumerate()
        .map(|(index, var)| (index, descent.remove_cost(*var)))
        .min_by_key(|(_, cost)| *cost)
        .map(|(index, _)| index)
}

/// Swaps at fixed `|S|` until nothing is violated. On stalling, re-seeds from
/// `anchor` minus a RANDOM member (a fresh size-`k` start, again re-derived
/// from scratch). Returns false when the budget ran out first.
fn descend_to_feasible(
    descent: &mut Descent<'_>,
    anchor: &[u32],
    stop: &dyn Fn() -> bool,
    budget: &mut u64,
) -> bool {
    let mut best_shortfall = i64::MAX;
    let mut stall: u64 = 0;
    let mut polled: u64 = 0;
    while !descent.is_feasible() {
        if *budget == 0 {
            return false;
        }
        *budget -= 1;
        descent.swap_step();
        polled += 1;
        if polled.is_multiple_of(STOP_POLL_INTERVAL) && stop() {
            return false;
        }
        if descent.total_shortfall < best_shortfall {
            best_shortfall = descent.total_shortfall;
            stall = 0;
        } else {
            stall += 1;
        }
        if stall >= STALL_LIMIT {
            let mut restart = anchor.to_vec();
            let victim = descent.rng.below(restart.len());
            restart.swap_remove(victim);
            descent.set_selection(&restart);
            best_shortfall = i64::MAX;
            stall = 0;
        }
    }
    true
}

/// SOUNDNESS GATE: re-verifies a candidate selection against ALL ORIGINAL
/// constraints and recomputes its objective exactly before reporting it.
/// Returns false only when the candidate fails verification — which would mean
/// the advisory view is wrong, so the caller stops using it (fail-closed).
fn record(
    instance: &PbInstance,
    objective: &PbObjective,
    selection: &[u32],
    best: &mut Option<i128>,
    on_improve: &mut dyn FnMut(i128, &[bool]),
) -> bool {
    let num_vars = usize::try_from(instance.num_vars).unwrap_or(0);
    let mut assignment = vec![false; num_vars];
    for &var in selection {
        if let Some(slot) = assignment.get_mut(var as usize) {
            *slot = true;
        }
    }
    if !verify_all_constraints(&instance.constraints, &assignment) {
        return false;
    }
    let value = eval_objective(objective, &assignment);
    if best.is_none_or(|found| value < found) {
        on_improve(value, &assignment);
        *best = Some(value);
    }
    true
}
