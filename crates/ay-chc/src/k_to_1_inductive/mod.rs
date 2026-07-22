// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! K-inductive to 1-inductive invariant conversion.
//!
//! When PDKind discovers a k-inductive invariant (k > 1), the standard
//! 1-inductive verification check may fail. This module converts k-inductive
//! invariants to 1-inductive invariants.
//!
//! ## Algorithms
//!
//! ### UNFOLD_HALVING (primary)
//!
//! Iteratively halves k by computing one binary interpolant per round:
//! split k = i + j (i >= j), interpolate between the i-unfolding and the
//! j-unfolding, conjoin the interpolant to strengthen the invariant, set k = i.
//! Converges in O(log k) interpolation calls.
//!
//! ### UNFOLD_SINGLE_QUERY (fallback)
//!
//! Uses chained binary interpolation: each step uses the previous interpolant
//! as part of the A-side, ensuring the chain property I_j ^ A_{j+1} => I_{j+1}.
//!
//! ## Reference
//!
//! - Golem: `reference/golem/src/TransitionSystem.cc:265-295` (halving)
//! - Golem: `reference/golem/src/TransitionSystem.cc:320-365` (single query)
//! - PDKind paper: "Property-Directed K-Induction" (FMCAD 2017)
//! - "Horn Clause Solvers for Program Verification", Section 4.2

use crate::interpolation::{interpolating_sat_constraints_until, InterpolatingSatResult};
use crate::smt::{SmtContext, SmtResult};
use crate::transition_system::TransitionSystem;
use crate::ChcExpr;

/// Default timeout for k-to-1 conversion interpolation queries (#3121).
/// On mod/div problems, interpolation can block indefinitely. This timeout
/// causes graceful fallback to the k-inductive invariant (sound: pdkind
/// falls back when convert returns None).
pub(crate) const DEFAULT_CONVERT_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(3);

/// Convert a k-inductive invariant to a 1-inductive invariant.
///
/// If the invariant is already 1-inductive (k <= 1), returns it unchanged.
/// Tries halving first (O(log k) interpolations), then chained single-query
/// (k interpolations) as fallback.
/// Returns `None` if all methods fail or the timeout is exceeded.
pub(crate) fn convert(k_invariant: &ChcExpr, k: usize, ts: &TransitionSystem) -> Option<ChcExpr> {
    convert_with_timeout(k_invariant, k, ts, DEFAULT_CONVERT_TIMEOUT)
}

/// Convert with an explicit wall-clock timeout.
pub(crate) fn convert_with_timeout(
    k_invariant: &ChcExpr,
    k: usize,
    ts: &TransitionSystem,
    timeout: std::time::Duration,
) -> Option<ChcExpr> {
    if k <= 1 {
        return Some(k_invariant.clone());
    }
    let deadline = ay_core::time::Instant::now() + timeout;
    // Try halving first: fewer interpolation calls, better convergence
    if let Some(result) = unfold_halving(k_invariant, k, ts, deadline) {
        return Some(result);
    }
    if ay_core::time::Instant::now() >= deadline {
        return None;
    }
    // Fall back to chained single-query interpolation
    unfold_single_query_chained(k_invariant, k, ts, deadline)
}

/// Build the unfolding formula for `n` steps of the transition system.
///
/// ```text
/// buildFormula(0, P, sys) = true
/// buildFormula(n, P, sys) = Init(x_n) ∨ (buildFormula(n-1, P, sys) ∧ P(x_{n-1}) ∧ Tr(x_{n-1}, x_n))
/// ```
///
/// Reference: Golem `TransitionSystem.cc:233-242`
fn build_formula(n: usize, invariant: &ChcExpr, ts: &TransitionSystem) -> ChcExpr {
    if n == 0 {
        return ChcExpr::Bool(true);
    }
    let previous = build_formula(n - 1, invariant, ts);
    let inv_shifted = ts.send_through_time(invariant, n - 1);
    let trans_shifted = ts.transition_at(n - 1);
    let init_shifted = ts.init_at(n);
    ChcExpr::or(
        init_shifted,
        ChcExpr::and_all([previous, inv_shifted, trans_shifted]),
    )
}

/// Halving approach: reduce k to 1 in O(log k) binary interpolation steps.
///
/// Each iteration splits k = i + j (i >= j), builds the i-unfolding and
/// j-unfolding, interpolates between them, and conjoins the interpolant
/// with the invariant to produce a stronger (i-inductive) invariant.
///
/// Reference: Golem `TransitionSystem.cc:265-295`
fn unfold_halving(
    invariant: &ChcExpr,
    mut k: usize,
    ts: &TransitionSystem,
    deadline: ay_core::time::Instant,
) -> Option<ChcExpr> {
    let mut strengthened = invariant.clone();

    while k > 1 {
        if ay_core::time::Instant::now() >= deadline {
            return None;
        }
        let j = k / 2;
        let i = k - j;

        // Build the two formula parts
        let ipart = build_formula(i, &strengthened, ts);
        let jpart = if i == j {
            ipart.clone()
        } else {
            build_formula(j, &strengthened, ts)
        };

        // Shift jpart to start at time i (all variables in jpart shift by +i)
        let shifted_jpart = ts.shift_versioned_state_vars(&jpart, i as i32);
        let neg_invariant = ChcExpr::not(ts.send_through_time(&strengthened, k));

        // Interpolate: A = ipart, B = shifted_jpart ∧ ¬Inv(x_k)
        let a_constraints = vec![ipart];
        let b_constraints = vec![shifted_jpart, neg_invariant];
        let shared_vars = ts.state_var_names_at(i);

        match interpolating_sat_constraints_until(
            &a_constraints,
            &b_constraints,
            &shared_vars,
            deadline,
        ) {
            InterpolatingSatResult::Unsat(interp) => {
                let shifted_interp = ts.shift_versioned_state_vars(&interp, -(i as i32));
                strengthened = ChcExpr::and(strengthened, shifted_interp);
                k = i;
            }
            InterpolatingSatResult::Unknown => return None,
        }
    }

    Some(strengthened)
}

/// Chained single-query approach: k binary interpolations with chain consistency.
///
/// Unlike the old independent approach, each interpolation step uses the
/// previous interpolant as part of the A-side, ensuring the chain property:
/// A_1 ^ ... ^ A_j => I_j, and I_j ^ A_{j+1} ^ ... ^ A_k ^ ¬P(x_k) is UNSAT.
fn unfold_single_query_chained(
    invariant: &ChcExpr,
    k: usize,
    ts: &TransitionSystem,
    deadline: ay_core::time::Instant,
) -> Option<ChcExpr> {
    fn build_conjunct(invariant: &ChcExpr, index: usize, ts: &TransitionSystem) -> ChcExpr {
        let inv_shifted = ts.send_through_time(invariant, index - 1);
        let trans_shifted = ts.transition_at(index - 1);
        let init_shifted = ts.init_at(index);
        ChcExpr::or(ChcExpr::and_all([inv_shifted, trans_shifted]), init_shifted)
    }

    if ay_core::time::Instant::now() >= deadline {
        return None;
    }

    // First verify the full query is UNSAT
    let mut ctx = SmtContext::new();
    let mut query_parts = Vec::with_capacity(k + 1);
    for i in 1..=k {
        query_parts.push(build_conjunct(invariant, i, ts));
    }
    query_parts.push(ChcExpr::not(ts.send_through_time(invariant, k)));

    let full_query = ChcExpr::and_all(query_parts);
    // Use timeout-bounded check_sat to prevent blocking on mod/div problems (#3121)
    let remaining = deadline.saturating_duration_since(ay_core::time::Instant::now());
    match ctx.check_sat_with_timeout(&full_query, remaining) {
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
        SmtResult::Sat(_) | SmtResult::Unknown => return None,
    }

    // Chained interpolation: each step uses previous interpolant as left context
    let mut interpolants = Vec::with_capacity(k);
    let mut left_context = ChcExpr::Bool(true); // S_0 = true

    for cut_idx in 1..=k {
        if ay_core::time::Instant::now() >= deadline {
            return None;
        }
        let current_conjunct = build_conjunct(invariant, cut_idx, ts);
        // A-side: S_{j-1} ∧ A_j (chain from previous interpolant)
        let a_constraints = vec![ChcExpr::and(left_context.clone(), current_conjunct)];

        // B-side: A_{j+1} ∧ ... ∧ A_k ∧ ¬P(x_k)
        let mut b_constraints: Vec<ChcExpr> = ((cut_idx + 1)..=k)
            .map(|i| build_conjunct(invariant, i, ts))
            .collect();
        b_constraints.push(ChcExpr::not(ts.send_through_time(invariant, k)));

        let shared_vars = ts.state_var_names_at(cut_idx);

        match interpolating_sat_constraints_until(
            &a_constraints,
            &b_constraints,
            &shared_vars,
            deadline,
        ) {
            InterpolatingSatResult::Unsat(interp) => {
                // Use this interpolant as left context for next step
                left_context = interp.clone();
                let shifted = ts.shift_versioned_state_vars(&interp, -(cut_idx as i32));
                interpolants.push(shifted);
            }
            InterpolatingSatResult::Unknown => return None,
        }
    }

    if interpolants.is_empty() {
        return None;
    }
    Some(ChcExpr::and_all(interpolants))
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
mod tests;
