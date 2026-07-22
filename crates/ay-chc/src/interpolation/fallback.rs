// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fallback interpolation strategies: disjunction-split and UNSAT-core.

use crate::engine_utils::check_sat_with_timeout;
use crate::interpolant_validation::is_valid_interpolant_with_check_sat;
use crate::smt::{SmtContext, SmtResult};
use crate::{ChcExpr, ChcOp};
use ay_core::kani_compat::DetHashSet as FxHashSet;
use ay_core::time::Instant;
use tracing::{debug, info};

use super::{
    deadline_expired, debug_assert_shared_var_locality, interpolating_sat_constraints_with_budget,
    timeout_for_deadline, InterpolatingSatResult,
};

/// Disjunction case-splitting for interpolation.
///
/// Flattens the A-side conjunction into disjunctive normal form (one level deep):
/// if any A-constraint is `A1 ∨ A2 ∨ ...`, distributes the other constraints
/// across the disjuncts and recursively interpolates each branch.
///
/// Returns `Some(Unsat(I1 ∨ ... ∨ In))` if all branches succeed,
/// `Some(Unknown)` if the A-side has no disjunctions, or `None` to signal
/// no disjunctions were found and the caller should return Unknown.
pub(super) fn interpolate_with_disjunction_split(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
    branch_budget: &mut usize,
    deadline: Option<Instant>,
) -> Option<InterpolatingSatResult> {
    if deadline_expired(deadline) {
        return Some(InterpolatingSatResult::Unknown);
    }

    // First, flatten any top-level AND in A-constraints into individual conjuncts.
    // This handles the case where a caller passes [And(ctx, Or(A1, A2))] —
    // we need to see the OR to split on it.
    let mut flat_a: Vec<ChcExpr> = Vec::with_capacity(a_constraints.len());
    for c in a_constraints {
        c.collect_conjuncts_nontrivial_into(&mut flat_a);
    }

    // Find the first flattened A-constraint that is a disjunction
    let Some((disj_idx, disjuncts)) = flat_a.iter().enumerate().find_map(|(i, c)| {
        if let ChcExpr::Op(ChcOp::Or, args) = c {
            Some((i, args.clone()))
        } else {
            None
        }
    }) else {
        debug!(
            event = "chc_interpolation_disjunction_skip",
            reason = "no_top_level_disjunction",
            "Disjunction-split fallback not applicable",
        );
        return None;
    };

    // Check branch budget before expanding disjuncts.
    // Each disjunct becomes a separate recursive interpolation call, and nested
    // disjunctions multiply: k disjuncts at n levels produces k^n branches.
    debug!(
        event = "chc_interpolation_disjunction_expand",
        disjunct_count = disjuncts.len(),
        branch_budget_before = *branch_budget,
        "Expanding disjunction branches",
    );
    if disjuncts.len() > *branch_budget {
        info!(
            event = "chc_interpolation_disjunction_budget_exhausted",
            disjunct_count = disjuncts.len(),
            branch_budget = *branch_budget,
            "Disjunction-split branch budget exhausted",
        );
        return Some(InterpolatingSatResult::Unknown);
    }
    *branch_budget -= disjuncts.len();

    // Collect the non-disjunctive A-constraints
    let other_a: Vec<ChcExpr> = flat_a
        .iter()
        .enumerate()
        .filter(|(i, _)| *i != disj_idx)
        .map(|(_, c)| c.clone())
        .collect();

    // For each disjunct, build a conjunctive A-side: other_a ∧ disjunct_i
    // Then recursively interpolate with the shared branch budget
    let mut branch_interpolants = Vec::with_capacity(disjuncts.len());
    for (branch_idx, disjunct) in disjuncts.iter().enumerate() {
        if deadline_expired(deadline) {
            return Some(InterpolatingSatResult::Unknown);
        }
        let mut branch_a: Vec<ChcExpr> = other_a.clone();
        // Flatten the disjunct if it's a conjunction
        disjunct.collect_conjuncts_nontrivial_into(&mut branch_a);

        debug!(
            event = "chc_interpolation_disjunction_branch_try",
            branch_index = branch_idx,
            branch_constraints = branch_a.len(),
            branch_budget_remaining = *branch_budget,
            "Trying interpolation on disjunction branch",
        );
        match interpolating_sat_constraints_with_budget(
            &branch_a,
            b_constraints,
            shared_vars,
            branch_budget,
            deadline,
        ) {
            InterpolatingSatResult::Unsat(interp) => {
                debug!(
                    event = "chc_interpolation_disjunction_branch_succeeded",
                    branch_index = branch_idx,
                    "Disjunction branch interpolation succeeded",
                );
                branch_interpolants.push(interp);
            }
            InterpolatingSatResult::Unknown => {
                // If any branch fails, we can't form a complete disjunctive interpolant
                info!(
                    event = "chc_interpolation_disjunction_branch_failed",
                    branch_index = branch_idx,
                    reason = "recursive_unknown",
                    "Disjunction branch interpolation failed",
                );
                return Some(InterpolatingSatResult::Unknown);
            }
        }
    }

    // Combine branch interpolants: I = I1 ∨ I2 ∨ ... ∨ In
    let combined = ChcExpr::or_all(branch_interpolants);

    // Validate the combined interpolant against the original (unflattened) A-constraints.
    // This is correct by construction, but the check catches implementation bugs.
    if is_valid_interpolant_until(
        a_constraints,
        b_constraints,
        &combined,
        shared_vars,
        deadline,
    ) {
        debug_assert_shared_var_locality(&combined, shared_vars, "disjunction_split_combined");
        debug!(
            event = "chc_interpolation_disjunction_combined_succeeded",
            branch_count = disjuncts.len(),
            "Combined disjunction interpolant passed validation",
        );
        Some(InterpolatingSatResult::Unsat(combined))
    } else {
        info!(
            event = "chc_interpolation_disjunction_combined_failed",
            branch_count = disjuncts.len(),
            reason = "craig_validation_failed",
            "Combined disjunction interpolant failed validation",
        );
        Some(InterpolatingSatResult::Unknown)
    }
}

/// UNSAT-core-based interpolation fallback.
///
/// When heuristic methods (Farkas, bound, transitivity) cannot find an interpolant,
/// use the SMT solver to check A ∧ B, extract an UNSAT core, and build an
/// interpolant from the A-side core conjuncts that mention only shared variables.
///
/// This produces a valid (though possibly weak) interpolant:
/// - A ⊨ I (I is a subset of A's conjuncts)
/// - I ∧ B is UNSAT (the core guarantees this)
/// - I mentions only shared variables (by construction — we filter)
///
/// The interpolant may be weaker than a proof-based Craig interpolant because:
/// 1. We can only use A-side core conjuncts with shared-variable-only mentions
/// 2. A-side core conjuncts with private variables are dropped
///
/// However, this is strictly better than the trivial fallback `not(formula)`.
pub(super) fn compute_unsat_core_interpolant_until(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
    deadline: Option<Instant>,
) -> Option<ChcExpr> {
    if deadline_expired(deadline) {
        return None;
    }

    debug!(
        event = "chc_interpolation_unsat_core_start",
        a_constraints = a_constraints.len(),
        b_constraints = b_constraints.len(),
        shared_vars = shared_vars.len(),
        "Starting UNSAT-core interpolation fallback",
    );

    // Build labeled conjunction: each A constraint gets a unique label.
    // We need to identify which core conjuncts came from A vs B.
    let a_set: FxHashSet<String> = a_constraints.iter().map(|c| format!("{c:?}")).collect();

    let all_constraints: Vec<ChcExpr> = a_constraints
        .iter()
        .chain(b_constraints.iter())
        .cloned()
        .collect();

    let full = ChcExpr::and_all(all_constraints);

    let mut smt = SmtContext::new();
    let result = if deadline.is_some() {
        let timeout = timeout_for_deadline(deadline, std::time::Duration::from_secs(2))?;
        smt.check_sat_with_timeout(&full, timeout)
    } else {
        smt.check_sat(&full)
    };

    let core_conjuncts = match result {
        SmtResult::UnsatWithCore(core) => {
            debug!(
                event = "chc_interpolation_unsat_core_extracted",
                core_conjuncts = core.conjuncts.len(),
                "SMT returned UNSAT core for interpolation fallback",
            );
            core.conjuncts
        }
        SmtResult::Unsat | SmtResult::UnsatWithFarkas(_) => {
            // UNSAT but no core extracted — fall back to using all A constraints
            info!(
                event = "chc_interpolation_unsat_core_missing",
                reason = "unsat_without_core",
                fallback_a_constraints = a_constraints.len(),
                "SMT returned UNSAT without a core; falling back to full A-side constraints",
            );
            a_constraints.to_vec()
        }
        SmtResult::Sat(_) => {
            info!(
                event = "chc_interpolation_unsat_core_failed",
                reason = "sat",
                "UNSAT-core interpolation fallback aborted: A ∧ B is SAT",
            );
            return None;
        }
        SmtResult::Unknown => {
            info!(
                event = "chc_interpolation_unsat_core_failed",
                reason = "unknown",
                "UNSAT-core interpolation fallback aborted: SMT solver returned Unknown",
            );
            return None;
        }
    };

    // Partition core conjuncts: keep only A-side conjuncts with shared-only vars.
    let mut a_core_shared: Vec<ChcExpr> = Vec::new();
    for conjunct in &core_conjuncts {
        let repr = format!("{conjunct:?}");
        if !a_set.contains(&repr) {
            continue; // B-side conjunct, skip
        }
        let vars: FxHashSet<String> = conjunct.vars().into_iter().map(|v| v.name).collect();
        if vars.iter().all(|v| shared_vars.contains(v)) {
            a_core_shared.push(conjunct.clone());
        }
    }

    if a_core_shared.is_empty() {
        // No A-side core conjuncts with only shared variables.
        // Try a weaker approach: use ALL A constraints with shared-only vars.
        debug!(
            event = "chc_interpolation_unsat_core_shared_filter_empty",
            "No shared-only A-side conjuncts in UNSAT core; retrying with full A-side scan",
        );
        for c in a_constraints {
            let vars: FxHashSet<String> = c.vars().into_iter().map(|v| v.name).collect();
            if vars.iter().all(|v| shared_vars.contains(v)) {
                a_core_shared.push(c.clone());
            }
        }
    }

    if a_core_shared.is_empty() {
        info!(
            event = "chc_interpolation_unsat_core_failed",
            reason = "no_shared_a_constraints",
            "UNSAT-core interpolation fallback found no shared-only A constraints",
        );
        return None;
    }

    let shared_a_conjuncts = a_core_shared.len();
    let candidate = if shared_a_conjuncts == 1 {
        a_core_shared.pop().expect("len == 1")
    } else {
        ChcExpr::and_all(a_core_shared)
    };

    // Validate the candidate interpolant before returning.
    if is_valid_interpolant_until(
        a_constraints,
        b_constraints,
        &candidate,
        shared_vars,
        deadline,
    ) {
        debug_assert_shared_var_locality(&candidate, shared_vars, "unsat_core");
        debug!(
            event = "chc_interpolation_unsat_core_succeeded",
            shared_a_conjuncts, "UNSAT-core interpolation fallback produced a valid candidate",
        );
        Some(candidate)
    } else {
        info!(
            event = "chc_interpolation_unsat_core_failed",
            reason = "craig_validation_failed",
            "UNSAT-core interpolation candidate failed Craig validation",
        );
        None
    }
}

#[cfg(test)]
pub(super) fn is_valid_interpolant(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    interpolant: &ChcExpr,
    shared_vars: &FxHashSet<String>,
) -> bool {
    is_valid_interpolant_until(a_constraints, b_constraints, interpolant, shared_vars, None)
}

/// Diagnose WHICH Craig validation leg a candidate fails (rank-4 inc-5
/// attribution; debug-side only — never used to accept a candidate).
///
/// Returns one of "locality", "a_implies_i", "i_and_b", "valid", or
/// "unknown_timeout" when a leg could not be decided before the deadline.
pub(super) fn diagnose_interpolant_failure(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    interpolant: &ChcExpr,
    shared_vars: &FxHashSet<String>,
    deadline: Option<Instant>,
) -> &'static str {
    let interpolant_vars: FxHashSet<String> = crate::expr_vars::expr_var_names(interpolant);
    if !interpolant_vars.iter().all(|v| shared_vars.contains(v)) {
        return "locality";
    }
    let per_check = std::time::Duration::from_secs(2);
    let check = |query: &ChcExpr| -> SmtResult {
        match timeout_for_deadline(deadline, per_check) {
            Some(t) => check_sat_with_timeout(query, t),
            None => SmtResult::Unknown,
        }
    };
    let a_conj = ChcExpr::and_all(a_constraints.to_vec());
    let a_and_not_i = ChcExpr::and(a_conj, ChcExpr::not(interpolant.clone()));
    match check(&a_and_not_i) {
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
        SmtResult::Unknown => return "unknown_timeout",
        _ => return "a_implies_i",
    }
    let b_conj = ChcExpr::and_all(b_constraints.to_vec());
    let i_and_b = ChcExpr::and(interpolant.clone(), b_conj);
    match check(&i_and_b) {
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => "valid",
        SmtResult::Unknown => "unknown_timeout",
        _ => "i_and_b",
    }
}

pub(super) fn is_valid_interpolant_until(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    interpolant: &ChcExpr,
    shared_vars: &FxHashSet<String>,
    deadline: Option<Instant>,
) -> bool {
    let a_conj = ChcExpr::and_all(a_constraints.to_vec());
    let b_conj = ChcExpr::and_all(b_constraints.to_vec());
    // Use a 2s timeout for validation checks to prevent hangs in reachability
    // loops where interpolation is called repeatedly (#4823).
    let timeout = std::time::Duration::from_secs(2);
    is_valid_interpolant_with_check_sat(&a_conj, &b_conj, interpolant, shared_vars, |query| {
        if deadline.is_some() {
            let Some(timeout) = timeout_for_deadline(deadline, timeout) else {
                return SmtResult::Unknown;
            };
            check_sat_with_timeout(query, timeout)
        } else {
            check_sat_with_timeout(query, timeout)
        }
    })
}
