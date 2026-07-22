// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Dual MBP interpolation for mixed Bool+LIA formulas.
//!
//! When A(x,y) ∧ B(y,z) is UNSAT, computes I(y) = ¬(∃z. B(y,z)) via
//! AllSAT+MBP enumeration on the B-partition. This handles mixed Bool+LIA
//! natively because MBP works with models rather than syntactic structure.
//!
//! Theory: Given A ∧ B UNSAT with shared variables y:
//!   I(y) = ¬(∃z. B(y,z))
//!   - A → I: From A∧B UNSAT, A(x,y) → ∀z.¬B(y,z) = I(y)
//!   - I ∧ B UNSAT: If B(y,z) holds, ∃z.B true, so I false
//!
//! The AllSAT+MBP approximation may be incomplete (not all B models covered),
//! so we validate I ∧ B is UNSAT before returning.
//!
//! Reference: same algorithmic pattern as `singleloop_safe.rs:226-261`
//! (alien-variable elimination via AllSAT+MBP).

use crate::mbp::Mbp;
use crate::smt::{SmtContext, SmtResult};
use crate::{ChcExpr, ChcVar};
use ay_core::kani_compat::DetHashSet as FxHashSet;
use ay_core::time::Instant;
use std::time::Duration;
use tracing::{debug, info, warn};

use super::{deadline_expired, timeout_for_deadline};

/// Maximum AllSAT iterations. Same order as alien-var elimination (50).
/// Each iteration involves one SMT call + one MBP projection.
const MAX_ALLSAT_ITERS: usize = 100;

/// Per-model cap for bounded AllSAT enumeration. Callers with a wall-clock
/// deadline should make forward progress to later fallback strategies instead
/// of spending the entire budget on one model query.
const ALLSAT_QUERY_TIMEOUT: Duration = Duration::from_millis(500);

/// Timeout for the final I ∧ B validation check.
const VALIDATION_TIMEOUT: Duration = Duration::from_secs(2);

/// Compute a dual MBP interpolant for A ∧ B UNSAT.
///
/// Returns `Some(I)` where I mentions only `shared_vars`, or `None` if the
/// budget is exhausted or the candidate fails validation.
#[cfg(test)]
pub(crate) fn compute_dual_mbp_interpolant(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
) -> Option<ChcExpr> {
    compute_dual_mbp_interpolant_until(a_constraints, b_constraints, shared_vars, None)
}

pub(crate) fn compute_dual_mbp_interpolant_until(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
    deadline: Option<Instant>,
) -> Option<ChcExpr> {
    if deadline_expired(deadline) {
        return None;
    }

    let b_formula = ChcExpr::and_all(b_constraints.iter().cloned());

    // Collect shared vars as ChcVar for MBP keep_only
    let all_b_vars = b_formula.vars();
    let shared_var_list: Vec<ChcVar> = all_b_vars
        .iter()
        .filter(|v| shared_vars.contains(&v.name))
        .cloned()
        .collect();

    if shared_var_list.is_empty() {
        debug!(
            event = "chc_dual_mbp_skip",
            reason = "no_shared_vars_in_b",
            b_vars = all_b_vars.len(),
        );
        return None;
    }

    let mbp = Mbp::new();
    let mut smt = SmtContext::new();
    let mut projections: Vec<ChcExpr> = Vec::new();
    let mut blocking = b_formula.clone();

    let mut hit_cap = false;
    for iter in 0..MAX_ALLSAT_ITERS {
        if deadline_expired(deadline) {
            return None;
        }

        let query_result = if deadline.is_some() {
            let timeout = timeout_for_deadline(deadline, ALLSAT_QUERY_TIMEOUT)?;
            smt.check_sat_with_timeout(&blocking, timeout)
        } else {
            smt.check_sat(&blocking)
        };

        match query_result {
            SmtResult::Sat(model) => {
                let projection = mbp.keep_only(&b_formula, &shared_var_list, &model);
                debug!(
                    event = "chc_dual_mbp_allsat_iter",
                    iter,
                    projection_vars = projection.vars().len(),
                );
                projections.push(projection.clone());
                // Block this model region
                blocking = ChcExpr::and(blocking, ChcExpr::not(projection));
                if iter + 1 == MAX_ALLSAT_ITERS {
                    hit_cap = true;
                }
            }
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                debug!(
                    event = "chc_dual_mbp_allsat_exhausted",
                    iter,
                    total_projections = projections.len(),
                );
                break;
            }
            SmtResult::Unknown => {
                info!(
                    event = "chc_dual_mbp_allsat_unknown",
                    iter, "Dual MBP AllSAT query returned Unknown",
                );
                return None;
            }
        }
    }

    if hit_cap {
        warn!(
            event = "chc_dual_mbp_allsat_cap_hit",
            cap = MAX_ALLSAT_ITERS,
            iterations_completed = projections.len(),
            "AllSAT iteration cap reached in dual MBP interpolation; \
             interpolant is weaker than exact, which may slow PDR convergence"
        );
    }

    if projections.is_empty() {
        // B is UNSAT by itself — I = true is a valid interpolant
        return Some(ChcExpr::Bool(true));
    }

    // I(y) = ¬(∃z. B(y,z)) ≈ ¬(P1 ∨ ... ∨ Pk)
    let exists_b_approx = ChcExpr::or_all(projections);
    let interpolant = ChcExpr::not(exists_b_approx).simplify_constants();

    // Check shared-variable locality before validation
    let interp_vars: FxHashSet<String> = interpolant.vars().into_iter().map(|v| v.name).collect();
    if !interp_vars.iter().all(|v| shared_vars.contains(v)) {
        info!(
            event = "chc_dual_mbp_locality_failure",
            non_shared = interp_vars.difference(shared_vars).count(),
        );
        return None;
    }

    // Validate: I ∧ B must be UNSAT
    let check_formula = ChcExpr::and(interpolant.clone(), b_formula);
    let mut smt_check = SmtContext::new();
    let validation_timeout = if deadline.is_some() {
        timeout_for_deadline(deadline, VALIDATION_TIMEOUT)?
    } else {
        VALIDATION_TIMEOUT
    };
    match smt_check.check_sat_with_timeout(&check_formula, validation_timeout) {
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
            // Also validate A → I: ¬(A → I) = A ∧ ¬I must be UNSAT
            let a_formula = ChcExpr::and_all(a_constraints.iter().cloned());
            let a_not_i = ChcExpr::and(a_formula, ChcExpr::not(interpolant.clone()));
            let mut smt_a = SmtContext::new();
            let validation_timeout = if deadline.is_some() {
                timeout_for_deadline(deadline, VALIDATION_TIMEOUT)?
            } else {
                VALIDATION_TIMEOUT
            };
            match smt_a.check_sat_with_timeout(&a_not_i, validation_timeout) {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    info!(
                        event = "chc_dual_mbp_succeeded",
                        "Dual MBP interpolant passed both Craig checks",
                    );
                    Some(interpolant)
                }
                _ => {
                    info!(
                        event = "chc_dual_mbp_a_implies_i_failed",
                        "Dual MBP interpolant failed A → I validation",
                    );
                    None
                }
            }
        }
        _ => {
            info!(
                event = "chc_dual_mbp_validation_failed",
                "Dual MBP interpolant failed I ∧ B UNSAT validation",
            );
            None
        }
    }
}

#[cfg(test)]
#[path = "mbp_interpolation_tests.rs"]
mod tests;
