// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A simplified SAT candidate is not an original-model refutation.
//! Replay the original formula, then use the actual original SMT query if the
//! candidate does not decide it. Every phase consumes the same original scope.

use super::*;
use ay_core::resource::CheckStop;
use ay_core::time::Instant;
use std::time::Duration;

#[cfg(test)]
mod tests;

impl PdrSolver {
    pub(in crate::pdr::verification) fn confirm_original_validation_sat(
        &mut self,
        original: &ChcExpr,
        definitions: &[(ChcVar, ChcExpr)],
        mut candidate: FxHashMap<String, SmtValue>,
        per_query: Duration,
        budget_start: Option<Instant>,
        budget: Option<Duration>,
    ) -> SmtResult {
        // Retain the original ABSOLUTE clause/solve clocks, not a duration
        // sampled earlier and restarted here. Evaluation consumes this clock.
        let Some(local_end) = Instant::now().checked_add(per_query) else {
            return SmtResult::Unknown;
        };
        let clause_end = match (budget_start, budget) {
            (Some(start), Some(limit)) => match start.checked_add(limit) {
                Some(end) => Some(end),
                None => return SmtResult::Unknown,
            },
            _ => None,
        };
        let deadline = [
            Some(local_end),
            clause_end,
            self.solve_deadline,
            self.smt.current_global_deadline(),
            crate::smt::deadline::effective_thread_deadline(),
        ]
        .into_iter()
        .flatten()
        .min()
        .unwrap_or(local_end);
        // Duration-based nested checks may sample their clock later. Keep the
        // exact original end installed throughout replay and actual solving.
        let _absolute = crate::smt::ScopedSmtDeadline::install_until(deadline);
        let stop = match ay_core::resource::current_check_stop() {
            Ok(stop) => stop,
            Err(_) => return SmtResult::Unknown,
        };
        if self.original_confirmation_stopped(deadline, stop.as_ref()) {
            return SmtResult::Unknown;
        }
        ChcExpr::extend_model_by_definitions(definitions, &mut candidate);
        if self.original_confirmation_stopped(deadline, stop.as_ref()) {
            return SmtResult::Unknown;
        }
        // Exact true is authority for THIS original formula. Missing values,
        // unsupported expressions and a false candidate are not refutations.
        let satisfied = exact_scalar_assignments(original, &candidate)
            && matches!(
                evaluate_expr(original, &candidate),
                Some(SmtValue::Bool(true))
            );
        if self.original_confirmation_stopped(deadline, stop.as_ref()) {
            return SmtResult::Unknown;
        }
        if satisfied {
            self.note_original_model_refutation();
            return SmtResult::Sat(candidate);
        }
        drop(candidate);
        if self.original_confirmation_stopped(deadline, stop.as_ref()) {
            return SmtResult::Unknown;
        }
        self.smt.reset();
        if self.original_confirmation_stopped(deadline, stop.as_ref()) {
            return SmtResult::Unknown;
        }
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return SmtResult::Unknown;
        }
        // The existing context keeps its original term cap; its timeout and
        // nested scopes intersect the retained caller's TLS ownership.
        let result = self.smt.check_sat_with_timeout(original, remaining);
        if self.original_confirmation_stopped(deadline, stop.as_ref()) {
            return SmtResult::Unknown;
        }
        if matches!(result, SmtResult::Sat(_)) {
            self.note_original_model_refutation();
        }
        result
    }

    fn original_confirmation_stopped(&self, deadline: Instant, stop: Option<&CheckStop>) -> bool {
        // Keep the captured callback even if a descendant changes the TLS view.
        // Poll it first so the original typed owner records its exact cause.
        stop.is_some_and(|stop| stop())
            || ay_core::resource::check_stop_requested()
            || self.is_cancelled()
            || Instant::now() >= deadline
    }
}

/// The generic evaluator's compatibility lookup may coerce a malformed model.
/// Its cheap positive path is authority only for exact scalar assignments.
/// Non-scalar variable bindings, missing/ambiguous bindings and opaque values
/// retain the COMPLETE original-query SMT path; they are not unsupported.
fn exact_scalar_assignments(original: &ChcExpr, model: &FxHashMap<String, SmtValue>) -> bool {
    use num_traits::ToPrimitive;
    original.vars().iter().all(|var| {
        let Some(value) = crate::expr::evaluate::lookup_model_value(model, var) else {
            return false;
        };
        match (&var.sort, value) {
            (ChcSort::Bool, SmtValue::Bool(_))
            | (ChcSort::Int, SmtValue::Int(_))
            | (ChcSort::Real, SmtValue::Real(_)) => true,
            (ChcSort::Int, SmtValue::BigInt(value)) => value.to_i128().is_none(),
            (ChcSort::BitVec(width), SmtValue::BitVec(value, actual)) => {
                width == actual
                    && (1..=128).contains(width)
                    && value.checked_shr(*width).unwrap_or(0) == 0
            }
            (ChcSort::BitVec(width), SmtValue::BigBitVec(value, actual)) => {
                width == actual && *width > 128 && value.bits() <= u64::from(*width)
            }
            _ => false,
        }
    })
}
