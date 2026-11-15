// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Owner custody spans the entire real default driver, not just individual
//! transactions. No selected unadmitted tail or late verdict escapes.

use super::*;
use crate::decision_trace::counted_decision::invalid;
use ay_core::original_query::{
    CountedAdmission, CountedAdmissionError, OriginalAdmissionError, QueryError, StopReason,
};

mod policy;
mod prepare;

#[cfg(test)]
mod internal_panic;

struct Counted<'a>(&'a CountedAdmission);
struct Guard<'a> {
    solver: &'a mut Solver,
    owner: CountedAdmission,
    completed: bool,
}

impl Drop for Guard<'_> {
    fn drop(&mut self) {
        let unwinding = std::thread::panicking();
        if unwinding {
            self.owner.refuse(CountedAdmissionError::Original(
                OriginalAdmissionError::OperationPanicked,
            ));
        }
        let healthy = self.owner.usage().is_ok_and(|u| u.refusal.is_none());
        if !self.completed || unwinding || !healthy {
            // Nested scopes retire their own scratch. These constant-time
            // authority fences do not allocate, poll callbacks or flush I/O.
            self.solver.clear_diagnostic_pass();
            if let Some(trace) = self.solver.cold.clause_trace.as_mut() {
                trace.mark_proof_work_exhausted();
            }
            if let Some(writer) = self.solver.cold.decision_trace.take() {
                writer.discard_without_flush();
            }
        }
    }
}

pub(in crate::solver::solve::theory_backend) fn run(
    solver: &mut Solver,
    stop: &dyn Fn() -> bool,
    progress: ProofProgress<'_>,
) -> SatResult {
    let Some(owner) = solver.cold.counted_admission.clone() else {
        solver.cold.last_unknown_reason = Some(SatUnknownReason::ResourceBudget);
        return SatResult::Unknown;
    };
    let mut guard = Guard {
        solver,
        owner,
        completed: false,
    };
    let outcome = prepare::entry(guard.solver, &guard.owner)
        .and_then(|()| super::run(guard.solver, stop, progress, &Counted(&guard.owner)));
    match outcome {
        Ok(result) => {
            if let Err(error) = guard.owner.check() {
                // Terminal helper admits disposal of any returned certificate
                // before granting it. No failed late fence publishes that data.
                drop(result);
                guard.solver.cold.last_unknown_reason = Some(counted_admission::reason(error));
                SatResult::Unknown
            } else {
                guard.completed = true;
                result
            }
        }
        Err(reason) => {
            let error = match reason {
                SatUnknownReason::DeadlineExceeded => CountedAdmissionError::Original(
                    OriginalAdmissionError::Query(QueryError::Interrupted(StopReason::Deadline)),
                ),
                SatUnknownReason::Interrupted => {
                    CountedAdmissionError::Original(OriginalAdmissionError::ObserverStopped)
                }
                _ => CountedAdmissionError::WorkExhausted,
            };
            let first = guard.owner.refuse(error);
            guard.solver.cold.last_unknown_reason =
                Some(if reason == SatUnknownReason::InvalidSatModel {
                    reason
                } else {
                    counted_admission::reason(first)
                });
            SatResult::Unknown
        }
    }
}

fn refusal(owner: &CountedAdmission, why: &'static str) -> SatUnknownReason {
    counted_admission::reason(invalid(owner, why))
}
