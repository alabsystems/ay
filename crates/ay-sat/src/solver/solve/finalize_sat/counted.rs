// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A retained-owner transaction over the ordinary model pipeline. It shares
//! mapping, reconstruction, original-ledger and arena validation kernels with
//! finalize_sat_model. No model or diagnostic is published after a refusal.

use super::*;
use crate::counted_storage::Result as AdmissionResult;
use crate::decision_trace::counted_decision::invalid;
use crate::reconstruct::admitted::{Counted, Work};
use ay_core::original_query::{CountedAdmission, CountedAdmissionError, OriginalAdmissionError};

mod prepare;
#[cfg(test)]
mod tests;
mod validate;

struct Guard<'a> {
    solver: &'a mut Solver,
    owner: &'a CountedAdmission,
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
        if !self.completed || unwinding || !self.owner.usage().is_ok_and(|u| u.refusal.is_none()) {
            if let Some(trace) = self.solver.cold.clause_trace.as_mut() {
                trace.mark_proof_work_exhausted();
            }
            if let Some(writer) = self.solver.cold.decision_trace.take() {
                writer.discard_without_flush();
            }
        }
    }
}

impl Solver {
    pub(in crate::solver) fn declare_counted_complete_assignment_sat(
        &mut self,
        owner: &CountedAdmission,
    ) -> Result<SatResult, SatUnknownReason> {
        let mut guard = Guard {
            solver: self,
            owner,
            completed: false,
        };
        let model =
            prepare::entry(guard.solver, owner).and_then(|()| finalize(guard.solver, owner));
        match model {
            Ok(model) => {
                // Every buffer, including this returned capacity, paid eventual
                // retirement before allocation. A late callback cannot leak it.
                owner.check().map_err(counted_admission::reason)?;
                guard.completed = true;
                Ok(SatResult::Sat(model))
            }
            Err(error) => {
                let reason = if is_invalid_model(error) {
                    guard.solver.cold.finalize_sat_fail_count =
                        guard.solver.cold.finalize_sat_fail_count.saturating_add(1);
                    SatUnknownReason::InvalidSatModel
                } else {
                    counted_admission::reason(error)
                };
                guard.solver.cold.last_unknown_reason = Some(reason);
                Err(reason)
            }
        }
    }
}

const INVALID_MODEL: &str = "counted SAT model violates the original model contract";

fn model_invalid(owner: &CountedAdmission) -> CountedAdmissionError {
    invalid(owner, INVALID_MODEL)
}

fn is_invalid_model(error: CountedAdmissionError) -> bool {
    matches!(
        error,
        CountedAdmissionError::Original(OriginalAdmissionError::Query(
            ay_core::original_query::QueryError::Invalid(INVALID_MODEL)
        ))
    )
}

fn finalize(s: &Solver, owner: &CountedAdmission) -> AdmissionResult<Vec<bool>> {
    let policy = Counted(owner);
    let model = s.current_model_admitted(&policy)?;
    // Early unit gate is part of ordinary finalize_sat_model, before replay.
    if s.first_unit_model_violation_admitted(&model, &policy)?
        .is_some()
    {
        return Err(model_invalid(owner));
    }
    #[cfg(debug_assertions)]
    validate::before(s, &model, owner)?;
    let mut external = s.external_model_admitted(&model, &policy)?;
    drop(model);
    s.inproc
        .reconstruction
        .reconstruct_admitted(&mut external, &policy)?;
    if s.first_original_violation_admitted(&external, OriginalDomain::Configured, &policy)?
        .is_some()
    {
        return Err(model_invalid(owner));
    }
    #[cfg(debug_assertions)]
    validate::after(s, &external, owner)?;
    let (internal, missing) = s.internal_model_admitted(&external, &policy)?;
    if missing.is_some()
        || s.first_arena_violation_admitted(
            &internal,
            crate::solver::preprocess_verify::admitted::ArenaMode::Full,
            &policy,
        )?
        .is_some()
    {
        return Err(model_invalid(owner));
    }
    drop(internal);
    policy.work(external.len())?;
    external.truncate(s.user_num_vars);
    // This is the very same full original-formula gate called by ordinary
    // verify_external_model, AFTER truncation, never merely arena validity.
    if s.first_original_violation_admitted(&external, OriginalDomain::Full, &policy)?
        .is_some()
    {
        return Err(model_invalid(owner));
    }
    policy.work(8)?;
    owner.check()?;
    Ok(external)
}
