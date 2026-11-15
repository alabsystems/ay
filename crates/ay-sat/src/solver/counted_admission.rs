// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Explicit shared admission at solve/driver/publication boundaries.
//!
//! This is not yet an all-operation SAT work metric. Construction, insertion,
//! non-search propagation, analysis, preprocessing and proof reconstruction still
//! need their own pre-admissions. An attached owner never retroactively charges
//! existing state. No search reset, clone or repeated solve renews its credit.

use super::*;
use ay_core::original_query::{
    AdmissionUsage, CountedAdmission, CountedAdmissionError, OriginalAdmissionError, QueryError,
    StopReason,
};
use ay_core::resource::Exhausted;

pub(super) mod propagation;

impl Solver {
    /// Attach the original invocation owner without replacing an existing one.
    ///
    /// A second attachment returns the supplied owner unchanged. This neither
    /// instruments nor charges work already performed (including construction
    /// and clause insertion); callers must account for that separately. Current
    /// integration charges solve-entry/driver/publication steps and search BCP
    /// watch transactions, not every SAT operation. Clones and repeated solves
    /// share the same terminal ledger.
    pub fn attach_counted_admission(
        &mut self,
        owner: CountedAdmission,
    ) -> Result<(), CountedAdmission> {
        if self.cold.counted_admission.is_some() {
            Err(owner)
        } else {
            self.cold.counted_admission = Some(owner);
            Ok(())
        }
    }

    /// Snapshot the attached original ledger, without polling or authorizing a
    /// verdict. It includes other consumers sharing the owner, not just SAT.
    pub fn counted_admission_usage(&self) -> Option<Result<AdmissionUsage, CountedAdmissionError>> {
        self.cold
            .counted_admission
            .as_ref()
            .map(CountedAdmission::usage)
    }

    pub(super) fn counted_step_stop_reason(&self) -> Option<SatUnknownReason> {
        self.cold
            .counted_admission
            .as_ref()?
            .admit(1, 0)
            .err()
            .map(reason)
    }

    pub(super) fn counted_stop_reason(&self) -> Option<SatUnknownReason> {
        self.cold
            .counted_admission
            .as_ref()?
            .check()
            .err()
            .map(reason)
    }

    pub(super) fn counted_proof_progress(&self, progress: &dyn Fn() -> bool) -> bool {
        let Some(owner) = &self.cold.counted_admission else {
            return progress();
        };
        owner
            .with_work(|work| {
                work.charge(1)?;
                if progress() {
                    Ok(())
                } else {
                    Err(QueryError::Interrupted(StopReason::Cancelled))
                }
            })
            .is_ok()
    }

    pub(super) fn counted_callback_stop<F>(&self, stop: &F) -> Option<SatUnknownReason>
    where
        F: Fn() -> bool + ?Sized,
    {
        let Some(owner) = &self.cold.counted_admission else {
            return stop().then_some(SatUnknownReason::Interrupted);
        };
        owner
            .with_work(|_| {
                if stop() {
                    Err(QueryError::Interrupted(StopReason::Cancelled))
                } else {
                    Ok(())
                }
            })
            .err()
            .map(reason)
    }

    /// Legacy external stop observations are terminal for an attached owner,
    /// too; clearing a callback/flag cannot revive this original invocation.
    pub(super) fn counted_latch_stop(&self, stop: SatUnknownReason) -> SatUnknownReason {
        let Some(owner) = self.cold.counted_admission.as_ref() else {
            return stop;
        };
        let error = if stop == SatUnknownReason::DeadlineExceeded {
            OriginalAdmissionError::Query(QueryError::Interrupted(StopReason::Deadline))
        } else {
            OriginalAdmissionError::ObserverStopped
        };
        reason(owner.refuse(CountedAdmissionError::Original(error)))
    }

    pub(super) fn finish_counted_sat(&mut self, result: SatResult) -> SatResult {
        // Every public solve entry returns through here: the solve's search
        // work is charged in full, to the node it ran in (`work_report.rs`).
        self.report_work_to_ledger();
        if let Some(reason) = self.counted_stop_reason() {
            drop(result);
            self.declare_unknown_with_reason(reason)
        } else {
            result
        }
    }

    pub(super) fn finish_counted_assume(&mut self, result: AssumeResult) -> AssumeResult {
        // As `finish_counted_sat`: the solve's work is charged at its end.
        self.report_work_to_ledger();
        if let Some(reason) = self.counted_stop_reason() {
            drop(result);
            self.declare_assume_unknown_with_reason(reason)
        } else {
            result
        }
    }
}

pub(in crate::solver) fn reason(error: CountedAdmissionError) -> SatUnknownReason {
    match error {
        CountedAdmissionError::Guard(Exhausted::Deadline | Exhausted::Cpu)
        | CountedAdmissionError::Original(OriginalAdmissionError::Query(
            QueryError::Interrupted(StopReason::Deadline),
        )) => SatUnknownReason::DeadlineExceeded,
        CountedAdmissionError::Guard(Exhausted::Cancelled)
        | CountedAdmissionError::Original(OriginalAdmissionError::ObserverStopped)
        | CountedAdmissionError::Original(OriginalAdmissionError::Query(
            QueryError::Interrupted(StopReason::Cancelled),
        )) => SatUnknownReason::Interrupted,
        _ => SatUnknownReason::ResourceBudget,
    }
}

#[cfg(test)]
mod tests;
