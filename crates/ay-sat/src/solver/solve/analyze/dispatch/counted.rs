// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::decision_trace::counted_decision::invalid;
use crate::solver::conflict_analysis_level::admitted as level;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError, OriginalAdmissionError};

mod policy;
mod prepare;

use policy::Counted;

/// Only an internal transition, never a SAT/UNSAT, model or proof result.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::solver) enum CountedDispatchStep {
    Forced,
    Learned {
        reference: ClauseRef,
        uip: Literal,
        backtrack: u32,
    },
    BailedOut,
}

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
        let healthy = self
            .owner
            .usage()
            .is_ok_and(|usage| usage.refusal.is_none());
        if !self.completed || unwinding || !healthy {
            // No callback, allocation or solver publication on retirement.
            // Nested analysis/learning scopes retire their own paid scratch.
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

impl Guard<'_> {
    fn run(&mut self, reference: ClauseRef) -> Result<CountedDispatchStep, SatUnknownReason> {
        prepare::entry(self.solver, reference, &self.owner)?;
        let mut policy = Counted(&self.owner);
        if self.solver.decision_level == 0 {
            policy.terminal(self.solver, reference)?;
        }
        match self
            .solver
            .conflict_dispatch_prelude(reference, &mut policy)?
        {
            Prelude::Forced => return Ok(CountedDispatchStep::Forced),
            Prelude::Terminal => {
                return Err(refusal(&self.owner, "terminal proof is not admitted"))
            }
            Prelude::Analyze => {}
        }
        let learned = match self.solver.begin_counted_standard_analysis(reference)? {
            Some(scope) => Some(scope.learn_and_assert()?),
            None => None,
        };
        if let Some(step) = learned {
            Ok(CountedDispatchStep::Learned {
                reference: step.reference,
                uip: step.uip,
                backtrack: step.backtrack,
            })
        } else {
            self.solver.conflict_dispatch_bailout(&mut policy)?;
            Ok(CountedDispatchStep::BailedOut)
        }
    }
}

impl Solver {
    /// Real ordinary conflict prelude through asserting learning under the
    /// already-attached owner. No callback or uncharged ordinary tail escapes.
    /// Surrounding search counters, reset, restart/maintenance and terminal
    /// publication remain separate admission obligations.
    pub(in crate::solver) fn dispatch_conflict_counted(
        &mut self,
        reference: ClauseRef,
    ) -> Result<CountedDispatchStep, SatUnknownReason> {
        let owner = self
            .cold
            .counted_admission
            .clone()
            .ok_or(SatUnknownReason::ResourceBudget)?;
        let mut guard = Guard {
            solver: self,
            owner,
            completed: false,
        };
        let step = guard.run(reference)?;
        guard.owner.check().map_err(counted_admission::reason)?;
        guard.completed = true;
        Ok(step)
    }
}

fn refusal(owner: &CountedAdmission, why: &'static str) -> SatUnknownReason {
    counted_admission::reason(invalid(owner, why))
}
