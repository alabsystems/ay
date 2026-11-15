// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Atomic real decision assignment with paid trace/replay/diagnostic effects.
//! This is one CDCL transaction, not a public counted solve endpoint.

use super::*;
use crate::counted_storage::{try_reserve, Result as AdmissionResult};
use crate::decision_trace::counted_decision::invalid;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError, OriginalAdmissionError};
use std::convert::Infallible;

pub(super) mod output;
#[cfg(test)]
mod tests;

pub(super) trait Policy {
    type Error;
    fn prepare(&mut self, s: &mut Solver, lit: Literal) -> Result<(), Self::Error>;
    fn trace(&mut self, s: &mut Solver, lit: Literal);
    fn triage(&self, s: &Solver, lit: Literal);
    fn assignment_log(&self, s: &Solver, lit: Literal);
    fn decision_log(&self, s: &Solver, lit: Literal);
    fn finish(&mut self, s: &mut Solver, lit: Literal) -> Result<(), Self::Error>;
}

pub(super) struct Ordinary;
impl Policy for Ordinary {
    type Error = Infallible;
    fn prepare(&mut self, _: &mut Solver, _: Literal) -> Result<(), Infallible> {
        Ok(())
    }
    fn trace(&mut self, s: &mut Solver, lit: Literal) {
        s.trace_decide(lit);
    }
    fn triage(&self, s: &Solver, lit: Literal) {
        s.trace_assignment_triage(lit, None);
    }
    fn assignment_log(&self, s: &Solver, lit: Literal) {
        s.log_assignment(lit, s.decision_level, None);
    }
    fn decision_log(&self, s: &Solver, lit: Literal) {
        s.log_decision(lit);
    }
    fn finish(&mut self, _: &mut Solver, _: Literal) -> Result<(), Infallible> {
        Ok(())
    }
}

struct Counted {
    owner: CountedAdmission,
    output: Option<output::PreparedOutput>,
}

/// Retirement is armed before any admission or mutation and remains armed
/// through the final owner fence. An observer's opaque panic payload can panic
/// again when dropped by the owner's catch boundary, so return-only cleanup is
/// insufficient even when ordinary observer panics become terminal errors.
struct DecisionRetirement<'a> {
    solver: &'a mut Solver,
    owner: &'a CountedAdmission,
    retain_trace: bool,
}

impl Drop for DecisionRetirement<'_> {
    fn drop(&mut self) {
        let unwinding = std::thread::panicking();
        if unwinding {
            // No observer is invoked here. Preserve an earlier refusal such as
            // ObserverPanicked; otherwise an internal panic forbids reuse too.
            self.owner.refuse(CountedAdmissionError::Original(
                OriginalAdmissionError::OperationPanicked,
            ));
        }
        if !self.retain_trace || unwinding {
            if let Some(writer) = self.solver.cold.decision_trace.take() {
                // Consume the exact descriptor: no path lookup, truncation,
                // implicit BufWriter flush, allocation, or callback.
                writer.discard_without_flush();
            }
        }
    }
}

impl Policy for Counted {
    type Error = CountedAdmissionError;
    fn prepare(&mut self, s: &mut Solver, lit: Literal) -> AdmissionResult<()> {
        self.owner.admit(1, 0)?;
        if ay_core::captured_misc_cli_flags().is_none() {
            return Err(invalid(
                &self.owner,
                "SAT process configuration was not captured",
            ));
        }
        let level = validate_decision(s, lit, &self.owner)?;
        try_reserve(&self.owner, &mut s.trail_lim, 1)?;
        try_reserve(&self.owner, &mut s.trail, 1)?;
        #[cfg(debug_assertions)]
        if (s.trail.len() + 1) & 0x3ff == 0 {
            self.owner.admit(s.num_vars, 0)?;
        }
        if let Some(replay) = &s.cold.replay_trace {
            replay.admit_decision(lit.to_dimacs(), &self.owner)?;
        }
        if let Some(writer) = &s.cold.decision_trace {
            writer.admit_decision(&self.owner)?;
        }
        self.output = output::PreparedOutput::prepare(s, lit, level, &self.owner)?;
        self.owner.check()
    }
    // Counted output is deferred, not suppressed: the complete assignment is
    // committed before any fallible I/O, so an I/O refusal cannot strand only
    // decision_level/trail_lim/counters without their associated assignment.
    fn trace(&mut self, _: &mut Solver, _: Literal) {}
    fn triage(&self, _: &Solver, _: Literal) {}
    fn assignment_log(&self, _: &Solver, _: Literal) {}
    fn decision_log(&self, _: &Solver, _: Literal) {}
    fn finish(&mut self, s: &mut Solver, lit: Literal) -> AdmissionResult<()> {
        if let Some(replay) = &mut s.cold.replay_trace {
            if !replay.commit_admitted_decision(lit.to_dimacs()) {
                return Err(invalid(
                    &self.owner,
                    "counted decision replay changed after admission",
                ));
            }
        }
        if let Some(writer) = &mut s.cold.decision_trace {
            writer
                .write_event(&TraceEvent::Decide {
                    lit_dimacs: lit.to_dimacs(),
                })
                .map_err(|_| invalid(&self.owner, "counted decision trace write failed"))?;
        }
        if let Some(output) = &self.output {
            std::io::stderr()
                .lock()
                .write_all(output.bytes())
                .map_err(|_| invalid(&self.owner, "counted decision diagnostic write failed"))?;
        }
        Ok(())
    }
}

fn validate_decision(s: &Solver, lit: Literal, owner: &CountedAdmission) -> AdmissionResult<u32> {
    let index = lit.variable().index();
    if index >= s.num_vars
        || s.trail.len() >= s.num_vars
        || s.qhead != s.trail.len()
        || s.var_is_assigned(index)
        || s.var_lifecycle.is_removed(index)
    {
        return Err(invalid(owner, "invalid counted decision assignment"));
    }
    let level = s
        .decision_level
        .checked_add(1)
        .ok_or_else(|| invalid(owner, "decision level overflow"))?;
    let mode_count = if s.stable_mode {
        s.stats.stable_decisions
    } else {
        s.stats.focused_decisions
    };
    if s.num_decisions.checked_add(1).is_none()
        || mode_count.checked_add(1).is_none()
        || s.stats.decision_level_count.checked_add(1).is_none()
        || s.stats
            .decision_level_sum
            .checked_add(u64::from(level))
            .is_none()
    {
        return Err(invalid(owner, "decision statistics overflow"));
    }
    Ok(level)
}

impl Solver {
    pub(super) fn enqueue_decision_state(&mut self, lit: Literal) {
        // Same actual assignment update as general enqueue(None). The decision
        // entry already checks removed variables and propagation fixpoint.
        debug_assert!(self.trail.len() < self.num_vars);
        debug_assert!(!self.var_is_assigned(lit.variable().index()));
        if !self.suppress_phase_saving {
            self.phase[lit.variable().index()] = lit.sign_i8();
        }
        self.commit_assignment(lit, None, self.decision_level, NO_REASON);
    }

    pub(in crate::solver) fn decide_counted(
        &mut self,
        lit: Literal,
    ) -> Result<(), SatUnknownReason> {
        let Some(owner) = self.cold.counted_admission.clone() else {
            self.decide(lit);
            return Ok(());
        };
        let mut retirement = DecisionRetirement {
            solver: self,
            owner: &owner,
            retain_trace: false,
        };
        let result = {
            let mut policy = Counted {
                owner: owner.clone(),
                output: None,
            };
            retirement.solver.decide_admitted(lit, &mut policy)
        };
        let fence = owner.check();
        retirement.retain_trace = result.is_ok() && fence.is_ok();
        fence.map_err(counted_admission::reason)?;
        result.map_err(counted_admission::reason)
    }
}
