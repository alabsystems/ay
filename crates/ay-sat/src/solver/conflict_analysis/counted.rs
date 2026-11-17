// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private ordinary-analysis and learned/asserting continuation. No public
//! answer, model, final proof, reset or maintenance is authorized by this scope.

use super::*;
use crate::counted_storage::Result as AdmissionResult;
use crate::decision_trace::counted_decision::invalid;
use crate::solver::conflict_analysis_finalize::admitted as finalize;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError, OriginalAdmissionError};

mod admission;
mod side_effects;
#[cfg(test)]
mod tests;

struct Retirement<'a> {
    solver: &'a mut Solver,
    owner: CountedAdmission,
    active: bool,
    retain_trace: bool,
    learning_started: bool,
}

impl Retirement<'_> {
    fn retire(&mut self) {
        if self.active {
            finalize::retire(self.solver);
            self.solver
                .conflict
                .retire_counted_standard(&mut self.solver.var_data);
            self.solver.clear_level_seen();
            self.solver.cold.lrat_level0_vars_buf.clear();
            #[cfg(all(feature = "jit", debug_assertions))]
            self.solver.cold.debug_jit_flags_buf.clear();
            self.active = false;
        }
    }
}

impl Drop for Retirement<'_> {
    fn drop(&mut self) {
        let unwinding = std::thread::panicking();
        if unwinding {
            self.owner.refuse(CountedAdmissionError::Original(
                OriginalAdmissionError::OperationPanicked,
            ));
        }
        self.retire();
        let healthy = self
            .owner
            .usage()
            .is_ok_and(|usage| usage.refusal.is_none());
        if !self.retain_trace || unwinding || !healthy {
            if self.learning_started {
                self.solver.clear_diagnostic_pass();
                if let Some(trace) = self.solver.cold.clause_trace.as_mut() {
                    trace.mark_proof_work_exhausted();
                }
            }
            if let Some(writer) = self.solver.cold.decision_trace.take() {
                writer.discard_without_flush();
            }
        }
    }
}

/// Exclusive actual solver state and owned learned result stay inside this
/// private scope. Learning/enqueue never escapes to an uncharged ordinary tail.
pub(in crate::solver) struct CountedStandardAnalysis<'a> {
    result: ConflictResult,
    retirement: Retirement<'a>,
}

/// Completed private transition metadata, not a solve/proof/model outcome.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::solver) struct CountedLearnedStep {
    pub(in crate::solver) reference: ClauseRef,
    pub(in crate::solver) uip: Literal,
    pub(in crate::solver) backtrack: u32,
}

impl CountedStandardAnalysis<'_> {
    pub(in crate::solver) fn learn_and_assert(
        mut self,
    ) -> Result<CountedLearnedStep, SatUnknownReason> {
        let owner = &self.retirement.owner;
        self.retirement
            .solver
            .prepare_counted_learning(&self.result, owner)
            .map_err(counted_admission::reason)?;
        // Arm before chrono/backtrack or any output publication. Dropping a
        // refused/abandoned continuation retains rows but removes authority.
        self.retirement.learning_started = true;
        let actual = self
            .retirement
            .solver
            .chrono_backtrack_level_admitted(self.result.backtrack_level, &finalize::Counted(owner))
            .map_err(counted_admission::reason)?;
        self.retirement.solver.backtrack_counted(actual)?;
        let uip = self.result.learned_clause[0];
        self.retirement.solver.fix_learned_uip_at_root(uip, actual);
        let off = self
            .retirement
            .solver
            .complete_counted_learning(&mut self.result, actual, owner)
            .map_err(counted_admission::reason)?;
        self.retirement.retire();
        self.retirement
            .owner
            .check()
            .map_err(counted_admission::reason)?;
        self.retirement.retain_trace = true;
        Ok(CountedLearnedStep {
            reference: ClauseRef(off as u32),
            uip,
            backtrack: actual,
        })
    }
}

impl Solver {
    pub(in crate::solver) fn begin_counted_standard_analysis(
        &mut self,
        reference: ClauseRef,
    ) -> Result<Option<CountedStandardAnalysis<'_>>, SatUnknownReason> {
        let owner = self
            .cold
            .counted_admission
            .clone()
            .ok_or(SatUnknownReason::ResourceBudget)?;
        let mut retirement = Retirement {
            solver: self,
            owner: owner.clone(),
            active: false,
            retain_trace: false,
            learning_started: false,
        };
        prepare_entry(retirement.solver, &owner).map_err(counted_admission::reason)?;
        finalize::prepare_scope(retirement.solver, &owner).map_err(counted_admission::reason)?;
        retirement.active = true;
        let result = admitted::run(retirement.solver, reference, &finalize::Counted(&owner))
            .map_err(counted_admission::reason)?;
        let Some(result) = result else {
            retirement.retire();
            let healthy = owner.check();
            retirement.retain_trace = healthy.is_ok();
            healthy.map_err(counted_admission::reason)?;
            return Ok(None);
        };
        owner.check().map_err(counted_admission::reason)?;
        Ok(Some(CountedStandardAnalysis { result, retirement }))
    }
}

fn prepare_entry(s: &Solver, owner: &CountedAdmission) -> AdmissionResult<()> {
    owner.admit(size_of::<CountedStandardAnalysis<'_>>(), 0)?;
    if s.cold.ic3_mode
        || s.decision_level == 0
        || s.decision_level as usize > s.num_vars
        || s.num_vars != s.var_data.len()
        || s.num_vars > (u32::MAX / 4) as usize
        || s.trail.len() > s.num_vars
        || s.vals.len() < s.num_vars.saturating_mul(2)
        || s.proof_manager.is_some()
        || (s.cold.lrat_enabled && !s.has_live_clause_trace())
        || s.cold.internal_lrat_enabled
        || s.cold.proof_bookkeeping_budget.is_some()
        || s.cold.backward_proof_limits.is_some()
        || s.cold.backward_proof_failure.is_some()
        || s.veripb_hints_cached_active()
        || triage_enabled()
    {
        return Err(invalid(
            owner,
            "counted ordinary analysis requires bounded standard state without external proof mutation",
        ));
    }
    #[cfg(ay_logging)]
    if s.log_enabled {
        return Err(invalid(
            owner,
            "counted ordinary diagnostic output is not admitted",
        ));
    }
    // ClauseTrace is intentionally allowed: this is SmtContext's real route.
    s.conflict.prepare_counted_ic3_entry(&s.var_data, owner)?;
    owner.admit(s.min.level_seen.len(), 0)?;
    if !s.min.level_seen_to_clear.is_empty()
        || !s.cold.lrat_level0_vars_buf.is_empty()
        || s.min
            .level_seen
            .iter()
            .any(|entry| *entry != minimization_state::LevelSeen::EMPTY)
    {
        return Err(invalid(
            owner,
            "counted ordinary analysis requires retired level scratch",
        ));
    }
    // Native code sets seen flags before Rust can register them. Prepay the
    // actual full-array exceptional retirement, not merely the dirty-list size.
    owner.admit(s.var_data.len().saturating_add(32), 0)?;
    Ok(())
}
