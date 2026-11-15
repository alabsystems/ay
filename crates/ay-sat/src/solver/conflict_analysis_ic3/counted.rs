// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original-owner scope for the actual first-UIP walk and pre-minimize LBD.
//! This is NOT complete conflict analysis/learning or a SAT/proof endpoint.

use super::*;
use crate::counted_storage::Result as AdmissionResult;
use crate::decision_trace::counted_decision::invalid;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError, OriginalAdmissionError};

mod admission;
mod minimize;
#[cfg(test)]
mod tests;

struct Retirement<'a> {
    solver: &'a mut Solver,
    owner: CountedAdmission,
    active: bool,
    minimization_active: bool,
    retain_trace: bool,
}

impl Retirement<'_> {
    fn retire(&mut self) {
        if self.minimization_active {
            minimize::retire(self.solver);
            self.minimization_active = false;
        }
        if self.active {
            self.solver
                .conflict
                .retire_counted_ic3(&mut self.solver.var_data);
            self.solver.clear_level_seen();
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
            if let Some(writer) = self.solver.cold.decision_trace.take() {
                writer.discard_without_flush();
            }
        }
    }
}

/// Owns exclusive access to the real solver's pre-minimization scratch.
/// No mutable solver escape, owned learned clause, verdict or proof authority.
/// Later finalization must be admitted inside this scope, not run after finish.
pub(in crate::solver) struct CountedIc3Resolution<'a> {
    retirement: Retirement<'a>,
    uip: Literal,
    lbd: u32,
}

impl CountedIc3Resolution<'_> {
    pub(in crate::solver) fn asserting_literal(&self) -> Literal {
        self.uip
    }

    /// Borrowing is not permission for an unmetered downstream traversal.
    pub(in crate::solver) fn lower_literals(&self) -> &[Literal] {
        self.retirement.solver.conflict.counted_ic3_lower_literals()
    }

    pub(in crate::solver) fn lbd(&self) -> u32 {
        self.lbd
    }

    pub(in crate::solver) fn finish(mut self) -> Result<(), SatUnknownReason> {
        self.retirement.retire();
        let result = self.retirement.owner.check();
        self.retirement.retain_trace = result.is_ok();
        result.map_err(counted_admission::reason)
    }
}

impl Solver {
    /// Complete paid first-UIP resolution and original pre-minimize LBD only.
    /// Ordinary callers use the identical walk with an infallible policy.
    /// There is intentionally no caller in a public counted solve yet: selected
    /// minimization, activity, learned insertion/enqueue and proof still need
    /// their own same-owner transactions before this can become a full loop.
    /// Clause references retain the ordinary trusted-internal-arena-boundary
    /// precondition; corrupt internal offsets can unwind, terminalizing owner.
    pub(in crate::solver) fn begin_counted_ic3_resolution(
        &mut self,
        conflict_ref: ClauseRef,
    ) -> Result<Option<CountedIc3Resolution<'_>>, SatUnknownReason> {
        let owner = self
            .cold
            .counted_admission
            .clone()
            .ok_or(SatUnknownReason::ResourceBudget)?;
        let mut retirement = Retirement {
            solver: self,
            owner: owner.clone(),
            active: false,
            minimization_active: false,
            retain_trace: false,
        };
        prepare_entry(retirement.solver, &owner).map_err(counted_admission::reason)?;
        retirement.active = true;
        retirement
            .solver
            .conflict
            .clear(&mut retirement.solver.var_data);
        let result = retirement
            .solver
            .resolve_ic3_first_uip(conflict_ref, &admission::Counted(&owner));
        let Some(uip) = result.map_err(counted_admission::reason)? else {
            retirement.retire();
            let result = owner.check();
            retirement.retain_trace = result.is_ok();
            result.map_err(counted_admission::reason)?;
            return Ok(None);
        };
        retirement
            .solver
            .conflict
            .prepare_counted_ic3_lbd(retirement.solver.var_data.len(), &owner)
            .map_err(counted_admission::reason)?;
        retirement.solver.conflict.set_asserting_literal(uip);
        let lbd = retirement
            .solver
            .conflict
            .compute_lbd(&retirement.solver.var_data);
        owner.check().map_err(counted_admission::reason)?;
        retirement.retain_trace = true;
        Ok(Some(CountedIc3Resolution {
            retirement,
            uip,
            lbd,
        }))
    }
}

fn prepare_entry(s: &Solver, owner: &CountedAdmission) -> AdmissionResult<()> {
    owner.admit(std::mem::size_of::<CountedIc3Resolution<'_>>().max(1), 0)?;
    if !s.cold.ic3_mode
        || s.chrono_enabled
        || s.ghost_guard_needed
        || s.decision_level == 0
        || s.decision_level as usize > s.num_vars
        || s.num_vars != s.var_data.len()
        || s.trail.len() > s.num_vars
        || s.vals.len() < s.num_vars.saturating_mul(2)
        || s.cold.lazy_materialization_failed
        || s.proof_manager.is_some()
        || s.cold.lrat_enabled
        || s.cold.internal_lrat_enabled
        || s.cold.clause_trace.is_some()
        || s.cold.proof_bookkeeping_budget.is_some()
        || s.cold.backward_proof_limits.is_some()
        || s.cold.backward_proof_failure.is_some()
    {
        return Err(invalid(
            owner,
            "counted first-UIP requires the proof-free IC3 state",
        ));
    }
    s.conflict.prepare_counted_ic3_entry(&s.var_data, owner)?;
    owner.admit(s.min.level_seen.len(), 0)?;
    if !s.min.level_seen_to_clear.is_empty()
        || s.min
            .level_seen
            .iter()
            .any(|level| *level != minimization_state::LevelSeen::EMPTY)
    {
        return Err(invalid(
            owner,
            "counted first-UIP requires retired level scratch",
        ));
    }
    Ok(())
}
