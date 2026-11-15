// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Admission of the ordinary root-conflict proof graph and terminal publication.
//! A completed private transition is not independent certificate authority.

use super::*;
use crate::counted_storage::Result as AdmissionResult;
use crate::decision_trace::counted_decision::invalid;
use crate::kani_compat::DetHashSet;
use crate::solver::conflict_analysis_lrat_unit_chain::admitted as chain;
use crate::solver::conflict_analysis_minimize_lrat::root;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError};
use std::convert::Infallible;

mod ids;

pub(in crate::solver) trait Policy: chain::Policy {
    fn conflict(&self, s: &Solver, reference: ClauseRef) -> Result<(), Self::Error>;
    fn empty(&self, s: &Solver) -> Result<(), Self::Error>;
    fn add_trace(&self, s: &mut Solver, id: u64, hints: Vec<u64>) -> Result<(), Self::Error>;
    fn new_ids(&self, len: usize) -> Result<DetHashSet<u64>, Self::Error>;
    fn ids(&self, ids: &DetHashSet<u64>) -> Result<(), Self::Error>;
}

impl Policy for root::Ordinary {
    fn conflict(&self, _: &Solver, _: ClauseRef) -> Result<(), Infallible> {
        Ok(())
    }
    fn empty(&self, _: &Solver) -> Result<(), Infallible> {
        Ok(())
    }
    fn add_trace(&self, s: &mut Solver, id: u64, hints: Vec<u64>) -> Result<(), Infallible> {
        if let Some(trace) = s.live_clause_trace_mut() {
            trace.add_clause_with_hints(id, Vec::new(), false, hints);
        }
        Ok(())
    }
    fn new_ids(&self, len: usize) -> Result<DetHashSet<u64>, Infallible> {
        Ok(crate::kani_compat::det_hash_set_with_capacity(len))
    }
    fn ids(&self, _: &DetHashSet<u64>) -> Result<(), Infallible> {
        Ok(())
    }
}

impl Policy for root::Counted<'_> {
    fn conflict(&self, s: &Solver, reference: ClauseRef) -> AdmissionResult<()> {
        self.0.admit(8, 0)?;
        let off = reference.0 as usize;
        if s.decision_level != 0 || !s.arena.is_active(off) {
            return Err(invalid(
                self.0,
                "counted terminal requires an active level-zero conflict",
            ));
        }
        for &lit in s.arena.literals(off) {
            self.0.admit(3, 0)?;
            let vi = lit.variable().index();
            if vi >= s.num_vars
                || lit.index() >= s.vals.len()
                || s.var_data[vi].level != 0
                || s.lit_val(lit) >= 0
            {
                return Err(invalid(
                    self.0,
                    "counted root conflict is not falsified at level zero",
                ));
            }
        }
        Ok(())
    }
    fn empty(&self, s: &Solver) -> AdmissionResult<()> {
        self.0.admit(64, 0)?;
        if s.proof_manager.is_some()
            || s.cold.forward_checker.is_some()
            || s.cold.backward_proof_limits.is_some()
            || s.cold.solution_witness.is_some()
            || s.cold.proof_vars_compacted
            || !s.veripb_hints_resolved_inactive()
            || s.cold.veripb_hints.derived.has_pending_emission()
            || !s.counted_emission_triage_inactive()
        {
            return Err(invalid(
                self.0,
                "selected terminal emission mode is not admitted",
            ));
        }
        if s.cold.next_clause_id == u64::MAX {
            return Err(invalid(self.0, "counted terminal clause ID overflow"));
        }
        // The real trace-only proof funnel updates these existing counters.
        self.0
            .admit(s.cold.veripb_hints.adds_by_pass.len().saturating_mul(2), 0)?;
        for &n in s
            .cold
            .veripb_hints
            .adds_by_pass
            .iter()
            .chain(s.cold.veripb_hints.derived.red_by_pass.iter())
        {
            if n == u64::MAX {
                return Err(invalid(self.0, "terminal emission counter overflow"));
            }
        }
        Ok(())
    }
    fn add_trace(&self, s: &mut Solver, id: u64, hints: Vec<u64>) -> AdmissionResult<()> {
        if let Some(trace) = s.live_clause_trace_mut() {
            let prepared = trace.prepare_counted_add(id, &[], false, &hints, self.0)?;
            self.0.check()?;
            prepared.commit();
        }
        Ok(())
    }
    fn new_ids(&self, len: usize) -> AdmissionResult<DetHashSet<u64>> {
        ids::new(len, self.0)
    }
    fn ids(&self, values: &DetHashSet<u64>) -> AdmissionResult<()> {
        ids::probe(values, self.0)
    }
}
