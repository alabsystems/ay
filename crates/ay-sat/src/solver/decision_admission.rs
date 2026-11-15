// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Paid real variable/phase selection. Refusal is not the empty-candidate
//! signal. Assignment and its trace/log emission, and terminal model checking
//! retain separate admission obligations; this does not expose counted solve.

use super::*;
use crate::counted_storage::{try_reserve, Result as AdmissionResult};
use ay_core::original_query::{CountedAdmission, CountedAdmissionError, QueryError};
use relevancy_frontier::{RelevancyFrontier, SelectionStorage};
use std::convert::Infallible;

#[cfg(test)]
mod tests;

pub(super) trait Policy {
    type Error;
    fn prepare(&mut self, s: &mut Solver) -> Result<(), Self::Error>;
    fn skipped(&mut self) -> &mut Vec<Variable>;
    fn sync(&mut self, frontier: &mut RelevancyFrontier, s: &Solver) -> bool;
    #[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
    fn reference(&mut self) -> &mut Vec<bool>;
}

#[derive(Default)]
pub(super) struct Ordinary {
    skipped: Vec<Variable>,
    #[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
    reference: Vec<bool>,
}

impl Policy for Ordinary {
    type Error = Infallible;
    fn prepare(&mut self, _: &mut Solver) -> Result<(), Infallible> {
        Ok(())
    }
    fn skipped(&mut self) -> &mut Vec<Variable> {
        &mut self.skipped
    }
    fn sync(&mut self, frontier: &mut RelevancyFrontier, s: &Solver) -> bool {
        frontier.sync(s)
    }
    #[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
    fn reference(&mut self) -> &mut Vec<bool> {
        &mut self.reference
    }
}

struct Counted {
    owner: CountedAdmission,
    skipped: Vec<Variable>,
    frontier: SelectionStorage,
}

impl Policy for Counted {
    type Error = CountedAdmissionError;
    fn prepare(&mut self, s: &mut Solver) -> AdmissionResult<()> {
        // The same process-cache precondition as initial construction. Never
        // lazily discover/allocate environment configuration inside a query.
        self.owner.admit(1, 0)?;
        if ay_core::captured_misc_cli_flags().is_none() {
            return Err(self.owner.refuse(CountedAdmissionError::Original(
                QueryError::Invalid("SAT process configuration was not captured").into(),
            )));
        }
        let scratch = if let Some(domain) = s.active_domain.as_ref() {
            let domain = s.decision_domain.as_deref().unwrap_or(domain);
            self.domain_bound(s, domain)?
        } else if s.relevancy_should_engage() {
            let mut frontier = std::mem::take(&mut s.relevancy_frontier);
            let prepared = frontier.prepare_selection(s, &self.owner);
            s.relevancy_frontier = frontier;
            self.frontier = prepared?;
            // The frontier's bitmap is computed by the actual sync. Bound the
            // domain selector without predicting or changing that membership.
            self.domain_bound_unknown(s)?
        } else {
            self.main_bound(s)?;
            0
        };
        try_reserve(&self.owner, &mut self.skipped, scratch)?;
        self.owner.check()
    }
    fn skipped(&mut self) -> &mut Vec<Variable> {
        &mut self.skipped
    }
    fn sync(&mut self, frontier: &mut RelevancyFrontier, s: &Solver) -> bool {
        frontier.sync_prepared(s, Some(&mut self.frontier))
    }
    #[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
    fn reference(&mut self) -> &mut Vec<bool> {
        &mut self.frontier.reference
    }
}

impl Counted {
    fn domain_bound(&self, s: &Solver, domain: &[bool]) -> AdmissionResult<usize> {
        if s.bucket_queue_active {
            s.vsids.admit_bucket_selection(&self.owner)?;
            return Ok(0);
        }
        if s.active_branch_heuristic == BranchHeuristic::Vmtf {
            self.owner.admit(domain.len(), 0)?;
            return Ok(0);
        }
        s.vsids.admit_heap_selection(
            &s.vals,
            s.var_lifecycle.as_slice(),
            Some(domain),
            &self.owner,
        )
    }

    fn domain_bound_unknown(&self, s: &Solver) -> AdmissionResult<usize> {
        if s.bucket_queue_active {
            s.vsids.admit_bucket_selection(&self.owner)?;
            Ok(0)
        } else if s.active_branch_heuristic == BranchHeuristic::Vmtf {
            self.owner.admit(s.num_vars, 0)?;
            Ok(0)
        } else {
            s.vsids.admit_domain_heap_selection(&self.owner)
        }
    }

    fn main_bound(&self, s: &Solver) -> AdmissionResult<()> {
        self.owner.admit(s.indep_support.len(), 0)?;
        if s.cold.random_var_freq > 0.0 {
            self.owner.admit(s.num_vars, 0)?;
        }
        // Cover a reachable burst, including its schedule update. Do not bill
        // a full random scan when the ordinary threshold/level gates forbid it.
        if random_burst_may_sample(s) {
            self.owner.admit(s.num_vars, 0)?;
        }
        if s.active_branch_heuristic == BranchHeuristic::Vmtf {
            s.vsids
                .admit_vmtf_selection(&s.vals, s.var_lifecycle.as_slice(), &self.owner)
        } else {
            s.vsids
                .admit_heap_selection(&s.vals, s.var_lifecycle.as_slice(), None, &self.owner)
                .map(|_| ())
        }
    }
}

impl Solver {
    /// The default pure driver uses the unrestricted MAIN selection route,
    /// not the domain/relevancy entry. Price and execute that exact route.
    pub(in crate::solver) fn pick_main_decision_literal_counted(
        &mut self,
    ) -> Result<Option<Literal>, SatUnknownReason> {
        let Some(owner) = self.cold.counted_admission.clone() else {
            return Ok(self
                .pick_next_decision_variable_main()
                .map(|v| self.pick_phase(v)));
        };
        owner.admit(32, 0).map_err(counted_admission::reason)?;
        if ay_core::captured_misc_cli_flags().is_none() {
            return Err(counted_admission::reason(owner.refuse(
                CountedAdmissionError::Original(
                    QueryError::Invalid("MAIN selection requires captured configuration").into(),
                ),
            )));
        }
        let policy = Counted {
            owner: owner.clone(),
            skipped: Vec::new(),
            frontier: SelectionStorage::default(),
        };
        policy.main_bound(self).map_err(counted_admission::reason)?;
        let selected = self
            .pick_next_decision_variable_main()
            .map(|v| self.pick_phase(v));
        drop(policy);
        owner.check().map_err(counted_admission::reason)?;
        Ok(selected)
    }
}

fn random_burst_may_sample(s: &Solver) -> bool {
    if s.stable_mode {
        return false;
    }
    if ay_core::sat_ab_switches().randec_kissat == Some(true) {
        let limit = if s.cold.random_decision_phases == 0 {
            500
        } else {
            s.cold.next_random_decision
        };
        s.cold.randomized_deciding > 0 || (s.num_conflicts >= limit && s.decision_level == 0)
    } else {
        s.num_conflicts >= s.cold.next_random_decision
            && (s.cold.randomized_deciding > 0 || s.decision_level == 0)
    }
}

impl Solver {
    pub(in crate::solver) fn pick_next_decision_literal_counted(
        &mut self,
    ) -> Result<Option<Literal>, SatUnknownReason> {
        let Some(owner) = self.cold.counted_admission.clone() else {
            return Ok(self
                .pick_next_decision_variable()
                .map(|var| self.pick_phase(var)));
        };
        let selected = {
            let mut policy = Counted {
                owner: owner.clone(),
                skipped: Vec::new(),
                frontier: SelectionStorage::default(),
            };
            self.pick_next_decision_variable_admitted(&mut policy)
                .map(|candidate| candidate.map(|var| self.pick_phase(var)))
        };
        // Both domain and frontier are restored, and scratch is destroyed,
        // before a selected literal or an empty candidate set can escape.
        owner.check().map_err(counted_admission::reason)?;
        selected.map_err(counted_admission::reason)
    }
}
