// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Counted SEARCH BCP admits a complete watch-list transaction before mutation.
//! The existing safe two-watch algorithm is unchanged; refusal is a separate
//! result, never a fabricated conflict or completed propagation fixpoint.

use super::*;
use crate::solver::propagation::bcp_mode;
use crate::watched;
use std::convert::Infallible;

mod reserve;

pub(in crate::solver) trait Admission {
    type Error;
    fn before_watch(&self, solver: &mut Solver) -> Result<(), Self::Error>;
}

pub(in crate::solver) struct Uncounted;

impl Admission for Uncounted {
    type Error = Infallible;
    fn before_watch(&self, _: &mut Solver) -> Result<(), Infallible> {
        Ok(())
    }
}

struct Counted(CountedAdmission);

impl Admission for Counted {
    type Error = SatUnknownReason;

    fn before_watch(&self, solver: &mut Solver) -> Result<(), SatUnknownReason> {
        self.0.admit(1, 0).map_err(reason)?;
        let false_lit = solver.trail[solver.qhead].negated();
        let len = solver.watches.len_of(false_lit);
        let mut tail_bound = 0usize;
        for index in 0..len {
            // Price the bound's own metadata walk before reading any watcher.
            self.0.admit(1, 0).map_err(reason)?;
            let entry = solver.watches.entry_raw(false_lit, index);
            let binary = watched::entry_is_binary(entry);
            let literals = if binary {
                2
            } else {
                solver
                    .arena
                    .len_of(watched::entry_clause_off(entry) as usize)
            };
            if !binary {
                tail_bound = tail_bound
                    .checked_add(literals.saturating_sub(2))
                    .ok_or_else(|| {
                        reason(self.0.refuse(CountedAdmissionError::StorageExhausted))
                    })?;
            }
            // Replacement, chrono reason and invariant scans each traverse at
            // most the clause length; admit their complete transaction first.
            let scans = literals.checked_add(1).and_then(|n| n.checked_mul(8));
            // Binary jump-reason shortening follows one link, not the whole
            // trail; it is included in this constant per-watcher allowance.
            let work =
                scans.ok_or_else(|| reason(self.0.refuse(CountedAdmissionError::WorkExhausted)))?;
            self.0.admit(work, 0).map_err(reason)?;
        }
        reserve::buffers(solver, &self.0, false_lit, len, tail_bound)?;
        self.0.check().map_err(reason)
    }
}

impl Solver {
    pub(in crate::solver) fn search_propagate_standard_counted(
        &mut self,
    ) -> Result<Option<ClauseRef>, SatUnknownReason> {
        if self.cold.counted_admission.is_some() {
            self.search_propagate_counted()
        } else {
            Ok(self.search_propagate_standard())
        }
    }

    /// Explicit counted search boundary. Optional preprocessing/probe/vivify
    /// callers keep their existing contract until migrated independently.
    pub(in crate::solver) fn search_propagate_counted(
        &mut self,
    ) -> Result<Option<ClauseRef>, SatUnknownReason> {
        let Some(owner) = self.cold.counted_admission.clone() else {
            return Ok(self.search_propagate());
        };
        owner.admit(1, 0).map_err(reason)?;
        self.reason_marks_invalidated = true;
        let admission = Counted(owner.clone());
        let result = if self.decision_level > 0 && self.active_domain.is_some() {
            self.counted_domain_propagation(&admission)
        } else {
            self.propagate_bcp_admitted::<{ bcp_mode::SEARCH }, _>(&admission)
        };
        // A transaction may finish just as an original stop fires. Neither its
        // conflict nor its fixpoint is published after refusal.
        owner.check().map_err(reason)?;
        result
    }

    fn counted_domain_propagation(
        &mut self,
        admission: &Counted,
    ) -> Result<Option<ClauseRef>, SatUnknownReason> {
        let Some(domain) = self.active_domain.take() else {
            return self.propagate_bcp_admitted::<{ bcp_mode::SEARCH }, _>(admission);
        };
        // Domain selection is a constant-time length comparison. Restore the
        // borrowed domain, including a refusal before entering the safe engine.
        let result = match admission.0.admit(1, 0).map_err(reason) {
            Err(reason) => Err(reason),
            Ok(()) if !self.should_use_domain_bcp_for(&domain) => {
                self.propagate_bcp_admitted::<{ bcp_mode::SEARCH }, _>(admission)
            }
            Ok(()) if self.cold.ic3_mode => {
                self.propagate_domain_bcp_impl::<true, _>(&domain, admission)
            }
            Ok(()) => self.propagate_domain_bcp_impl::<false, _>(&domain, admission),
        };
        self.active_domain = Some(domain);
        result
    }
}
