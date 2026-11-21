// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Derived publication through the ordinary database kernel.

use super::*;
use crate::counted_storage::{try_reserve, Result};
use crate::decision_trace::counted_decision::invalid;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError};

pub(super) trait Trace {
    fn publish(
        s: &mut Solver,
        id: u64,
        literals: &[Literal],
        derived: bool,
        hints: &[u64],
        registered: Option<u64>,
    );
}

pub(super) struct Ordinary;
impl Trace for Ordinary {
    fn publish(
        s: &mut Solver,
        id: u64,
        lits: &[Literal],
        derived: bool,
        hints: &[u64],
        registered: Option<u64>,
    ) {
        s.trace_clause_db_add(id, lits, derived, hints, registered);
    }
}

// Constructible only in this module, after the exact borrowed trace token commits.
struct CommittedDerived;
impl Trace for CommittedDerived {
    fn publish(
        _: &mut Solver,
        _: u64,
        _: &[Literal],
        derived: bool,
        _: &[u64],
        registered: Option<u64>,
    ) {
        debug_assert!(derived && registered.is_none());
    }
}

impl Solver {
    pub(in crate::solver) fn add_derived_clause_db_counted(
        &mut self,
        lits: &[Literal],
        hints: &[u64],
        owner: &CountedAdmission,
    ) -> Result<usize> {
        self.prepare_derived_clause_db(lits, owner)?;
        let id = self.cold.next_clause_id;
        let trace = self.cold.clause_trace.as_mut().ok_or_else(|| {
            invalid(
                owner,
                "counted learned insertion requires its live clause trace",
            )
        })?;
        let prepared = trace.prepare_counted_add(id, lits, false, hints, owner)?;
        owner.check()?;
        prepared.commit();
        // No allocation or observer between trace publication and arena/ID
        // publication. The exclusive outer guard poisons authority on unwind.
        Ok(self.add_clause_db_admitted::<CommittedDerived>(lits, true, true, hints))
    }

    fn prepare_derived_clause_db(
        &mut self,
        lits: &[Literal],
        owner: &CountedAdmission,
    ) -> Result<()> {
        owner.admit(16, 0)?;
        if lits.is_empty()
            || lits.len() > u16::MAX as usize
            || self.proof_manager.is_some()
            || self.cold.forward_checker.is_some()
            || self.gc_occ.is_some()
            || self.cold.factor_marks_undo.is_some()
            || self.cold.registered_original_clause_id.is_some()
            || self.cold.clause_ids_disabled
            || self.cold.next_clause_id == 0
            || self.cold.next_clause_id == u64::MAX
            || self.is_original_clause_id(self.cold.next_clause_id)
            || self.cold.diagnostic_trace.is_some()
            || self.two_stage_clause_management
        {
            return Err(invalid(
                owner,
                "selected learned database side effect is not admitted",
            ));
        }
        for lit in lits {
            owner.admit(1, 0)?;
            if lit.variable().index() >= self.num_vars {
                return Err(invalid(owner, "learned database literal is out of bounds"));
            }
        }
        if let Some(witness) = &self.cold.solution_witness {
            if witness.len() != self.num_vars {
                return Err(invalid(owner, "learned witness width mismatch"));
            }
            let mut allowed = false;
            for lit in lits {
                owner.admit(1, 0)?;
                allowed |=
                    witness[lit.variable().index()].is_none_or(|value| value == lit.is_positive());
            }
            if !allowed {
                return Err(invalid(
                    owner,
                    "learned clause contradicts the configured witness",
                ));
            }
        }
        let offset = self.arena.reserve_learned_counted(lits.len(), owner)?;
        self.reserve_derived_identity(offset, owner)?;
        self.provenance.reserve_tag_counted(offset, owner)?;
        // Validation + optional witness + binary factor marks. Arena literal
        // writes were prepaid by reserve_learned_counted; no graph is rescanned.
        owner.admit(lits.len().saturating_mul(3).saturating_add(32), 0)?;
        Ok(())
    }

    fn reserve_derived_identity(&mut self, offset: usize, owner: &CountedAdmission) -> Result<()> {
        let end = offset
            .checked_add(1)
            .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
        let hint = self.cold.clause_ids_reserve_hint;
        if !self.cold.clause_ids.is_allocated() && hint > 0 {
            self.cold
                .clause_ids
                .try_reserve_exact_len_counted(owner, hint)?;
        }
        self.cold.clause_ids.try_reserve_len_counted(owner, end)?;
        owner.admit(end.saturating_sub(self.cold.clause_ids.len()), 0)?;
        if self.cold.incremental_solve_count > 0 {
            let extra = end.saturating_sub(self.cold.clause_birth_solve.len());
            try_reserve(owner, &mut self.cold.clause_birth_solve, extra)?;
            owner.admit(extra, 0)?;
        }
        if self.cold.bcp_learned_1963_identity_profile {
            let extra = end.saturating_sub(self.cold.bcp_learned_clause_birth_conflicts.len());
            try_reserve(
                owner,
                &mut self.cold.bcp_learned_clause_birth_conflicts,
                extra,
            )?;
            owner.admit(extra, 0)?;
        }
        Ok(())
    }
}
