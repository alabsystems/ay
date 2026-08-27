// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ownership transitions for attached proof outputs and in-memory traces.

use super::*;

#[derive(Clone, Copy)]
enum ProofLifecycleRequirement {
    NoClauseAuthorityForInternalLrat,
    NoClauseAuthorityForClauseTrace,
    NoRetainedProofStateForIc3,
    LiveTraceForBudget,
    ExhaustedBudgetForDegrade,
}

impl Solver {
    /// Enforce every proof-lifecycle precondition through one release
    /// assertion before its caller mutates solver state.
    fn assert_proof_lifecycle(&self, requirement: ProofLifecycleRequirement) {
        let (valid, message) = match requirement {
            ProofLifecycleRequirement::NoClauseAuthorityForInternalLrat => (
                self.has_no_prior_clause_authority()
                    && self.cold.proof_bookkeeping_budget.is_none(),
                "BUG: enable_lrat() must be called before adding any clauses and without a proof bookkeeping budget",
            ),
            ProofLifecycleRequirement::NoClauseAuthorityForClauseTrace => (
                self.has_no_prior_clause_authority(),
                "BUG: enable_clause_trace() must be called before adding any clauses",
            ),
            ProofLifecycleRequirement::NoRetainedProofStateForIc3 => (
                self.proof_manager.is_none()
                    && !self.cold.lrat_enabled
                    && !self.cold.internal_lrat_enabled
                    && self.cold.clause_trace.is_none()
                    && self.cold.proof_bookkeeping_budget.is_none()
                    && self.cold.backward_proof_limits.is_none()
                    && self.cold.backward_proof_failure.is_none(),
                "BUG: set_ic3_mode() requires all attached or retained proof state to be detached",
            ),
            ProofLifecycleRequirement::LiveTraceForBudget => (
                self.proof_manager.is_none()
                    && !self.cold.internal_lrat_enabled
                    && self.cold.lrat_enabled
                    && self.has_live_clause_trace(),
                "BUG: a proof bookkeeping budget requires one live synthesized clause trace",
            ),
            ProofLifecycleRequirement::ExhaustedBudgetForDegrade => (
                self.proof_manager.is_none()
                    && !self.cold.internal_lrat_enabled
                    && self.cold.clause_trace.is_some()
                    && self.cold.proof_bookkeeping_budget == Some(0),
                "BUG: proof bookkeeping degradation requires an exhausted synthesized clause trace",
            ),
        };
        assert!(valid, "{message}");
    }

    fn has_no_prior_clause_authority(&self) -> bool {
        self.arena.is_empty() && self.cold.original_ledger.is_empty() && !self.has_empty_clause
    }

    pub(in crate::solver) fn assert_can_enable_internal_lrat(&self) {
        self.assert_proof_lifecycle(ProofLifecycleRequirement::NoClauseAuthorityForInternalLrat);
    }

    pub(in crate::solver) fn assert_can_enable_clause_trace(&self) {
        self.assert_proof_lifecycle(ProofLifecycleRequirement::NoClauseAuthorityForClauseTrace);
    }

    pub(in crate::solver) fn assert_can_enter_ic3_mode(&self) {
        self.assert_proof_lifecycle(ProofLifecycleRequirement::NoRetainedProofStateForIc3);
    }

    pub(in crate::solver) fn assert_can_set_proof_bookkeeping_budget(&self) {
        self.assert_proof_lifecycle(ProofLifecycleRequirement::LiveTraceForBudget);
    }

    pub(in crate::solver) fn assert_can_degrade_proof_bookkeeping(&self) {
        self.assert_proof_lifecycle(ProofLifecycleRequirement::ExhaustedBudgetForDegrade);
    }

    /// Whether the retained trace still owns LRAT bookkeeping.
    ///
    /// An exhausted trace remains attached as fail-closed evidence for its
    /// consumer, but it must not reactivate proof bookkeeping after another
    /// proof consumer is detached.
    pub(in crate::solver) fn has_live_clause_trace(&self) -> bool {
        self.live_clause_trace().is_some()
    }

    pub(in crate::solver) fn live_clause_trace(&self) -> Option<&ClauseTrace> {
        self.cold
            .clause_trace
            .as_ref()
            .filter(|trace| !trace.proof_work_exhausted())
    }

    pub(in crate::solver) fn live_clause_trace_mut(&mut self) -> Option<&mut ClauseTrace> {
        self.cold
            .clause_trace
            .as_mut()
            .filter(|trace| !trace.proof_work_exhausted())
    }

    /// Recompute composite proof state after an ownership transition.
    ///
    /// Output LRAT, explicit internal LRAT, and a live clause trace own LRAT
    /// bookkeeping independently. When the last proof consumer is detached,
    /// discard the old pre-proof control snapshot without restoring it: the
    /// already-clamped controls are the conservative no-proof continuation.
    pub(in crate::solver) fn refresh_proof_consumer_state(&mut self) {
        let output_lrat = self
            .proof_manager
            .as_ref()
            .is_some_and(ProofManager::is_lrat);
        self.cold.lrat_enabled =
            self.cold.internal_lrat_enabled || output_lrat || self.has_live_clause_trace();
        if !self.has_live_clause_trace() {
            self.cold.proof_bookkeeping_budget = None;
        }
        if self.proof_manager.is_some() || self.cold.lrat_enabled {
            self.enforce_inprocessing_proof_overrides();
        } else {
            self.inproc_ctrl_pre_proof = None;
        }
    }

    /// Detach the proof output and normalize the remaining consumer state.
    pub(in crate::solver) fn detach_proof_writer(&mut self) -> Option<ProofOutput> {
        let output = self.proof_manager.take().map(ProofManager::into_output);
        self.cold.backward_proof_limits = None;
        self.cold.backward_proof_failure = None;
        self.refresh_proof_consumer_state();
        output
    }

    /// Take the clause trace, consuming its ownership from the solver.
    ///
    /// Returns `None` only when no trace is attached. An exhausted tombstone
    /// returns `Some` even though [`Self::clause_trace_enabled`] is `false`.
    /// Other proof consumers remain active; otherwise the solver transitions
    /// conservatively to no-proof state.
    pub fn take_clause_trace(&mut self) -> Option<ClauseTrace> {
        let solver_num_vars = self.total_num_vars();
        let scope_assumptions = self.active_scope_assumptions();
        if let Some(t) = self.cold.clause_trace.as_mut() {
            t.stamp_solver_provenance(solver_num_vars, &scope_assumptions);
            // #A2b observability: search-time proof bookkeeping meters used
            // to calibrate the construction work budget.
            tracing::debug!(
                trace_used_bytes = t.used_bytes(),
                trace_entries = t.len(),
                materialize_root_trail_entries =
                    self.stats.lrat_materialize_root_trail_entries
                        + self.stats.lrat_materialize_minimize_root_trail_entries,
                budget_remaining = ?self.cold.proof_bookkeeping_budget,
                "clause trace taken (#A2b bookkeeping meters)"
            );
        }
        let trace = self.cold.clause_trace.take();
        self.refresh_proof_consumer_state();
        trace
    }
}
