// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Copies of the session's persistent lanes for one query-local window.
//!
//! A `check-sat-assuming` window merged into the assertion vector must never
//! reach the session's own lanes: they encode every root they are handed and
//! activate it at the current depth, at depth 0 for good. Solving the window on
//! a COPY keeps what the session learned from its permanent assertions (the
//! warm state origin/main's non-incremental scoped route used, and leaked) and
//! drops everything the window put there with the copy.
//!
//! The SAT solvers are copied with `Solver::clone_for_incremental`, which does
//! not carry proof logging, so a copy serves only a query that demands no
//! checked certificate (`solve_scoped_window`, check_sat_assuming/stateless_subsolve.rs).

use super::{IncrementalBvState, IncrementalTheoryState, SatSolver};

impl IncrementalTheoryState {
    /// A copy of this lane for one query-local window, or `None` when the lane
    /// holds a warm theory solver (`--lra-warm-theory`), which cannot be copied.
    pub(crate) fn fork_for_window(&self) -> Option<Self> {
        if self.persist_theory.is_some() {
            return None;
        }
        Some(Self {
            persistent_sat: self
                .persistent_sat
                .as_ref()
                .map(SatSolver::clone_for_incremental),
            persist_theory: None,
            lia_persistent_sat: self
                .lia_persistent_sat
                .as_ref()
                .map(SatSolver::clone_for_incremental),
            encoded_assertions: self.encoded_assertions.clone(),
            assertion_activation_scope: self.assertion_activation_scope.clone(),
            tseitin_state: self.tseitin_state.clone(),
            lia_tseitin_state: self.lia_tseitin_state.clone(),
            lia_encoded_assertions: self.lia_encoded_assertions.clone(),
            lia_assertion_activation_scope: self.lia_assertion_activation_scope.clone(),
            clausification_proofs: self.clausification_proofs.clone(),
            original_clause_theory_proofs: self.original_clause_theory_proofs.clone(),
            theory_lemmas: self.theory_lemmas.clone(),
            theory_lemma_keys: self.theory_lemma_keys.clone(),
            proof_scope_starts: self.proof_scope_starts.clone(),
            scope_depth: self.scope_depth,
            pending_push: self.pending_push,
            lia_derived_assertions: self.lia_derived_assertions.clone(),
            theory_atoms: self.theory_atoms.clone(),
            pre_push_assertions: self.pre_push_assertions.clone(),
            needs_activation_reassert: self.needs_activation_reassert,
            theory_conflicts: self.theory_conflicts,
            theory_propagations: self.theory_propagations,
            round_trips: self.round_trips,
            sat_solve_secs: self.sat_solve_secs,
            theory_sync_secs: self.theory_sync_secs,
            theory_check_secs: self.theory_check_secs,
            sat_warm_state: self.sat_warm_state.clone(),
            scratch_var_to_term: self.scratch_var_to_term.clone(),
            bound_axiom_cache: self.bound_axiom_cache.clone(),
            bool_uf_arg_cache: self.bool_uf_arg_cache.clone(),
            dead_atom_stats: self.dead_atom_stats,
        })
    }
}

impl IncrementalBvState {
    /// A copy of this lane for one query-local window.
    pub(crate) fn fork_for_window(&self) -> Self {
        Self {
            term_to_bits: self.term_to_bits.clone(),
            next_bv_var: self.next_bv_var,
            scope_depth: self.scope_depth,
            pending_pushes: self.pending_pushes,
            persistent_sat: self
                .persistent_sat
                .as_ref()
                .map(SatSolver::clone_for_incremental),
            tseitin_state: self.tseitin_state.clone(),
            encoded_assertions: self.encoded_assertions.clone(),
            assertion_activation_scope: self.assertion_activation_scope.clone(),
            sat_num_vars: self.sat_num_vars,
            bv_var_offset: self.bv_var_offset,
            emitted_bv_eq_congruence_pairs: self.emitted_bv_eq_congruence_pairs.clone(),
            predicate_to_var: self.predicate_to_var.clone(),
            bool_to_var: self.bool_to_var.clone(),
            linked_equivalence_terms: self.linked_equivalence_terms.clone(),
            bv_ite_conditions: self.bv_ite_conditions.clone(),
            delayed_ops: self.delayed_ops.clone(),
            congruence_partial: self.congruence_partial,
        }
    }
}
