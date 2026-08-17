// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fresh-SAT authority-ledger alignment for incremental pipelines.

use super::{IncrementalTheoryState, SatSolver, TseitinState};

impl IncrementalTheoryState {
    /// Construct a fresh SAT solver whose clause IDs start against empty
    /// original-clause proof-authority ledgers.
    pub(crate) fn fresh_sat_solver(&mut self, total_vars: usize, random_seed: u64) -> SatSolver {
        self.clear_original_clause_authority();
        let mut solver = SatSolver::new(total_vars);
        solver.set_random_seed(random_seed);
        solver
    }

    /// Reset LIA-specific SAT solver and encoding state (#6853).
    ///
    /// LIA preprocessing can change the assertion set between check-sats.
    /// Accumulated global Tseitin definition clauses from prior check-sats
    /// over-constrain the variable space when combined with new activation
    /// clauses, causing false UNSAT. Resetting the LIA state before each
    /// check-sat ensures a clean encoding.
    pub(crate) fn reset_lia_sat(&mut self) {
        self.lia_persistent_sat = None;
        self.lia_encoded_assertions.clear();
        self.lia_assertion_activation_scope.clear();
        self.lia_tseitin_state = TseitinState::new();
        self.clear_original_clause_authority();
    }

    /// Clear authority rows before any replacement SAT solver reuses clause IDs.
    ///
    /// A new solver issues original-clause IDs from one, while these ledgers are
    /// indexed by `clause_id - 1`. Rows authored by a discarded solver would
    /// therefore collide with identically numbered clauses in its replacement.
    /// The next encode loop rebuilds both ledgers against the fresh numbering.
    fn clear_original_clause_authority(&mut self) {
        self.clausification_proofs.clear();
        self.original_clause_theory_proofs.clear();
    }
}

#[cfg(test)]
mod tests {
    use ay_core::TermId;

    use super::*;

    #[test]
    fn fresh_sat_solver_starts_against_empty_authority_ledgers() {
        let mut state = IncrementalTheoryState::new();
        state.clausification_proofs.push(None);
        state.original_clause_theory_proofs.push(None);

        let solver = state.fresh_sat_solver(3, 17);

        assert_eq!(solver.num_variables(), 3);
        assert_eq!(solver.random_seed(), 17);
        assert!(state.clausification_proofs.is_empty());
        assert!(state.original_clause_theory_proofs.is_empty());
    }

    #[test]
    fn reset_lia_sat_clears_encoding_and_authority_state() {
        let mut state = IncrementalTheoryState::new();
        state.lia_persistent_sat = Some(SatSolver::new(2));
        state.lia_encoded_assertions.insert(TermId::new(1), 7);
        state
            .lia_assertion_activation_scope
            .insert(TermId::new(1), 2);
        state.lia_tseitin_state.next_var = 9;
        state.clausification_proofs.push(None);
        state.original_clause_theory_proofs.push(None);

        state.reset_lia_sat();

        assert!(state.lia_persistent_sat.is_none());
        assert!(state.lia_encoded_assertions.is_empty());
        assert!(state.lia_assertion_activation_scope.is_empty());
        assert_eq!(state.lia_tseitin_state.next_var, 1);
        assert!(state.clausification_proofs.is_empty());
        assert!(state.original_clause_theory_proofs.is_empty());
    }
}
