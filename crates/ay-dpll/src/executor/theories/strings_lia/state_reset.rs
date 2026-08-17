// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::incremental_state::IncrementalTheoryState;

impl IncrementalTheoryState {
    /// Reset state whose identities belong to the discarded SLIA SAT solver.
    ///
    /// Rebuilding the solver restarts its original-clause IDs at one. Keeping
    /// either proof ledger would let a later escalation pass reuse authority
    /// slots authored by an earlier solver instance.
    pub(crate) fn reset_rebuilt_slia_solver(&mut self) {
        self.lia_persistent_sat = None;
        self.encoded_assertions.clear();
        self.clausification_proofs.clear();
        self.original_clause_theory_proofs.clear();
    }
}
