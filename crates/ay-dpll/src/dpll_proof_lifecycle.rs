// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DPLL(T) proof-trace ownership accessors.

use super::*;

impl<T: TheorySolver> DpllT<'_, T> {
    /// Detach and return the SAT clause trace for terminal reconstruction.
    pub fn take_clause_trace(&mut self) -> Option<ClauseTrace> {
        self.sat.take_clause_trace()
    }

    /// Snapshot the SAT clause trace without detaching it from a reusable solver.
    #[must_use]
    pub fn snapshot_clause_trace(&self) -> Option<ClauseTrace> {
        self.sat.snapshot_clause_trace()
    }

    /// Set the deterministic search-time proof bookkeeping work budget.
    ///
    /// `None` is unbudgeted. See [`SatSolver::set_proof_bookkeeping_budget`].
    ///
    /// # Panics
    ///
    /// Panics for `Some` unless a live synthesized clause trace is the sole
    /// proof consumer. `None` is always accepted.
    pub fn set_proof_bookkeeping_budget(&mut self, budget: Option<u64>) {
        self.sat.set_proof_bookkeeping_budget(budget);
    }
}
