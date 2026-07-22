// Copyright 2026 Andrew Yates
// Public accessor API for cross-crate consumers (ay-sat ForwardChecker adapter).
// Thin wrappers over `pub(super)` internals to provide a stable interface.

use crate::literal::Literal;

use super::DratChecker;

impl DratChecker {
    /// Current trail length. Used for incremental push/pop.
    #[inline]
    pub fn trail_len(&self) -> usize {
        self.trail.len()
    }

    /// Whether the checker has derived a contradiction.
    #[inline]
    pub fn is_inconsistent(&self) -> bool {
        self.inconsistent
    }

    /// Set the inconsistent flag (used by incremental pop to restore state).
    #[inline]
    pub fn set_inconsistent(&mut self, v: bool) {
        self.inconsistent = v;
    }

    /// Undo trail assignments back to `saved_trail_len`.
    #[inline]
    pub fn backtrack_to(&mut self, saved_trail_len: usize) {
        self.backtrack(saved_trail_len);
    }

    /// Evaluate a literal under the current assignment.
    #[inline]
    pub fn lit_value(&self, lit: Literal) -> Option<bool> {
        self.value(lit)
    }

    /// Add a trusted clause (no RUP check). Used for inprocessing transforms
    /// that are sound but not necessarily RUP derivable.
    pub fn add_trusted(&mut self, clause: &[Literal]) {
        if self.inconsistent {
            return;
        }
        self.stats.additions += 1;
        self.add_clause_internal(clause);
    }

    /// Number of live (non-deleted) clauses in the database.
    #[inline]
    pub fn live_clause_count(&self) -> usize {
        self.live_clauses
    }
}
