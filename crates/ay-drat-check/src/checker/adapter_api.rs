// Copyright 2026 Andrew Yates
// Public diagnostic adapter API for ay-sat's cross-crate ForwardChecker.
// Unchecked mutations permanently disable authoritative proof conclusion.

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

    /// Set the inconsistent flag for diagnostic incremental state restoration.
    ///
    /// This is not proof evidence. Calling it permanently prevents
    /// [`Self::conclude_unsat`] from returning an authoritative verdict.
    #[inline]
    pub fn set_inconsistent(&mut self, v: bool) {
        self.authority_tainted = true;
        self.inconsistent = v;
    }

    /// Undo diagnostic trail assignments back to `saved_trail_len`.
    ///
    /// Calling this permanently disables authoritative proof conclusion.
    #[inline]
    pub fn backtrack_to(&mut self, saved_trail_len: usize) {
        self.authority_tainted = true;
        self.backtrack(saved_trail_len);
    }

    /// Evaluate a literal under the current assignment.
    #[inline]
    pub fn lit_value(&self, lit: Literal) -> Option<bool> {
        self.value(lit)
    }

    /// Add an unchecked clause for diagnostic inprocessing validation.
    ///
    /// The clause is not RUP/RAT checked. Calling this permanently disables
    /// authoritative proof conclusion, even if the clause is non-empty.
    pub fn add_trusted(&mut self, clause: &[Literal]) {
        self.authority_tainted = true;
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
