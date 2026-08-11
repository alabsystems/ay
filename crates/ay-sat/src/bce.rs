// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Blocked Clause Elimination (BCE)
//!
//! A clause C is blocked on literal L if for every clause D containing ~L,
//! the resolvent of C and D on L is a tautology (contains both a literal and
//! its negation). If a clause is blocked, it can be safely removed without
//! changing satisfiability.
//!
//! BCE is a powerful preprocessing/inprocessing technique that can significantly
//! reduce formula size, especially on structured instances.
//!
//! Reference: Järvisalo, Biere, Heule, "Blocked Clause Elimination", TACAS 2010.

use crate::clause_arena::ClauseArena;
use crate::lit_marks::LitMarks;
use crate::literal::{Literal, Variable};

#[cfg(test)]
mod tests;

/// Maximum number of clauses to check per blocked literal candidate
const MAX_RESOLUTION_CHECKS: usize = 50;

/// Statistics for BCE operations
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct BCEStats {
    /// Number of blocked clauses eliminated
    pub clauses_eliminated: u64,
    /// Number of blocking checks performed
    pub checks_performed: u64,
    /// Number of clauses skipped (too many resolutions)
    pub skipped_expensive: u64,
    /// Number of BCE rounds
    pub rounds: u64,
    /// Eliminations taken on the PURE arm — the blocking literal's negation
    /// occurs nowhere, so the clause could never have propagated onto it and
    /// removing it costs no unit propagation.
    ///
    /// The complement (`clauses_eliminated - pure_blocked`) is the
    /// tautological-resolvent arm, which removes a LIVE implication. Callers
    /// that depend on the surviving implication structure — MaxSAT's AM1
    /// clique-cover mining reads the binary conflict graph — need to tell the
    /// two apart: a reduction that is mostly pure is free, a reduction that is
    /// mostly non-pure can destroy the very structure they mine.
    pub pure_blocked: u64,
}

/// Information about an eliminated blocked clause
#[derive(Debug, Clone)]
pub(crate) struct EliminatedClause {
    /// Index of the eliminated clause in the clause database
    pub clause_idx: usize,
    /// The blocking literal (witness) - setting this true satisfies the clause
    pub blocking_literal: Literal,
}

/// Occurrence list for BCE — uses the shared `OccList` type.
pub(crate) type BCEOccList = crate::occ_list::OccList;

/// Blocked Clause Elimination engine
#[allow(clippy::upper_case_acronyms)] // -D warnings overrides crate-level #![allow]
pub(crate) struct BCE {
    /// Occurrence lists
    occ: BCEOccList,
    /// Statistics
    stats: BCEStats,
    /// Clauses that have been checked and found not blocked (avoid rechecking)
    checked: Vec<bool>,
    /// Reusable buffer for occurrence indices (avoids per-call allocations)
    occ_buf: Vec<usize>,
    /// Reusable buffer for elimination candidates (avoids per-round allocations)
    candidate_buf: Vec<usize>,
}

impl BCE {
    /// Create a new BCE engine for n variables
    pub(crate) fn new(_num_vars: usize) -> Self {
        Self {
            // Sized on first use by the BCE entry point, which calls
            // `ensure_num_vars` before rebuilding. `OccList::new(n)` commits
            // 128 resident bytes per variable, on every instance, whether or
            // not BCE ever runs.
            occ: BCEOccList::new(0),
            stats: BCEStats::default(),
            checked: Vec::new(),
            occ_buf: Vec::new(),
            candidate_buf: Vec::new(),
        }
    }

    /// Ensure internal buffers can handle `num_vars` variables.
    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        self.occ.ensure_num_vars(num_vars);
    }

    /// Get statistics
    pub(crate) fn stats(&self) -> &BCEStats {
        &self.stats
    }

    /// Restore previously saved statistics after compaction recreates the engine.
    pub(crate) fn restore_stats(&mut self, stats: BCEStats) {
        self.stats = stats;
    }

    /// Initialize/rebuild occurrence lists from clause database.
    ///
    /// Only includes irredundant (non-learned) clauses, matching CaDiCaL's
    /// `block_schedule` (block.cpp:167-179) which skips redundant clauses.
    /// Learned clauses are redundant by definition and can be deleted at any
    /// time, so they do not affect blocked clause soundness.
    pub(crate) fn rebuild(&mut self, clauses: &ClauseArena) {
        self.occ.clear();
        self.checked = vec![false; clauses.len()];

        for idx in clauses.indices() {
            if clauses.is_empty_clause(idx) || clauses.is_learned(idx) {
                continue;
            }
            self.occ.add_clause(idx, clauses.literals(idx));
        }
    }

    /// Use a pre-built occurrence list (from BVE's persistent occ lists, #8096)
    /// instead of rebuilding from scratch.
    ///
    /// When BVE's occ lists are already populated and incrementally maintained,
    /// BCE can reuse them directly. This avoids the O(clause_literals) rebuild
    /// cost each BCE round.
    ///
    /// The caller must ensure the provided occ list contains only irredundant
    /// clauses and is consistent with the current clause database.
    pub(crate) fn adopt_occ_list(&mut self, occ: &crate::occ_list::OccList, clauses: &ClauseArena) {
        // Clone the occ list so BCE can modify it during elimination
        // (removing eliminated clauses from occ lists).
        // Uses OccList::clone_from_other to rebuild both the occ vecs and
        // the position maps so that remove_clause has O(1) lookup (#3036).
        self.occ.clone_from_other(occ);
        self.checked = vec![false; clauses.len()];
    }

    /// Check if resolving two clauses on a variable produces a tautology
    ///
    /// Returns true if the resolvent would be a tautology.
    fn is_tautological_resolvent_with_marks(
        &mut self,
        clause_c: &[Literal],
        clause_d: &[Literal],
        pivot_var: Variable,
        marks: &mut LitMarks,
    ) -> bool {
        // CaDiCaL block.cpp:49-52: clause and pivot preconditions
        debug_assert!(
            !clause_c.is_empty() && !clause_d.is_empty(),
            "BUG: tautological resolvent check with empty clause",
        );
        debug_assert!(
            clause_c.iter().any(|l| l.variable() == pivot_var),
            "BUG: pivot {pivot_var:?} not in clause_c",
        );
        debug_assert!(
            clause_d.iter().any(|l| l.variable() == pivot_var),
            "BUG: pivot {pivot_var:?} not in clause_d",
        );
        // Mark literals from clause C (except the pivot).
        // Only clause_c is marked; clause_d is read-only.
        for &lit in clause_c {
            if lit.variable() != pivot_var {
                marks.mark(lit);
            }
        }

        // Check if any literal from clause D (except pivot) has opposite
        // polarity to its mark from clause C — that means the resolvent
        // would contain both x and ¬x, making it a tautology.
        let is_taut = clause_d
            .iter()
            .any(|&lit| lit.variable() != pivot_var && marks.get(lit.variable()) == -lit.sign_i8());

        // Single clear path — only clause_c was marked.
        marks.clear_clause(clause_c);
        // Postcondition: marks must be fully cleared
        debug_assert!(
            clause_c.iter().all(|l| marks.get(l.variable()) == 0),
            "BUG: marks not cleared after tautology check",
        );
        is_taut
    }

    /// Test helper wrapper using a temporary mark array.
    #[cfg(test)]
    fn is_tautological_resolvent(
        &mut self,
        clause_c: &[Literal],
        clause_d: &[Literal],
        pivot_var: Variable,
    ) -> bool {
        let mut marks = LitMarks::new(self.occ.occ.len() / 2);
        self.is_tautological_resolvent_with_marks(clause_c, clause_d, pivot_var, &mut marks)
    }

    /// Check if a clause is blocked on a given literal
    ///
    /// A clause C is blocked on literal L if for every clause D containing ~L,
    /// the resolvent of C and D on L is a tautology.
    fn is_blocked_with_marks(
        &mut self,
        clause_idx: usize,
        blocking_lit: Literal,
        clauses: &ClauseArena,
        marks: &mut LitMarks,
    ) -> bool {
        // CaDiCaL block.cpp:49: clause index in range
        debug_assert!(
            clause_idx < clauses.len(),
            "BUG: is_blocked: clause_idx {clause_idx} out of range",
        );
        if clauses.is_empty_clause(clause_idx) {
            return false;
        }
        // CaDiCaL block.cpp:49: blocking literal must appear in the clause
        debug_assert!(
            clauses.literals(clause_idx).contains(&blocking_lit),
            "BUG: blocking literal {blocking_lit:?} not in clause {clause_idx}",
        );
        let clause_c = clauses.literals(clause_idx);

        // Get clauses containing the negation of the blocking literal
        // Copy into reusable buffer to avoid borrow issues
        let neg_lit = blocking_lit.negated();
        self.occ_buf.clear();
        self.occ_buf.extend_from_slice(self.occ.get(neg_lit));

        // If no clauses contain ~L, the clause is trivially blocked
        if self.occ_buf.is_empty() {
            // PURE arm: nothing can resolve on ~L, so this deletion removes no
            // reachable propagation (see BCEStats::pure_blocked).
            self.stats.pure_blocked += 1;
            return true;
        }

        // Too many resolution partners - skip for efficiency
        if self.occ_buf.len() > MAX_RESOLUTION_CHECKS {
            self.stats.skipped_expensive += 1;
            return false;
        }

        let pivot_var = blocking_lit.variable();

        // Check each clause D containing ~L
        // Use index-based iteration to avoid borrow conflicts with mutable method calls
        let occ_len = self.occ_buf.len();
        for i in 0..occ_len {
            let d_idx = self.occ_buf[i];
            if d_idx == clause_idx {
                continue; // Skip self
            }
            if d_idx >= clauses.len() || clauses.is_empty_clause(d_idx) {
                continue;
            }

            self.stats.checks_performed += 1;

            // If any resolvent is not tautological, the clause is not blocked on L
            if !self.is_tautological_resolvent_with_marks(
                clause_c,
                clauses.literals(d_idx),
                pivot_var,
                marks,
            ) {
                return false;
            }
        }

        // All resolvents are tautological - clause is blocked
        true
    }

    /// Test helper wrapper using a temporary mark array.
    #[cfg(test)]
    fn is_blocked(
        &mut self,
        clause_idx: usize,
        blocking_lit: Literal,
        clauses: &ClauseArena,
    ) -> bool {
        let mut marks = LitMarks::new(self.occ.occ.len() / 2);
        self.is_blocked_with_marks(clause_idx, blocking_lit, clauses, &mut marks)
    }

    /// Find a blocking literal for a clause
    ///
    /// Returns Some(literal) if the clause is blocked on that literal, None otherwise.
    /// The `frozen` slice contains reference counts - a variable is frozen if its count > 0.
    /// Frozen literals are skipped as blocking candidates (per CaDiCaL behavior).
    #[cfg(test)]
    fn find_blocking_literal(
        &mut self,
        clause_idx: usize,
        clauses: &ClauseArena,
        frozen: &[u32],
    ) -> Option<Literal> {
        let mut marks = LitMarks::new(self.occ.occ.len() / 2);
        self.find_blocking_literal_with_marks(clause_idx, clauses, frozen, &mut marks)
    }

    fn find_blocking_literal_with_marks(
        &mut self,
        clause_idx: usize,
        clauses: &ClauseArena,
        frozen: &[u32],
        marks: &mut LitMarks,
    ) -> Option<Literal> {
        if clauses.is_empty_clause(clause_idx) || clauses.len_of(clause_idx) < 2 {
            return None;
        }
        let lits = clauses.literals(clause_idx);

        // Try each literal as a potential blocking literal.
        // Skip frozen literals (per CaDiCaL behavior, #1482).
        for &lit in lits {
            let var_idx = lit.variable().index();
            if var_idx < frozen.len() && frozen[var_idx] > 0 {
                continue;
            }
            if self.is_blocked_with_marks(clause_idx, lit, clauses, marks) {
                return Some(lit);
            }
        }
        None
    }

    /// Run BCE as inprocessing
    ///
    /// Attempts to eliminate blocked clauses to simplify the formula.
    /// Should be called at decision level 0 (e.g., after a restart).
    ///
    /// The `frozen` slice contains reference counts - a variable is frozen if its count > 0.
    /// Frozen literals will not be used as blocking candidates.
    ///
    /// Returns a list of eliminated clauses with their blocking literals (for reconstruction).
    #[cfg(test)]
    pub(crate) fn run_elimination(
        &mut self,
        clauses: &ClauseArena,
        frozen: &[u32],
        max_eliminations: usize,
    ) -> Vec<EliminatedClause> {
        let mut marks = LitMarks::new(self.occ.occ.len() / 2);
        self.run_elimination_with_marks(clauses, frozen, max_eliminations, &mut marks)
    }

    pub(crate) fn run_elimination_with_marks(
        &mut self,
        clauses: &ClauseArena,
        frozen: &[u32],
        max_eliminations: usize,
        marks: &mut LitMarks,
    ) -> Vec<EliminatedClause> {
        self.stats.rounds += 1;
        let mut eliminated = Vec::new();

        // Reuse candidate buffer across rounds to avoid per-round allocation.
        // Check learned clauses first (more likely to be blocked and less important),
        // then check non-learned clauses.
        self.candidate_buf.clear();

        // First pass: learned clauses
        for idx in clauses.indices() {
            if clauses.is_empty_clause(idx) || clauses.len_of(idx) < 2 {
                continue;
            }
            if idx < self.checked.len() && self.checked[idx] {
                continue;
            }
            if clauses.is_learned(idx) {
                self.candidate_buf.push(idx);
            }
        }

        // Second pass: non-learned clauses
        for idx in clauses.indices() {
            if clauses.is_empty_clause(idx) || clauses.len_of(idx) < 2 || clauses.is_learned(idx) {
                continue;
            }
            if idx < self.checked.len() && self.checked[idx] {
                continue;
            }
            self.candidate_buf.push(idx);
        }

        for i in 0..self.candidate_buf.len().min(max_eliminations * 2) {
            let clause_idx = self.candidate_buf[i];

            // Skip if already eliminated in this round
            if eliminated
                .iter()
                .any(|e: &EliminatedClause| e.clause_idx == clause_idx)
            {
                continue;
            }

            // Skip empty or unit clauses
            if clause_idx >= clauses.len()
                || clauses.is_empty_clause(clause_idx)
                || clauses.len_of(clause_idx) < 2
            {
                continue;
            }

            // Try to find a blocking literal
            if let Some(blocking_literal) =
                self.find_blocking_literal_with_marks(clause_idx, clauses, frozen, marks)
            {
                eliminated.push(EliminatedClause {
                    clause_idx,
                    blocking_literal,
                });
                self.stats.clauses_eliminated += 1;

                // Update occurrence lists
                self.occ
                    .remove_clause(clause_idx, clauses.literals(clause_idx));

                if eliminated.len() >= max_eliminations {
                    break;
                }
            } else {
                // Mark as checked to avoid rechecking
                if clause_idx < self.checked.len() {
                    self.checked[clause_idx] = true;
                }
            }
        }

        eliminated
    }
}
