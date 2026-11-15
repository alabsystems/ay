// Copyright 2026 Andrew Yates
// Clause additions and deletions: the per-step operations of forward DRAT
// checking, and the one-shot bulk `verify` that drives them over a proof.

use super::{ConcludeResult, DratChecker};
use crate::drat_parser::ProofStep;
use crate::error::DratCheckError;
use crate::literal::Literal;

impl DratChecker {
    fn process_unit(&mut self, lit: Literal) {
        match self.value(lit) {
            Some(true) => {}
            Some(false) => self.inconsistent = true,
            None => {
                self.assign(lit);
                if !self.propagate() {
                    self.inconsistent = true;
                }
            }
        }
    }

    /// O(n) tautology check using per-literal markers (drat-trim pattern).
    /// Callers must ensure_capacity() for all literals before calling.
    pub(super) fn is_tautology(&mut self, clause: &[Literal]) -> bool {
        let mut found = false;
        for &lit in clause {
            if self.marks[lit.negated().index()] {
                found = true;
                break;
            }
            self.marks[lit.index()] = true;
        }
        for &lit in clause {
            self.marks[lit.index()] = false;
        }
        found
    }

    pub(super) fn add_clause_internal(&mut self, clause: &[Literal]) {
        for &lit in clause {
            if let Err(refusal) = self.ensure_capacity(lit.variable().index()) {
                // The clause cannot be stored. Dropping it only weakens the
                // database, and the sticky refusal keeps any UNSAT conclusion
                // from resting on the incomplete formula.
                self.record_dense_refusal(refusal);
                return;
            }
        }
        // Filter falsified literals into a retained scratch buffer to avoid
        // per-call heap allocation (#5626, allocation #3).
        //
        // Take the buffer out of `self` to avoid borrow-checker conflicts:
        // the filter closure needs `self.assigns` (via `value`) while `extend`
        // needs `&mut buf`. Putting it back after is zero-cost (just pointer swap).
        let mut buf = std::mem::take(&mut self.simplify_buf);
        buf.clear();
        buf.extend(
            clause
                .iter()
                .copied()
                .filter(|&lit| self.value(lit) != Some(false)),
        );
        if self.is_tautology(&buf) {
            self.simplify_buf = buf;
            return;
        }
        if buf.iter().any(|&lit| self.value(lit) == Some(true)) {
            self.simplify_buf = buf;
            return;
        }
        match buf.len() {
            0 => {
                self.simplify_buf = buf;
                self.inconsistent = true;
            }
            1 => {
                let unit = buf[0];
                let owned = buf.clone();
                self.simplify_buf = buf;
                self.process_unit(unit);
                self.insert_clause(owned);
            }
            _ => {
                let owned = buf.clone();
                self.simplify_buf = buf;
                self.insert_clause(owned);
            }
        }
    }

    // -- Public API --

    /// Add an original (input formula) clause. No RUP/RAT check.
    pub fn add_original(&mut self, clause: &[Literal]) {
        if self.inconsistent {
            return;
        }
        self.stats.original = self.stats.original.saturating_add(1);
        self.add_clause_internal(clause);
    }

    /// Add a derived clause. Returns `Ok(())` if RUP (or RAT) implied.
    pub fn add_derived(&mut self, clause: &[Literal]) -> Result<(), DratCheckError> {
        if self.inconsistent && !clause.is_empty() {
            self.stats.additions = self.stats.additions.saturating_add(1);
            return Ok(());
        }
        self.stats.additions = self.stats.additions.saturating_add(1);
        for &lit in clause {
            let variable = lit.variable().index();
            if let Err(refusal) = self.ensure_capacity(variable) {
                self.stats.failures = self.stats.failures.saturating_add(1);
                return Err(refusal.step_error(variable, self.stats.additions));
            }
        }
        if self.is_tautology(clause) {
            return Ok(());
        }
        if self.check_rup(clause) {
            self.add_clause_internal(clause);
            return Ok(());
        }
        if self.check_rat && !clause.is_empty() && self.check_rat_for_clause(clause) {
            self.add_clause_internal(clause);
            return Ok(());
        }
        self.stats.failures = self.stats.failures.saturating_add(1);
        let lits: Vec<_> = clause.iter().map(ToString::to_string).collect();
        Err(DratCheckError::NotImplied {
            clause: format!("{lits:?}"),
            step: self.stats.additions,
            kind: if self.check_rat { "RUP/RAT " } else { "RUP " },
        })
    }

    /// Delete a clause from the database.
    ///
    /// Pseudo-unit protection (drat-trim.c:806-814): if the clause is the
    /// current propagation reason for its first literal, the deletion is
    /// silently ignored. Deleting a reason clause would corrupt the BCP
    /// trail -- the literal was assigned because of this clause, and removing
    /// it while keeping the assignment breaks the invariant that every
    /// assigned literal has a valid reason.
    pub fn delete_clause(&mut self, clause: &[Literal]) {
        self.stats.deletions = self.stats.deletions.saturating_add(1);
        for &lit in clause {
            if self.ensure_capacity(lit.variable().index()).is_err() {
                // No stored clause mentions a variable outside the universe,
                // so this deletion cannot match anything.
                self.stats.missed_deletes = self.stats.missed_deletes.saturating_add(1);
                return;
            }
        }
        let hash = Self::hash_clause(clause);
        let bucket = self.bucket_idx(hash);
        if let Some(cidx) = self.find_clause_idx(clause) {
            // Pseudo-unit check: if this clause is the reason for its first
            // literal's assignment, skip the deletion (drat-trim.c:807).
            if self.is_reason_for_first_lit(cidx) {
                self.stats.pseudo_unit_skips = self.stats.pseudo_unit_skips.saturating_add(1);
                return;
            }
            if let Some(bucket_pos) = self.hash_buckets[bucket]
                .iter()
                .position(|&candidate| candidate == cidx)
            {
                self.hash_buckets[bucket].swap_remove(bucket_pos);
            }
            self.unlink_clause(cidx);
            // A found clause is live, so the count is at least one here.
            self.live_clauses = self.live_clauses.saturating_sub(1);
        } else {
            self.stats.missed_deletes = self.stats.missed_deletes.saturating_add(1);
        }
    }

    /// Check if a clause is the propagation reason for its first literal.
    ///
    /// drat-trim.c:807: `S->reason[abs(lemmas[0])] - 1 == lemmas - S->DB`
    /// Our BCP engine reorders clause[0] to the propagated literal
    /// (propagation.rs visit_clause/visit_long), matching drat-trim.c:212.
    pub(super) fn is_reason_for_first_lit(&self, cidx: usize) -> bool {
        let clause = match &self.clauses[cidx] {
            // Top-level unit clauses are assigned without a reason index.
            // Refuse to delete a currently satisfied unit anyway: retaining a
            // redundant clause is always safe, while unlinking it and keeping
            // the assignment makes later RUP/RAT checks unsound.
            Some(c) if c.len() == 1 => return self.value(c[0]) == Some(true),
            Some(c) if c.len() >= 2 => c,
            _ => return false,
        };
        let var_idx = clause[0].variable().index();
        var_idx < self.reasons.len() && self.reasons[var_idx] == Some(cidx)
    }

    /// Verify a complete proof against a formula on a fresh checker.
    ///
    /// This bulk API is one-shot: reusing a checker could bind retained clauses
    /// or an earlier contradiction to a different formula, so every later call
    /// fails closed. Incremental diagnostic users should use the individual
    /// adapter methods and must not treat that state as proof authority.
    pub fn verify(
        &mut self,
        clauses: &[Vec<Literal>],
        steps: &[ProofStep],
    ) -> Result<(), DratCheckError> {
        self.begin_bulk_verify()?;
        for clause in clauses {
            self.add_original(clause);
        }
        if self.inconsistent {
            return match self.conclude_unsat() {
                ConcludeResult::Verified => Ok(()),
                ConcludeResult::Failed(reason) => Err(DratCheckError::from(reason)),
            };
        }
        for (i, step) in steps.iter().enumerate() {
            match step {
                ProofStep::Add(lits) => {
                    self.add_derived(lits)
                        .map_err(|e| DratCheckError::StepFailed {
                            step: i.saturating_add(1),
                            source: Box::new(e),
                        })?;
                }
                ProofStep::Delete(lits) => {
                    self.delete_clause(lits);
                }
                ProofStep::AddPr { clause, .. } => {
                    // PR/DPR additions are outside the RUP/RAT trusted fragment.
                    // Fail closed: never silently accept an unverified PR step.
                    return Err(DratCheckError::StepFailed {
                        step: i.saturating_add(1),
                        source: Box::new(DratCheckError::UnsupportedPr {
                            clause: format!("{clause:?}"),
                        }),
                    });
                }
            }
        }
        match self.conclude_unsat() {
            ConcludeResult::Verified => Ok(()),
            ConcludeResult::Failed(reason) => Err(DratCheckError::from(reason)),
        }
    }
}
