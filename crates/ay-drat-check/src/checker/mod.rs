// Copyright 2026 Andrew Yates
// Core DRAT/DRUP proof checker with two-watched-literal BCP engine.
// Originally extracted from ay-sat/src/forward_checker.rs (Biere 2021, CaDiCaL checker parity).

mod adapter_api;
pub mod backward;
mod clause_db;
mod propagation;
mod rat;
mod rup_deps;
pub mod sr;
mod sr_reduct_core;
mod types;

pub use sr::SrChecker;
pub use types::{ConcludeFailure, ConcludeResult, Stats};
pub(crate) use types::{Visit, Watch};

use crate::drat_parser::ProofStep;
use crate::error::DratCheckError;
use crate::literal::Literal;
use rustc_hash::FxHashMap;

const INITIAL_HASH_CAPACITY: usize = 1024;

/// Largest dense variable universe accepted by the checker frontends.
///
/// Each variable owns two polarity slots in both `watches` and `occ_lists`.
/// The ceiling matches AY's supported 58.6M-variable competition giant while
/// rejecting the former 268M-variable worst-case envelope before allocation.
pub const MAX_DENSE_VARS: usize = 1 << 26;

/// Forward DRAT checker.
///
/// Verifies each added clause is either RUP (Reverse Unit Propagation) implied
/// or RAT (Resolution Asymmetric Tautology) with respect to the current clause
/// database. Uses a self-contained 2WL BCP engine.
pub struct DratChecker {
    pub(super) num_vars: usize,
    pub(super) assigns: Vec<Option<bool>>,
    pub(super) trail: Vec<Literal>,
    pub(super) propagate_cursor: usize,
    pub(super) watches: Vec<Vec<Watch>>,
    /// Per-literal live-clause occurrences for RAT candidate lookup.
    pub(super) occ_lists: Vec<Vec<usize>>,
    pub(super) clauses: Vec<Option<Vec<Literal>>>,
    /// Fully unlinked tombstone slots available for reuse.
    pub(super) free_clause_slots: Vec<usize>,
    pub(super) hash_buckets: Vec<Vec<usize>>,
    pub(super) live_clauses: usize,
    pub(super) inconsistent: bool,
    pub(crate) stats: Stats,
    check_rat: bool,
    /// Marker array indexed by literal code for O(n) tautology/duplicate detection.
    /// Size = 2 * num_vars. Avoids O(n^2) nested loops per drat-trim pattern.
    marks: Vec<bool>,
    /// Per-variable reason clause index. Set during BCP when a literal is
    /// propagated by a clause. Used by `rup_deps::collect_conflict_deps` and
    /// `backward::mark_active` for dependency tracking.
    pub(super) reasons: Vec<Option<usize>>,
    /// Clause index of the last BCP conflict. Set by `propagate_watches`
    /// when a conflict is detected. Used by `collect_conflict_deps`.
    pub(super) bcp_conflict_cidx: Option<usize>,
    /// Persistent marker array for conflict analysis (avoids allocation per call).
    pub(super) conflict_marked: Vec<bool>,
    /// Dirty list for `conflict_marked` cleanup.
    pub(super) conflict_marked_dirty: Vec<usize>,
    /// Reusable buffer for RAT resolvent construction.
    pub(super) scratch_resolvent: Vec<Literal>,
    /// Retained scratch for exact, order-independent O(k) clause matching.
    clause_match_counts: FxHashMap<Literal, usize>,
    clause_match_consumed: Vec<Literal>,
    /// Core-first BCP mode. When enabled, `propagate()` processes ACTIVE
    /// watch entries before non-ACTIVE ones (drat-trim.c:196-230).
    /// Toggled by the backward checker.
    pub(super) core_first: bool,
    /// Adaptive prep mode toggle (drat-trim.c:647-652). Turns core-first
    /// on when RUP checks have low indegree (<=2 resolution steps),
    /// off when high (>2). Automatically managed during backward checking.
    pub(super) prep: bool,
    /// Reusable scratch buffer for clause simplification in `add_clause_internal`.
    /// Avoids per-call heap allocation when filtering falsified literals (#5626).
    simplify_buf: Vec<Literal>,
}

impl DratChecker {
    pub fn stats(&self) -> &Stats {
        &self.stats
    }

    /// Conclude the proof as UNSAT. Checks: (1) steps were processed,
    /// (2) no step failures, (3) empty clause derived.
    ///
    /// Unlike LRAT, DRAT has no finalization coverage check.
    /// The reference implementation (CaDiCaL checker.cpp) has no explicit
    /// conclusion API -- it relies on the `inconsistent` flag. This method
    /// provides a structured alternative for API parity with ay-lrat-check.
    pub fn conclude_unsat(&self) -> ConcludeResult {
        if self.stats.failures > 0 {
            return ConcludeResult::Failed(ConcludeFailure::StepFailures);
        }
        if !self.inconsistent {
            return ConcludeResult::Failed(ConcludeFailure::NoEmptyClause);
        }
        ConcludeResult::Verified
    }

    pub fn new(num_vars: usize, check_rat: bool) -> Self {
        Self {
            num_vars,
            assigns: vec![None; num_vars],
            trail: Vec::new(),
            propagate_cursor: 0,
            watches: vec![Vec::new(); num_vars * 2],
            occ_lists: vec![Vec::new(); num_vars * 2],
            clauses: Vec::new(),
            free_clause_slots: Vec::new(),
            hash_buckets: vec![Vec::new(); INITIAL_HASH_CAPACITY],
            live_clauses: 0,
            inconsistent: false,
            stats: Stats::default(),
            check_rat,
            marks: vec![false; num_vars * 2],
            reasons: vec![None; num_vars],
            bcp_conflict_cidx: None,
            conflict_marked: vec![false; num_vars],
            conflict_marked_dirty: Vec::new(),
            scratch_resolvent: Vec::new(),
            clause_match_counts: FxHashMap::default(),
            clause_match_consumed: Vec::new(),
            core_first: false,
            prep: false,
            simplify_buf: Vec::new(),
        }
    }

    pub(super) fn ensure_capacity(&mut self, var_idx: usize) {
        if var_idx >= self.num_vars {
            let new_num_vars = var_idx + 1;
            self.assigns.resize(new_num_vars, None);
            self.watches.resize(new_num_vars * 2, Vec::new());
            self.occ_lists.resize(new_num_vars * 2, Vec::new());
            self.marks.resize(new_num_vars * 2, false);
            self.reasons.resize(new_num_vars, None);
            self.conflict_marked.resize(new_num_vars, false);
            self.num_vars = new_num_vars;
        }
    }

    #[inline]
    pub(super) fn value(&self, lit: Literal) -> Option<bool> {
        let vi = lit.variable().index();
        if vi >= self.num_vars {
            return None;
        }
        self.assigns[vi].map(|v| v == lit.is_positive())
    }

    /// Assign a literal without a reason (used for assumptions in RUP checks).
    ///
    /// Silently skips if the variable is already assigned (robustness against
    /// malformed proofs -- drat-trim does not crash on double-assignment).
    #[inline]
    pub(super) fn assign(&mut self, lit: Literal) {
        let vi = lit.variable().index();
        if self.assigns[vi].is_some() {
            return; // Already assigned -- skip (malformed proof robustness).
        }
        self.assigns[vi] = Some(lit.is_positive());
        self.reasons[vi] = None;
        self.trail.push(lit);
    }

    /// Assign a literal with a reason clause (used during BCP propagation).
    ///
    /// Silently skips if the variable is already assigned (robustness against
    /// malformed proofs -- drat-trim does not crash on double-assignment).
    #[inline]
    pub(super) fn assign_with_reason(&mut self, lit: Literal, reason_cidx: usize) {
        let vi = lit.variable().index();
        if self.assigns[vi].is_some() {
            return; // Already assigned -- skip (malformed proof robustness).
        }
        self.assigns[vi] = Some(lit.is_positive());
        self.reasons[vi] = Some(reason_cidx);
        self.trail.push(lit);
    }

    pub(super) fn backtrack(&mut self, saved_trail_len: usize) {
        while self.trail.len() > saved_trail_len {
            let Some(lit) = self.trail.pop() else {
                break; // Structurally unreachable but safe.
            };
            let vi = lit.variable().index();
            self.assigns[vi] = None;
            self.reasons[vi] = None;
        }
        self.propagate_cursor = saved_trail_len;
    }

    /// Check if `clause` is RUP (Reverse Unit Propagation) implied:
    /// assume the negation of each literal, propagate, check for conflict.
    pub(super) fn check_rup(&mut self, clause: &[Literal]) -> bool {
        self.stats.checks += 1;
        self.bcp_conflict_cidx = None;
        if self.inconsistent {
            return true;
        }
        let saved = self.trail.len();
        if clause.iter().any(|&lit| self.value(lit) == Some(true)) {
            return true;
        }
        for &lit in clause {
            let neg = lit.negated();
            match self.value(neg) {
                Some(true) => {}
                Some(false) => {
                    self.backtrack(saved);
                    return true;
                }
                None => self.assign(neg),
            }
        }
        let no_conflict = self.propagate();
        self.backtrack(saved);
        !no_conflict
    }

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
            self.ensure_capacity(lit.variable().index());
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
        self.stats.original += 1;
        self.add_clause_internal(clause);
    }

    /// Add a derived clause. Returns `Ok(())` if RUP (or RAT) implied.
    pub fn add_derived(&mut self, clause: &[Literal]) -> Result<(), DratCheckError> {
        if self.inconsistent && !clause.is_empty() {
            self.stats.additions += 1;
            return Ok(());
        }
        self.stats.additions += 1;
        for &lit in clause {
            self.ensure_capacity(lit.variable().index());
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
        self.stats.failures += 1;
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
        self.stats.deletions += 1;
        for &lit in clause {
            self.ensure_capacity(lit.variable().index());
        }
        let hash = Self::hash_clause(clause);
        let bucket = self.bucket_idx(hash);
        if let Some(cidx) = self.find_clause_idx(clause) {
            // Pseudo-unit check: if this clause is the reason for its first
            // literal's assignment, skip the deletion (drat-trim.c:807).
            if self.is_reason_for_first_lit(cidx) {
                self.stats.pseudo_unit_skips += 1;
                return;
            }
            if let Some(bucket_pos) = self.hash_buckets[bucket]
                .iter()
                .position(|&candidate| candidate == cidx)
            {
                self.hash_buckets[bucket].swap_remove(bucket_pos);
            }
            self.unlink_clause(cidx);
            self.live_clauses -= 1;
        } else {
            self.stats.missed_deletes += 1;
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

    /// Verify a complete proof against a formula.
    pub fn verify(
        &mut self,
        clauses: &[Vec<Literal>],
        steps: &[ProofStep],
    ) -> Result<(), DratCheckError> {
        for clause in clauses {
            self.add_original(clause);
        }
        if self.inconsistent {
            return Ok(());
        }
        for (i, step) in steps.iter().enumerate() {
            match step {
                ProofStep::Add(lits) => {
                    self.add_derived(lits)
                        .map_err(|e| DratCheckError::StepFailed {
                            step: i + 1,
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
                        step: i + 1,
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

#[cfg(test)]
mod adapter_api_tests;
#[cfg(test)]
mod binary_format_tests;
#[cfg(test)]
mod test_helpers;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_algorithm_audit;
#[cfg(test)]
mod tests_coverage;
#[cfg(test)]
mod tests_performance;
#[cfg(test)]
mod tests_proptest;
