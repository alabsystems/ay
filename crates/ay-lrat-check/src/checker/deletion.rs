// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause deletion, content verification, weaken/restore, and finalization.
//!
//! CaDiCaL `lratchecker.cpp:634-649` verifies that deletion commands match
//! the stored clause contents. `lratchecker.cpp:757-794` verifies that
//! finalize commands match stored clauses at proof end (completeness audit).
//! `lratchecker.cpp:679-755` implements weaken/restore for incremental SAT.
//!
//! Note: the LRAT file format does not carry literals in deletion steps (only
//! clause IDs), so `delete_verified()` is only usable via the in-memory API.
//! CaDiCaL's internal checker receives literals through its tracer API, not
//! from the LRAT file.
//!
//! Extracted from checker/mod.rs for the 500-line limit (#5142).

use crate::dimacs::Literal;
use std::io::Write;

use super::types::ClauseEntry;
use super::LratChecker;

impl LratChecker {
    /// Verify that `provided_lits` contains all literals in the stored clause
    /// identified by `entry`.
    ///
    /// When `exact_length` is `true`, also checks that the lengths match
    /// (bidirectional completeness). Set to `false` for `delete_verified`
    /// which allows superset deletion commands (CaDiCaL parity).
    ///
    /// Uses the `marks` scratch array for O(n) mark-and-check.
    /// Callers: `delete_verified`, `weaken`, `finalize_clause`.
    fn verify_content(
        &mut self,
        clause_id: u64,
        entry: ClauseEntry,
        provided_lits: &[Literal],
        op_name: &str,
        exact_length: bool,
    ) -> bool {
        // Ensure marks array is large enough.
        for &lit in provided_lits {
            let idx = lit.index();
            if idx >= self.marks.len() {
                self.marks.resize(idx + 1, false);
            }
        }
        // Phase 1: Mark all provided literals.
        for &lit in provided_lits {
            self.marks[lit.index()] = true;
        }
        // Phase 2: Verify every stored literal is marked.
        // Index-based iteration avoids borrow on clause_arena conflicting
        // with mutable access to marks during cleanup.
        let start = entry.start as usize;
        let end = start + entry.len as usize;
        let mut ok = true;
        for i in start..end {
            let lit = self.clause_arena[i];
            let idx = lit.index();
            if idx >= self.marks.len() || !self.marks[idx] {
                let _ = writeln!(
                    std::io::stderr(),
                    "LRAT FAIL: {op_name} of clause {clause_id} content mismatch: \
                     stored literal {lit} not in provided literals"
                );
                ok = false;
                break;
            }
        }
        // Also check length for bidirectional completeness (when required).
        if ok && exact_length && provided_lits.len() != entry.len as usize {
            let _ = writeln!(
                std::io::stderr(),
                "LRAT FAIL: {op_name} of clause {clause_id} length mismatch: \
                 stored {} literals, provided {}",
                entry.len,
                provided_lits.len()
            );
            ok = false;
        }
        // Phase 3: Clear marks.
        for &lit in provided_lits {
            let idx = lit.index();
            if idx < self.marks.len() {
                self.marks[idx] = false;
            }
        }
        ok
    }

    /// Look up a clause entry by ID, emitting an error on missing ID.
    fn require_clause(&mut self, clause_id: u64, op_name: &str) -> Option<ClauseEntry> {
        match self.clause_index.get(&clause_id) {
            Some(&e) => Some(e),
            None => {
                let _ = writeln!(
                    std::io::stderr(),
                    "LRAT FAIL: {op_name} of non-existent clause {clause_id}"
                );
                self.record_failure();
                None
            }
        }
    }

    /// Delete a clause from the checker database.
    ///
    /// Returns `true` on success, `false` if the clause ID doesn't exist
    /// or the checker has already failed in strict mode.
    /// CaDiCaL lratchecker.cpp:634-649 treats deletion of non-existent clauses
    /// as a fatal error. Arena is compacted when dead space exceeds 2x live (#8624).
    pub fn delete(&mut self, clause_id: u64) -> bool {
        if self.failed {
            return false;
        }
        if let Some(entry) = self.clause_index.remove(&clause_id) {
            self.stats.deleted += 1;
            if entry.original {
                self.stats.deleted_originals += 1;
            }
            // Compact arena when dead space exceeds live data size (#8624).
            self.maybe_compact_arena();
            true
        } else {
            let _ = writeln!(
                std::io::stderr(),
                "LRAT FAIL: deletion of non-existent clause {clause_id}"
            );
            self.record_failure();
            false
        }
    }

    /// Delete a clause with content verification (CaDiCaL lratchecker.cpp:634-649).
    ///
    /// Verifies that every literal in the stored clause appears in the provided
    /// deletion literals. Returns `false` if the stored clause contains a literal
    /// not in the deletion command (content mismatch), or if the clause ID does
    /// not exist (CaDiCaL parity: non-existent deletion = fatal, #5288).
    ///
    /// Note: the LRAT file format does not carry literals in deletion steps
    /// (only clause IDs), so this method is only usable via the in-memory API.
    pub fn delete_verified(&mut self, clause_id: u64, deletion_lits: &[Literal]) -> bool {
        if self.failed {
            return false;
        }
        let entry = match self.require_clause(clause_id, "deletion") {
            Some(e) => e,
            None => return false,
        };
        if !self.verify_content(clause_id, entry, deletion_lits, "deletion", false) {
            self.record_failure();
            return false;
        }
        self.clause_index.remove(&clause_id);
        self.stats.deleted += 1;
        if entry.original {
            self.stats.deleted_originals += 1;
        }
        // Compact arena when dead space exceeds live data size (#8624).
        self.maybe_compact_arena();
        true
    }

    /// Weaken a clause: save content for later restoration, then remove from
    /// the active clause set.
    ///
    /// CaDiCaL lratchecker.cpp:679-716 (`weaken_minus`) + delete. This is the
    /// combined operation CaDiCaL calls `weaken_plus` in proof.cpp: save the
    /// clause content into `clauses_to_reconstruct`, then delete from the hash
    /// table. Used by incremental SAT (BVE, BCE, sweeping) to temporarily
    /// remove clauses that may be restored later.
    ///
    /// Returns `false` if: clause doesn't exist, content mismatch, already
    /// weakened (duplicate), or checker has failed.
    pub fn weaken(&mut self, clause_id: u64, clause_lits: &[Literal]) -> bool {
        if self.failed {
            return false;
        }
        let entry = match self.require_clause(clause_id, "weaken") {
            Some(e) => e,
            None => return false,
        };
        if !self.verify_content(clause_id, entry, clause_lits, "weaken", true) {
            self.record_failure();
            return false;
        }
        // Prevent double-weaken (CaDiCaL would crash on duplicate restore).
        if self.weakened_clauses.contains_key(&clause_id) {
            let _ = writeln!(
                std::io::stderr(),
                "LRAT FAIL: clause {clause_id} already weakened"
            );
            self.record_failure();
            return false;
        }
        // Save sorted content + original + tautological flags (CaDiCaL lratchecker.cpp:715).
        let start = entry.start as usize;
        let end = start + entry.len as usize;
        let mut saved: Vec<Literal> = self.clause_arena[start..end].to_vec();
        saved.sort_by_key(|l| l.index());
        self.weakened_clauses
            .insert(clause_id, (saved, entry.original, entry.tautological));
        // Remove from active set (= CaDiCaL weaken_plus delete step).
        self.clause_index.remove(&clause_id);
        self.stats.deleted += 1;
        if entry.original {
            self.stats.deleted_originals += 1;
        }
        self.stats.weakened += 1;
        // Compact arena when dead space exceeds live data size (#8624).
        self.maybe_compact_arena();
        true
    }

    /// Restore a previously weakened clause: verify content matches the saved
    /// copy, then re-add to the active clause set with its original flag.
    ///
    /// CaDiCaL lratchecker.cpp:718-755 (`restore_clause`) verifies content
    /// integrity, then the caller re-inserts via `add_original_clause`. Here
    /// we combine both steps: verify + re-insert.
    ///
    /// Returns `false` if: clause was never weakened, content mismatch,
    /// clause ID already in use (re-added by another path), or checker failed.
    pub fn restore(&mut self, clause_id: u64, clause_lits: &[Literal]) -> bool {
        if self.failed {
            return false;
        }
        // Look up saved content + original flag (CaDiCaL lratchecker.cpp:720-727).
        let (saved, was_original, was_tautological) = match self.weakened_clauses.remove(&clause_id)
        {
            Some(s) => s,
            None => {
                let _ = writeln!(
                    std::io::stderr(),
                    "LRAT FAIL: restore of clause {clause_id} not previously weakened"
                );
                self.record_failure();
                return false;
            }
        };
        // Verify content matches saved copy (CaDiCaL lratchecker.cpp:728-752).
        let mut provided_sorted: Vec<Literal> = clause_lits.to_vec();
        provided_sorted.sort_by_key(|l| l.index());
        if provided_sorted.len() != saved.len()
            || provided_sorted
                .iter()
                .zip(saved.iter())
                .any(|(a, b)| a != b)
        {
            let _ = writeln!(
                std::io::stderr(),
                "LRAT FAIL: restore of clause {clause_id} content mismatch: \
                 saved {} literals vs provided {}",
                saved.len(),
                provided_sorted.len()
            );
            self.record_failure();
            return false;
        }
        // Re-add clause (CaDiCaL add_original_clause with restore=true).
        if self.clause_index.contains_key(&clause_id) {
            let _ = writeln!(
                std::io::stderr(),
                "LRAT FAIL: restore of clause {clause_id} but ID already in use"
            );
            self.record_failure();
            return false;
        }
        if self
            .insert_clause(clause_id, clause_lits, was_tautological, was_original)
            .is_none()
        {
            self.record_failure();
            return false;
        }
        self.stats.restored += 1;
        // Undo the deleted_originals increment from weaken() when the clause
        // was originally an original. Keeps finalization coverage correct.
        if was_original && self.stats.deleted_originals > 0 {
            self.stats.deleted_originals -= 1;
        }
        true
    }

    /// Finalize a clause: verify it exists and content matches, without removing it.
    ///
    /// CaDiCaL lratchecker.cpp:757-794 `finalize_clause()`: verifies each clause
    /// is accounted for at proof end. `report_status()` (line 797) then checks
    /// `num_finalized == num_clauses`.
    ///
    /// Unlike `delete_verified()`, finalization does NOT remove the clause from
    /// the index. It confirms the clause is present and matches the expected
    /// content, then increments `stats.finalized`.
    ///
    /// Returns `false` if the clause doesn't exist or content mismatches.
    pub fn finalize_clause(&mut self, clause_id: u64, expected_lits: &[Literal]) -> bool {
        if self.failed {
            return false;
        }
        let entry = match self.require_clause(clause_id, "finalize") {
            Some(e) => e,
            None => return false,
        };
        if !self.verify_content(clause_id, entry, expected_lits, "finalize", true) {
            self.record_failure();
            return false;
        }
        // CaDiCaL only counts original clauses in finalization coverage.
        if entry.original {
            self.stats.finalized += 1;
        }
        true
    }
}
