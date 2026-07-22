// Copyright 2026 Andrew Yates
// RAT (Resolution Asymmetric Tautology) verification for the LRAT checker.
//
// Extracted from checker/mod.rs for the 500-line limit.
// Reference: drat-trim `lrat-check.c:checkClause()` lines 135-191 and
// `checkRedundancy()` lines 88-133.

use crate::dimacs::Literal;
use std::io::Write;

use super::{HintAction, LratChecker};

impl LratChecker {
    /// Verify RAT witnesses for a derived clause.
    ///
    /// `rat_hints` starts at the first negative hint ID. It consists of groups:
    /// `[-C1, h1, h2, ..., -C2, h3, h4, ..., ...]` where each `-Ci` is a
    /// clause containing `~pivot`, and the following positive hints prove
    /// the resolvent of `clause` with `Ci` (minus `~pivot`) yields a conflict.
    ///
    /// After verifying all explicit witnesses, performs a **completeness check**:
    /// every clause in the database containing `~pivot` must be covered by a
    /// witness group. Without this, an incomplete proof (missing witnesses for
    /// some `~pivot` clauses) would be wrongly accepted.
    ///
    /// Reference: drat-trim `lrat-check.c:checkClause()` lines 135-191.
    /// Completeness check corresponds to lines 166-172 (pre-witness scan),
    /// 94-99 (inter-witness scan inside checkRedundancy), and 184-189
    /// (post-witness tail scan).
    pub(super) fn verify_rat_witnesses(
        &mut self,
        pivot: Literal,
        rat_hints: &[i64],
        base_trail: usize,
    ) -> bool {
        let neg_pivot = pivot.negated();

        // Collect witness clause IDs for the completeness check.
        // Typically small (< 20), so Vec + linear scan beats HashSet.
        let mut witness_ids: Vec<u64> = Vec::new();

        // Parse witness groups: each starts with a negative hint ID.
        let mut i = 0;
        while i < rat_hints.len() {
            let hint = rat_hints[i];
            if hint >= 0 {
                // Unexpected positive hint after RAT section started.
                return false;
            }
            debug_assert!(hint != i64::MIN, "hint i64::MIN would overflow on negation");
            let witness_clause_id = (-hint) as u64;
            witness_ids.push(witness_clause_id);
            i += 1;

            // Collect the positive hints for this witness.
            let rup_start = i;
            while i < rat_hints.len() && rat_hints[i] > 0 {
                i += 1;
            }
            let witness_rup_hints = &rat_hints[rup_start..i];

            // Verify this RAT witness.
            if !self.verify_one_rat_witness(
                neg_pivot,
                witness_clause_id,
                witness_rup_hints,
                base_trail,
            ) {
                return false;
            }
        }

        // Completeness check: every active clause containing ~pivot must have a witness.
        // Reference: drat-trim lrat-check.c lines 166-172, 184-189.
        //
        // Uses occurrence lists for O(occ(~pivot)) instead of O(|clause_index|).
        // Deleted clause IDs are lazily skipped (not in clause_index).
        self.check_rat_completeness(neg_pivot, &witness_ids)
    }

    /// Check that all active clauses containing `neg_pivot` are in the witness set.
    ///
    /// Uses `occ_lists[neg_pivot.index()]` for O(occ) lookup instead of scanning
    /// the entire clause database. Deleted clauses (absent from `clause_index`)
    /// are lazily skipped. Reference: drat-trim `intro` array + ordered scan.
    fn check_rat_completeness(&self, neg_pivot: Literal, witness_ids: &[u64]) -> bool {
        let occ_idx = neg_pivot.index();
        if occ_idx >= self.occ_lists.len() {
            // No occurrence list for this literal → no clauses contain it → complete.
            return true;
        }
        let occ = &self.occ_lists[occ_idx];
        let mut uncovered: Vec<u64> = Vec::new();
        for &clause_id in occ {
            // Lazy deletion: skip clause IDs no longer in the active database.
            if !self.clause_index.contains_key(&clause_id) {
                continue;
            }
            // Verify the clause still actually contains neg_pivot (arena is append-only,
            // so if it was inserted with neg_pivot, it still has it unless weakened+restored
            // with different content — which is caught by the weaken content check).
            if !witness_ids.contains(&clause_id) {
                uncovered.push(clause_id);
            }
        }
        if !uncovered.is_empty() {
            let _ = writeln!(
                std::io::stderr(),
                "LRAT RAT: {} clause(s) containing ~pivot {neg_pivot} not covered by witnesses: {:?}",
                uncovered.len(),
                &uncovered[..uncovered.len().min(10)],
            );
            return false;
        }
        true
    }

    /// Verify a single RAT witness: resolving the derived clause with
    /// `witness_clause` (on `pivot`/`~pivot`) yields a conflict under RUP.
    ///
    /// Algorithm:
    /// 1. Reset to base trail (clause negation is still assumed).
    /// 2. Also assume the negation of each literal in `witness_clause` except `~pivot`.
    /// 3. Walk the `rup_hints` to find a conflict.
    ///
    /// Reference: drat-trim `lrat-check.c:checkRedundancy()` lines 88-133.
    fn verify_one_rat_witness(
        &mut self,
        neg_pivot: Literal,
        witness_clause_id: u64,
        rup_hints: &[i64],
        base_trail: usize,
    ) -> bool {
        // Reset trail to base (clause negation is still assumed from verify_chain).
        self.backtrack(base_trail);

        // Look up the witness clause entry (Copy, 16 bytes). No heap clone. (#5267)
        let entry = match self.clause_index.get(&witness_clause_id) {
            Some(&e) => e,
            None => {
                let _ = writeln!(
                    std::io::stderr(),
                    "LRAT RAT: witness clause {witness_clause_id} not found"
                );
                return false;
            }
        };

        // Verify witness clause contains ~pivot (read-only scan of arena).
        if !self.clause_lits(entry).contains(&neg_pivot) {
            let _ = writeln!(
                std::io::stderr(),
                "LRAT RAT: witness clause {witness_clause_id} does not contain ~pivot {neg_pivot}"
            );
            return false;
        }

        // Assume negation of each literal in witness clause, except ~pivot.
        // (The resolvent of `clause` with `witness_clause` on pivot is:
        //  `clause \ {pivot}` ∪ `witness_clause \ {~pivot}`.
        //  We already assumed negation of `clause`. Now assume negation of
        //  `witness_clause \ {~pivot}`.)
        //
        // Iterate by arena index: `clause_arena[i]` copies the Literal (u32),
        // releasing the borrow before `assign` mutates self. (#5267)
        let start = entry.start as usize;
        let end = start + entry.len as usize;
        for i in start..end {
            let lit = self.clause_arena[i];
            if lit == neg_pivot {
                continue; // Skip ~pivot — it resolves with pivot.
            }
            let neg = lit.negated();
            match self.value(neg) {
                Some(true) => {} // Already assigned.
                Some(false) => {
                    // Literal is already true → resolvent trivially satisfied.
                    return true;
                }
                None => {
                    self.ensure_var_extended(neg);
                    self.assign(neg);
                }
            }
        }

        // Walk the RUP hints to find a conflict in the resolvent.
        self.propagate_rup_hints(rup_hints)
    }

    /// Process positive hint clauses for RUP, propagating units and detecting
    /// conflicts.
    ///
    /// Rejects duplicate hints (CaDiCaL lratchecker.cpp:340-347) and
    /// tautological hint clauses (CaDiCaL lratchecker.cpp:334-339).
    ///
    /// Duplicate detection uses a generation counter on `ClauseEntry.hint_gen`
    /// instead of a `HashSet<u64>`. Each call increments `hint_generation`;
    /// stamping `entry.hint_gen = hint_generation` marks a clause as used.
    /// O(1) per hint, no hashing overhead, no allocation. (#5267)
    pub(super) fn propagate_rup_hints(&mut self, hints: &[i64]) -> bool {
        self.hint_generation = self.hint_generation.wrapping_add(1);
        // Skip generation 0: ClauseEntry.hint_gen is initialized to 0,
        // so wrapping to 0 would cause all unused clauses to false-positive
        // as "duplicate hint" (#5362).
        if self.hint_generation == 0 {
            self.hint_generation = 1;
        }
        let current_gen = self.hint_generation;

        for &hint_id_signed in hints {
            debug_assert!(hint_id_signed >= 0, "negative hint in RUP section");
            let hint_id = hint_id_signed as u64;

            // CaDiCaL lratchecker.cpp:340-347: reject duplicate hint IDs.
            // Generation-based: if entry.hint_gen == current_gen, it was already
            // used in this derivation step. get_mut stamps the generation atomically.
            let entry = match self.clause_index.get_mut(&hint_id) {
                Some(e) => {
                    if e.hint_gen == current_gen {
                        return false; // Duplicate hint ID.
                    }
                    e.hint_gen = current_gen;
                    *e // Copy out the entry (16 bytes) to release &mut borrow.
                }
                None => return false, // Unknown hint ID — strict LRAT requires all hints exist.
            };

            // CaDiCaL lratchecker.cpp:334-339: reject tautological hint clauses.
            if entry.tautological {
                return false;
            }

            // Scan the hint clause under immutable borrow to determine the
            // action (conflict, unit propagation, or skip). The borrow ends
            // before any mutation.
            //
            // Use arena index iteration: `clause_arena[i]` copies the Literal,
            // releasing the borrow before `value()` reads self.assigns. Since
            // `value()` is a pure read of `assigns` (disjoint from clause_arena),
            // and the HintAction enum captures the result, no borrow conflict
            // occurs.
            let action = {
                let mut non_falsified_count = 0u32;
                let mut unit_lit: Option<Literal> = None;

                let start = entry.start as usize;
                let end = start + entry.len as usize;
                for arena_idx in start..end {
                    let lit = self.clause_arena[arena_idx];
                    self.ensure_mark_capacity(lit);
                    // Clauses are logical sets even when a DIMACS/LRAT input
                    // repeats a literal.  Count each literal once so (a v a)
                    // remains unit rather than being misclassified as
                    // non-unit.  Reuse the resolution scratch stack to avoid
                    // allocating a set in this hot loop.
                    if self.checked_lits[lit.index()] {
                        continue;
                    }
                    self.set_checked(lit.index());
                    match self.value(lit) {
                        Some(false) => {} // falsified — skip
                        _ => {
                            // Not falsified: either true (satisfied) or unassigned.
                            // CaDiCaL counts both as non-falsified (#5233).
                            non_falsified_count += 1;
                            if non_falsified_count >= 2 {
                                break; // early exit: already non-unit
                            }
                            unit_lit = Some(lit);
                        }
                    }
                }

                let action = if non_falsified_count == 0 {
                    HintAction::Conflict
                } else if non_falsified_count == 1 {
                    // The single non-falsified literal. If unassigned, propagate.
                    // If already true (satisfied), it's a no-op (like CaDiCaL's
                    // checked_lit(unit)=true when unit is already true).
                    let Some(lit) = unit_lit else {
                        // Structurally unreachable (non_falsified_count == 1
                        // guarantees unit_lit is Some), but safe fallback.
                        return false;
                    };
                    if self.value(lit) == Some(true) {
                        HintAction::SatisfiedUnit
                    } else {
                        HintAction::Propagate(lit)
                    }
                } else {
                    HintAction::NonUnit
                };
                self.clear_checked_stack();
                action
            }; // immutable borrow of self.clause_arena ends here

            match action {
                HintAction::Conflict => return true,
                HintAction::Propagate(unit) => self.assign(unit),
                HintAction::SatisfiedUnit => {} // no-op: continue to next hint
                HintAction::NonUnit => return false, // CaDiCaL parity: non-unit hint = failure
            }
        }
        false
    }
}
