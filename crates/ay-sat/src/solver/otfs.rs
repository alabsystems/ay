// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! On-the-fly self-subsumption (OTFS).
//!
//! During 1UIP conflict analysis, when the intermediate resolvent subsumes
//! the current reason clause, the reason clause is strengthened in-place by
//! removing the pivot literal (and any level-0 literals).
//!
//! Reference: CaDiCaL analyze.cpp:770-865 (`on_the_fly_strengthen`).

use crate::literal::Literal;
use crate::proof_manager::ProofAddKind;
use crate::solver::WatchOrderPolicy;
use crate::watched::ClauseRef;

impl super::Solver {
    /// Strengthen a reason clause via on-the-fly self-subsumption.
    ///
    /// Removes the pivot variable and any level-0 literals from the clause,
    /// updates watched literals, and emits proof obligations.
    ///
    /// Returns `true` if the clause was strengthened.
    pub(super) fn otfs_strengthen(&mut self, reason_ref: ClauseRef, pivot: Literal) -> bool {
        let clause_idx = reason_ref.0 as usize;
        let old_lits: Vec<Literal> = self.arena.literals(clause_idx).to_vec();
        let old_size = old_lits.len();
        // NOTE: proof-mode stability (solve_proof_mode) is asserted centrally
        // in proof_emit.rs — no per-caller check needed here.

        // Precondition: pivot must appear in the clause
        debug_assert!(
            old_lits.iter().any(|l| l.variable() == pivot.variable()),
            "BUG: OTFS pivot {pivot:?} not found in clause {clause_idx}",
        );
        // Precondition: one of the watched literals must be true (propagated)
        debug_assert!(
            old_size < 2 || self.lit_val(old_lits[0]) > 0 || self.lit_val(old_lits[1]) > 0,
            "BUG: OTFS clause {clause_idx} has no true watched literal",
        );

        // Cannot strengthen binary or unit clauses (CaDiCaL analyze.cpp:772)
        if old_size <= 2 {
            return false;
        }

        // LRAT mode requires a full resolution hint chain for each strengthening
        // step. OTFS emits TrustedTransform which works for DRAT but not LRAT.
        // The backward reconstruction (#8105) does not yet account for
        // OTFS-modified clauses. Keep OTFS disabled in LRAT mode until the
        // backward pass can reconstruct valid hint chains for OTFS steps.
        if self.cold.lrat_enabled {
            return false;
        }

        // Build new literal list: remove pivot variable and level-0 literals
        let mut new_lits: Vec<Literal> = Vec::with_capacity(old_size);
        for &lit in &old_lits {
            let var_idx = lit.variable().index();
            if lit.variable() == pivot.variable() {
                continue;
            }
            if self.var_data[var_idx].level == 0 {
                continue;
            }
            new_lits.push(lit);
        }

        let new_size = new_lits.len();

        // CaDiCaL analyze.cpp:903: strengthened clause must be strictly shorter
        debug_assert!(
            new_size < old_size,
            "BUG: OTFS strengthened clause not shorter ({new_size} >= {old_size})"
        );
        // No duplicate literals after removing pivot/level-0 lits
        debug_assert!(
            {
                let mut sorted: Vec<u32> = new_lits.iter().map(|l| l.variable().0).collect();
                sorted.sort_unstable();
                sorted.windows(2).all(|w| w[0] != w[1])
            },
            "BUG: OTFS strengthened clause has duplicate variables"
        );

        // Must have at least 2 literals remaining and must actually shrink.
        // CaDiCaL analyze.cpp:844-851: new_size==1 bails, new_size==2 allowed.
        if new_size < 2 || new_size >= old_size {
            return false;
        }

        // 2WL maintenance after OTFS: the pivot (propagated literal) was removed,
        // so ALL remaining literals are false under the current assignment.
        // Arrange the two highest-level false literals at watch positions 0 and 1
        // so BCP fires correctly on backtrack.
        // CaDiCaL reference: analyze.cpp:826-841.
        let old_watch0 = old_lits[0];
        let old_watch1 = old_lits[1];

        // All remaining literals must be falsified (pivot was the only true one)
        debug_assert!(
            new_lits.iter().all(|&lit| self.lit_val(lit) < 0),
            "BUG: OTFS strengthened clause has non-false literal in clause {clause_idx}",
        );

        // Put highest-level literal at position 0
        let mut best0 = 0;
        let mut best0_level = self.var_data[new_lits[0].variable().index()].level;
        for (i, &lit) in new_lits.iter().enumerate().skip(1) {
            let lv = self.var_data[lit.variable().index()].level;
            if lv > best0_level {
                best0 = i;
                best0_level = lv;
            }
        }
        if best0 != 0 {
            new_lits.swap(0, best0);
        }

        // Put second-highest-level literal at position 1
        let mut best1 = 1;
        let mut best1_level = self.var_data[new_lits[1].variable().index()].level;
        for (i, &lit) in new_lits.iter().enumerate().skip(2) {
            let lv = self.var_data[lit.variable().index()].level;
            if lv > best1_level {
                best1 = i;
                best1_level = lv;
            }
        }
        if best1 != 1 {
            new_lits.swap(1, best1);
        }

        // Post-sort: position 0 at highest level, position 1 at second-highest
        debug_assert!(
            new_lits[2..].iter().all(|&lit| {
                self.var_data[lit.variable().index()].level
                    <= self.var_data[new_lits[1].variable().index()].level
            }),
            "BUG: OTFS new_lits[1] not at second-highest level in clause {clause_idx}",
        );
        // Watched literals must be distinct (CaDiCaL implicit invariant)
        debug_assert_ne!(
            new_lits[0], new_lits[1],
            "BUG: OTFS watched literals are identical: {:?}",
            new_lits[0],
        );

        // Remove old watches.
        // Note: remove_watch is a no-op if the watch entry doesn't exist.
        // This can happen legitimately when JIT watches are detached (#8941).
        self.remove_watch(old_watch0, reason_ref);
        self.remove_watch(old_watch1, reason_ref);

        // DRAT/LRAT proof obligations: add strengthened, delete original.
        // CaDiCaL reference: analyze.cpp:807-822 (LRAT mini_chain handling).
        let old_id = self.clause_id(reason_ref);
        // OTFS strengthening: for LRAT, pass the old clause ID as a hint.
        let hints: Vec<u64> = if self.cold.lrat_enabled && old_id != 0 {
            vec![old_id]
        } else {
            Vec::new()
        };
        // OTFS strengthening is a self-subsumption resolution step (CaDiCaL
        // analyze.cpp:807-822). The strengthened clause is semantically derived
        // but is NOT RUP-derivable from the forward checker's clause set (the
        // checker doesn't mirror the solver's search assignment — see proof_manager
        // comment at the Derived/LRAT branch). Use TrustedTransform so the
        // forward checker verifies well-formedness (non-empty, non-tautological,
        // not fully-falsified) without requiring a full RUP derivation.
        if let Ok(new_id) = self.proof_emit_add(&new_lits, &hints, ProofAddKind::TrustedTransform) {
            // Update clause ID mapping: the clause at this index now has a new
            // LRAT ID (the old ID was deleted). Without this update,
            // clause_id(reason_ref) returns the stale deleted ID.
            let idx = reason_ref.0 as usize;
            if new_id != 0 && idx < self.cold.clause_ids.len() {
                self.cold.clause_ids[idx] = new_id;
            }
            // Sync next_clause_id so subsequent learned clauses don't
            // collide with IDs allocated by the proof manager.
            if new_id != 0 && new_id >= self.cold.next_clause_id {
                self.cold.next_clause_id = new_id;
            }
        }
        let _ = self.proof_emit_delete(&old_lits, old_id);
        self.clear_level0_reasons_removed_by_replacement(clause_idx, &old_lits, &new_lits, old_id);

        // Snapshot irredundant status before replace for BVE occ list notification (#8363).
        let was_irredundant = !self.arena.is_learned(clause_idx);

        if let Some(ref mut gc_occ) = self.gc_occ {
            gc_occ.remove_clause(clause_idx, &old_lits);
        }
        // Replace clause in-place (old literals become garbage)
        self.drain_pending_garbage_mark(clause_idx);
        self.stats.clear_bcp_learned_1963_blocker_cert(clause_idx);
        self.arena.replace(clause_idx, &new_lits);
        if let Some(ref mut gc_occ) = self.gc_occ {
            gc_occ.add_clause(clause_idx, &new_lits);
        }

        // Notify BVE occ lists of in-place clause replacement (#8363).
        // OTFS modifies irredundant clauses during CDCL search without going
        // through the inprocessing replace_clause_impl path, so BVE occ lists
        // would have stale entries. This was the primary cause of #8223 (P0
        // soundness bug) that forced the revert of incremental occ lists.
        if was_irredundant {
            self.note_irredundant_clause_replaced_for_bve(clause_idx, &old_lits, &new_lits);
        }

        self.arena.set_saved_pos(clause_idx, 2);
        self.arena
            .set_used(clause_idx, crate::clause_arena::MAX_USED);
        // CaDiCaL analyze.cpp:850: post-replace size must match new_lits
        debug_assert_eq!(
            self.arena.len_of(clause_idx),
            new_lits.len(),
            "BUG: OTFS clause_db header len {} != new_lits.len() {} after replace",
            self.arena.len_of(clause_idx),
            new_lits.len(),
        );

        // Keep the pivot variable's reason pointer intact (#8439).
        // After OTFS removes the pivot literal from this reason clause,
        // the clause still implies the pivot (all remaining literals are
        // false, so the pivot must be true). Conflict analysis handles
        // this correctly: the `if lit == p_lit { continue; }` skip is
        // a no-op (pivot not present), and all remaining literals are
        // processed — producing the same resolvent as the non-OTFS case.
        //
        // Previously (#8241), the reason was cleared to NO_REASON. This
        // caused a worse bug during backbone probing (#8356): subsequent
        // conflicts would encounter the pivot with NO_REASON and treat
        // it as a decision variable, corrupting the 1UIP resolution
        // counter and causing trail exhaustion panics. Keeping the
        // reason pointer avoids this entirely while preserving
        // correctness, and also protects the clause from being deleted
        // by reduce_db (it remains marked as a reason clause).

        // Add new watches. Binary clauses use implicit binary watch encoding.
        let is_binary = new_size == 2;
        let watched = self
            .prepare_watched_literals(&mut new_lits, WatchOrderPolicy::Preserve)
            .expect("OTFS strengthened clauses have >= 2 literals");
        self.attach_clause_watches(reason_ref, watched, is_binary);

        // Post-OTFS watch consistency check: verify the arena's first two
        // literals match the watches we just attached (#8941 crash fix).
        debug_assert!(
            {
                let (aw0, aw1) = self.arena.watched_literals(clause_idx);
                aw0 == watched.0 && aw1 == watched.1
            },
            "BUG: OTFS post-attach: arena watched lits {:?} != attached {:?} for clause {clause_idx}",
            self.arena.watched_literals(clause_idx),
            watched,
        );

        // Pivot reason retained (#8439): see comment above. The reason
        // pointer still points to this clause (now strengthened), which
        // correctly implies the pivot and protects the clause from GC.

        // JIT interaction: OTFS modified the clause in-place but JIT has
        // compiled code referencing the OLD clause layout. Mark as deleted
        // in the JIT guard bitmap so compiled functions skip it.

        self.stats.otfs_strengthened += 1;
        true
    }

    /// On-the-fly subsumption: delete a clause when another clause
    /// (typically the OTFS-strengthened reason) subsumes it.
    ///
    /// CaDiCaL reference: analyze.cpp:868-894 (`otfs_subsume_clause`).
    ///
    /// This fires when `resolved == 1` and the strengthened reason clause
    /// subsumes the original conflict clause. The conflict clause is all-false
    /// under the current assignment and cannot be a propagation reason, so
    /// it is safe to mark as garbage.
    ///
    /// If the subsumed clause is irredundant and the subsuming clause is
    /// redundant, the subsuming clause is promoted to irredundant (CaDiCaL
    /// analyze.cpp:881-894).
    ///
    /// Uses `mark_garbage_keep_data` (deferred GC) instead of `arena.delete()`
    /// so that reason pointers remain valid until the next reduce_db pass.
    /// CaDiCaL uses the same deferred pattern via `mark_garbage`.
    pub(super) fn otfs_subsume(&mut self, subsuming_ref: ClauseRef, subsumed_ref: ClauseRef) {
        let subsuming_idx = subsuming_ref.0 as usize;
        let subsumed_idx = subsumed_ref.0 as usize;

        debug_assert_ne!(
            subsuming_idx, subsumed_idx,
            "BUG: OTFS subsume called with same clause"
        );
        debug_assert!(
            !self.arena.is_empty_clause(subsumed_idx),
            "BUG: OTFS subsumed clause already deleted"
        );

        let subsumed_lits: Vec<Literal> = self.arena.literals(subsumed_idx).to_vec();
        let subsumed_id = self.clause_id(subsumed_ref);
        let subsumed_learned = self.arena.is_learned(subsumed_idx);
        let subsuming_learned = self.arena.is_learned(subsuming_idx);

        // CaDiCaL analyze.cpp:878-880: if subsumed is redundant, just delete.
        // If subsumed is irredundant and subsuming is also irredundant, delete.
        // If subsumed is irredundant and subsuming is redundant, promote subsuming.

        // Proof delete DEFERRED in proof mode (2026-07-03): the subsumed
        // clause is the CURRENT REASON of a live propagation (that is why
        // mark_garbage_keep_data below keeps its literal data valid for
        // reason pointers). Emitting the DRAT delete here removes it from
        // the checker's formula while later conflicts still resolve through
        // it, making those learned clauses unverifiable (70da0b78 certified
        // route: phantom clause (12598,19329,-19343,19346), proof add
        // #118944 deleted early, live instance still justifying resolutions
        // at proof offset 143160 -> step-143161 NOT-VERIFIED). Deletion
        // lines are only a checker optimization; the clause is deleted from
        // the proof when it is actually collected later. No-proof mode keeps
        // the original accounting.
        if self.proof_manager.is_none() {
            let _ = self.proof_emit_delete(&subsumed_lits, subsumed_id);
        }

        // Remove watches for the subsumed clause.
        if subsumed_lits.len() >= 2 {
            self.remove_watch(subsumed_lits[0], subsumed_ref);
            self.remove_watch(subsumed_lits[1], subsumed_ref);
        }

        // Remove from occurrence lists if present.
        if let Some(ref mut gc_occ) = self.gc_occ {
            gc_occ.remove_clause(subsumed_idx, &subsumed_lits);
        }

        // Mark the subsumed clause as garbage (deferred deletion).
        // CaDiCaL analyze.cpp:879,885: mark_garbage(subsumed).
        // Using mark_garbage_keep_data keeps literal data intact so that
        // reason pointers referencing this clause remain valid until the
        // next reduce_db/GC pass cleans it up.
        self.drain_pending_garbage_mark(subsumed_idx);
        self.stats.clear_bcp_learned_1963_blocker_cert(subsumed_idx);
        self.arena.mark_garbage_keep_data(subsumed_idx);

        // Notify BVE occ lists of irredundant clause removal (#8363).
        // Must use the pre-garbage `subsumed_learned` flag captured above
        // since the header may change after mark_garbage_keep_data.
        if !subsumed_learned {
            self.note_irredundant_clause_removed_for_bve(subsumed_idx, &subsumed_lits);
        }

        // JIT interaction (#8241): mark the subsumed clause as deleted in the
        // JIT guard bitmap. The JIT compiled code must not propagate using a
        // garbage-marked clause — the literal data is kept for reason pointer
        // validity but the clause is logically deleted.

        // CaDiCaL analyze.cpp:881-894: promote redundant (learned) subsuming
        // clause to irredundant if the subsumed clause was irredundant (original).
        if !subsumed_learned && subsuming_learned {
            self.arena.set_learned(subsuming_idx, false);
            // Notify BVE occ lists about the promotion (#8363). The subsuming
            // clause was learned (not in occ lists) and is now irredundant.
            let promoted_lits: Vec<Literal> = self.arena.literals(subsuming_idx).to_vec();
            self.note_clause_promoted_to_irredundant(subsuming_idx, &promoted_lits);
        }

        self.stats.otfs_clause_subsumed += 1;
    }
}
