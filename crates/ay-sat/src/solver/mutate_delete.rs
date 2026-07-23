// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause deletion helpers for inprocessing passes.
//!
//! Split from `mutate.rs` for file-size compliance (#5142).
//! Contains `delete_clause_checked`, `delete_clause_unchecked`,
//! `delete_clause_observed`, and `apply_decompose_mutation`.

use super::mutate::{DeleteResult, ReasonPolicy};
use super::*;

impl Solver {
    #[inline]
    fn emit_lrat_delete_unit_derivation(
        &mut self,
        clause_idx: usize,
        unit_lit_idx: usize,
        clause_id: u64,
    ) -> u64 {
        if !self.lrat_delete_unit_derivation_hints_ready_for_clause(
            clause_idx,
            unit_lit_idx,
            clause_id,
        ) {
            return 0;
        }

        let lit = self.arena.literal(clause_idx, unit_lit_idx);
        let clause_len = self.arena.len_of(clause_idx);
        let mut hints = std::mem::take(&mut self.cold.lrat_delete_unit_hints_buf);
        hints.clear();

        for j in 0..clause_len {
            if j == unit_lit_idx {
                continue;
            }
            let other_lit = self.arena.literal(clause_idx, j);
            if other_lit.variable().index() < self.num_vars {
                if let Some(pid) = self.level0_unit_chain_proof_id_for_lit(other_lit.negated()) {
                    if !hints.contains(&pid) {
                        hints.push(pid);
                    }
                }
            }
        }
        hints.push(clause_id);

        let unit_id = self
            .proof_emit_add(&[lit], &hints, ProofAddKind::Derived)
            .unwrap_or(0);
        hints.clear();
        self.cold.lrat_delete_unit_hints_buf = hints;
        unit_id
    }

    #[inline]
    pub(super) fn lrat_delete_unit_derivation_hints_ready_for_clause(
        &self,
        clause_idx: usize,
        unit_lit_idx: usize,
        clause_id: u64,
    ) -> bool {
        if !self.lrat_hint_id_visible(clause_id) {
            return false;
        }
        let unit_var = self.arena.literal(clause_idx, unit_lit_idx).variable();
        let clause_len = self.arena.len_of(clause_idx);
        for j in 0..clause_len {
            if j == unit_lit_idx {
                continue;
            }
            let other_lit = self.arena.literal(clause_idx, j);
            if other_lit.variable() == unit_var {
                continue;
            }
            if other_lit.variable().index() < self.num_vars
                && self
                    .level0_unit_chain_proof_id_for_lit(other_lit.negated())
                    .is_none()
            {
                return false;
            }
        }
        true
    }

    #[inline]
    pub(super) fn lrat_delete_unit_derivation_hints_ready_for_lits(
        &self,
        lits: &[Literal],
        unit_var: Variable,
        clause_id: u64,
    ) -> bool {
        if !self.lrat_hint_id_visible(clause_id) {
            return false;
        }
        for &other_lit in lits {
            if other_lit.variable() == unit_var {
                continue;
            }
            if other_lit.variable().index() < self.num_vars
                && self
                    .level0_unit_chain_proof_id_for_lit(other_lit.negated())
                    .is_none()
            {
                return false;
            }
        }
        true
    }

    #[inline]
    pub(super) fn lrat_clause_unit_rederivations_ready_for_delete(
        &mut self,
        clause_idx: usize,
    ) -> bool {
        if !self.cold.lrat_enabled {
            return true;
        }
        let clause_id = self.clause_id(ClauseRef(clause_idx as u32));
        if clause_id == 0 {
            return true;
        }
        self.materialize_level0_unit_proofs();
        let clause_len = self.arena.len_of(clause_idx);
        for k in 0..clause_len {
            let lit = self.arena.literal(clause_idx, k);
            let vi = lit.variable().index();
            if vi < self.unit_proof_id.len()
                && self.unit_proof_id[vi] == clause_id
                && self.unit_proof_sign.get(vi).copied().unwrap_or(0) == lit.sign_i8()
                && self.var_data[vi].level == 0
                && !self
                    .lrat_delete_unit_derivation_hints_ready_for_clause(clause_idx, k, clause_id)
            {
                return false;
            }
        }
        true
    }

    #[inline]
    pub(super) fn lrat_delete_retained_active_clause(&mut self, clause_idx: usize) -> bool {
        self.cold.lrat_enabled
            && self.arena.is_active(clause_idx)
            && !self.lrat_clause_unit_rederivations_ready_for_delete(clause_idx)
    }

    /// Fix #6270: Before deleting a clause from the LRAT proof, check if
    /// any variable's unit_proof_id references this clause's ID. If so,
    /// re-derive the unit proof so the ID stays live. This handles all
    /// deletion paths (reduce_db, inprocessing, ClearLevel0 overflow), and
    /// is also used by the congruence forward-subsumption husk path, which
    /// emits its proof deletions without going through
    /// `delete_clause_observed` (husk adjudication).
    ///
    /// Must run BEFORE the proof delete is emitted for `clause_id` (the
    /// re-derivation hints reference `clause_id`, which must still be known
    /// to the checker).
    pub(super) fn lrat_rederive_units_referencing_clause(
        &mut self,
        clause_idx: usize,
        clause_id: u64,
    ) {
        if !self.cold.lrat_enabled || clause_id == 0 {
            return;
        }
        self.materialize_level0_unit_proofs();
        let clause_len = self.arena.len_of(clause_idx);
        for k in 0..clause_len {
            let lit = self.arena.literal(clause_idx, k);
            let vi = lit.variable().index();
            if vi < self.unit_proof_id.len()
                && self.unit_proof_id[vi] == clause_id
                && self.unit_proof_sign.get(vi).copied().unwrap_or(0) == lit.sign_i8()
                && self.var_data[vi].level == 0
            {
                // Build hints: proof IDs of other falsified literals first,
                // then the clause itself last. Multi-literal antecedents
                // need their materialized unit proof IDs here; using the
                // raw reason clause ID leaves the derived unit chain
                // incomplete (#6270).
                let unit_id = self.emit_lrat_delete_unit_derivation(clause_idx, k, clause_id);
                if unit_id != 0 {
                    self.record_unit_proof_id_for_lit(lit, unit_id);
                }
            }
        }
    }

    #[inline]
    pub(super) fn delete_clause_observed(
        &mut self,
        clause_idx: usize,
        reason_policy: ReasonPolicy,
    ) {
        self.drain_pending_garbage_mark(clause_idx);
        self.stats.clear_bcp_learned_1963_blocker_cert(clause_idx);
        let clause_id = self.clause_id(ClauseRef(clause_idx as u32));
        // Fix #6270: re-derive unit proofs that reference this clause's ID
        // before the delete is emitted (see helper doc).
        self.lrat_rederive_units_referencing_clause(clause_idx, clause_id);
        // Forward DRUP check + proof deletion via unified wrapper (#4564).
        // Uses arena-direct variant to avoid .to_vec() allocation (#5075).
        if self.cold.forward_checker.is_some() || self.proof_manager.is_some() {
            let _ = self.proof_emit_delete_arena(clause_idx, clause_id);
        }
        // SAT diagnostic trace: clause_delete event (Wave 2, #4211)
        // Derive DeleteReason from diagnostic_pass for specific attribution,
        // falling back to ReasonPolicy-based generic reason (#4172).
        if let Some(ref writer) = self.cold.diagnostic_trace {
            let diag_reason = match self.cold.diagnostic_pass {
                DiagnosticPass::Reduce => crate::diagnostic_trace::DeleteReason::Reduce,
                DiagnosticPass::Subsume => crate::diagnostic_trace::DeleteReason::Subsumed,
                DiagnosticPass::BCE => crate::diagnostic_trace::DeleteReason::Blocked,
                DiagnosticPass::Vivify => crate::diagnostic_trace::DeleteReason::Replaced,
                _ => match reason_policy {
                    ReasonPolicy::ClearLevel0 => crate::diagnostic_trace::DeleteReason::Eliminated,
                    ReasonPolicy::Skip => crate::diagnostic_trace::DeleteReason::Inprocessing,
                },
            };
            writer.emit_clause_delete(clause_id, self.cold.diagnostic_pass, diag_reason);
        }
        // Binary watcher lifecycle split (#4924): unlink binary watches eagerly
        // on deletion so BCP hot paths can skip clause liveness checks.
        // Skip when watches are disconnected (watch-free BVE mode) — lists are
        // empty and will be rebuilt in bulk after BVE completes.
        if !self.watches_disconnected {
            self.delete_binary_clause_watches(clause_idx);
        } else {
            // Track deletions during disconnected mode (#8093). When nonzero,
            // reconnect_bve_watches must run the Phase 1 purge to remove stale
            // binary watch entries. When zero, the purge can be skipped.
            self.cold.disconnected_deletions = self.cold.disconnected_deletions.saturating_add(1);
        }
        // Long-clause watchers remain lazily filtered in BCP/flush_watches().
        // Mark their watched literals dirty so flush_watches only scans those
        // lists instead of doing an O(total_watches) full sweep (#8101).
        if !self.watches_disconnected {
            let clause_len = self.arena.len_of(clause_idx);
            if clause_len > 2 {
                let (w0, w1) = self.arena.watched_literals(clause_idx);
                if w0.index() < self.dirty_watches.len() {
                    self.dirty_watches[w0.index()] = true;
                    self.dirty_watch_list.push(w0.index() as u32);
                }
                if w1.index() < self.dirty_watches.len() {
                    self.dirty_watches[w1.index()] = true;
                    self.dirty_watch_list.push(w1.index() as u32);
                }
            }
        }
        // JIT guard bit: mark deleted clauses in the compiled length range
        // (3-12) so JIT code skips them without recompilation (#8202).
        // When the compiled formula is stashed for delta recompilation (#8228),
        // guard bits cannot be set. Instead, mark the clause's variables dirty
        // so delta recompile regenerates their JIT functions instead of
        // memcpy'ing stale code that references this deleted clause (#8241).
        //
        // (#8356) When the formula is guardless, guard bits are inert (the JIT
        // code doesn't check them). Mark variables dirty instead. The formula
        // is typically already stashed by reduce_db's pre-deletion invalidation,
        // but this handles other deletion paths (inprocessing) correctly too.
        //
        // (#8397) Guard bit must be set for ANY JIT-compiled clause at deletion,
        // regardless of current tier eligibility. The JIT compiles tier-1 learned
        // clauses based on tier2_lbd at compile time, but reduce_db may delete them
        // after recompute_tier() shifts the threshold. Use OR: is_jit_eligible
        // catches currently-eligible clauses, jit_guards.is_active catches clauses
        // compiled under a previous threshold that are no longer "eligible".
        if let Some(ref mut gc_occ) = self.gc_occ {
            let lits = self.arena.literals(clause_idx);
            gc_occ.remove_clause(clause_idx, lits);
        }
        self.arena.delete(clause_idx);
        self.cold.clause_db_changes += 1; // BVE dual-signal fixpoint guard (#3416)
    }

    /// Delete a clause with uniform watch removal, reason protection, and proof logging.
    ///
    /// This is the single entry point for clause deletion during inprocessing.
    /// All techniques should call this instead of directly manipulating
    /// `clause_db`, `watches`, and `proof_manager`.
    pub(super) fn delete_clause_checked(
        &mut self,
        clause_idx: usize,
        reason_policy: ReasonPolicy,
    ) -> DeleteResult {
        // CaDiCaL clause.cpp: deletion only during inprocessing at level 0.
        // Soundness-critical: deleting at higher levels corrupts solver state (#4560).
        assert_eq!(
            self.decision_level, 0,
            "BUG: delete_clause_checked at decision level {}",
            self.decision_level,
        );
        self.ensure_reason_clause_marks_current();
        if !self.can_delete_clause(clause_idx, reason_policy) {
            return DeleteResult::Skipped;
        }
        if !self.lrat_clause_unit_rederivations_ready_for_delete(clause_idx) {
            return DeleteResult::Skipped;
        }

        match reason_policy {
            ReasonPolicy::Skip => {
                if self.is_reason_clause_marked(clause_idx) {
                    unreachable!(
                        "can_delete_clause rejected reason-protected clause with ReasonPolicy::Skip"
                    )
                }
            }
            ReasonPolicy::ClearLevel0 => {
                // BVE pattern: level-0 reason clauses are safe to delete because
                // conflict analysis drops level-0 literals entirely. Clear the
                // reason reference first.
                //
                // Optimization: for live level-0 reasons, scan only the clause's
                // literals instead of all variables. The invariant
                // reason[vi] == Some(cref) implies vi appears in the clause
                // (proven in test_reason_clause_contains_propagated_variable).
                // This reduces cost from O(num_vars) to O(clause_len) per
                // deletion — critical for BVE which deletes O(K) clauses.
                //
                // A second full scan clears stale non-root reason references left
                // behind by probe/backtrack or in-place rewrites; these edges are
                // no longer semantically live once the clause is being deleted.
                let cref = ClauseRef(clause_idx as u32);
                let clause_len = self.arena.len_of(clause_idx);
                let mut cleared_any_reason = false;

                if self.is_reason_clause_marked(clause_idx) {
                    if self.cold.lrat_enabled {
                        self.materialize_level0_unit_proofs();
                        let cid = self.clause_id(cref);
                        for i in 0..clause_len {
                            let lit = self.arena.literal(clause_idx, i);
                            let vi = lit.variable().index();
                            if vi < self.num_vars
                                && self.var_data[vi].reason == cref.0
                                && self.var_data[vi].level == 0
                                && !self.lrat_delete_unit_derivation_hints_ready_for_clause(
                                    clause_idx, i, cid,
                                )
                            {
                                return DeleteResult::Skipped;
                            }
                        }
                    }
                    for i in 0..clause_len {
                        let lit = self.arena.literal(clause_idx, i);
                        let vi = lit.variable().index();
                        if vi < self.num_vars
                            && self.var_data[vi].reason == cref.0
                            && self.var_data[vi].level == 0
                        {
                            // Minimal trail rewind (#8095): record the trail position
                            // of this variable whose reason is being cleared. BCP must
                            // re-check from here to ensure no propagation is missed.
                            self.mark_trail_affected(self.var_data[vi].trail_pos as usize);

                            // ClearLevel0 victims: preserve a checker-visible
                            // unit proof ID before clearing their reason (#5686).
                            // The clause C is about to be deleted. Instead of saving
                            // C's ID (which would become stale), derive a unit clause
                            // {lit} from C + the proof IDs of the other falsified
                            // literals. The new unit's ID replaces C's in the chain.
                            if self.cold.lrat_enabled {
                                let cid = self.clause_id(cref);
                                if cid != 0 {
                                    let unit_id =
                                        self.emit_lrat_delete_unit_derivation(clause_idx, i, cid);
                                    if unit_id != 0 {
                                        self.record_level0_proof_id_for_lit(lit, unit_id);
                                    }
                                }
                            }
                            if self.cold.lrat_enabled {
                                self.lower_lrat_level0_unit_materialize_cursor_for_var(vi);
                            }
                            self.var_data[vi].reason = NO_REASON;
                            cleared_any_reason = true;
                        }
                    }
                }

                // Stale reason cleanup for unassigned/non-level-0 variables.
                //
                // During watch-free BVE (watches_disconnected), skip entirely —
                // stale references are deferred to the post-BVE cleanup pass.
                //
                // During deferred stale-reason mode (defer_stale_reason_cleanup),
                // push affected variable indices from the clause onto the dirty
                // list instead of scanning all variables. This reduces per-deletion
                // cost from O(num_vars) to O(clause_len). The dirty list is
                // processed by clear_stale_reasons() after the batch completes.
                if self.watches_disconnected {
                    // Skip entirely — post-BVE cleanup handles it.
                } else if self.defer_stale_reason_cleanup {
                    // Collect stale variable indices from the clause's literals.
                    // Block 1 above already cleared level-0 vars with reason == cref;
                    // here we catch non-level-0 stale refs (backtracked variables).
                    for i in 0..clause_len {
                        let lit = self.arena.literal(clause_idx, i);
                        let vi = lit.variable().index();
                        if vi < self.num_vars
                            && self.var_data[vi].reason == cref.0
                            && self.var_data[vi].level != 0
                        {
                            self.stale_reasons.push(vi as u32);
                        }
                    }
                } else {
                    for vi in 0..self.num_vars {
                        if self.var_data[vi].reason == cref.0 {
                            self.var_data[vi].reason = NO_REASON;
                            cleared_any_reason = true;
                        }
                    }
                }

                // Postcondition: when NOT in deferred or watch-free mode, no
                // variable should reference this clause.
                #[cfg(debug_assertions)]
                if !self.watches_disconnected && !self.defer_stale_reason_cleanup {
                    for vi in 0..self.num_vars {
                        debug_assert!(
                            self.var_data[vi].reason != cref.0,
                            "BUG: var {vi} still references deleted clause {clause_idx} as reason \
                             after ClearLevel0 (level={}, assigned={})",
                            self.var_data[vi].level,
                            self.var_is_assigned(vi),
                        );
                    }
                }
                if cleared_any_reason {
                    // Incrementally unmark this clause as a reason (#8100).
                    self.unmark_reason_clause(clause_idx);
                }
            }
        }

        self.delete_clause_observed(clause_idx, reason_policy);
        DeleteResult::Deleted
    }

    /// Delete after external reason checks while preserving observed side effects.
    ///
    /// # Contract
    ///
    /// Callers must guarantee that reason-clause protection has been verified
    /// externally before calling this. When `reason_policy` is `Skip`, the
    /// clause must not be an active reason for any assigned variable.
    /// The `debug_assert!` below samples this invariant (#4674).
    pub(super) fn delete_clause_unchecked(
        &mut self,
        clause_idx: usize,
        reason_policy: ReasonPolicy,
    ) -> DeleteResult {
        if !self.arena.is_active(clause_idx) {
            return DeleteResult::Skipped;
        }
        if self.is_pending_theory_conflict_clause(clause_idx) {
            return DeleteResult::Skipped;
        }
        if !self.lrat_clause_unit_rederivations_ready_for_delete(clause_idx) {
            return DeleteResult::Skipped;
        }

        // Sampled reason-protection invariant (#4674): when policy is Skip,
        // the caller guarantees this clause is not an active reason.
        debug_assert!(
            reason_policy == ReasonPolicy::ClearLevel0 || !self.is_reason_clause_marked(clause_idx),
            "BUG: delete_clause_unchecked called on reason clause {clause_idx} with Skip policy",
        );

        self.delete_clause_observed(clause_idx, reason_policy);
        DeleteResult::Deleted
    }

    /// Apply a precomputed decompose rewrite mutation without proof side effects.
    ///
    /// Decompose emits proof additions and deletions in two global phases for LRAT
    /// validity across the entire rewrite batch. This helper applies the planned
    /// clause-database edits after proof emission is complete.
    ///
    /// Watch lists are maintained incrementally (#8093): watches are detached
    /// before clause deletion/replacement and re-attached after replacement.
    /// This eliminates the need for a full `rebuild_watches()` after the
    /// rewrite pass, reducing cost from O(active_clauses) to O(mutations).
    pub(super) fn apply_decompose_mutation(&mut self, mutation: &crate::decompose::ClauseMutation) {
        // Decompose operates at decision level 0 only (same as all inprocessing).
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: apply_decompose_mutation at decision level {}",
            self.decision_level,
        );

        // #5031: Mark that inprocessing has permanently modified clause_db.
        // reset_search_state() will rebuild from original_clauses on next solve.
        self.cold.inprocessing_modified_clause_db = true;

        match mutation {
            crate::decompose::ClauseMutation::Deleted { clause_idx, .. }
            | crate::decompose::ClauseMutation::Unit { clause_idx, .. } => {
                debug_assert!(
                    *clause_idx < self.arena.len(),
                    "BUG: decompose mutation references out-of-bounds clause_idx {clause_idx}",
                );
                if self.arena.is_active(*clause_idx) {
                    // Reason clause protection (#5222): clear level-0 reason
                    // references before deletion, same as delete_clause_checked
                    // with ClearLevel0 policy.
                    self.ensure_reason_clause_marks_current();
                    if self.is_reason_clause_marked(*clause_idx) {
                        if self.cold.lrat_enabled {
                            self.materialize_level0_unit_proofs();
                        }
                        let cref = ClauseRef(*clause_idx as u32);
                        let clause_len = self.arena.len_of(*clause_idx);
                        if self.cold.lrat_enabled {
                            let cid = self.clause_id(cref);
                            for i in 0..clause_len {
                                let lit = self.arena.literal(*clause_idx, i);
                                let vi = lit.variable().index();
                                if vi < self.num_vars
                                    && self.var_data[vi].reason == cref.0
                                    && self.var_data[vi].level == 0
                                    && !self.lrat_delete_unit_derivation_hints_ready_for_clause(
                                        *clause_idx,
                                        i,
                                        cid,
                                    )
                                {
                                    return;
                                }
                            }
                        }
                        for i in 0..clause_len {
                            let lit = self.arena.literal(*clause_idx, i);
                            let vi = lit.variable().index();
                            if vi < self.num_vars
                                && self.var_data[vi].reason == cref.0
                                && self.var_data[vi].level == 0
                            {
                                // ClearLevel0 victims: preserve a checker-visible
                                // unit proof ID before deletion clears their reason (#5686).
                                if self.cold.lrat_enabled {
                                    let cid = self.clause_id(cref);
                                    if cid != 0 {
                                        let unit_id = self.emit_lrat_delete_unit_derivation(
                                            *clause_idx,
                                            i,
                                            cid,
                                        );
                                        if unit_id != 0 {
                                            self.record_level0_proof_id_for_lit(lit, unit_id);
                                        }
                                    }
                                }
                                if self.cold.lrat_enabled {
                                    self.lower_lrat_level0_unit_materialize_cursor_for_var(vi);
                                }
                                self.var_data[vi].reason = NO_REASON;
                            }
                        }
                        // Incrementally unmark this clause as a reason (#8100).
                        self.unmark_reason_clause(*clause_idx);
                    }
                    // Incremental watch maintenance (#8093): detach watches
                    // before deleting the clause so that stale watch entries
                    // do not linger until a full rebuild_watches() sweep.
                    if !self.watches_disconnected {
                        let clause_len = self.arena.len_of(*clause_idx);
                        if clause_len >= 2 {
                            let lit0 = self.arena.literal(*clause_idx, 0);
                            let lit1 = self.arena.literal(*clause_idx, 1);
                            self.detach_clause_watches(ClauseRef(*clause_idx as u32), lit0, lit1);
                        }
                    }
                    if let Some(ref mut gc_occ) = self.gc_occ {
                        let lits = self.arena.literals(*clause_idx);
                        gc_occ.remove_clause(*clause_idx, lits);
                    }
                    // Incremental BVE occ + dirty candidate + bve_marked + JIT
                    // maintenance (#8096, #8202): use the wrapper for irredundant
                    // clauses so all side-effects stay in sync.
                    if !self.arena.is_learned(*clause_idx) {
                        let lits: Vec<Literal> = self.arena.literals(*clause_idx).to_vec();
                        self.note_irredundant_clause_removed_for_bve(*clause_idx, &lits);
                    } else {
                        // JIT dirty marking (#8202, #8241): for non-irredundant
                        // tier-1 learned clauses, mark JIT dirty vars directly.
                    }
                    self.drain_pending_garbage_mark(*clause_idx);
                    self.stats.clear_bcp_learned_1963_blocker_cert(*clause_idx);
                    self.arena.delete(*clause_idx);
                }
            }
            crate::decompose::ClauseMutation::Replaced {
                clause_idx, new, ..
            } => {
                debug_assert!(
                    *clause_idx < self.arena.len(),
                    "BUG: decompose mutation references out-of-bounds clause_idx {clause_idx}",
                );
                debug_assert!(
                    !new.is_empty(),
                    "BUG: decompose replacement with empty literals for clause {clause_idx}",
                );
                debug_assert!(
                    new.iter().all(|l| l.variable().index() < self.num_vars),
                    "BUG: decompose replacement literal variable out of range (num_vars={})",
                    self.num_vars,
                );
                debug_assert!(
                    {
                        let mut vars: Vec<u32> = new.iter().map(|l| l.variable().0).collect();
                        vars.sort_unstable();
                        vars.windows(2).all(|w| w[0] != w[1])
                    },
                    "BUG: decompose replacement has duplicate variables for clause {clause_idx}",
                );
                if self.arena.is_active(*clause_idx) {
                    // CaDiCaL decompose.cpp has zero reason-clause protection
                    // at level 0 — replacement is in-place so the ClauseRef
                    // remains valid as a reason reference (#5237, R1:1113).
                    let was_irredundant = !self.arena.is_learned(*clause_idx);
                    let old_lits = self.arena.literals(*clause_idx).to_vec();
                    let old_clause_id = self.clause_id(ClauseRef(*clause_idx as u32));
                    if self.cold.lrat_enabled {
                        self.materialize_level0_unit_proofs();
                        if !self.lrat_replacement_level0_reason_units_ready(
                            *clause_idx,
                            &old_lits,
                            new,
                            old_clause_id,
                        ) {
                            return;
                        }
                    }

                    // Incremental watch maintenance (#8093): detach old watches
                    // before replacement. The old watched literals may not appear
                    // in the replacement clause.
                    if !self.watches_disconnected {
                        let old_len = self.arena.len_of(*clause_idx);
                        if old_len >= 2 {
                            let old_lit0 = self.arena.literal(*clause_idx, 0);
                            let old_lit1 = self.arena.literal(*clause_idx, 1);
                            self.detach_clause_watches(
                                ClauseRef(*clause_idx as u32),
                                old_lit0,
                                old_lit1,
                            );
                        }
                    }

                    self.clear_level0_reasons_removed_by_replacement(
                        *clause_idx,
                        &old_lits,
                        new,
                        old_clause_id,
                    );
                    if let Some(ref mut gc_occ) = self.gc_occ {
                        gc_occ.remove_clause(*clause_idx, &old_lits);
                    }
                    // Incremental BVE occ + dirty candidate + bve_marked + JIT
                    // maintenance (#8096, #8202): use the wrapper for irredundant
                    // clauses so all side-effects stay in sync.
                    if was_irredundant {
                        self.note_irredundant_clause_replaced_for_bve(*clause_idx, &old_lits, new);
                    } else {
                        // JIT dirty marking (#8202, #8241): for non-irredundant
                        // tier-1 learned clauses, mark JIT dirty vars directly.
                    }
                    self.drain_pending_garbage_mark(*clause_idx);
                    self.stats.clear_bcp_learned_1963_blocker_cert(*clause_idx);
                    self.arena.replace(*clause_idx, new);
                    if let Some(ref mut gc_occ) = self.gc_occ {
                        gc_occ.add_clause(*clause_idx, new);
                    }

                    // Incremental watch maintenance (#8093): attach new watches
                    // after replacement. Reorder watched literals for optimal
                    // placement before attaching.
                    if !self.watches_disconnected && new.len() >= 2 {
                        let clause_ref = ClauseRef(*clause_idx as u32);
                        let new_is_binary = new.len() == 2;
                        let watched = {
                            let lits = self.arena.literals_mut(*clause_idx);
                            Self::prepare_watched_literals_with_state(
                                &self.vals,
                                &self.var_data,
                                lits,
                                WatchOrderPolicy::AssignmentScore,
                            )
                            .expect("replaced clause has len >= 2")
                        };
                        self.attach_clause_watches(clause_ref, watched, new_is_binary);
                    }

                    if was_irredundant {
                        self.mark_factor_candidates_dirty_clause(new);
                    }
                }
            }
        }
    }
}
