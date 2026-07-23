// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared clause mutation helpers for inprocessing passes.
//!
//! All inprocessing techniques that delete, replace, or strengthen clauses
//! should use these helpers instead of directly manipulating the clause database
//! and watch lists. This ensures uniform handling of:
//!
//! - Watch removal/addition
//! - Reason clause protection
//! - DRAT proof logging (add-before-delete ordering)
//! - Unit/empty clause detection
//!
//! # Reference
//!
//! CaDiCaL centralizes mutation primitives in `clause.cpp` (`mark_garbage`)
//! and `watch.hpp` (`remove_watch`, `watch_clause`). This module serves the
//! same role for AY.

use super::*;

/// Policy for handling reason clauses during deletion.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ReasonPolicy {
    /// Skip deletion if clause is a current reason (default for most techniques).
    Skip,
    /// Clear level-0 reason references, then delete (BVE behavior).
    ClearLevel0,
}

/// Result of attempting to delete a clause.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum DeleteResult {
    /// Clause was deleted.
    Deleted,
    /// Clause was skipped (invalid index, already empty, or protected reason).
    Skipped,
}

/// Result of replacing a clause with new (shorter) literals.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ReplaceResult {
    /// Clause was replaced with 2+ literals (normal clause).
    Replaced,
    /// Clause was replaced and became a unit — caller should propagate.
    Unit,
    /// Clause was replaced and became empty — UNSAT derived.
    Empty,
    /// Clause was skipped (invalid index, already empty, or protected reason).
    Skipped,
}

/// Result of adding a new irredundant clause with watches.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum AddResult {
    /// Clause was added as a normal 2+ literal clause.
    Added(ClauseRef),
    /// Clause was added as a unit — literal enqueued for propagation.
    Unit(ClauseRef),
    /// Clause was empty — UNSAT derived.
    Empty,
}

impl Solver {
    /// Clear deferred-HBR garbage mark and keep `pending_garbage_count` in sync.
    ///
    /// Pending marks are created in probing, then normally consumed by
    /// `collect_level0_garbage`. If another mutation path deletes/replaces the
    /// clause first, we still need to drain the mark to avoid a stale counter.
    #[inline]
    pub(super) fn drain_pending_garbage_mark(&mut self, clause_idx: usize) -> bool {
        if clause_idx >= self.arena.len() {
            return false;
        }
        if !self.arena.is_pending_garbage(clause_idx) {
            return false;
        }
        self.arena.set_pending_garbage(clause_idx, false);
        self.pending_garbage_count = self.pending_garbage_count.saturating_sub(1);
        true
    }

    /// Return whether a clause can be deleted under `reason_policy`.
    ///
    /// This centralizes the precondition used by preprocess/inprocessing passes
    /// before they snapshot clauses for reconstruction metadata.
    #[inline]
    pub(super) fn can_delete_clause(&self, clause_idx: usize, reason_policy: ReasonPolicy) -> bool {
        if !self.arena.is_active(clause_idx) {
            return false;
        }
        if self.is_pending_theory_conflict_clause(clause_idx) {
            return false;
        }
        if !self.is_reason_clause_marked(clause_idx) {
            return true;
        }
        matches!(reason_policy, ReasonPolicy::ClearLevel0)
    }

    /// Delete a clause after capturing a literal snapshot for side effects
    /// such as reconstruction metadata.
    ///
    /// The callback is executed only when deletion is allowed by
    /// `can_delete_clause` under the requested `reason_policy`.
    #[inline]
    pub(super) fn delete_clause_with_snapshot<F>(
        &mut self,
        clause_idx: usize,
        reason_policy: ReasonPolicy,
        snapshot_consumer: F,
    ) -> DeleteResult
    where
        F: FnOnce(&mut Self, Vec<Literal>),
    {
        self.ensure_reason_clause_marks_current();
        if !self.can_delete_clause(clause_idx, reason_policy) {
            return DeleteResult::Skipped;
        }
        let clause_lits = self.arena.literals(clause_idx).to_vec();
        snapshot_consumer(self, clause_lits);
        self.delete_clause_checked(clause_idx, reason_policy)
    }

    // delete_clause_observed, delete_clause_checked, delete_clause_unchecked,
    // apply_decompose_mutation extracted to mutate_delete.rs

    #[inline]
    pub(super) fn delete_binary_clause_watches(&mut self, clause_idx: usize) {
        if self.arena.len_of(clause_idx) != 2 {
            return;
        }
        let clause_ref = ClauseRef(clause_idx as u32);
        let lit0 = self.arena.literal(clause_idx, 0);
        let lit1 = self.arena.literal(clause_idx, 1);
        self.remove_watch(lit0, clause_ref);
        self.remove_watch(lit1, clause_ref);
    }

    fn add_clause_watched_impl(
        &mut self,
        lits: &mut [Literal],
        learned: bool,
        forward_check_derived: bool,
    ) -> AddResult {
        // No duplicate variables in the clause being added.
        // Soundness-critical: duplicates break 2WL invariant (#4560).
        debug_assert!(
            {
                let mut vars: Vec<u32> = lits.iter().map(|l| l.variable().0).collect();
                vars.sort_unstable();
                vars.windows(2).all(|w| w[0] != w[1])
            },
            "BUG: add_clause_watched_impl: duplicate variables in lits [{}]",
            lits.iter()
                .map(|l| l.to_dimacs().to_string())
                .collect::<Vec<_>>()
                .join(", "),
        );
        // All literal variables must be in range.
        // Soundness-critical: out-of-range causes silent corruption (#4560).
        // MUST be assert!() not debug_assert!() — release builds silently
        // corrupt the clause DB if this check is removed, causing index-out-
        // of-bounds panics later in BCP (#5141: 90% crash rate on SAT-COMP).
        assert!(
            lits.iter().all(|l| l.variable().index() < self.num_vars),
            "BUG: literal variable out of range (num_vars={})",
            self.num_vars,
        );
        // Catch any inprocessing technique creating clauses with eliminated variables.
        #[cfg(debug_assertions)]
        debug_assert!(
            lits.iter()
                .all(|l| !self.var_lifecycle.is_removed(l.variable().index())),
            "BUG: add_clause_watched_impl: clause contains eliminated variable \
             (lits=[{}], eliminated=[{}])",
            lits.iter()
                .map(|l| l.to_dimacs().to_string())
                .collect::<Vec<_>>()
                .join(", "),
            lits.iter()
                .filter(|l| self.var_lifecycle.is_removed(l.variable().index()))
                .map(|l| format!("var{}", l.variable().index()))
                .collect::<Vec<_>>()
                .join(", "),
        );
        if lits.is_empty() {
            // Empty derived clause: the caller (BVE/HTR/factorize) already
            // emitted the proof entry via proof_emit_add_prechecked with
            // proper hints. mark_empty_clause only fires if that emission
            // didn't set empty_clause_in_proof (#5236 Gap 1).
            self.mark_empty_clause();
            return AddResult::Empty;
        }

        // Watch-free BVE mode (CaDiCaL fastelim.cpp:463): skip watch literal
        // preparation and attachment when watches are disconnected. Clauses are
        // still added to the arena; watches are rebuilt in bulk after BVE.
        let watched = if self.watches_disconnected {
            if lits.len() >= 2 {
                Some((lits[0], lits[1]))
            } else {
                None
            }
        } else {
            self.prepare_watched_literals(lits, WatchOrderPolicy::AssignmentScore)
        };
        // Inprocessing products (BVE resolvents, HTR resolvents, factorization
        // clauses) are forward-checked as derived (RUP check). Preserved learned
        // clauses from previous sessions are forward-checked as originals (axioms)
        // since they were already proven in the previous proof context (#3882).
        let clause_idx = self.add_clause_db_checked(lits, learned, forward_check_derived, &[]);
        let clause_ref = ClauseRef(clause_idx as u32);
        self.cold.clause_db_changes += 1; // BVE dual-signal fixpoint guard (#3416)

        if let Some((lit0, lit1)) = watched {
            if !self.watches_disconnected {
                self.attach_clause_watches(clause_ref, (lit0, lit1), lits.len() == 2);
            }

            // Soundness fix (#8222): skip unit/conflict detection when watches
            // are disconnected (BVE mode). Without prepare_watched_literals(),
            // lit0 and lit1 are arbitrary — both might be false at level 0
            // while other literals in the clause are unassigned, causing a
            // spurious empty-clause or incorrect unit propagation. CaDiCaL
            // (elim.cpp:643, clause.cpp:643) asserts !watching() and defers
            // all conflict/unit detection to post-reconnection propagation.
            // Unit resolvents (len==1) are handled in the else branch below
            // and correctly detect units/conflicts on the single literal.
            if !self.watches_disconnected {
                // Check for unit or conflict at level 0.
                let lit0_val = self.lit_value(lit0);
                let lit1_val = self.lit_value(lit1);

                if lit0_val == Some(false) && lit1_val == Some(false) {
                    if self.decision_level == 0 {
                        // All literals false at level 0: derive empty clause from
                        // this clause + level-0 assignment reasons (#5236 Gap 1).
                        // Use BFS transitive closure for complete LRAT chain (#7108).
                        if self.cold.lrat_enabled {
                            let hints =
                                self.collect_empty_clause_hints_for_conflict(clause_ref, lits);
                            self.mark_empty_clause_with_hints(&hints);
                        } else {
                            self.mark_empty_clause();
                        }
                    }
                } else if lit0_val.is_none() && lit1_val == Some(false) {
                    self.enqueue(lit0, Some(clause_ref));
                }
            }

            AddResult::Added(clause_ref)
        } else {
            // Unit clause
            let unit_lit = lits[0];
            if !self.var_is_assigned(unit_lit.variable().index()) {
                // Unit clause: enqueue with reason=None. Conflict analysis
                // requires reason clauses of length >= 2 (propagated literal +
                // antecedents). A unit clause has no antecedents, so using it
                // as a reason breaks resolution (#6242, #6257).
                // Store proof ID for LRAT and clause-trace (#6368).
                let cid = self.clause_id(clause_ref);
                if cid != 0 {
                    self.record_unit_proof_id_for_lit(unit_lit, cid);
                }
                // Minimal trail rewind (#8095): record the trail position where
                // this new unit will be enqueued so rebuild_watches can rewind
                // precisely instead of to 0.
                if self.decision_level == 0 {
                    self.mark_trail_affected(self.trail.len());
                }
                self.enqueue(unit_lit, None);
            } else if self.lit_value(unit_lit) == Some(false) && self.decision_level == 0 {
                // Unit contradicts level-0 assignment: derive empty clause
                // from this clause + existing assignment reason (#5236 Gap 1).
                // Use BFS transitive closure for complete LRAT chain (#7108).
                if self.cold.lrat_enabled {
                    let hints =
                        self.collect_empty_clause_hints_for_conflict(clause_ref, &[unit_lit]);
                    self.mark_empty_clause_with_hints(&hints);
                } else {
                    self.mark_empty_clause();
                }
            }
            AddResult::Unit(clause_ref)
        }
    }

    /// Add a new irredundant clause with watches and unit propagation.
    ///
    /// Handles reordering for optimal watch selection, adding to the clause
    /// database, setting up watches (binary vs long), and detecting unit/empty
    /// clauses at decision level 0.
    ///
    /// Proof logging (DRAT add) is NOT done here — callers handle it because
    /// some techniques (BVE, HTR) log before calling, while others (factorization)
    /// skip proof logging entirely.
    ///
    /// # Arguments
    ///
    /// * `lits` - Mutable literal slice; will be reordered for watch placement.
    pub(super) fn add_clause_watched(&mut self, lits: &mut [Literal]) -> AddResult {
        self.add_clause_watched_impl(lits, false, true)
    }

    /// Add an irredundant clause whose validity is established OUT OF BAND (e.g. a
    /// DPR PR symmetry lex-leader verified by the external dpr-trim→cake_lpr loop,
    /// #8011) rather than by an internal RUP/RAT forward check.
    ///
    /// Like [`Self::add_clause_watched`] but with `forward_check_derived = false`,
    /// so the forward DRUP checker treats the clause as a trusted axiom (no RUP
    /// obligation). The caller MUST have already emitted the corresponding trusted
    /// proof step (`proof_emit_add_pr`) so the proof stream stays complete.
    pub(super) fn add_clause_watched_trusted(&mut self, lits: &mut [Literal]) -> AddResult {
        self.add_clause_watched_impl(lits, false, false)
    }

    /// Add a learned clause from a previous solve session, with full watch setup.
    ///
    /// Used for carrying learned clauses across solver recreations (branch-and-
    /// bound iterations). When DRAT/LRAT proof output is enabled, the clause is
    /// emitted as an axiom — it was already derived in the previous session's
    /// proof, so it is trusted in the new proof context. Without this emission,
    /// any UNSAT derivation that depends on a preserved clause would produce an
    /// incomplete proof that `drat-trim` rejects. Fixes #3882.
    pub(super) fn add_preserved_learned_watched(&mut self, lits: &mut [Literal]) -> bool {
        // Emit as axiom in the proof stream before adding to the clause DB.
        // The subsequent add_clause_watched_impl → add_clause_db_checked path
        // clears pending_forward_check (#4641 contract). forward_check_derived=
        // false so the forward checker treats this as an original (axiom), not
        // a derived clause requiring RUP verification.
        if self.proof_manager.is_some() && !lits.is_empty() {
            let _ = self.proof_emit_add_prechecked(lits, &[], ProofAddKind::Axiom);
        }
        !matches!(
            self.add_clause_watched_impl(lits, true, false),
            AddResult::Empty
        )
    }
}

#[cfg(test)]
#[path = "mutate_tests.rs"]
mod tests;
