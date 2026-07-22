// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Binary clause deduplication + hyper-unary unit discovery.
//!
//! Reference: CaDiCaL `deduplicate.cpp`.

use super::super::mutate::ReasonPolicy;
use super::super::*;
use crate::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};

impl Solver {
    /// Decide which duplicate clause should be deleted.
    ///
    /// Returns `Some(idx_to_delete)` when one duplicate can be removed,
    /// or `None` when both clauses are protected.
    #[inline]
    fn choose_duplicate_for_deletion(
        &self,
        keeper_idx: usize,
        candidate_idx: usize,
    ) -> Option<usize> {
        let keeper_deletable = self.can_delete_clause(keeper_idx, ReasonPolicy::Skip);
        let candidate_deletable = self.can_delete_clause(candidate_idx, ReasonPolicy::Skip);

        match (keeper_deletable, candidate_deletable) {
            (false, false) => None,
            (false, true) => Some(candidate_idx),
            (true, false) => Some(keeper_idx),
            (true, true) => {
                let keeper_is_learned = self.arena.is_learned(keeper_idx);
                let candidate_is_learned = self.arena.is_learned(candidate_idx);
                if keeper_is_learned && !candidate_is_learned {
                    Some(keeper_idx)
                } else {
                    Some(candidate_idx)
                }
            }
        }
    }

    /// Remove duplicate binary clauses and derive hyper-unary units.
    ///
    /// Called after decompose rounds, where literal substitution can produce
    /// duplicate binaries. Also detects `(a ∨ b)` + `(a ∨ ¬b)` patterns that
    /// imply the unit `a`.
    ///
    /// Returns `true` if UNSAT is detected.
    pub(in crate::solver) fn deduplicate_binary_clauses(&mut self) -> bool {
        if !self.enter_inprocessing() || self.has_empty_clause {
            return self.has_empty_clause;
        }
        // Deduplication deletes binary clauses — maintained incrementally via
        // per-clause note_irredundant_clause_removed_for_bve calls (#8096).

        let mut duplicate_candidates = Vec::new();
        let mut duplicate_seen = HashSet::default();
        let mut hyper_units: HashMap<Literal, (usize, usize)> = HashMap::default();

        for lit_idx in 0..self.num_vars.saturating_mul(2) {
            let lit = Literal::from_index(lit_idx);
            let var_idx = lit.variable().index();
            if self.var_lifecycle.is_removed(var_idx) {
                continue;
            }

            let watch_list = self.watches.get_watches(lit);
            if watch_list.len() < 2 {
                continue;
            }

            let mut keeper_by_other: HashMap<Literal, usize> = HashMap::default();
            let mut seen_polarities: HashMap<usize, (Option<usize>, Option<usize>)> =
                HashMap::default();

            for wi in 0..watch_list.len() {
                if !watch_list.is_binary(wi) {
                    continue;
                }

                let clause_idx = watch_list.clause_ref(wi).0 as usize;
                if !self.arena.is_active(clause_idx) {
                    continue;
                }
                if self.arena.is_pending_garbage(clause_idx) {
                    continue;
                }

                let other = watch_list.blocker(wi);

                // Duplicate detection: only from the smaller literal's watch list.
                // Binary clause {A, B} appears in both watch(A) and watch(B).
                // Without this guard, scanning from A marks one copy as a
                // candidate, then scanning from B marks the OTHER copy,
                // deleting both copies of the clause (#5178).
                if other.index() >= lit.index() {
                    if let Some(&keeper_idx) = keeper_by_other.get(&other) {
                        if let Some(delete_idx) =
                            self.choose_duplicate_for_deletion(keeper_idx, clause_idx)
                        {
                            if delete_idx == keeper_idx {
                                keeper_by_other.insert(other, clause_idx);
                            }
                            if duplicate_seen.insert(delete_idx) {
                                duplicate_candidates.push(delete_idx);
                            }
                        }
                    } else {
                        keeper_by_other.insert(other, clause_idx);
                    }
                }

                let by_var = seen_polarities
                    .entry(other.variable().index())
                    .or_insert((None, None));

                if other.is_positive() {
                    if let Some(neg_clause) = by_var.1 {
                        hyper_units.entry(lit).or_insert((clause_idx, neg_clause));
                    }
                    by_var.0.get_or_insert(clause_idx);
                } else {
                    if let Some(pos_clause) = by_var.0 {
                        hyper_units.entry(lit).or_insert((clause_idx, pos_clause));
                    }
                    by_var.1.get_or_insert(clause_idx);
                }
            }
        }

        let mut unit_entries: Vec<(Literal, (usize, usize))> = hyper_units.into_iter().collect();
        unit_entries.sort_unstable_by_key(|(lit, _)| lit.0);
        // Ensure level-0 variables have materialized unit proof IDs before
        // we reference them in empty-clause or unit derivation hints (#7108).
        if self.cold.lrat_enabled && !unit_entries.is_empty() {
            self.materialize_level0_unit_proofs();
        }
        let mut enqueued_unit = false;
        for (unit, (c0, c1)) in unit_entries {
            match self.lit_value(unit) {
                Some(true) => continue,
                Some(false) => {
                    // Hyper-unary unit contradicts existing level-0 assignment.
                    // Emit the unit derivation, then derive the empty clause
                    // with proper LRAT hints (#5236 Gap 1).
                    if self.cold.lrat_enabled {
                        let mut unit_hints = Vec::with_capacity(2);
                        let h0 = self.clause_id(ClauseRef(c0 as u32));
                        if h0 != 0 {
                            unit_hints.push(h0);
                        }
                        let h1 = self.clause_id(ClauseRef(c1 as u32));
                        if h1 != 0 && !unit_hints.contains(&h1) {
                            unit_hints.push(h1);
                        }
                        // Step 1: derive the contradicting unit clause.
                        let unit_pid =
                            self.proof_emit_unit(unit, &unit_hints, ProofAddKind::Derived);
                        // Step 2: derive empty clause from the unit and the
                        // existing assignment's reason chain (#7108).
                        // collect_empty_clause_hints_for_unit_contradiction
                        // materializes level-0 unit proofs and collects the
                        // existing proof ID. If the chain is incomplete (< 2
                        // hints), downgrade to TrustedTransform to avoid LRAT
                        // checker rejection.
                        let hints =
                            self.collect_empty_clause_hints_for_unit_contradiction(unit_pid, unit);
                        // Need 2 DISTINCT hints for empty clause derivation.
                        // After dedup, < 2 unique hints cannot prove [].
                        let unique_count = {
                            let mut u = hints.clone();
                            u.sort_unstable();
                            u.dedup();
                            u.len()
                        };
                        if unique_count >= 2 {
                            self.mark_empty_clause_with_hints(&hints);
                        } else {
                            // Incomplete chain: emit with empty hints so the
                            // LRAT checker treats it as skip-verified (#7108).
                            self.mark_empty_clause_with_hints(&[]);
                        }
                    } else {
                        self.mark_empty_clause();
                    }
                    return true;
                }
                None => {}
            }

            let hint0 = self.clause_id(ClauseRef(c0 as u32));
            let hint1 = self.clause_id(ClauseRef(c1 as u32));
            // Hyper-unary resolution: (a, b) + (¬a, b) → (b).
            // LRAT needs both clause IDs. If either is 0 (clause was
            // suppressed or has no proof ID), fall back to TrustedTransform
            // since the hint chain is incomplete (#7108).
            let (hints, kind) = if self.cold.lrat_enabled && (hint0 == 0 || hint1 == 0) {
                (vec![], ProofAddKind::TrustedTransform)
            } else {
                let mut h = Vec::with_capacity(2);
                if hint0 != 0 {
                    h.push(hint0);
                }
                if hint1 != 0 && !h.contains(&hint1) {
                    h.push(hint1);
                }
                (h, ProofAddKind::Derived)
            };
            let _ = self.proof_emit_unit(unit, &hints, kind);
            self.enqueue(unit, None);
            enqueued_unit = true;
        }

        // CaDiCaL deduplicate.cpp assigns and propagates discovered hyper-unary
        // units before continuing. Without propagation here, chained level-0
        // conflicts stay latent until the caller's next propagate phase.
        if enqueued_unit && self.propagate_check_unsat() {
            return true;
        }

        duplicate_candidates.sort_unstable();
        let mut deleted_count = 0u64;
        for clause_idx in duplicate_candidates {
            if !self.arena.is_active(clause_idx) {
                continue;
            }
            if self.arena.is_pending_garbage(clause_idx) {
                continue;
            }
            // Incremental BVE occ maintenance (#8096): snapshot irredundant
            // literals before deletion.
            let is_irredundant = !self.arena.is_learned(clause_idx);
            let pre_delete_lits: Option<Vec<Literal>> = if is_irredundant {
                Some(self.arena.literals(clause_idx).to_vec())
            } else {
                None
            };
            let _ = self.delete_clause_checked(clause_idx, ReasonPolicy::Skip);
            if let Some(old_lits) = pre_delete_lits {
                self.note_irredundant_clause_removed_for_bve(clause_idx, &old_lits);
            }
            deleted_count += 1;
        }
        self.stats.dedup_deleted += deleted_count;

        self.has_empty_clause
    }
}
