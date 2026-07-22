// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Transitive reduction of the binary implication graph.

use super::super::mutate::ReasonPolicy;
use super::super::*;

impl Solver {
    /// Run transitive reduction (wrapper: always reschedules).
    pub(in crate::solver) fn transred(&mut self) {
        self.transred_body();
        self.inproc_ctrl
            .transred
            .reschedule(self.num_conflicts, TRANSRED_INTERVAL);
        // Record ticks for tick-threshold scheduling (#8148).
        self.cold.last_transred_ticks = self.search_ticks[0] + self.search_ticks[1];
    }

    /// Transitive reduction body — early returns are safe; wrapper handles rescheduling.
    ///
    /// A binary clause `(a -> b)` is transitive if there exists an alternate path
    /// from `a` to `b` through other binary clauses. Transitive clauses can be
    /// safely removed without affecting satisfiability.
    ///
    /// This must be called at decision level 0 (after a restart) for correctness.
    fn transred_body(&mut self) {
        if !self.enter_inprocessing() {
            return;
        }
        // Transred deletes binary clauses — maintained incrementally via
        // per-clause note_irredundant_clause_removed_for_bve calls (#8096).

        // Compute tick-proportional effort budget (#8148).
        // CaDiCaL transred.cpp:30-36 uses propagation delta * permille / 1000.
        // AY uses search_ticks delta for consistency with the unified
        // tick-proportional scheduling model (SET_EFFORT_LIMIT pattern).
        // Clamped to [TRANSRED_MIN_EFFORT, TRANSRED_MAX_EFFORT], floor at 2*active_vars.
        let active_vars = self
            .num_vars
            .saturating_sub(self.var_lifecycle.count_removed()) as u64;
        let ticks_now = self.search_ticks[0] + self.search_ticks[1];
        let ticks_delta = ticks_now.saturating_sub(self.cold.last_transred_ticks);
        let effort = (ticks_delta * TRANSRED_EFFORT_PERMILLE / 1000)
            .clamp(TRANSRED_MIN_EFFORT, TRANSRED_MAX_EFFORT);
        let effort = effort.max(2 * active_vars);

        // Run transitive reduction
        let result = self.inproc.transred_engine.run(
            &self.arena,
            &self.watches,
            &self.vals,
            self.cold.original_clause_boundary,
            effort,
        );
        self.inproc
            .transred_engine
            .set_last_propagations(self.num_propagations);

        // Process failed literals (propagate units).
        // Transred BFS found that probing `src` reaches both `x` and `¬x`,
        // so `¬src` (the stored unit) must be true.
        //
        // For LRAT we need explicit hint chains. Transred's internal BFS
        // doesn't record reason clauses, so we re-probe through the solver's
        // BCP to collect the conflict chain — matching probe.rs's pattern.
        // For DRAT (non-LRAT), empty hints are acceptable.
        for unit in &result.failed_literals {
            if self.var_is_assigned(unit.variable().index()) {
                continue;
            }
            if self.cold.lrat_enabled {
                // Re-probe the negation of the unit through solver BCP.
                // unit = ¬src, so unit.negated() = src — the literal whose
                // implications cause a contradiction.
                let probe_lit = unit.negated();
                self.decide(probe_lit);
                if let Some(conflict_ref) = self.search_propagate() {
                    let lrat_hints = self.collect_probe_conflict_lrat_hints(
                        conflict_ref,
                        probe_lit,
                        Some(*unit),
                    );
                    self.backtrack(0);
                    // LRAT soundness gate: only learn the derived unit when we
                    // have a complete, checker-visible hint chain. With empty
                    // hints, learn_derived_unit emits a hidden TrustedTransform
                    // unit (enqueue_derived_unit downgrades empty-hint LRAT
                    // units) that is stripped from the proof file, leaving later
                    // search-learned clauses that resolve through this level-0
                    // assignment with a missing antecedent (RUP failure). The
                    // unit is a sound optimization, not required for UNSAT, so
                    // skip it when uncertifiable; normal probing re-derives and
                    // properly certifies it later. (Same fix as intree.rs.)
                    if lrat_hints.is_empty() {
                        continue;
                    }
                    if self.learn_derived_unit(*unit, &lrat_hints) {
                        // Level-0 conflict — UNSAT. Remaining failed literals
                        // and transitive deletions are irrelevant.
                        return;
                    }
                } else {
                    // BCP didn't reproduce the conflict. This can happen if
                    // a prior unit's level-0 propagation resolved intermediate
                    // clauses in the BFS chain. Skip this unit; normal probing
                    // will discover and properly certify it later.
                    self.backtrack(0);
                }
            } else {
                self.proof_emit_unit(*unit, &[], ProofAddKind::Derived);
                self.enqueue(*unit, None);
            }
        }

        // Delete transitive clauses
        for clause_ref in &result.transitive_clauses {
            let clause_idx = clause_ref.0 as usize;
            let is_irredundant = clause_idx < self.arena.len()
                && self.arena.is_active(clause_idx)
                && !self.arena.is_learned(clause_idx);
            let pre_delete_lits: Option<Vec<Literal>> = if is_irredundant {
                Some(self.arena.literals(clause_idx).to_vec())
            } else {
                None
            };
            self.delete_clause_checked(clause_idx, ReasonPolicy::Skip);
            // Incremental BVE occ maintenance (#8096).
            if let Some(old_lits) = pre_delete_lits {
                self.note_irredundant_clause_removed_for_bve(clause_idx, &old_lits);
            }
        }

        #[cfg(debug_assertions)]
        {
            // Post-condition: each failed literal from this round must now be assigned
            // (either pre-existing or enqueued above) — UNLESS LRAT mode skipped it
            // because re-probing didn't reproduce the conflict.
            if !self.cold.lrat_enabled {
                for &unit in &result.failed_literals {
                    let var_idx = unit.variable().index();
                    debug_assert!(
                        self.var_is_assigned(var_idx),
                        "BUG: transred() left failed literal {unit:?} unassigned"
                    );
                }
            }

            // Post-condition: each transitive clause is either deleted or retained
            // only because reason-clause protection blocked deletion.
            for &clause_ref in &result.transitive_clauses {
                let clause_idx = clause_ref.0 as usize;
                if clause_idx >= self.arena.len() || !self.arena.is_active(clause_idx) {
                    continue;
                }
                debug_assert!(
                    self.is_reason_clause_marked(clause_idx),
                    "BUG: transred() left transitive clause {clause_idx} active without reason protection"
                );
            }
        }

        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: transred() did not restore decision level to 0"
        );
    }
}
