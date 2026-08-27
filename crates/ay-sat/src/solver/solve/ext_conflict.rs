// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Extension-conflict postprocessing.
//!
//! Computes the backtrack level for a theory conflict clause and applies
//! the conflict as a learned nogood.

use super::super::*;

impl Solver {
    /// Compute the backtrack level for a theory conflict clause.
    ///
    /// Returns the second-highest decision level among assigned literals.
    /// Theory conflicts can't use full 1UIP analysis because some literals
    /// may be decisions without reason clauses.
    fn ext_conflict_backtrack_level(&self, conflict: &[Literal]) -> u32 {
        // Find the two highest distinct decision levels in O(n) without allocation.
        // Cap levels at decision_level to handle stale var_data[].level from
        // prior chrono BT out-of-order assignments (#9148).
        let dl = self.decision_level;
        let mut top1: u32 = 0;
        let mut top2: u32 = 0;
        let mut found_any = false;
        for lit in conflict {
            let idx = lit.variable().index();
            if idx < self.num_vars && self.var_is_assigned(idx) {
                let lev = self.var_data[idx].level.min(dl);
                found_any = true;
                if lev > top1 {
                    top2 = top1;
                    top1 = lev;
                } else if lev > top2 && lev != top1 {
                    top2 = lev;
                }
            }
        }
        let bt = if top1 != top2 && found_any {
            top2
        } else if found_any {
            top1.saturating_sub(1)
        } else {
            0
        };
        debug_assert!(
            bt <= self.decision_level,
            "BUG: ext conflict backtrack_level ({bt}) > decision_level ({})",
            self.decision_level,
        );
        bt
    }

    /// Handle a non-empty theory conflict from an Extension callback.
    ///
    /// Counts the conflict, computes the backtrack level, adds the clause
    /// as a learned nogood, backtracks with extension notification, and
    /// enqueues any resulting unit literal.
    ///
    /// The caller must have already:
    /// - Checked for empty clause (returns UNSAT directly)
    /// - Emitted the TLA trace `DetectConflict` step
    pub(in crate::solver) fn handle_ext_conflict(
        &mut self,
        conflict: Vec<Literal>,
        ext: &mut dyn Extension,
    ) {
        // Theory conflict clause must be non-empty (caller checks for empty)
        debug_assert!(
            !conflict.is_empty(),
            "BUG: handle_ext_conflict called with empty conflict clause"
        );
        // All conflict literals must have variables in range
        debug_assert!(
            conflict
                .iter()
                .all(|l| l.variable().index() < self.num_vars),
            "BUG: theory conflict contains out-of-range variable"
        );
        self.conflicts_since_restart += 1;
        self.num_conflicts += 1;
        self.on_conflict_random_decision();

        // #8452: Track theory conflict for ratio-based restart policy.
        self.cold.ext_conflict_count += 1;
        self.update_theory_conflict_ratio(true);

        // Notify programmatic observer of theory conflict (#8155).
        // TheoryId::Other is used as the SAT layer does not know which
        // specific theory produced the conflict. Finer-grained attribution
        // can be added when the DPLL(T) layer passes theory identity down.
        self.notify_observer_theory_conflict(crate::observer::TheoryId::Other);

        let backtrack_level = self.ext_conflict_backtrack_level(&conflict);

        // DEBUG: trace theory conflict handling for #7935 investigation
        if self.cold.trace_ext_conflict {
            eprintln!(
                "[EXT_CONFLICT] dl={} bt_level={} conflict_len={} lits={:?}",
                self.decision_level,
                backtrack_level,
                conflict.len(),
                conflict
                    .iter()
                    .map(|l| (l.variable().index(), l.is_positive()))
                    .collect::<Vec<_>>()
            );
            for lit in &conflict {
                let var = lit.variable();
                let assigned = self.var_is_assigned(var.index());
                let level = if assigned {
                    self.var_data[var.index()].level
                } else {
                    u32::MAX
                };
                let val = self.var_value_from_vals(var.index());
                eprintln!(
                    "[EXT_CONFLICT]   var={} pos={} assigned={} level={} val={:?}",
                    var.index(),
                    lit.is_positive(),
                    assigned,
                    level,
                    val
                );
            }
        }

        // Backtrack BEFORE adding the theory lemma (CaDiCaL pattern).
        // Adding the lemma pre-backtrack causes three problems:
        // 1. Watches are computed for the wrong (pre-backtrack) assignment state
        // 2. add_theory_lemma may enqueue at the wrong decision level
        // 3. Requires redundant manual unit-check code after backtracking
        // After backtracking, the clause becomes unit (one asserting literal
        // unassigned), and add_theory_lemma handles watch setup and enqueue
        // at the correct level.
        //
        // Lazy theory reason handles are owned by extension-side theory state.
        // Materialize any SAT-trail lazy reasons before popping that state, so
        // chronological backtracking does not leave surviving assignments with
        // stale opaque handles.
        self.materialize_lazy_reasons_through_level_for_backtrack(ext, backtrack_level);
        self.cold.lazy_materialization_failed = false;
        ext.backtrack(backtrack_level);
        self.backtrack(backtrack_level);

        if self.cold.trace_ext_conflict {
            eprintln!(
                "[EXT_CONFLICT] after backtrack: dl={} trail_len={}",
                self.decision_level,
                self.trail.len()
            );
            for lit in &conflict {
                let var = lit.variable();
                let assigned = self.var_is_assigned(var.index());
                let val = self.var_value_from_vals(var.index());
                eprintln!(
                    "[EXT_CONFLICT]   var={} assigned={} val={:?}",
                    var.index(),
                    assigned,
                    val
                );
            }
        }

        // #inc-scoped-lemmas: use the scope-aware variant so mid-solve theory
        // conflict lemmas are disabled when the current assertion scope is
        // popped (identical to the unscoped call when no selectors exist —
        // non-incremental lanes unaffected). Root cause of the eager-lazy
        // post-pop arena corruption: unscoped lemmas desynced the ledger and
        // the arena across pop (see the #inc campaign autopsy).
        //
        // #unguarded-tvalid-lemmas STAGE 1: routed through the conflict-lemma
        // gate — scoped by default (exactly the line above), unscoped when
        // `unguarded_theory_conflict_lemmas` is enabled (the incremental
        // QF_LRA engine lane only). T-validity provenance of THIS conflict
        // vector, verified: it is an Extension conflict
        // (ExtPropagateResult/ExtCheckResult::Conflict or an all-false
        // theory-lemma batch entry from theory_callback.rs), and the eager
        // TheoryExtension builds those clauses by mapping theory `conflict_terms`
        // through `term_to_literal` with the #3826 fail-closed guard (a
        // partial mapping returns Unknown, never a partial clause), then
        // weakens them only via `minimize_conflict_with_levels` (drops
        // literals falsified at level 0 — session-permanent root facts). So
        // every literal is a term-semantic atom literal and the clause is
        // entailed by theory axioms + permanent root facts at EVERY scope.
        // The autopsy hazards above are closed centrally since then: pop()
        // unconditionally clears pending_theory_conflicts, the ledger rebuild
        // normalizes reasons to NO_REASON (#inc-rebuild-reasons), and the
        // reset census counts only non-learned clauses, so a surviving
        // unscoped learned lemma cannot desync it. The
        // `can_use_incremental_reset` FALLBACK (full reset) either preserves
        // learned clauses (L0-GC rebuild) or DROPS them all (destructive
        // rebuild) — both sound for re-derivable theory axioms.
        if self.add_theory_conflict_lemma(conflict).is_some() {
            self.tla_trace_step(
                CdclTraceState::Propagating,
                Some(CdclTraceAction::AnalyzeAndLearn),
            );
            if self.stable_mode {
                self.vsids.decay();
            }
            // `OnPeriodicDecay()` (arXiv:2602.20829 Algorithm 1 lines 17-18):
            // every T=4096 conflicts. Placed beside the reduce check but
            // deliberately independent of it — the paper's decay clock is
            // conflicts, not reduction rounds. No-op unless the arm is armed.
            self.two_stage_periodic_decay_if_due();
            if self.should_reduce_db() {
                self.reduce_db();
            }
        }
    }
}
