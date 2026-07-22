// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Blocked clause elimination (BCE).

use super::super::mutate::ReasonPolicy;
use super::super::*;

impl Solver {
    /// Run blocked clause elimination (wrapper: always reschedules).
    pub(in crate::solver) fn bce(&mut self) {
        self.bce_body();
        self.inproc_ctrl
            .bce
            .reschedule(self.num_conflicts, BCE_INTERVAL);
        // Record ticks for tick-threshold scheduling (#8148).
        self.cold.last_bce_ticks = self.search_ticks[0] + self.search_ticks[1];
    }

    /// BCE body — early returns are safe; wrapper handles rescheduling.
    ///
    /// A clause is blocked on literal L if for every clause D containing ~L,
    /// resolving C and D on L produces a tautology. Blocked clauses can be
    /// safely removed without changing satisfiability.
    ///
    /// This must be called at decision level 0 (after a restart) for correctness.
    fn bce_body(&mut self) {
        if !self.enter_inprocessing() {
            return;
        }

        // Defense-in-depth: BCE uses reconstruction stack (push_bce), so it
        // must not fire in incremental mode even if re-enabled via set_bce_enabled.
        // Matches the guard pattern in condition() and decompose() (#3662).
        //
        // Migration (#8162 Part A step 1): superset-OR with in_scoped_mode()
        // so the new query is exercised. Behavior is unchanged while
        // has_been_incremental is still set — but once the permanent flag is
        // removed (Part A final step), the guard fires only on live scopes.
        if self.in_scoped_mode() || self.cold.has_been_incremental {
            return;
        }

        // Reuse BVE's persistent occ list when available (#8096), avoiding
        // the O(clause_literals) rebuild each BCE round. BVE's occ list
        // contains only irredundant clauses, matching CaDiCaL's block_schedule
        // behavior (block.cpp:167-179).
        if let Some(shared_occ) = self.inproc.bve.borrow_occ_list() {
            self.inproc.bce.adopt_occ_list(shared_occ, &self.arena);
        } else {
            self.inproc.bce.rebuild(&self.arena);
        }

        // Compute tick-proportional effort budget (#8148).
        // CaDiCaL runs BCE inside the elimination loop with the BVE resolution
        // budget. AY runs BCE standalone, so it uses the SET_EFFORT_LIMIT
        // pattern: budget = (search_ticks_delta * permille / 1000), clamped,
        // with a floor at 2 * active_vars.
        let active_vars = self
            .num_vars
            .saturating_sub(self.var_lifecycle.count_removed());
        let ticks_now = self.search_ticks[0] + self.search_ticks[1];
        let ticks_delta = ticks_now.saturating_sub(self.cold.last_bce_ticks);
        let effort = (ticks_delta * BCE_EFFORT_PER_MILLE / 1000) as usize;
        let effort = effort.clamp(BCE_MIN_EFFORT, BCE_MAX_EFFORT);
        let bce_limit = effort.max(2 * active_vars);

        // Run elimination (pass freeze_counts to skip frozen literals as blocking candidates)
        let eliminated = self.inproc.bce.run_elimination_with_marks(
            &self.arena,
            &self.cold.freeze_counts,
            bce_limit,
            &mut self.lit_marks,
        );

        // Delete the eliminated clauses and save for reconstruction.
        // Also notify BVE of irredundant clause removals (CaDiCaL
        // elim.cpp:1084-1098 feedback): BCE clause deletions within the
        // interleaved BVE cascade mark BVE candidates dirty, enabling
        // further variable elimination in subsequent rounds.
        for elim in eliminated {
            let clause_idx = elim.clause_idx;
            let blocking_literal = elim.blocking_literal;
            let is_irredundant = !self.arena.is_learned(clause_idx);
            let pre_delete_lits: Option<Vec<Literal>> = if is_irredundant {
                Some(self.arena.literals(clause_idx).to_vec())
            } else {
                None
            };
            let _ = self.delete_clause_with_snapshot(
                clause_idx,
                ReasonPolicy::Skip,
                move |solver, clause_lits| {
                    // CaDiCaL block.cpp: blocking literal must be present in clause
                    debug_assert!(
                        clause_lits.contains(&blocking_literal),
                        "BUG: BCE blocking literal {blocking_literal:?} not in clause {clause_idx}",
                    );
                    let ext_blocking = solver.externalize(blocking_literal);
                    let ext_lits = solver.externalize_lits(&clause_lits);
                    solver
                        .inproc
                        .reconstruction
                        .push_bce(ext_blocking, ext_lits);
                },
            );
            // Notify BVE of irredundant clause removal for cascade feedback.
            if let Some(old_lits) = pre_delete_lits {
                self.note_irredundant_clause_removed_for_bve(clause_idx, &old_lits);
            }
        }
    }
}
