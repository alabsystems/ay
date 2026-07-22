// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Covered clause elimination (CCE) — solver integration.
//!
//! Wires the standalone CCE engine (`crate::cce`) into the solver's
//! inprocessing pipeline. Follows the same pattern as `bce.rs`.

use super::super::mutate::ReasonPolicy;
use super::super::*;

impl Solver {
    /// Run covered clause elimination (wrapper: always reschedules).
    pub(in crate::solver) fn cce(&mut self) {
        self.cce_body();
        self.inproc_ctrl
            .cce
            .reschedule(self.num_conflicts, CCE_INTERVAL);
    }

    /// CCE body — early returns are safe; wrapper handles rescheduling.
    ///
    /// ACCE extends clauses with ALA (asymmetric literal addition through
    /// watched clauses) and CLA (covered literal addition through occurrence
    /// lists) to find elimination opportunities that BCE alone misses.
    ///
    /// Must be called at decision level 0. CCE strictly subsumes BCE:
    /// every blocked clause is also covered-tautological. Disabled via
    /// `--disable cce`.
    ///
    /// Reference: CaDiCaL `cover.cpp`, Heule/Järvisalo/Biere LPAR 2010.
    fn cce_body(&mut self) {
        if !self.enter_inprocessing() {
            return;
        }

        // CCE uses the reconstruction stack (same as BCE: push_bce).
        // Must not fire in incremental mode.
        //
        // Migration (#8162 Part A step 1): superset-OR with in_scoped_mode().
        if self.in_scoped_mode() || self.cold.has_been_incremental {
            return;
        }
        // CCE deletes covered clauses — maintained incrementally via
        // per-clause note_irredundant_clause_removed_for_bve calls (#8096).

        // Compute effort limit: proportional to search propagations.
        // CaDiCaL: covereffort=4 per-mille of search props, clamped to
        // [covermineff=0, covermaxeff=1e8], floor at 2*active_vars.
        let active_vars = self
            .num_vars
            .saturating_sub(self.var_lifecycle.count_removed()) as u64;
        let effort = (self.num_propagations as f64 * CCE_EFFORT_PER_MILLE as f64 / 1000.0) as u64;
        let effort = effort.clamp(CCE_MIN_EFFORT, CCE_MAX_EFFORT);
        let effort = effort.max(2 * active_vars);

        // Rebuild occurrence lists and run one CCE round.
        self.inproc.cce.ensure_num_vars(self.num_vars);
        self.inproc.cce.rebuild(&self.arena);
        let eliminated = self.inproc.cce.run_round(
            &self.arena,
            &self.vals,
            &self.cold.freeze_counts,
            &self.watches,
            effort,
        );

        // Delete eliminated clauses and save for reconstruction.
        // Use the covered set (original + CLA-added literals) for
        // reconstruction, not the original clause. The blocking literal
        // may be a CLA-added literal not present in the original clause.
        // CaDiCaL: cover_push_extension saves coveror.covered (cover.cpp:49-60).
        //
        // Also notify BVE of irredundant clause removals (CaDiCaL
        // elim.cpp:1093-1098 feedback): CCE clause deletions within the
        // interleaved BVE cascade mark BVE candidates dirty, enabling
        // further variable elimination in subsequent rounds.
        for elim in eliminated {
            let clause_idx = elim.clause_idx;
            let blocking_literal = elim.blocking_literal;
            let covered_lits = elim.covered_lits;
            let is_irredundant = !self.arena.is_learned(clause_idx);
            let pre_delete_lits: Option<Vec<Literal>> = if is_irredundant {
                Some(self.arena.literals(clause_idx).to_vec())
            } else {
                None
            };
            let _ = self.delete_clause_with_snapshot(
                clause_idx,
                ReasonPolicy::Skip,
                move |solver, _clause_lits| {
                    debug_assert!(
                        covered_lits.contains(&blocking_literal),
                        "BUG: CCE blocking literal {blocking_literal:?} not in covered set",
                    );
                    let ext_blocking = solver.externalize(blocking_literal);
                    let ext_lits = solver.externalize_lits(&covered_lits);
                    // CCE reconstruction: blocking literal + covered set.
                    // The covered set = original clause ∪ CLA-added literals.
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
