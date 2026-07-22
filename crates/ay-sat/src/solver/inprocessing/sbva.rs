// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SBVA (Structured Bounded Variable Addition) inprocessing integration.
//!
//! Wires the standalone SBVA engine (`crate::sbva`) into the solver's
//! inprocessing pipeline, following the same pattern as `factorize.rs`.

use super::super::mutate::{AddResult, ReasonPolicy};
use super::super::*;
use crate::er_proof::ErDefinition;
use crate::sbva::SBVA_SIZE_LIMIT;

impl Solver {
    /// Run SBVA with growing backoff scheduling.
    ///
    /// Uses growing backoff when unproductive: the interval grows 1.5x
    /// per idle call, up to SBVA_MAX_INTERVAL. Productive calls reset
    /// to base interval.
    pub(in crate::solver) fn sbva(&mut self) {
        let productive = self.sbva_body();
        if productive {
            self.inproc_ctrl
                .sbva
                .reschedule(self.num_conflicts, SBVA_INTERVAL);
        } else {
            self.inproc_ctrl.sbva.reschedule_growing(
                self.num_conflicts,
                SBVA_INTERVAL,
                3,
                2, // 1.5x growth
                SBVA_MAX_INTERVAL,
            );
        }
    }

    /// SBVA body: finds and applies structured variable additions.
    ///
    /// Returns `true` if any groups were compressed.
    fn sbva_body(&mut self) -> bool {
        if !self.require_level_zero() {
            return false;
        }

        // Skip in incremental mode: SBVA introduces extension variables
        // and rewrites clauses, which cannot be reversed across solve
        // boundaries.
        if self.cold.has_been_incremental {
            return false;
        }

        // #8397: Skip SBVA when BVE/BCE/sweep have reconstruction entries.
        // Same rationale as factorize_body(): extension variables from SBVA
        // compose unsoundly with BVE reconstruction. See factorize.rs.
        if self.inproc.reconstruction.len() > 0 {
            return false;
        }

        let drat_proof = self.proof_manager.is_some();

        // Compute tick-proportional effort limit.
        let ticks_now = self.search_ticks[0] + self.search_ticks[1];
        let ticks_delta = ticks_now.saturating_sub(self.cold.last_sbva_ticks);
        let mut effort = ticks_delta * SBVA_EFFORT_PERMILLE / 1000;
        if self.cold.sbva_rounds == 0 {
            effort = effort.saturating_add(SBVA_INIT_TICKS);
        }
        let effort = effort.min(SBVA_MAX_EFFORT);

        // Build occurrence lists for SBVA.
        self.inproc.sbva_engine.ensure_num_vars(self.num_vars);
        let occ = self.build_sbva_occ();

        let config = crate::sbva::SbvaConfig {
            next_var_id: self.num_vars,
            effort_limit: effort,
        };

        let mut result = self.inproc.sbva_engine.run(
            &self.arena,
            &occ,
            &self.vals,
            self.var_lifecycle.as_slice(),
            &config,
        );

        self.cold.sbva_rounds += 1;
        self.cold.sbva_groups_total += result.groups_applied as u64;
        self.cold.sbva_extension_vars_total += result.extension_vars_needed as u64;
        self.cold.last_sbva_ticks = self.search_ticks[0] + self.search_ticks[1];

        if result.groups_applied == 0 {
            return false;
        }

        self.apply_sbva_result(&mut result, drat_proof);
        true
    }

    /// Build occurrence lists for SBVA-eligible clauses.
    ///
    /// Includes irredundant clauses with 3..=SBVA_SIZE_LIMIT literals.
    /// Binary clauses are excluded (SBVA needs >= 3 to have a shared subset).
    fn build_sbva_occ(&self) -> crate::occ_list::OccList {
        let mut occ = crate::occ_list::OccList::new(self.num_vars);

        // live_indices (husk adjudication): garbage-kept husks must not enter
        // SBVA occurrence lists — bundling a husk produces Some(0) ids in the
        // er_proof_log and double-deletes on apply.
        for ci in self.arena.live_indices() {
            if self.arena.is_learned(ci) {
                continue;
            }
            let lits = self.arena.literals(ci);
            let len = lits.len();
            if (3..=SBVA_SIZE_LIMIT).contains(&len) {
                occ.add_clause(ci, lits);
            }
        }

        occ
    }

    /// Apply SBVA results to the clause database.
    fn apply_sbva_result(&mut self, result: &mut crate::sbva::SbvaResult, drat_proof: bool) {
        // Create extension variables.
        let ext_var_start = self.num_vars;
        // Record the boundary where extension variables begin (#8397).
        if result.extension_vars_needed > 0 && self.cold.first_extension_var_index == usize::MAX {
            self.cold.first_extension_var_index = ext_var_start;
        }
        for _ in 0..result.extension_vars_needed {
            self.new_var_internal();
        }
        // Bury extension vars in VSIDS: zero activity so search doesn't
        // branch on them before BVE eliminates them.
        for vi in ext_var_start..self.num_vars {
            self.vsids.set_activity(Variable(vi as u32), 0.0);
        }

        for app in &result.applications {
            let source_clause_ids = app
                .to_delete
                .iter()
                .filter_map(|&idx| self.cold.clause_ids.get(idx).copied())
                .collect();
            self.cold.er_proof_log.push(ErDefinition::sbva(
                app.fresh_var,
                app.definition_clause.clone(),
                app.tail_clauses.clone(),
                app.blocked_clause.clone(),
                source_clause_ids,
            ));
        }

        if drat_proof {
            // DRAT proof transaction per SbvaApplication.
            // Order matters for checker:
            //   1. Add definition clause `{x} ∪ S`     — RAT on fresh x
            //   2. Add blocked clause `{¬x, ¬s_1, ...}` — RAT on ¬x (proof only)
            //   3. Add tail clauses `{¬x} ∪ D_i`       — RUP derivable
            //   4. Delete blocked clause
            //   5. Delete original clauses
            for app in &result.applications {
                let _ = self.proof_emit_add(
                    &app.definition_clause,
                    &[],
                    ProofAddKind::TrustedTransform,
                );
                let blocked_id = self
                    .proof_emit_add(&app.blocked_clause, &[], ProofAddKind::TrustedTransform)
                    .ok()
                    .filter(|&id| id != 0);
                for tail in &app.tail_clauses {
                    let _ = self.proof_emit_add(tail, &[], ProofAddKind::TrustedTransform);
                }
                if let Some(blocked_id) = blocked_id {
                    let _ = self.proof_emit_delete(&app.blocked_clause, blocked_id);
                }
            }

            // Add new clauses to clause DB (no proof emit -- already done above).
            for mut lits in std::mem::take(&mut result.new_clauses) {
                let add_result = self.add_clause_watched(&mut lits);
                // Notify BVE occ lists of new irredundant clause (#8096).
                match add_result {
                    AddResult::Added(cref) | AddResult::Unit(cref) => {
                        let ci = cref.0 as usize;
                        let new_lits = self.arena.literals(ci).to_vec();
                        self.note_irredundant_clause_added_for_bve(ci, &new_lits);
                    }
                    AddResult::Empty => {}
                }
                if self.has_empty_clause {
                    return;
                }
            }

            // Delete originals from clause DB.
            self.ensure_reason_clause_marks_current();
            for &clause_idx in &result.to_delete {
                // Notify BVE occ lists of irredundant clause removal (#8096).
                if !self.arena.is_learned(clause_idx) {
                    let old_lits = self.arena.literals(clause_idx).to_vec();
                    self.note_irredundant_clause_removed_for_bve(clause_idx, &old_lits);
                }
                self.delete_clause_checked(clause_idx, ReasonPolicy::Skip);
            }
        } else {
            // Non-proof path: delete originals first, then add new clauses.
            self.ensure_reason_clause_marks_current();
            for &clause_idx in &result.to_delete {
                // Notify BVE occ lists of irredundant clause removal (#8096).
                if !self.arena.is_learned(clause_idx) {
                    let old_lits = self.arena.literals(clause_idx).to_vec();
                    self.note_irredundant_clause_removed_for_bve(clause_idx, &old_lits);
                }
                self.delete_clause_checked(clause_idx, ReasonPolicy::Skip);
            }

            for mut lits in std::mem::take(&mut result.new_clauses) {
                let add_result = self.add_clause_watched(&mut lits);
                // Notify BVE occ lists of new irredundant clause (#8096).
                match add_result {
                    AddResult::Added(cref) | AddResult::Unit(cref) => {
                        let ci = cref.0 as usize;
                        let new_lits = self.arena.literals(ci).to_vec();
                        self.note_irredundant_clause_added_for_bve(ci, &new_lits);
                    }
                    AddResult::Empty => {}
                }
                if self.has_empty_clause {
                    return;
                }
            }
        }
    }
}

#[cfg(test)]
#[path = "sbva_tests.rs"]
mod tests;
