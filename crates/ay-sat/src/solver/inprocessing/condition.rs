// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Globally blocked clause elimination (conditioning).

use super::super::mutate::ReasonPolicy;
use super::super::*;
use crate::condition::Conditioning;

impl Solver {
    // ==================== Conditioning (Globally Blocked Clause Elimination) ====================

    /// Run conditioning (wrapper: always reschedules).
    pub(in crate::solver) fn condition(&mut self) {
        self.defer_stale_reason_cleanup = true;
        self.condition_body();
        self.defer_stale_reason_cleanup = false;
        self.clear_stale_reasons();
        self.inproc_ctrl
            .condition
            .reschedule(self.num_conflicts, CONDITION_INTERVAL);
    }

    /// Conditioning body.
    fn condition_body(&mut self) {
        if !self.enter_inprocessing() {
            return;
        }
        // Migration (#8162 Part A step 1): superset-OR with in_scoped_mode().
        if self.in_scoped_mode() || self.cold.has_been_incremental {
            return;
        }
        // Conditioning deletes irredundant clauses — maintained incrementally
        // via per-clause note_irredundant_clause_removed_for_bve calls (#8096).
        self.ensure_level0_unit_proof_ids();

        // CaDiCaL condition.cpp:59-61: skip if clause-variable ratio too high.
        let active_vars = self
            .num_vars
            .saturating_sub(self.var_lifecycle.count_removed());
        let irredundant_clauses = self.arena.irredundant_count();
        if Conditioning::should_skip_ratio(irredundant_clauses, active_vars) {
            return;
        }

        // Dynamic propagation limit (CaDiCaL condition.cpp:908-920).
        let prop_limit = Conditioning::compute_prop_limit(
            self.num_propagations,
            active_vars,
            irredundant_clauses,
        );

        let mut total_vals = vec![0i8; self.num_vars * 2];
        for var_idx in 0..self.num_vars {
            if self.var_is_assigned(var_idx) || self.var_lifecycle.is_removed(var_idx) {
                continue;
            }
            let positive = self.phase[var_idx] >= 0; // 0 (unset) defaults to positive
            let var = Variable(var_idx as u32);
            let lit = if positive {
                Literal::positive(var)
            } else {
                Literal::negative(var)
            };
            total_vals[lit.index()] = 1;
            total_vals[lit.negated().index()] = -1;
        }

        self.inproc.conditioning.ensure_num_vars(self.num_vars);
        let result = self.inproc.conditioning.condition_round(
            &mut self.arena,
            &total_vals,
            &self.vals,
            &self.cold.freeze_counts,
            &self.reason_clause_marks,
            self.reason_clause_epoch,
            MAX_CONDITION_ELIMINATIONS,
            prop_limit,
        );

        #[cfg(debug_assertions)]
        if !result.eliminated.is_empty() || !result.root_satisfied.is_empty() {
            let witnesses_per_clause = result
                .eliminated
                .first()
                .map(|e| e.witnesses.len())
                .unwrap_or(0);
            safe_eprintln!(
                "c CONDITIONING round {}: eliminated {} clauses, gc {} root-satisfied (witnesses_per_clause={}, reconstruction_steps={})",
                self.inproc.conditioning.stats().rounds,
                result.eliminated.len(),
                result.root_satisfied.len(),
                witnesses_per_clause,
                self.inproc.reconstruction.len()
            );
        }

        for clause_idx in result.root_satisfied {
            let lits = self.arena.literals(clause_idx).to_vec();
            let is_irredundant = !self.arena.is_learned(clause_idx);
            #[cfg(debug_assertions)]
            {
                let has_level0_true = lits.iter().any(|&lit| {
                    let li = lit.index();
                    li < self.vals.len()
                        && self.vals[li] > 0
                        && lit.variable().index() < self.var_data.len()
                        && self.var_data[lit.variable().index()].level == 0
                });
                if !has_level0_true {
                    let detail: Vec<String> = lits
                        .iter()
                        .map(|&lit| {
                            let vi = lit.variable().index();
                            let val = if lit.index() < self.vals.len() {
                                self.vals[lit.index()]
                            } else {
                                0
                            };
                            let lvl = if vi < self.var_data.len() {
                                self.var_data[vi].level as i32
                            } else {
                                -1
                            };
                            let is_removed =
                                vi < self.var_lifecycle.len() && self.var_lifecycle.is_removed(vi);
                            format!(
                                "lit={:?}(var={},pos={},val={},lvl={},removed={})",
                                lit,
                                vi,
                                lit.is_positive(),
                                val,
                                lvl,
                                is_removed
                            )
                        })
                        .collect();
                    panic!(
                        "BUG: root-satisfied clause has no level-0 true literal! \
                         clause_idx={}, lits=[{}], trail_len={}, decision_level={}",
                        clause_idx,
                        detail.join(", "),
                        self.trail.len(),
                        self.decision_level,
                    );
                }
            }
            let ext_lits = self.externalize_lits(&lits);
            self.cold.root_satisfied_saved.push(ext_lits);
            self.delete_clause_checked(clause_idx, ReasonPolicy::ClearLevel0);
            // Incremental BVE occ maintenance (#8096).
            if is_irredundant {
                self.note_irredundant_clause_removed_for_bve(clause_idx, &lits);
            }
        }

        for elim in result.eliminated {
            let clause_idx = elim.clause_idx;
            let witnesses = elim.witnesses;
            let is_irredundant = clause_idx < self.arena.len()
                && self.arena.is_active(clause_idx)
                && !self.arena.is_learned(clause_idx);
            let pre_delete_lits: Option<Vec<Literal>> = if is_irredundant {
                Some(self.arena.literals(clause_idx).to_vec())
            } else {
                None
            };
            let _ = self.delete_clause_with_snapshot(
                clause_idx,
                ReasonPolicy::Skip,
                move |solver, clause_lits| {
                    let ext_witnesses = solver.externalize_lits(&witnesses);
                    let ext_lits = solver.externalize_lits(&clause_lits);
                    solver
                        .inproc
                        .reconstruction
                        .push_witness_clause(ext_witnesses, ext_lits);
                },
            );
            // Incremental BVE occ maintenance (#8096).
            if let Some(old_lits) = pre_delete_lits {
                self.note_irredundant_clause_removed_for_bve(clause_idx, &old_lits);
            }
        }
    }
}
