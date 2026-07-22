// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BVE occurrence management and scheduling.

use crate::clause_arena::ClauseArena;
use crate::gates::GateExtractor;
#[cfg(debug_assertions)]
use crate::kani_compat::DetHashMap as HashMap;
use crate::lit_marks::LitMarks;
use crate::literal::{Literal, Variable};

use super::{BVE, ELIM_OCC_LIMIT};

#[derive(Debug, Default)]
struct OccDeltaValidation {
    occ_entries_checked: u64,
    missing_entries: u64,
    stale_live_entries: u64,
    live_learned_entries: u64,
    oversize: bool,
}

impl OccDeltaValidation {
    fn is_valid(&self) -> bool {
        !self.oversize
            && self.missing_entries == 0
            && self.stale_live_entries == 0
            && self.live_learned_entries == 0
    }
}

impl BVE {
    /// Notify the BVE engine that a resolvent clause was added to the clause DB.
    /// Updates occurrence lists so subsequent eliminations see the new clause.
    /// (CaDiCaL equivalent: `elim_update_added_clause`.)
    ///
    /// REQUIRES: clause must be irredundant, literals does not contain eliminated variables
    /// ENSURES: each literal in the clause has clause_idx in its occ list
    pub(crate) fn notify_resolvent_added(&mut self, clause_idx: usize, literals: &[Literal]) {
        // CaDiCaL elim.cpp: resolvents added to occ lists must be non-empty.
        // An empty resolvent means UNSAT was detected during resolution and
        // should be handled before reaching occ list updates.
        debug_assert!(
            !literals.is_empty(),
            "BUG: notify_resolvent_added called with empty clause (UNSAT not handled)",
        );
        debug_assert!(
            literals
                .iter()
                .all(|l| l.variable().index() < self.num_vars),
            "BUG: resolvent literal variable index >= num_vars {}",
            self.num_vars,
        );
        debug_assert!(
            literals
                .iter()
                .all(|l| !self.eliminated[l.variable().index()]),
            "BUG: resolvent contains eliminated variable(s): {literals:?}"
        );
        self.occ.add_clause(clause_idx, literals);
        self.occ_delta
            .record_clause(clause_idx, literals, self.num_vars);
        // CaDiCaL elim.cpp:90-105: update existing heap entries on addition.
        for &lit in literals {
            let var = lit.variable();
            if !self.eliminated[var.index()] && self.schedule.contains(var) {
                self.schedule
                    .update(var, &self.occ, &self.schedule_gate_pair_credit);
            }
        }
    }

    /// Notify the BVE engine that an existing clause was strengthened in-place.
    ///
    /// Removes old literal occurrences and adds the new literal occurrences so
    /// subsequent eliminations in the same round see the updated clause.
    ///
    /// REQUIRES: clause must be irredundant, new_lits does not contain eliminated variables
    pub(crate) fn notify_clause_replaced(
        &mut self,
        clause_idx: usize,
        old_lits: &[Literal],
        new_lits: &[Literal],
    ) {
        debug_assert!(
            !new_lits.is_empty(),
            "BUG: notify_clause_replaced called with empty clause",
        );
        debug_assert!(
            new_lits
                .iter()
                .all(|l| l.variable().index() < self.num_vars),
            "BUG: replacement literal variable index >= num_vars {}",
            self.num_vars,
        );
        debug_assert!(
            new_lits
                .iter()
                .all(|l| !self.eliminated[l.variable().index()]),
            "BUG: replacement clause contains eliminated variable(s): {new_lits:?}",
        );
        self.occ.remove_clause(clause_idx, old_lits);
        self.occ.add_clause(clause_idx, new_lits);
        self.occ_delta
            .record_replace(clause_idx, old_lits, new_lits, self.num_vars);
        // CaDiCaL elim_update_removed_clause: update-or-reinsert removed lits.
        for &lit in old_lits {
            let var = lit.variable();
            if self.eliminated[var.index()] {
                continue;
            }
            if self.schedule.contains(var) {
                self.schedule
                    .update(var, &self.occ, &self.schedule_gate_pair_credit);
            } else {
                self.schedule
                    .push(var, &self.occ, &self.schedule_gate_pair_credit);
            }
        }
        // CaDiCaL elim_update_added_clause: update only for added lits.
        for &lit in new_lits {
            let var = lit.variable();
            if !self.eliminated[var.index()] && self.schedule.contains(var) {
                self.schedule
                    .update(var, &self.occ, &self.schedule_gate_pair_credit);
            }
        }
    }

    /// Initialize/rebuild occurrence lists from clause database.
    ///
    /// REQUIRES: clauses contains valid clause data (headers consistent with literals)
    /// ENSURES: occ lists reflect exactly the non-deleted irredundant clauses in `clauses`,
    ///          schedule is empty (rebuilt lazily on next next_candidate call)
    #[cfg(test)]
    pub(crate) fn rebuild(&mut self, clauses: &ClauseArena) {
        self.rebuild_inner(clauses, &[]);
        // A full rebuild (no vals) resets the entire occurrence state.
        // Mark all non-eliminated variables dirty so build_schedule
        // considers every variable as a candidate (#7917).
        self.mark_all_candidates_dirty();
    }

    /// Rebuild occurrence lists, filtering out clauses satisfied at root level.
    ///
    /// CaDiCaL elimfast.cpp:302-316: before building occurrence lists, scan
    /// each irredundant clause and skip any that are satisfied by root-level
    /// assignments. Without this filter, satisfied clauses inflate occurrence
    /// counts and distort elimination decisions. AY's 2WL propagation skips
    /// satisfied clauses at runtime but doesn't remove them from the arena,
    /// so they accumulate across probing/decompose/HTR passes.
    ///
    /// `vals` is the literal value array: `vals[lit.index()] > 0` means true.
    /// An empty `vals` slice disables the filter (used by `rebuild()`).
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn rebuild_with_vals(&mut self, clauses: &ClauseArena, vals: &[i8]) {
        self.rebuild_inner(clauses, vals);
    }

    /// Rebuild occurrence lists and remember the solver clause-DB mutation epoch
    /// that this rebuild validated.
    pub(crate) fn rebuild_with_vals_at_epoch(
        &mut self,
        clauses: &ClauseArena,
        vals: &[i8],
        clause_db_epoch: u64,
    ) {
        self.rebuild_inner(clauses, vals);
        self.occ_consistency_epoch = Some(clause_db_epoch);
    }

    fn rebuild_inner(&mut self, clauses: &ClauseArena, vals: &[i8]) {
        let filter_satisfied = !vals.is_empty();

        #[cfg(debug_assertions)]
        self.debug_check_no_eliminated_in_active(clauses, vals, filter_satisfied);

        self.occ.clear();

        // CaDiCaL elim.cpp:804-805, 863-864: occurrence lists must contain
        // only irredundant (original) clauses. Including learned clauses inflates
        // bound decisions and may produce invalid reconstruction witnesses (#5019).
        for idx in clauses.indices() {
            if clauses.is_dead(idx) || clauses.is_learned(idx) {
                continue;
            }
            if filter_satisfied {
                let mut satisfied = false;
                let mut falsified = false;
                for &lit in clauses.literals(idx) {
                    let val = vals.get(lit.index()).copied().unwrap_or(0);
                    if val > 0 {
                        satisfied = true;
                        break;
                    }
                    if val < 0 {
                        falsified = true;
                    }
                }
                // CaDiCaL elimfast.cpp:315-316: skip satisfied clauses.
                if satisfied {
                    continue;
                }
                // CaDiCaL elim.cpp:804-822 marks all active literals in clauses
                // touched by root-level falsifications. These are the variables
                // whose occurrence counts changed since the last completed BVE
                // round and need to be reconsidered.
                if falsified {
                    for &lit in clauses.literals(idx) {
                        let var_idx = lit.variable().index();
                        if vals.get(lit.index()).copied().unwrap_or(0) == 0
                            && var_idx < self.candidate_dirty.len()
                            && !self.eliminated[var_idx]
                        {
                            self.candidate_dirty[var_idx] = true;
                        }
                    }
                }
            }
            self.occ.add_clause(idx, clauses.literals(idx));
        }

        // Gate pair credit is only used for gate-aware BVE scheduling.
        // Skip in fastelim mode (preprocessing) where gate extraction is
        // disabled. On shuffling-2 (138K vars), this avoids O(vars * gate)
        // work per BVE round during preprocessing.
        if !self.fastelim_mode {
            self.refresh_schedule_gate_pair_credit(clauses, vals);
        }

        // Schedule heap cleared; rebuilt lazily on next next_candidate call.
        self.schedule.clear();
        self.schedule_built = false;
        self.occ_populated = true;
        self.occ_consistency_epoch = None;
        self.occ_delta.clear_validated();

        #[cfg(debug_assertions)]
        self.debug_check_occ_consistency(clauses, vals, filter_satisfied);
    }

    /// Check if a clause is satisfied by root-level assignments in `vals`.
    fn clause_satisfied(clauses: &ClauseArena, idx: usize, vals: &[i8]) -> bool {
        clauses
            .literals(idx)
            .iter()
            .any(|&lit| (lit.index()) < vals.len() && vals[lit.index()] > 0)
    }

    /// Precondition: no active irredundant clause in occ-list scope should
    /// contain a variable we've already eliminated. Satisfied clauses are
    /// excluded from occ lists and may legitimately contain eliminated variables.
    #[cfg(debug_assertions)]
    fn debug_check_no_eliminated_in_active(
        &self,
        clauses: &ClauseArena,
        vals: &[i8],
        filter_satisfied: bool,
    ) {
        for idx in clauses.indices() {
            if clauses.is_dead(idx) || clauses.is_learned(idx) {
                continue;
            }
            if filter_satisfied && Self::clause_satisfied(clauses, idx, vals) {
                continue;
            }
            for &lit in clauses.literals(idx) {
                let vi = lit.variable().index();
                debug_assert!(
                    vi >= self.eliminated.len() || !self.eliminated[vi],
                    "BUG: live irredundant clause {idx} contains eliminated variable {vi}",
                );
            }
        }
    }

    /// Quick consistency check: verify that every active irredundant
    /// non-satisfied clause is present in the occ list for each of its
    /// literals, and that every live occurrence-list entry still points to a
    /// clause that contains the indexed literal. Returns true if a rebuild is
    /// needed (inconsistency found).
    ///
    /// Multiple mutation paths (elim_propagate, backward subsumption,
    /// arena compaction, L0 GC) may miss occ list notifications. This
    /// check detects such gaps so refresh_incremental can fall back to a full
    /// rebuild (#8473). The reverse check is intentionally release-mode:
    /// a stale extra occurrence can otherwise feed BVE a parent clause that no
    /// longer contains the pivot literal, which is not proof/model safe.
    ///
    /// NOT debug-only: this is a correctness mechanism, not an assertion.
    /// Runs once per BVE round, same order as rebuild itself.
    fn occ_needs_rebuild(
        &self,
        clauses: &ClauseArena,
        vals: &[i8],
        filter_satisfied: bool,
    ) -> bool {
        for idx in clauses.indices() {
            if clauses.is_dead(idx) || clauses.is_learned(idx) {
                continue;
            }
            if filter_satisfied && Self::clause_satisfied(clauses, idx, vals) {
                continue;
            }
            for &lit in clauses.literals(idx) {
                if !self.occ.get(lit).contains(&idx) {
                    return true;
                }
            }
        }

        for var_idx in 0..self.num_vars {
            if self.eliminated[var_idx] {
                continue;
            }
            for polarity in 0..2u32 {
                let lit = if polarity == 0 {
                    Literal::positive(Variable(var_idx as u32))
                } else {
                    Literal::negative(Variable(var_idx as u32))
                };
                for &idx in self.occ.get(lit) {
                    if idx >= clauses.len() || clauses.is_dead(idx) {
                        continue;
                    }
                    if clauses.is_learned(idx) {
                        return true;
                    }
                    if filter_satisfied && Self::clause_satisfied(clauses, idx, vals) {
                        continue;
                    }
                    if !clauses.literals(idx).contains(&lit) {
                        return true;
                    }
                }
            }
        }

        false
    }

    fn validate_occ_delta(
        &self,
        clauses: &ClauseArena,
        vals: &[i8],
        filter_satisfied: bool,
        touched_clauses: &[usize],
        touched_lits: &[Literal],
        max_occ_entries: u64,
    ) -> OccDeltaValidation {
        let mut result = OccDeltaValidation::default();

        for &idx in touched_clauses {
            if idx >= clauses.len() || clauses.is_dead(idx) || clauses.is_learned(idx) {
                continue;
            }
            if filter_satisfied && Self::clause_satisfied(clauses, idx, vals) {
                continue;
            }
            for &lit in clauses.literals(idx) {
                if !self.occ.contains(lit, idx) {
                    result.missing_entries = result.missing_entries.saturating_add(1);
                }
            }
        }

        for &lit in touched_lits {
            let var_idx = lit.variable().index();
            if var_idx < self.eliminated.len() && self.eliminated[var_idx] {
                continue;
            }
            for &idx in self.occ.get(lit) {
                result.occ_entries_checked = result.occ_entries_checked.saturating_add(1);
                if result.occ_entries_checked > max_occ_entries {
                    result.oversize = true;
                    return result;
                }
                if idx >= clauses.len() || clauses.is_dead(idx) {
                    continue;
                }
                if clauses.is_learned(idx) {
                    result.live_learned_entries = result.live_learned_entries.saturating_add(1);
                    continue;
                }
                if filter_satisfied && Self::clause_satisfied(clauses, idx, vals) {
                    continue;
                }
                if !clauses.literals(idx).contains(&lit) {
                    result.stale_live_entries = result.stale_live_entries.saturating_add(1);
                }
            }
        }

        result
    }

    /// Post-condition: occurrence counts must be consistent with clause DB.
    #[cfg(debug_assertions)]
    fn debug_check_occ_consistency(
        &self,
        clauses: &ClauseArena,
        vals: &[i8],
        filter_satisfied: bool,
    ) {
        for idx in clauses.indices() {
            if clauses.is_dead(idx) || clauses.is_learned(idx) {
                continue;
            }
            if filter_satisfied && Self::clause_satisfied(clauses, idx, vals) {
                continue;
            }
            for &lit in clauses.literals(idx) {
                debug_assert!(
                    self.occ.get(lit).contains(&idx),
                    "BUG: rebuild() occ list for {lit:?} missing clause {idx}"
                );
            }
        }
    }

    #[inline]
    pub(super) fn candidate_occurrence_counts(
        &self,
        var_idx: usize,
        vals: &[i8],
        frozen: &[u32],
    ) -> Option<(Variable, usize, usize)> {
        debug_assert!(
            var_idx < self.num_vars,
            "BUG: candidate index {var_idx} out of bounds for num_vars {}",
            self.num_vars
        );
        if var_idx < self.scope_var_floor {
            return None;
        } // #8369
        if self.eliminated[var_idx] {
            return None;
        }
        if var_idx * 2 < vals.len() && vals[var_idx * 2] != 0 {
            return None;
        }
        if var_idx < frozen.len() && frozen[var_idx] > 0 {
            return None;
        }

        let var = Variable(var_idx as u32);
        let pos_count = self.occ.count(Literal::positive(var));
        let neg_count = self.occ.count(Literal::negative(var));

        // Dead variables (0 in both polarities) have no clauses to eliminate.
        // Skip these — they may be substituted or otherwise removed.
        if pos_count == 0 && neg_count == 0 {
            return None;
        }
        // Pure variables (0 in one polarity) ARE eligible for elimination.
        // Pure elimination requires zero resolvents — just delete all clauses
        // containing the variable. check_bounded_elimination_with_marks filters
        // stale occ entries inline, so stale counts here don't affect correctness.
        // Kissat resolve.c:282-289: total occurrence limit (not per-polarity).
        if pos_count + neg_count > ELIM_OCC_LIMIT {
            return None;
        }

        Some((var, pos_count, neg_count))
    }

    /// Build the elimination schedule as an indexed min-heap.
    ///
    /// REQUIRES: occ lists are up-to-date with clause DB
    /// ENSURES: schedule contains only non-eliminated, unassigned, unfrozen vars
    ///          with both-polarity occurrences, ordered by score (min-heap)
    pub(super) fn build_schedule(&mut self, vals: &[i8], frozen: &[u32]) {
        self.schedule.clear();
        let use_dirty_filter = !self.fastelim_mode;

        for var_idx in 0..self.num_vars {
            if use_dirty_filter && !self.candidate_dirty.get(var_idx).copied().unwrap_or(false) {
                continue;
            }
            let Some((var, _, _)) = self.candidate_occurrence_counts(var_idx, vals, frozen) else {
                continue;
            };

            self.schedule
                .push(var, &self.occ, &self.schedule_gate_pair_credit);
        }
    }

    /// CaDiCaL `elim_update_removed_clause` (elim.cpp:107-134): when a clause
    /// is deleted, re-insert its variables into the schedule with updated scores.
    /// The eliminated variable (`except`) is skipped.
    pub(crate) fn update_schedule_after_clause_removal(
        &mut self,
        clause_lits: &[Literal],
        except: Variable,
        vals: &[i8],
        frozen: &[u32],
    ) {
        for &lit in clause_lits {
            let var = lit.variable();
            if var == except {
                continue;
            }
            let vi = var.index();
            // Skip eliminated, assigned, or frozen variables.
            if vi < self.eliminated.len() && self.eliminated[vi] {
                continue;
            }
            if vi * 2 < vals.len() && vals[vi * 2] != 0 {
                continue;
            }
            if vi < frozen.len() && frozen[vi] != 0 {
                continue;
            }
            self.schedule
                .push_or_update(var, &self.occ, &self.schedule_gate_pair_credit);
        }
    }

    /// CaDiCaL `elim_update_added_clause` (elim.cpp:90-105): when a clause
    /// is added (resolvent), update scores only for variables already in the heap.
    /// New variables are NOT inserted — only existing entries are rescored.
    pub(crate) fn update_schedule_after_clause_addition(&mut self, clause_lits: &[Literal]) {
        for &lit in clause_lits {
            let var = lit.variable();
            if self.schedule.contains(var) {
                self.schedule
                    .update(var, &self.occ, &self.schedule_gate_pair_credit);
            }
        }
    }

    fn refresh_schedule_gate_pair_credit(&mut self, clauses: &ClauseArena, vals: &[i8]) {
        if self.schedule_gate_pair_credit.len() < self.num_vars {
            self.schedule_gate_pair_credit.resize(self.num_vars, 0);
        }
        for credit in &mut self.schedule_gate_pair_credit {
            *credit = 0;
        }

        let mut extractor = GateExtractor::new(self.num_vars);
        let mut marks = LitMarks::new(self.num_vars.max(1));

        for var_idx in 0..self.num_vars {
            let Some((var, _, _)) = self.candidate_occurrence_counts(var_idx, vals, &[]) else {
                continue;
            };
            let pos_occs = self.occ.get(Literal::positive(var));
            let neg_occs = self.occ.get(Literal::negative(var));
            let Some(gate) = extractor.find_gate_for_schedule_with_vals_and_marks(
                var, clauses, pos_occs, neg_occs, vals, &mut marks,
            ) else {
                continue;
            };

            let mut pos_gate = 0u64;
            let mut neg_gate = 0u64;
            let pos_lit = Literal::positive(var);
            let neg_lit = Literal::negative(var);
            for clause_idx in gate.defining_clauses {
                let lits = clauses.literals(clause_idx);
                if lits.contains(&pos_lit) {
                    pos_gate += 1;
                } else if lits.contains(&neg_lit) {
                    neg_gate += 1;
                }
            }
            if pos_gate > 0 && neg_gate > 0 {
                self.schedule_gate_pair_credit[var_idx] = pos_gate.saturating_mul(neg_gate);
            }
        }
    }

    /// Update occurrence lists after successful elimination.
    ///
    /// CaDiCaL equivalent: `elim_update_removed_clause` (elim.cpp:125-134)
    /// combined with `remove_occs` (backward.cpp:198). CaDiCaL keeps
    /// separate `noccs` counters that are decremented eagerly on clause
    /// deletion, giving the elimination heap accurate scores.
    ///
    /// AY's ElimHeap scores are computed from `occ.count()` = `occ.get().len()`.
    /// Without eager removal, deleted clauses inflate occurrence counts,
    /// making variables appear more expensive to eliminate than they are.
    /// This breaks the cascading elimination pattern: a variable whose
    /// neighbor was just eliminated (reducing its occ count) should move
    /// up in priority, but stale entries prevent the score drop.
    pub(crate) fn update_occs_after_elimination(
        &mut self,
        to_delete: &[usize],
        clauses: &ClauseArena,
    ) {
        for &c_idx in to_delete {
            if c_idx >= clauses.len() || clauses.is_dead(c_idx) {
                continue;
            }
            let lits = clauses.literals(c_idx);
            self.occ.remove_clause(c_idx, lits);
            self.occ_delta.record_clause(c_idx, lits, self.num_vars);
        }
    }

    /// Fill `buf` with clause indices satisfied by a newly-true literal.
    ///
    /// CaDiCaL elim_propagate (elim.cpp:190-197): walks the positive occ list
    /// and marks satisfied clauses as garbage. The caller deletes them via
    /// `delete_clause_checked`, which garbage-marks the header; stale occ
    /// entries are tolerated by all iteration sites (lazy removal).
    ///
    /// Takes a reusable buffer to avoid per-call heap allocation (#5085).
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn satisfied_clauses_into(
        &self,
        lit: Literal,
        clauses: &ClauseArena,
        buf: &mut Vec<usize>,
    ) {
        buf.clear();
        buf.extend(
            self.occ
                .get(lit)
                .iter()
                .copied()
                .filter(|&c_idx| c_idx < clauses.len() && !clauses.is_dead(c_idx)),
        );
    }

    // --- Incremental occurrence list maintenance (#8096) ---

    /// Whether occ lists are currently populated (incremental refresh available).
    pub(crate) fn is_occ_populated(&self) -> bool {
        self.occ_populated
    }

    /// Mark occ lists as needing full rebuild (e.g., after compaction,
    /// or when a technique modifies irredundant clauses without per-clause
    /// occ list notification).
    pub(crate) fn invalidate_occ_lists(&mut self) {
        self.occ_populated = false;
        self.occ_consistency_epoch = None;
        self.occ_delta.mark_uncertified();
    }

    /// Finish a preprocessing or restart-inprocessing round that had populated
    /// BVE occurrence lists.
    ///
    /// Same-round consumers use `occ_populated` while the round is active. At
    /// the boundary, keep the saved state only for the explicit reuse candidate;
    /// otherwise make later mutation hooks no-ops without clearing allocated
    /// buffers.
    pub(crate) fn finish_occ_saved_state_round(&mut self) {
        if !self.occ_populated {
            return;
        }
        if self.occ_saved_state_reuse_enabled {
            self.stats.occ_saved_state_round_end_retains = self
                .stats
                .occ_saved_state_round_end_retains
                .saturating_add(1);
        } else {
            self.stats.occ_saved_state_round_end_drops =
                self.stats.occ_saved_state_round_end_drops.saturating_add(1);
            self.invalidate_occ_lists();
        }
    }

    /// Remove a clause from occurrence lists during inter-round maintenance.
    ///
    /// Called by `note_irredundant_clause_removed_for_bve` when occ lists are
    /// already populated. When occ lists are not populated (occ_populated=false),
    /// this is a no-op since the next `rebuild_with_vals` will rebuild from scratch.
    pub(crate) fn occ_remove_clause(&mut self, clause_idx: usize, literals: &[Literal]) {
        if !self.occ_populated {
            return;
        }
        self.occ.remove_clause(clause_idx, literals);
        self.occ_delta
            .record_clause(clause_idx, literals, self.num_vars);
    }

    /// Add a clause to occurrence lists during inter-round maintenance.
    ///
    /// Called by `note_irredundant_clause_added_for_bve` when occ lists are
    /// already populated. When occ lists are not populated (occ_populated=false),
    /// this is a no-op since the next `rebuild_with_vals` will rebuild from scratch.
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn occ_add_clause(&mut self, clause_idx: usize, literals: &[Literal]) {
        if !self.occ_populated {
            return;
        }
        self.occ.add_clause(clause_idx, literals);
        self.occ_delta
            .record_clause(clause_idx, literals, self.num_vars);
    }

    /// Add a newly-irredundant clause to occurrence lists.
    ///
    /// Called when a learned clause is promoted to irredundant (e.g., during
    /// subsumption when a redundant clause subsumes an irredundant one and the
    /// subsumer is promoted). BVE occ lists only track irredundant clauses, so
    /// promotions must explicitly add the clause (#8135).
    pub(crate) fn occ_add_new_irredundant(&mut self, clause_idx: usize, literals: &[Literal]) {
        if !self.occ_populated {
            return;
        }
        self.occ.add_clause(clause_idx, literals);
        self.occ_delta
            .record_clause(clause_idx, literals, self.num_vars);
    }

    /// Update occurrence lists for a replaced clause during inter-round maintenance.
    ///
    /// Called by `note_irredundant_clause_replaced_for_bve` when occ lists are
    /// already populated. Removes old literal occurrences and adds new ones.
    pub(crate) fn occ_replace_clause(
        &mut self,
        clause_idx: usize,
        old_lits: &[Literal],
        new_lits: &[Literal],
    ) {
        if !self.occ_populated {
            return;
        }
        self.occ.remove_clause(clause_idx, old_lits);
        self.occ.add_clause(clause_idx, new_lits);
        self.occ_delta
            .record_replace(clause_idx, old_lits, new_lits, self.num_vars);
    }

    /// Incremental refresh: filter out satisfied clauses from occ lists and
    /// rebuild the schedule, without a full O(clause_literals) scan (#8096).
    ///
    /// Called instead of `rebuild_with_vals` when occ lists are already populated
    /// from incremental maintenance. The key savings: we only need to scan occ
    /// lists of true-valued literals (to remove satisfied clauses) rather than
    /// scanning all clauses.
    ///
    /// REQUIRES: `occ_populated == true`, occ lists reflect current irredundant state
    /// ENSURES: satisfied clauses removed from occ lists, schedule rebuilt
    ///
    /// Returns `true` when the incremental path was used. Returns `false`
    /// when consistency checks forced a full rebuild fallback.
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn refresh_incremental(&mut self, clauses: &ClauseArena, vals: &[i8]) -> bool {
        self.refresh_incremental_inner(clauses, vals, None)
    }

    /// Incremental refresh with a solver clause-DB mutation epoch.
    ///
    /// The expensive bidirectional consistency scan runs only when the epoch has
    /// changed since the last validated refresh/rebuild. This is proof/model
    /// fail-closed: any checked add/delete/replace moves `clause_db_changes`,
    /// forcing the existing scan and full-rebuild fallback before BVE can reuse
    /// the saved state.
    pub(crate) fn refresh_incremental_at_epoch(
        &mut self,
        clauses: &ClauseArena,
        vals: &[i8],
        clause_db_epoch: u64,
    ) -> bool {
        self.refresh_incremental_inner(clauses, vals, Some(clause_db_epoch))
    }

    fn refresh_incremental_inner(
        &mut self,
        clauses: &ClauseArena,
        vals: &[i8],
        clause_db_epoch: Option<u64>,
    ) -> bool {
        let filter_satisfied = !vals.is_empty();

        #[cfg(debug_assertions)]
        self.debug_check_no_eliminated_in_active(clauses, vals, filter_satisfied);

        // Consistency check (#8473): verify that the incremental occ list
        // still matches the clause arena. Multiple mutation paths (elim_propagate,
        // backward subsumption, L0 GC, arena compaction) may miss occ list
        // notifications. When inconsistencies are detected, fall back to a
        // full rebuild instead of propagating stale data.
        //
        // Epoch fast path (#9106): when production BVE passes the same
        // `clause_db_changes` value that was already validated, no checked
        // clause add/delete/replace occurred since the last validation. In that
        // case, the structural consistency scan is redundant; root-level
        // assignments are handled by the satisfied/falsified literal loops
        // below. Callers without an epoch keep the conservative always-scan
        // behavior.
        let should_validate = clause_db_epoch
            .map(|epoch| self.occ_consistency_epoch != Some(epoch))
            .unwrap_or(true);
        let mut needs_full_validation = should_validate;
        let mut delta_validated = false;
        if self.occ_delta.needs_validation() {
            if self.occ_delta.uncertified_since_validation {
                self.stats.occ_delta_uncertified_fallbacks =
                    self.stats.occ_delta_uncertified_fallbacks.saturating_add(1);
                needs_full_validation = true;
            } else {
                self.occ_delta.prepare_unique_touches();
                let touched_clauses = self.occ_delta.touched_clauses.clone();
                let touched_lits = self.occ_delta.touched_lits.clone();
                self.stats.occ_delta_touched_clauses = self
                    .stats
                    .occ_delta_touched_clauses
                    .saturating_add(touched_clauses.len() as u64);
                self.stats.occ_delta_touched_lits = self
                    .stats
                    .occ_delta_touched_lits
                    .saturating_add(touched_lits.len() as u64);

                if !self.occ_delta.within_budget() {
                    self.stats.occ_delta_oversize_fallbacks =
                        self.stats.occ_delta_oversize_fallbacks.saturating_add(1);
                    needs_full_validation = true;
                } else {
                    let validation = self.validate_occ_delta(
                        clauses,
                        vals,
                        filter_satisfied,
                        &touched_clauses,
                        &touched_lits,
                        self.occ_delta.max_occ_entries,
                    );
                    self.stats.occ_delta_occ_entries_checked = self
                        .stats
                        .occ_delta_occ_entries_checked
                        .saturating_add(validation.occ_entries_checked);
                    self.stats.occ_delta_missing_entries = self
                        .stats
                        .occ_delta_missing_entries
                        .saturating_add(validation.missing_entries);
                    self.stats.occ_delta_stale_live_entries = self
                        .stats
                        .occ_delta_stale_live_entries
                        .saturating_add(validation.stale_live_entries);
                    self.stats.occ_delta_live_learned_entries = self
                        .stats
                        .occ_delta_live_learned_entries
                        .saturating_add(validation.live_learned_entries);

                    if validation.oversize {
                        self.stats.occ_delta_oversize_fallbacks =
                            self.stats.occ_delta_oversize_fallbacks.saturating_add(1);
                        needs_full_validation = true;
                    } else if validation.is_valid() {
                        self.stats.occ_delta_validated_refreshes =
                            self.stats.occ_delta_validated_refreshes.saturating_add(1);
                        self.occ_consistency_epoch = clause_db_epoch;
                        needs_full_validation = false;
                        delta_validated = true;
                    } else {
                        self.stats.occ_delta_validation_fallbacks =
                            self.stats.occ_delta_validation_fallbacks.saturating_add(1);
                        needs_full_validation = true;
                    }
                }
            }
        }

        if needs_full_validation && self.occ_needs_rebuild(clauses, vals, filter_satisfied) {
            self.rebuild_inner(clauses, vals);
            self.occ_consistency_epoch = clause_db_epoch;
            self.occ_delta.clear_validated();
            return false;
        }
        if needs_full_validation || delta_validated {
            self.occ_consistency_epoch = clause_db_epoch;
            self.occ_delta.clear_validated();
        } else if !should_validate {
            self.stats.occ_epoch_fastpath_refreshes =
                self.stats.occ_epoch_fastpath_refreshes.saturating_add(1);
        }

        // Remove satisfied clauses from occ lists. A clause is satisfied if any
        // of its literals is true at root level (vals[lit.index()] > 0).
        //
        // Strategy: iterate occ lists of true-valued literals. For each clause
        // found there, remove it from ALL its literals' occ lists and mark
        // remaining variables dirty for rescheduling.
        if filter_satisfied {
            for var_idx in 0..self.num_vars {
                if self.eliminated[var_idx] {
                    continue;
                }
                for polarity in 0..2u32 {
                    let lit_idx = var_idx * 2 + polarity as usize;
                    if lit_idx >= vals.len() || vals[lit_idx] <= 0 {
                        continue;
                    }
                    // This literal is true at root level. All clauses containing
                    // it are satisfied and should be removed from occ lists.
                    let lit = if polarity == 0 {
                        Literal::positive(Variable(var_idx as u32))
                    } else {
                        Literal::negative(Variable(var_idx as u32))
                    };
                    // Collect clause indices first (can't modify while iterating).
                    let satisfied_clauses: Vec<usize> = self
                        .occ
                        .get(lit)
                        .iter()
                        .copied()
                        .filter(|&idx| idx < clauses.len() && !clauses.is_dead(idx))
                        .collect();
                    for clause_idx in satisfied_clauses {
                        let clause_lits = clauses.literals(clause_idx);
                        self.occ.remove_clause(clause_idx, clause_lits);
                        // Mark remaining variables dirty for rescheduling.
                        for &cl in clause_lits {
                            let vi = cl.variable().index();
                            if vi < self.candidate_dirty.len() && !self.eliminated[vi] {
                                self.candidate_dirty[vi] = true;
                            }
                        }
                    }
                }
            }

            // Mark dirty for clauses with falsified (but not satisfied) literals.
            // Instead of scanning ALL clauses O(clause_literals), use occ-list-
            // guided lookup: for each false-valued literal, iterate its occ list
            // to find clauses that contain a falsified literal. After the satisfied
            // clause removal loop above, occ lists only contain non-satisfied
            // clauses, so each clause found here has a false literal but is NOT
            // satisfied. Mark the non-false, non-eliminated variables dirty so
            // their elimination scores are recomputed.
            //
            // Cost: O(sum of occ-list sizes for false-valued literals) instead of
            // O(all_clause_literals). On formulas with few root-level units, this
            // is dramatically cheaper than the full scan (#8096).
            for var_idx in 0..self.num_vars {
                if self.eliminated[var_idx] {
                    continue;
                }
                for polarity in 0..2u32 {
                    let lit_idx = var_idx * 2 + polarity as usize;
                    if lit_idx >= vals.len() || vals[lit_idx] >= 0 {
                        // Not false-valued; skip.
                        continue;
                    }
                    // This literal is false at root level. Clauses containing it
                    // have an effectively shorter length, changing elimination
                    // scores for their remaining variables.
                    let lit = if polarity == 0 {
                        Literal::positive(Variable(var_idx as u32))
                    } else {
                        Literal::negative(Variable(var_idx as u32))
                    };
                    for &clause_idx in self.occ.get(lit) {
                        if clause_idx >= clauses.len() || clauses.is_dead(clause_idx) {
                            continue;
                        }
                        for &cl in clauses.literals(clause_idx) {
                            let vi = cl.variable().index();
                            if vals.get(cl.index()).copied().unwrap_or(0) == 0
                                && vi < self.candidate_dirty.len()
                                && !self.eliminated[vi]
                            {
                                self.candidate_dirty[vi] = true;
                            }
                        }
                    }
                }
            }
        }

        // Gate pair credit refresh (same as in rebuild_inner).
        if !self.fastelim_mode {
            self.refresh_schedule_gate_pair_credit(clauses, vals);
        }

        // Clear and rebuild schedule.
        self.schedule.clear();
        self.schedule_built = false;
        true
    }

    /// Shadow-mode verification: compare current incremental occ lists against
    /// what a full rebuild would produce. Catches incremental maintenance bugs
    /// (#8096). Only runs in debug builds.
    #[cfg(debug_assertions)]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn debug_verify_occ_against_rebuild(&self, clauses: &ClauseArena, vals: &[i8]) {
        let filter_satisfied = !vals.is_empty();

        // Build expected occ lists from scratch.
        let mut expected: HashMap<Literal, Vec<usize>> = HashMap::default();
        for idx in clauses.indices() {
            if clauses.is_dead(idx) || clauses.is_learned(idx) {
                continue;
            }
            if filter_satisfied {
                let satisfied = clauses
                    .literals(idx)
                    .iter()
                    .any(|&lit| vals.get(lit.index()).copied().unwrap_or(0) > 0);
                if satisfied {
                    continue;
                }
            }
            for &lit in clauses.literals(idx) {
                expected.entry(lit).or_default().push(idx);
            }
        }

        // Compare: for each literal, the occ list should contain exactly
        // the same clause indices (order doesn't matter).
        for (&lit, expected_clauses) in &expected {
            let actual = self.occ.get(lit);
            // Filter out dead and learned clauses from actual (lazy removal).
            // BVE occ lists should only contain irredundant clauses, but stale
            // entries for learned clauses may appear when: (1) arena compaction
            // remaps indices, or (2) an irredundant clause is subsumed and the
            // subsumer was learned. Filter both dead and learned to match the
            // expected set which excludes both (#8096).
            let mut actual_live: Vec<usize> = actual
                .iter()
                .copied()
                .filter(|&idx| {
                    if idx >= clauses.len() || clauses.is_dead(idx) || clauses.is_learned(idx) {
                        return false;
                    }
                    // Also filter satisfied clauses to match the expected set.
                    // Occ lists may retain stale entries for clauses that became
                    // satisfied after BCP propagation. These are cleaned up by
                    // `refresh_incremental` before the next BVE round, so their
                    // presence in the occ list between rounds is benign (#8366).
                    if filter_satisfied && Self::clause_satisfied(clauses, idx, vals) {
                        return false;
                    }
                    true
                })
                .collect();
            actual_live.sort_unstable();
            actual_live.dedup();
            let mut expected_sorted = expected_clauses.clone();
            expected_sorted.sort_unstable();
            expected_sorted.dedup();
            debug_assert!(
                actual_live == expected_sorted,
                "BUG (#8096): incremental occ list mismatch for literal {lit:?}\n\
                 expected clauses: {expected_sorted:?}\n\
                 actual (live):    {actual_live:?}\n\
                 extra in actual:  {:?}\n\
                 missing from actual: {:?}",
                actual_live
                    .iter()
                    .filter(|c| !expected_sorted.contains(c))
                    .collect::<Vec<_>>(),
                expected_sorted
                    .iter()
                    .filter(|c| !actual_live.contains(c))
                    .collect::<Vec<_>>(),
            );
        }

        // Check reverse: occ lists shouldn't have clauses not in expected.
        for var_idx in 0..self.num_vars {
            if self.eliminated[var_idx] {
                continue;
            }
            for polarity in 0..2u32 {
                let lit = if polarity == 0 {
                    Literal::positive(Variable(var_idx as u32))
                } else {
                    Literal::negative(Variable(var_idx as u32))
                };
                let actual = self.occ.get(lit);
                for &idx in actual {
                    if idx >= clauses.len() || clauses.is_dead(idx) || clauses.is_learned(idx) {
                        continue; // Stale/learned entries are tolerated.
                    }
                    // Satisfied clauses are benign stale entries (#8366).
                    if filter_satisfied && Self::clause_satisfied(clauses, idx, vals) {
                        continue;
                    }
                    debug_assert!(
                        expected.get(&lit).is_some_and(|v| v.contains(&idx)),
                        "BUG (#8096): occ list for {lit:?} has unexpected live clause {idx}",
                    );
                }
            }
        }
    }
}
