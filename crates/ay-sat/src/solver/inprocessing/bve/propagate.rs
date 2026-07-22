// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//\! Occ-list-based unit propagation for BVE.

use super::super::super::mutate::ReasonPolicy;
use super::super::super::*;

impl Solver {
    /// Occ-list-based unit propagation for BVE (CaDiCaL `elim_propagate`,
    /// `elim.cpp:142-199`).
    ///
    /// Replaces `propagate_check_unsat()` (#5085). Instead of full 2WL BCP,
    /// walks BVE occurrence lists to find new units and mark satisfied clauses
    /// as garbage. This is cheaper because:
    /// - BVE already maintains occ lists — no extra data structure
    /// - No watch list scanning (avoids cache-line pollution from unrelated clauses)
    /// - Satisfied clause GC is immediate via `delete_clause_checked`
    ///
    /// Uses a local worklist starting from `start_pos` (the trail position
    /// before this variable's resolvent addition). Does NOT use `qhead` — the
    /// 2WL watch lists may not cover clauses seen by occ lists (watches are
    /// only set up for resolvents via `add_clause_watched`, not for the full
    /// clause database). The existing `qhead` entries will be processed by
    /// `search_propagate` when CDCL search resumes.
    ///
    /// Returns true if UNSAT was derived (empty clause found).
    ///
    /// REQUIRES: decision_level == 0
    /// ENSURES: if false returned, all unit implications from BVE occ lists
    ///          discovered, satisfied clauses deleted
    pub(super) fn elim_propagate(
        &mut self,
        start_pos: usize,
        elim_var: Variable,
        lits_buf: &mut Vec<Literal>,
        sat_buf: &mut Vec<usize>,
    ) -> bool {
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: elim_propagate called at non-zero decision level"
        );

        // Local worklist index: processes trail entries from start_pos onward,
        // including any new units discovered during propagation. This mirrors
        // CaDiCaL's local `work` vector in elim_propagate (elim.cpp:148-149).
        let mut work_pos = start_pos;

        while work_pos < self.trail.len() {
            let lit = self.trail[work_pos];
            work_pos += 1;

            // --- Negative occurrences: clauses containing ~lit ---
            // These clauses lost a literal (now false). Check for unit/empty.
            // Copy occ list to avoid borrow conflict with self mutation.
            let neg_lit = lit.negated();
            sat_buf.clear();
            sat_buf.extend_from_slice(self.inproc.bve.get_occs(neg_lit));

            for &c_idx in sat_buf.iter() {
                if !self.arena.is_active(c_idx) {
                    continue;
                }

                // Scan clause to classify: satisfied / unit / empty / undetermined
                let clause_lits = self.arena.literals(c_idx);
                let mut unit: Option<Literal> = None;
                let mut satisfied = false;
                let mut multiple_unassigned = false;

                for &other in clause_lits {
                    let v = self.lit_val(other);
                    if v > 0 {
                        // Literal is true → clause satisfied
                        satisfied = true;
                        break;
                    }
                    if v < 0 {
                        // Literal is false → skip
                        continue;
                    }
                    // v == 0: unassigned
                    if unit.is_some() {
                        // Two or more unassigned → not yet determined
                        multiple_unassigned = true;
                        break;
                    }
                    unit = Some(other);
                }

                if satisfied {
                    // CaDiCaL: elim_update_removed_clause + mark_garbage
                    lits_buf.clear();
                    lits_buf.extend_from_slice(clause_lits);
                    self.delete_clause_checked(c_idx, ReasonPolicy::ClearLevel0);
                    self.inproc.bve.update_schedule_after_clause_removal(
                        lits_buf,
                        elim_var,
                        &self.vals,
                        &self.cold.freeze_counts,
                    );
                } else if multiple_unassigned {
                    // 2+ unassigned literals: clause not yet determined, skip
                } else if let Some(unit_lit) = unit {
                    // Exactly one unassigned literal → unit clause
                    let clause_ref = ClauseRef(c_idx as u32);
                    self.enqueue(unit_lit, Some(clause_ref));
                    // New unit goes on trail; work_pos will reach it
                } else {
                    // All literals false → empty clause → UNSAT
                    let conflict_ref = ClauseRef(c_idx as u32);
                    self.record_level0_conflict_chain(conflict_ref);
                    return true;
                }
            }

            // --- Positive occurrences: clauses containing lit ---
            // These clauses are now satisfied. Mark as garbage.
            self.inproc
                .bve
                .satisfied_clauses_into(lit, &self.arena, sat_buf);
            for &c_idx in sat_buf.iter() {
                lits_buf.clear();
                lits_buf.extend_from_slice(self.arena.literals(c_idx));
                self.delete_clause_checked(c_idx, ReasonPolicy::ClearLevel0);
                self.inproc.bve.update_schedule_after_clause_removal(
                    lits_buf,
                    elim_var,
                    &self.vals,
                    &self.cold.freeze_counts,
                );
            }
        }

        false
    }
}
