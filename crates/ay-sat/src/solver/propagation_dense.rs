// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Dense (occurrence-list-based) propagation for inprocessing at decision level 0.
//!
//! Port of Kissat `propdense.c` (#8088). During elimination passes (BVE, sweep),
//! occurrence lists are already built for all irredundant clauses. Dense
//! propagation iterates ALL clauses containing a literal (via occ lists),
//! which is more thorough than 2WL during elimination where watch lists may
//! not cover newly added resolvents.
//!
//! Dense propagation is NOT for the main search loop — 2WL is far superior
//! for search. This is only used during preprocessing/inprocessing phases
//! where occurrence lists are already maintained.
//!
//! Reference: Kissat `propdense.c:86-108` (`kissat_dense_propagate`).

use super::mutate::ReasonPolicy;
use super::*;

impl Solver {
    /// Occurrence-list-based unit propagation for inprocessing (#8088).
    ///
    /// Processes the propagation queue (trail from `qhead` onward) using BVE
    /// occurrence lists instead of 2WL watch lists. For each propagated literal:
    ///
    /// 1. **Negative occurrences** (clauses containing `~lit`): these clauses
    ///    lost a literal. Classify each as satisfied/unit/empty/undetermined.
    /// 2. **Positive occurrences** (clauses containing `lit`): these clauses
    ///    are now satisfied. Mark as garbage immediately.
    ///
    /// Returns `Some(conflict_ref)` on conflict, `None` if all propagations
    /// complete without conflict.
    ///
    /// Kissat `propdense.c:86-108`: processes trail entries sequentially,
    /// advancing the propagation pointer. Satisfied clauses are marked as
    /// garbage immediately (Kissat `kissat_mark_clause_as_garbage`).
    ///
    /// REQUIRES: decision_level == 0, BVE occurrence lists are built
    /// ENSURES: all unit implications from occ lists discovered and enqueued,
    ///          satisfied clauses marked as garbage
    pub(super) fn propagate_dense(&mut self) -> Option<ClauseRef> {
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: propagate_dense called at non-zero decision level {}",
            self.decision_level
        );

        // Reusable buffers -- allocated once, cleared each iteration.
        // Avoids per-literal heap allocation in the propagation loop.
        let mut neg_occs_buf: Vec<usize> = Vec::new();
        let mut pos_occs_buf: Vec<usize> = Vec::new();
        let mut satisfied_buf: Vec<usize> = Vec::new();
        let qhead_start = self.qhead;

        while self.qhead < self.trail.len() {
            let lit = self.trail[self.qhead];
            self.qhead += 1;
            let neg_lit = lit.negated();

            // -- Phase 1: Negative occurrences (clauses containing ~lit) --
            // These clauses lost a literal (now false). Check for unit/empty.
            neg_occs_buf.clear();
            neg_occs_buf.extend_from_slice(self.inproc.bve.get_occs(neg_lit));

            for &c_idx in &neg_occs_buf {
                if !self.arena.is_active(c_idx) {
                    continue;
                }

                // Classify clause: scan literals to determine status.
                // Kissat propdense.c:46-67.
                let clause_lits = self.arena.literals(c_idx);
                let mut unit_lit: Option<Literal> = None;
                let mut satisfied = false;
                let mut multiple_unassigned = false;

                for &other in clause_lits {
                    let v = self.lit_val(other);
                    if v > 0 {
                        // Literal is true -> clause is satisfied.
                        satisfied = true;
                        break;
                    }
                    if v < 0 {
                        // Literal is false -> skip.
                        continue;
                    }
                    // v == 0: unassigned literal.
                    if unit_lit.is_some() {
                        // Two or more unassigned -> not yet determined.
                        multiple_unassigned = true;
                        break;
                    }
                    unit_lit = Some(other);
                }

                if satisfied {
                    // Kissat propdense.c:57-59: mark satisfied clause as garbage.
                    satisfied_buf.push(c_idx);
                    continue;
                }

                if multiple_unassigned {
                    // 2+ unassigned: clause not yet determined, skip.
                    continue;
                }

                if let Some(unit) = unit_lit {
                    // Exactly one unassigned literal -> unit propagation.
                    // Kissat propdense.c:75-76.
                    let clause_ref = ClauseRef(c_idx as u32);
                    self.enqueue(unit, Some(clause_ref));
                } else {
                    // All literals false -> empty clause -> conflict.
                    // Kissat propdense.c:70-72.
                    self.stats.dense_propagations += (self.qhead - qhead_start) as u64;
                    self.stats.dense_conflicts += 1;
                    return Some(ClauseRef(c_idx as u32));
                }
            }

            // -- Phase 2: Positive occurrences (clauses containing lit) --
            // These clauses are now satisfied. Mark as garbage.
            // Kissat propdense.c:56-60 (satisfied branch within large clause scan)
            // and Kissat eliminate.c:176-184 (kissat_flush_units_while_connected).
            pos_occs_buf.clear();
            pos_occs_buf.extend(
                self.inproc
                    .bve
                    .get_occs(lit)
                    .iter()
                    .copied()
                    .filter(|&c_idx| self.arena.is_active(c_idx)),
            );
            satisfied_buf.extend_from_slice(&pos_occs_buf);

            // -- Phase 3: Delete all satisfied clauses collected above --
            // Batching deletions avoids interleaving mutation with occ-list
            // iteration. Clause deletion is idempotent (skip if already dead).
            for &c_idx in &satisfied_buf {
                if self.arena.is_active(c_idx) {
                    // Per-clause BVE occ notification (#8364): capture literals
                    // before deletion so the occ list can be updated incrementally.
                    let is_irredundant = !self.arena.is_learned(c_idx);
                    let old_lits_for_bve = if is_irredundant {
                        Some(self.arena.literals(c_idx).to_vec())
                    } else {
                        None
                    };
                    self.delete_clause_checked(c_idx, ReasonPolicy::ClearLevel0);
                    if let Some(ref old_lits) = old_lits_for_bve {
                        self.note_irredundant_clause_removed_for_bve(c_idx, old_lits);
                    }
                    self.stats.dense_satisfied_deleted += 1;
                }
            }
            satisfied_buf.clear();
        }

        // Update propagation counter (Kissat propdense.c:96-98).
        // Dense propagations count toward the global propagation budget.
        let propagated = (self.qhead - qhead_start) as u64;
        self.stats.dense_propagations += propagated;

        None
    }

    /// Convenience wrapper: check for UNSAT using dense propagation.
    ///
    /// Returns `true` if UNSAT was derived (empty clause found or conflict
    /// at decision level 0). Mirrors `propagate_check_unsat()` but uses
    /// dense (occ-list) propagation instead of 2WL BCP.
    ///
    /// Use this during inprocessing phases where BVE occurrence lists are
    /// already built and 2WL watch lists may be incomplete for newly added
    /// resolvents.
    #[inline]
    pub(super) fn propagate_dense_check_unsat(&mut self) -> bool {
        if self.has_empty_clause {
            return true;
        }
        if let Some(conflict_ref) = self.propagate_dense() {
            self.record_level0_conflict_chain(conflict_ref);
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::{Literal, Variable};

    /// Helper: DIMACS literal to internal Literal.
    #[allow(dead_code)]
    fn dimacs_to_lit(d: i32) -> Literal {
        let var = Variable(d.unsigned_abs() - 1);
        if d > 0 {
            Literal::positive(var)
        } else {
            Literal::negative(var)
        }
    }

    /// Helper: create a solver with given clauses and variables.
    /// Uses `add_clause_db` (internal API) to avoid normalization side effects.
    #[allow(dead_code)]
    fn make_solver(num_vars: usize, clauses: &[&[i32]]) -> Solver {
        let mut solver = Solver::new(num_vars);
        for clause in clauses {
            let lits: Vec<Literal> = clause.iter().map(|&d| dimacs_to_lit(d)).collect();
            solver.add_clause_db(&lits, false);
        }
        // Run 2WL propagation to process any unit clauses from add_clause_db.
        // This enqueues unit literals onto the trail so dense propagation
        // can process their implications.
        solver.initialize_watches();
        let _ = solver.search_propagate();
        solver
    }

    #[test]
    fn test_propagate_dense_unit_propagation() {
        // Clauses: (1), (-1 | 2), (-2 | 3)
        // Unit 1 → 2 → 3.
        // The 2WL propagation in make_solver handles unit clause (1) and chains,
        // so qhead should be at trail end. We need to test that dense propagation
        // handles newly-added clauses that the 2WL might not see (BVE resolvents).
        //
        // To test dense propagation specifically, add clauses manually and use
        // enqueue to put a literal on the trail without 2WL processing.
        let mut solver = Solver::new(4);
        let a = Variable(0);
        let b = Variable(1);
        let c = Variable(2);

        // Add non-unit clauses only (so 2WL doesn't propagate them).
        solver.add_clause_db(&[Literal::negative(a), Literal::positive(b)], false);
        solver.add_clause_db(&[Literal::negative(b), Literal::positive(c)], false);
        solver.initialize_watches();

        // Build BVE occurrence lists for dense propagation.
        solver
            .inproc
            .bve
            .rebuild_with_vals(&solver.arena, &solver.vals);

        // Manually assign a=true (as if BVE produced a resolvent unit).
        solver.enqueue(Literal::positive(a), None);
        // Don't advance qhead through 2WL — leave it for dense propagation.

        let conflict = solver.propagate_dense();
        assert!(conflict.is_none(), "should not conflict");

        // All three variables should be assigned: a=T → b=T → c=T.
        assert!(solver.var_is_assigned(0), "var a should be assigned");
        assert!(solver.var_is_assigned(1), "var b should be assigned");
        assert!(solver.var_is_assigned(2), "var c should be assigned");

        assert_eq!(solver.lit_val(Literal::positive(a)), 1);
        assert_eq!(solver.lit_val(Literal::positive(b)), 1);
        assert_eq!(solver.lit_val(Literal::positive(c)), 1);
    }

    #[test]
    fn test_propagate_dense_conflict_detection() {
        // Clauses: (-a), (a | b)
        // Manually assign a=T → (-a) becomes empty → conflict.
        let mut solver = Solver::new(2);
        let a = Variable(0);
        let b = Variable(1);

        solver.add_clause_db(&[Literal::negative(a)], false);
        solver.add_clause_db(&[Literal::positive(a), Literal::positive(b)], false);
        solver.initialize_watches();

        solver
            .inproc
            .bve
            .rebuild_with_vals(&solver.arena, &solver.vals);

        // Force a=true on trail without 2WL propagation.
        solver.enqueue(Literal::positive(a), None);

        let conflict = solver.propagate_dense();
        assert!(
            conflict.is_some(),
            "should detect conflict from empty clause"
        );
    }

    #[test]
    fn test_propagate_dense_satisfied_clause_deletion() {
        // Clauses: (a | b | c), (-b | c)
        // Assign a=T → (a | b | c) is satisfied → should be deleted.
        let mut solver = Solver::new(3);
        let a = Variable(0);
        let b = Variable(1);
        let c = Variable(2);

        solver.add_clause_db(
            &[
                Literal::positive(a),
                Literal::positive(b),
                Literal::positive(c),
            ],
            false,
        );
        solver.add_clause_db(&[Literal::negative(b), Literal::positive(c)], false);
        solver.initialize_watches();

        let active_before = solver.arena.active_clause_count();
        solver
            .inproc
            .bve
            .rebuild_with_vals(&solver.arena, &solver.vals);

        // Assign a=true.
        solver.enqueue(Literal::positive(a), None);
        let conflict = solver.propagate_dense();
        assert!(conflict.is_none(), "should not conflict");

        let active_after = solver.arena.active_clause_count();
        assert!(
            active_after < active_before,
            "satisfied clause should be deleted: before={active_before}, after={active_after}",
        );
    }

    #[test]
    fn test_propagate_dense_no_propagation_needed() {
        // Clauses: (a | b), (-a | -b)
        // No unit clauses, no assignments, no propagation possible.
        let mut solver = Solver::new(2);
        let a = Variable(0);
        let b = Variable(1);

        solver.add_clause_db(&[Literal::positive(a), Literal::positive(b)], false);
        solver.add_clause_db(&[Literal::negative(a), Literal::negative(b)], false);
        solver.initialize_watches();

        solver
            .inproc
            .bve
            .rebuild_with_vals(&solver.arena, &solver.vals);

        let conflict = solver.propagate_dense();
        assert!(conflict.is_none(), "should not conflict");
        assert!(!solver.var_is_assigned(0), "var a should be unassigned");
        assert!(!solver.var_is_assigned(1), "var b should be unassigned");
    }

    #[test]
    fn test_propagate_dense_check_unsat_wrapper() {
        // Test the convenience wrapper mirrors propagate_check_unsat behavior.
        let mut solver = Solver::new(2);
        let a = Variable(0);
        let b = Variable(1);

        solver.add_clause_db(&[Literal::positive(a), Literal::positive(b)], false);
        solver.initialize_watches();
        solver
            .inproc
            .bve
            .rebuild_with_vals(&solver.arena, &solver.vals);

        // No conflict.
        assert!(!solver.propagate_dense_check_unsat(), "should not be UNSAT");
    }
}
