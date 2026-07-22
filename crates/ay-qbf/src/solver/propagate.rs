// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl QbfSolver {
    /// Convert a literal to its watch index
    #[inline]
    fn lit_to_watch_idx(lit: Literal) -> usize {
        let var = lit.variable().id() as usize;
        var * 2 + usize::from(!lit.is_positive())
    }

    /// Initialize watches for all original clauses
    pub(super) fn init_watches(&mut self) {
        for i in 0..self.formula.clauses.len() {
            let clause = &self.formula.clauses[i];
            if clause.len() >= 2 {
                // Watch first two literals
                let lit0 = clause[0];
                let lit1 = clause[1];
                let idx0 = Self::lit_to_watch_idx(lit0);
                let idx1 = Self::lit_to_watch_idx(lit1);
                self.watches[idx0].push(WatchInfo {
                    clause_idx: i,
                    blocker: lit1,
                });
                self.watches[idx1].push(WatchInfo {
                    clause_idx: i,
                    blocker: lit0,
                });
            }
            // Unit and empty clauses don't need watches - handled specially
        }
    }

    /// Add watches for a learned clause
    pub(super) fn add_learned_watches(&mut self, clause_idx: usize) {
        let clause = &self.learned[clause_idx];
        if clause.len() >= 2 {
            let lit0 = clause[0];
            let lit1 = clause[1];
            let idx0 = Self::lit_to_watch_idx(lit0);
            let idx1 = Self::lit_to_watch_idx(lit1);
            // Mark as learned with high bit
            let marked_idx = clause_idx | LEARNED_CLAUSE_BIT;
            self.watches[idx0].push(WatchInfo {
                clause_idx: marked_idx,
                blocker: lit1,
            });
            self.watches[idx1].push(WatchInfo {
                clause_idx: marked_idx,
                blocker: lit0,
            });
        }
    }

    /// Unit propagation using two-watched literals
    ///
    /// For QBF, we use a hybrid approach:
    /// 1. Track two watched literals per clause (for clauses with >= 2 literals)
    /// 2. When a literal becomes false, check only clauses watching it
    /// 3. Try to find a new watch; if not possible, do full QBF analysis
    pub(super) fn propagate(&mut self) -> PropResult {
        // First, handle unit clauses (not covered by 2WL)
        if let Some(conflict) = self.propagate_unit_clauses() {
            return PropResult::Conflict(conflict);
        }

        // Main propagation loop using watched literals
        while self.qhead < self.trail.len() {
            let false_lit = self.trail[self.qhead];
            self.qhead += 1;

            // Check clauses watching the negation of this literal
            // (those clauses now have one of their watched literals false)
            let watch_idx = Self::lit_to_watch_idx(false_lit.negated());

            // Process watches - we'll rebuild the watch list as we go
            let mut i = 0;
            while i < self.watches[watch_idx].len() {
                let watch = self.watches[watch_idx][i];
                let is_learned = (watch.clause_idx & LEARNED_CLAUSE_BIT) != 0;
                let clause_idx = watch.clause_idx & !LEARNED_CLAUSE_BIT;

                // Quick check: if blocker is true, clause is satisfied
                if self.lit_value(watch.blocker) == Assignment::True {
                    i += 1;
                    continue;
                }

                // Get the clause
                let clause = if is_learned {
                    &self.learned[clause_idx]
                } else {
                    &self.formula.clauses[clause_idx]
                };

                // Skip deleted (empty) learned clauses — lazy watch cleanup
                if is_learned && clause.is_empty() {
                    self.watches[watch_idx].swap_remove(i);
                    continue;
                }

                // Find the positions of the two watched literals
                let watched_lit = false_lit.negated();
                let (w0_pos, w1_pos) =
                    Self::find_watch_positions(clause, watched_lit, watch.blocker);

                // Try to find a new watch
                if let Some(new_watch) = self.find_new_watch(clause, w0_pos, w1_pos) {
                    // Found a new watch - update
                    let new_watch_lit = clause[new_watch];
                    let new_watch_idx = Self::lit_to_watch_idx(new_watch_lit);

                    // Remove from current watch list
                    self.watches[watch_idx].swap_remove(i);

                    // Add to new watch list
                    self.watches[new_watch_idx].push(watch);

                    // Don't increment i - we swapped in a new element
                    continue;
                }

                // No new watch found - do full QBF clause analysis
                let global_clause_idx = if is_learned {
                    self.formula.clauses.len() + clause_idx
                } else {
                    clause_idx
                };

                match self.check_clause_unit(clause, is_learned) {
                    ClauseStatus::Satisfied => {
                        // Shouldn't normally happen if blocker check worked
                        i += 1;
                    }
                    ClauseStatus::Falsified | ClauseStatus::UniversallyBlocked => {
                        return PropResult::Conflict(global_clause_idx);
                    }
                    ClauseStatus::Unit(prop_lit) => {
                        self.propagations += 1;
                        self.assign(prop_lit, Reason::Propagated(global_clause_idx));
                        i += 1;
                    }
                    ClauseStatus::Unresolved => {
                        i += 1;
                    }
                }
            }
        }

        PropResult::Ok
    }

    /// Propagate unit clauses (not covered by 2WL)
    fn propagate_unit_clauses(&mut self) -> Option<usize> {
        // Check original unit clauses
        for i in 0..self.formula.clauses.len() {
            let clause = &self.formula.clauses[i];
            if clause.len() == 1 {
                let lit = clause[0];
                match self.lit_value(lit) {
                    Assignment::True => {}
                    Assignment::False => return Some(i),
                    Assignment::Unassigned => {
                        if self.formula.lit_is_existential(lit) {
                            self.propagations += 1;
                            self.assign(lit, Reason::Propagated(i));
                        } else {
                            // Universal unit clause - blocked
                            return Some(i);
                        }
                    }
                }
            } else if clause.is_empty() {
                return Some(i);
            }
        }

        // Check learned unit clauses (skip empty = deleted by reduction)
        for i in 0..self.learned.len() {
            let clause = &self.learned[i];
            if clause.is_empty() {
                continue; // deleted by reduce_learned_clauses
            }
            if clause.len() == 1 {
                let lit = clause[0];
                let global_idx = self.formula.clauses.len() + i;
                match self.lit_value(lit) {
                    Assignment::True => {}
                    Assignment::False => return Some(global_idx),
                    Assignment::Unassigned => {
                        // Learned clauses can propagate universals
                        self.propagations += 1;
                        self.assign(lit, Reason::Propagated(global_idx));
                    }
                }
            }
        }

        // Check cubes for propagation
        // Cubes are stored as negated literals, so they propagate like clauses
        // A cube (¬u1 ∨ ¬u2) propagates when all but one literal is false
        // (i.e., u1 is true and u2 is unassigned → propagate ¬u2 = u2 = false)
        self.propagate_cubes()
    }

    /// Propagate cubes
    ///
    /// Cubes are stored as disjunctions of negated literals.
    /// When all but one literal is false (original literal is true),
    /// the remaining literal must be true (original must be false).
    fn propagate_cubes(&mut self) -> Option<usize> {
        for i in 0..self.cubes.len() {
            let cube = &self.cubes[i];
            if cube.is_empty() {
                continue; // deleted by reduction, or empty (SAT handled elsewhere)
            }
            // Check cube status
            let mut num_false = 0;
            let mut num_unassigned = 0;
            let mut unassigned_lit = None;
            let mut has_true = false;

            for &lit in cube {
                match self.lit_value(lit) {
                    Assignment::True => {
                        has_true = true;
                        break;
                    }
                    Assignment::False => {
                        num_false += 1;
                    }
                    Assignment::Unassigned => {
                        num_unassigned += 1;
                        unassigned_lit = Some(lit);
                    }
                }
            }

            if has_true {
                // Cube is satisfied, no propagation needed
                continue;
            }

            if num_unassigned == 0 && num_false == cube.len() {
                // All literals false - this is a conflict!
                // The cube says "at least one of these must be true"
                // But all are false - should not happen if cube is correct
                // This indicates SAT (the existential always wins)
                continue;
            }

            if num_unassigned == 1 && num_false == cube.len() - 1 {
                // Unit propagation: one literal must be true
                // This forces a universal variable
                let lit = unassigned_lit.expect("num_unassigned==1 guarantees Some");
                self.propagations += 1;
                if i < self.cube_used.len() {
                    self.cube_used[i] = true;
                }
                self.assign(lit, Reason::CubePropagated(i));
            }
        }

        None
    }

    /// Find positions of two watched literals in a clause
    fn find_watch_positions(clause: &[Literal], w0: Literal, w1: Literal) -> (usize, usize) {
        let mut pos0 = 0;
        let mut pos1 = 1;
        for (i, &lit) in clause.iter().enumerate() {
            if lit == w0 {
                pos0 = i;
            } else if lit == w1 {
                pos1 = i;
            }
        }
        (pos0, pos1)
    }

    /// Try to find a new literal to watch (not at positions w0_pos or w1_pos)
    fn find_new_watch(&self, clause: &[Literal], w0_pos: usize, w1_pos: usize) -> Option<usize> {
        for (i, &lit) in clause.iter().enumerate() {
            if i == w0_pos || i == w1_pos {
                continue;
            }
            // Can watch if not false
            if self.lit_value(lit) != Assignment::False {
                return Some(i);
            }
        }
        None
    }

    /// Check clause status for unit propagation
    ///
    /// Key insight for QBF: A clause is "universally blocked" if:
    /// - No existential literals are unassigned
    /// - No literals are satisfied
    /// - Universal literals remain unassigned
    /// - The clause is NOT a tautology (doesn't contain both x and ¬x)
    ///
    /// For learned clauses, a single universal literal CAN be propagated because
    /// it represents a constraint the SAT player derived. For original clauses,
    /// single universal literals are blocked (adversary controls them).
    fn check_clause_unit(&self, clause: &[Literal], is_learned: bool) -> ClauseStatus {
        let mut unassigned_existential = None;
        let mut num_unassigned_exist = 0;
        let mut unassigned_univ_lits = Vec::new();
        let mut has_satisfied = false;

        for &lit in clause {
            match self.lit_value(lit) {
                Assignment::True => {
                    has_satisfied = true;
                    break;
                }
                Assignment::False => {}
                Assignment::Unassigned => {
                    if self.formula.lit_is_existential(lit) {
                        num_unassigned_exist += 1;
                        unassigned_existential = Some(lit);
                    } else {
                        unassigned_univ_lits.push(lit);
                    }
                }
            }
        }

        if has_satisfied {
            ClauseStatus::Satisfied
        } else if num_unassigned_exist == 0 && unassigned_univ_lits.is_empty() {
            // All literals are false
            ClauseStatus::Falsified
        } else if num_unassigned_exist == 0 && unassigned_univ_lits.len() == 1 && is_learned {
            // Single universal literal in LEARNED clause - propagate it!
            // This represents a constraint the SAT player derived.
            ClauseStatus::Unit(unassigned_univ_lits[0])
        } else if num_unassigned_exist == 0 && !unassigned_univ_lits.is_empty() {
            // Universal literals remain - check if UNSAT player can falsify
            // They CAN'T falsify if the clause is a tautology (contains both x and ¬x)
            let is_tautology = Self::contains_complementary(&unassigned_univ_lits);
            if is_tautology {
                // Tautology - always satisfied regardless of universal assignment
                ClauseStatus::Satisfied
            } else {
                // Non-tautology with only universals - UNSAT player can falsify
                ClauseStatus::UniversallyBlocked
            }
        } else if num_unassigned_exist == 1 && unassigned_univ_lits.is_empty() {
            // Single existential literal - can propagate
            ClauseStatus::Unit(unassigned_existential.expect("num_unassigned_exist==1"))
        } else {
            ClauseStatus::Unresolved
        }
    }

    /// Check if a set of literals contains a complementary pair (x and ¬x)
    fn contains_complementary(lits: &[Literal]) -> bool {
        for i in 0..lits.len() {
            for j in (i + 1)..lits.len() {
                // Check if lits[i] and lits[j] are complements (same var, different polarity)
                if lits[i].variable() == lits[j].variable()
                    && lits[i].is_positive() != lits[j].is_positive()
                {
                    return true;
                }
            }
        }
        false
    }
}
