// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl QbfSolver {
    pub(super) fn bump_clause_activity(&mut self, clause: &[Literal]) {
        for &lit in clause {
            self.bump_var_activity(lit.variable().id());
        }
    }

    fn bump_var_activity(&mut self, var: u32) {
        let idx = var as usize - 1;
        self.activity[idx] += self.var_inc;
        if self.activity[idx] > 1e100 {
            self.rescale_var_activity();
        }
    }

    pub(super) fn var_decay_activity(&mut self) {
        self.var_inc *= 1.0 / self.var_decay;
        if self.var_inc > 1e100 {
            self.rescale_var_activity();
        }
    }

    fn rescale_var_activity(&mut self) {
        for act in &mut self.activity {
            *act *= 1e-100;
        }
        self.var_inc *= 1e-100;
    }

    #[allow(clippy::float_cmp)]
    fn pick_branch_var(&self) -> Option<u32> {
        let mut min_level: Option<u32> = None;
        for &var in &self.decision_order {
            if self.value(var) == Assignment::Unassigned {
                let lvl = self.formula.var_level(var);
                min_level = Some(min_level.map_or(lvl, |cur| cur.min(lvl)));
            }
        }
        let min_level = min_level?;

        let mut best_var: Option<u32> = None;
        let mut best_activity = f64::NEG_INFINITY;
        for &var in &self.decision_order {
            if self.value(var) != Assignment::Unassigned || self.formula.var_level(var) != min_level
            {
                continue;
            }

            let act = self.activity[var as usize - 1];
            if best_var.is_none()
                || act > best_activity
                || (act == best_activity && best_var.is_some_and(|bv| var < bv))
            {
                best_var = Some(var);
                best_activity = act;
            }
        }

        best_var
    }

    /// Make a decision
    pub(super) fn decide(&mut self) -> Option<Literal> {
        let var = self.pick_branch_var()?;

        // New decision level
        self.decision_level += 1;
        self.trail_lim.push(self.trail.len());

        // Decide: try true first for existential, false for universal
        let polarity = self.formula.is_existential(var);
        let lit = if polarity {
            Literal::positive(Variable::new(var))
        } else {
            Literal::negative(Variable::new(var))
        };

        self.assign(lit, Reason::Decision);
        Some(lit)
    }

    /// Backtrack to a given level
    pub(super) fn backtrack(&mut self, level: u32) {
        if level < self.decision_level {
            let trail_pos = if level == 0 {
                0
            } else {
                self.trail_lim[level as usize - 1]
            };

            self.unassign_to(trail_pos);

            // Reset propagation queue head
            self.qhead = trail_pos;

            // Truncate trail limits
            self.trail_lim.truncate(level as usize);
            self.decision_level = level;
        }
    }

    /// Analyze conflict and return (learned clause, backtrack level)
    ///
    /// Implements Q-resolution based 1-UIP conflict analysis:
    /// 1. Start with the conflict clause
    /// 2. Resolve backwards using reason clauses until reaching 1-UIP
    /// 3. Apply universal reduction at each resolution step (Q-resolution)
    /// 4. The resulting clause has exactly one literal at the current decision level
    ///
    /// This learns more specific clauses than simple decision-negation,
    /// leading to better pruning and faster solving.
    pub(super) fn analyze_conflict(&mut self, conflict_clause_idx: usize) -> (Vec<Literal>, u32) {
        // Get the conflict clause and mark it as used
        let conflict_clause = if conflict_clause_idx < self.formula.clauses.len() {
            self.formula.clauses[conflict_clause_idx].clone()
        } else {
            let learned_idx = conflict_clause_idx - self.formula.clauses.len();
            self.mark_clause_used(learned_idx);
            self.learned[learned_idx].clone()
        };

        let mut seen = vec![false; self.formula.num_vars];
        let mut learned: Vec<Literal> = Vec::new();
        let mut counter = 0;

        // Start with the conflict clause
        for &lit in &conflict_clause {
            let var = lit.variable().id();
            let level = self.levels[var as usize - 1];

            if !seen[var as usize - 1] {
                seen[var as usize - 1] = true;
                if level == self.decision_level {
                    counter += 1;
                } else if level > 0 {
                    // Literal from earlier level goes directly to learned clause
                    learned.push(lit.negated());
                }
            }
        }

        // Work backwards through the trail
        let mut trail_idx = self.trail.len();
        let mut asserting_lit: Option<Literal> = None;

        while counter > 0 {
            // Find the next literal on the trail that we've seen
            trail_idx -= 1;
            let lit = self.trail[trail_idx];
            let var = lit.variable().id();

            if !seen[var as usize - 1] {
                continue;
            }

            // This variable was involved in the conflict
            seen[var as usize - 1] = false;
            counter -= 1;

            if counter == 0 {
                // This is the 1-UIP - the asserting literal
                asserting_lit = Some(lit.negated());
                break;
            }

            // Get the reason clause and resolve
            let reason = self.reasons[var as usize - 1];
            if let Reason::Propagated(reason_idx) = reason {
                let reason_clause = if reason_idx < self.formula.clauses.len() {
                    self.formula.clauses[reason_idx].clone()
                } else {
                    let learned_idx = reason_idx - self.formula.clauses.len();
                    self.mark_clause_used(learned_idx);
                    self.learned[learned_idx].clone()
                };
                for &reason_lit in &reason_clause {
                    let reason_var = reason_lit.variable().id();
                    if reason_var == var {
                        continue;
                    }
                    let level = self.levels[reason_var as usize - 1];
                    if !seen[reason_var as usize - 1] {
                        seen[reason_var as usize - 1] = true;
                        if level == self.decision_level {
                            counter += 1;
                        } else if level > 0 {
                            learned.push(reason_lit.negated());
                        }
                    }
                }
            } else if matches!(reason, Reason::CubePropagated(_)) {
                // Cube-propagated: treat like decision, include without resolving
                let level = self.levels[var as usize - 1];
                if level > 0 {
                    learned.push(lit.negated());
                }
            }
        }

        // Add the asserting literal
        if let Some(lit) = asserting_lit {
            learned.push(lit);
        }

        // Apply universal reduction (Q-resolution)
        // This removes universal literals that are "blocked"
        let reduced = self.formula.universal_reduce(&learned);

        // Compute backtrack level (second highest level in learned clause)
        let backtrack_level = self.compute_backtrack_level(&reduced);

        (reduced, backtrack_level)
    }

    /// Compute the backtrack level for a learned clause
    /// Returns the second-highest decision level (or 0 for unit clauses)
    fn compute_backtrack_level(&self, clause: &[Literal]) -> u32 {
        if clause.is_empty() || clause.len() == 1 {
            return 0;
        }

        let mut max_level = 0;
        let mut second_level = 0;

        for lit in clause {
            let level = self.levels[lit.variable().id() as usize - 1];
            if level > max_level {
                second_level = max_level;
                max_level = level;
            } else if level > second_level && level < max_level {
                second_level = level;
            }
        }

        second_level
    }

    /// Learn a cube from a partial solution state
    ///
    /// Called when all clauses are satisfied but not all variables are assigned.
    /// This means the existential player has a winning strategy for the current
    /// universal assignments. We learn a cube (conjunction) representing this.
    ///
    /// The cube blocks this universal search path - the universal player cannot
    /// make these same choices and expect to win.
    pub(super) fn learn_cube_from_solution(&mut self) -> Option<CubeResult> {
        // Find the first unassigned universal variable (if any)
        // If no unassigned universals, the existential player wins for all paths
        let has_unassigned_universal = self.decision_order.iter().any(|&var| {
            self.value(var) == Assignment::Unassigned && self.formula.is_universal(var)
        });

        if !has_unassigned_universal {
            // All universal variables are assigned, and formula is satisfied
            // This is a complete solution - SAT
            return Some(CubeResult::Solved);
        }

        // Build the cube from universal decisions on the trail
        // The cube contains the universal literals that led to this solution
        let cube: Vec<Literal> = self
            .trail
            .iter()
            .filter(|lit| self.formula.lit_is_universal(**lit))
            .copied()
            .collect();

        if cube.is_empty() {
            // No universal decisions made yet - can't learn useful cube
            return None;
        }

        // Apply existential reduction (dual of universal reduction)
        // Remove existential literals that are "outer" to the universals
        let reduced_cube = self.existential_reduce_cube(&cube);

        if reduced_cube.is_empty() {
            // Cube reduced to empty - formula is SAT
            return Some(CubeResult::Solved);
        }

        // Compute backtrack level for the cube
        // We backtrack to the second-highest level and flip the universal decision
        let backtrack_level = self.compute_cube_backtrack_level(&reduced_cube);

        // Add the cube (stored as negated literals for propagation)
        // A cube C = (l1 ∧ l2 ∧ ... ∧ ln) is blocked when any li is false
        // So we store it as blocking condition: ¬l1 ∨ ¬l2 ∨ ... ∨ ¬ln
        let negated_cube: Vec<Literal> = reduced_cube.iter().map(|l| l.negated()).collect();
        self.cubes.push(negated_cube);
        self.cube_used.push(true); // newly learned = used

        self.bump_clause_activity(&reduced_cube);
        self.var_decay_activity();

        if self.decision_level == 0 {
            // Cube learned at level 0 - all paths lead to SAT
            return Some(CubeResult::Solved);
        }

        Some(CubeResult::Learned(backtrack_level))
    }

    /// Apply existential reduction to a cube
    ///
    /// This is the dual of universal reduction:
    /// Remove existential literals whose level is >= the minimum universal level.
    /// These existential choices don't affect the universal winning strategy.
    fn existential_reduce_cube(&self, cube: &[Literal]) -> Vec<Literal> {
        // Find the minimum universal level in the cube
        let min_univ_level = cube
            .iter()
            .filter(|lit| self.formula.lit_is_universal(**lit))
            .map(|lit| self.formula.lit_level(*lit))
            .min();

        match min_univ_level {
            Some(min_level) => {
                cube.iter()
                    .filter(|lit| {
                        // Keep universal literals and existential literals with level < min_univ
                        self.formula.lit_is_universal(**lit)
                            || self.formula.lit_level(**lit) < min_level
                    })
                    .copied()
                    .collect()
            }
            None => {
                // No universal literals - keep everything
                cube.to_vec()
            }
        }
    }

    /// Compute backtrack level for a cube
    /// Similar to clause backtrack, but we want to flip a universal decision
    fn compute_cube_backtrack_level(&self, cube: &[Literal]) -> u32 {
        if cube.is_empty() || cube.len() == 1 {
            return 0;
        }

        // Find the second-highest decision level among universal variables in cube
        let mut levels: Vec<u32> = cube
            .iter()
            .filter(|lit| self.formula.lit_is_universal(**lit))
            .map(|lit| self.levels[lit.variable().id() as usize - 1])
            .collect();

        levels.sort_unstable();
        levels.dedup();

        if levels.len() < 2 {
            return levels.first().copied().unwrap_or(0).saturating_sub(1);
        }

        // Return second-highest level
        levels[levels.len() - 2]
    }
}
