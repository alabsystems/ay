// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl QbfSolver {
    /// Store a learned clause and set up its watches.
    pub(super) fn add_learned_clause(&mut self, clause: Vec<Literal>) {
        if !clause.is_empty() {
            self.learned.push(clause);
            self.clause_used.push(true);
            let idx = self.learned.len() - 1;
            self.add_learned_watches(idx);
        }
    }

    /// Mark a learned clause as recently used (protects from deletion).
    #[inline]
    pub(super) fn mark_clause_used(&mut self, learned_idx: usize) {
        if learned_idx < self.clause_used.len() {
            self.clause_used[learned_idx] = true;
        }
    }

    /// Run clause/cube reduction if the conflict threshold has been reached.
    pub(super) fn maybe_reduce_db(&mut self) {
        if self.conflicts >= self.next_reduce {
            self.reduce_learned_clauses();
            self.reduce_cubes();
            self.next_reduce = self.conflicts + REDUCE_DB_INC;
            self.reductions += 1;
        }
    }

    /// Collect the set of learned clause indices currently used as reasons
    /// for assigned variables on the trail.
    fn reason_clause_indices(&self) -> HashSet<usize> {
        let num_original = self.formula.clauses().len();
        let mut reason_set = HashSet::new();
        for &reason in &self.reasons {
            if let Reason::Propagated(idx) = reason {
                if idx >= num_original {
                    reason_set.insert(idx - num_original);
                }
            }
        }
        reason_set
    }

    /// Reduce the learned clause database.
    ///
    /// Deletes unused, long learned clauses. Short clauses (len <= 3) and
    /// reason clauses are protected. Deleted clauses are set to empty;
    /// stale watch entries are cleaned up lazily during propagation.
    fn reduce_learned_clauses(&mut self) {
        let reason_set = self.reason_clause_indices();

        // Collect candidate indices for deletion: not a reason, not short, not recently used
        let mut candidates: Vec<usize> = (0..self.learned.len())
            .filter(|&i| {
                let clause = &self.learned[i];
                !clause.is_empty()
                    && clause.len() > REDUCE_PROTECT_LEN
                    && !reason_set.contains(&i)
                    && !self.clause_used[i]
            })
            .collect();

        // Sort by clause length descending (delete longest first)
        candidates.sort_by(|&a, &b| self.learned[b].len().cmp(&self.learned[a].len()));

        // Delete the top half of candidates
        let num_to_delete = candidates.len() / 2;
        for &idx in candidates.iter().take(num_to_delete) {
            self.learned[idx].clear();
            self.clauses_deleted += 1;
        }

        // Reset all used flags
        self.clause_used.fill(false);
    }

    /// Reduce the learned cube database.
    ///
    /// Same strategy as clause reduction: delete unused long cubes.
    fn reduce_cubes(&mut self) {
        // Cubes used as reasons for CubePropagated assignments are protected
        let mut cube_reason_set = HashSet::new();
        for &reason in &self.reasons {
            if let Reason::CubePropagated(idx) = reason {
                cube_reason_set.insert(idx);
            }
        }

        let mut candidates: Vec<usize> = (0..self.cubes.len())
            .filter(|&i| {
                let cube = &self.cubes[i];
                !cube.is_empty()
                    && cube.len() > REDUCE_PROTECT_LEN
                    && !cube_reason_set.contains(&i)
                    && !self.cube_used[i]
            })
            .collect();

        candidates.sort_by(|&a, &b| self.cubes[b].len().cmp(&self.cubes[a].len()));

        let num_to_delete = candidates.len() / 2;
        for &idx in candidates.iter().take(num_to_delete) {
            self.cubes[idx].clear();
            self.cubes_deleted += 1;
        }

        // Reset all used flags
        self.cube_used.fill(false);
    }
}
