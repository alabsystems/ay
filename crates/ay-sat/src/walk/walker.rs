// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Walker state for local search with O(1) amortized operations.
//!
//! Matches CaDiCaL `walk_full_occs.cpp` architecture: full occurrence lists
//! with per-clause satisfaction counters and lazy best-model tracking via
//! a flips trail.

use super::{fit_cb_value, Random};

/// Walker state for local search with O(1) amortized operations.
///
/// Matches CaDiCaL `walk_full_occs.cpp` architecture: full occurrence lists
/// with per-clause satisfaction counters and lazy best-model tracking via
/// a flips trail.
pub(super) struct Walker {
    pub(super) random: Random,
    pub(super) values: Vec<bool>, // current assignment (true = positive)
    pub(super) occurs: Vec<Vec<usize>>, // per-literal → clause indices
    pub(super) sat_count: Vec<u32>, // per-clause satisfied literal count
    pub(super) broken: Vec<usize>, // indices of unsatisfied clauses
    pub(super) broken_pos: Vec<i32>, // clause → position in broken (-1 if not)
    score_table: Vec<f64>,        // precomputed ProbSAT scores by break-count
    epsilon: f64,                 // smallest score (fallback)
    pub(super) scores_buf: Vec<f64>, // reusable scoring buffer

    // Lazy best-model tracking (CaDiCaL walk.cpp flips trail).
    pub(super) best_values: Vec<bool>, // best assignment found so far
    pub(super) flips_trail: Vec<usize>, // trail of flipped variable indices
    pub(super) best_trail_pos: i32,    // position in flips_trail of best model
    trail_limit: usize,                // max trail length before forced flush

    pub(super) minimum: usize, // minimum broken count seen
    pub(super) ticks: u64,     // effort counter
    pub(super) limit: u64,     // tick limit
}

impl Walker {
    /// Create new walker for n variables with given tick limit.
    pub(super) fn new(num_vars: usize, num_clauses: usize, seed: u64, limit: u64) -> Self {
        Self {
            random: Random::new(seed),
            values: vec![false; num_vars],
            occurs: vec![Vec::new(); 2 * num_vars],
            sat_count: vec![0; num_clauses],
            broken: Vec::new(),
            broken_pos: vec![-1; num_clauses],
            score_table: Vec::new(),
            epsilon: 0.0,
            scores_buf: Vec::with_capacity(16), // typical clause size

            best_values: vec![false; num_vars],
            flips_trail: Vec::with_capacity(num_vars / 4 + 1),
            best_trail_pos: -1,
            trail_limit: num_vars / 4 + 1,

            minimum: usize::MAX,
            ticks: 0,
            limit,
        }
    }

    /// Populate score table based on average clause size.
    #[allow(clippy::while_float)] // Exponential decay loop; terminates once score underflows
    pub(super) fn populate_table(&mut self, avg_size: f64, walk_count: u64) {
        // Alternate between size-based CB and default CB=2.0.
        // Kissat walk.c:167: `(GET(walks) & 1) ? fit_cbval(size) : 2.0`
        // Odd walks use size-based CB, even walks use CB=2.0.
        let use_size_based = (walk_count & 1) != 0;
        let cb = if use_size_based {
            fit_cb_value(avg_size)
        } else {
            2.0
        };
        let base = 1.0 / cb;

        self.score_table.clear();
        // score[i] = base^i, so score[0] = 1.0, score[1] = base, etc.
        // Higher break count = lower score (exponential decay)
        let mut score = 1.0;
        while score > 1e-300 {
            self.score_table.push(score);
            score *= base;
        }
        self.epsilon = score.max(1e-300);
    }

    /// Get score for a given break count.
    #[inline]
    pub(super) fn score(&self, break_count: usize) -> f64 {
        if break_count < self.score_table.len() {
            self.score_table[break_count]
        } else {
            self.epsilon
        }
    }

    /// Add clause to broken list.
    #[inline]
    pub(super) fn add_broken(&mut self, clause_idx: usize) {
        if self.broken_pos[clause_idx] < 0 {
            self.broken_pos[clause_idx] = self.broken.len() as i32;
            self.broken.push(clause_idx);
        }
    }

    /// Compute break-value for flipping a variable: how many currently satisfied
    /// clauses would become unsatisfied if we flip this variable.
    /// O(degree) - only scans clauses containing the variable.
    ///
    /// Reference: CaDiCaL `walk_full_occs.cpp:walk_full_occs_break_value()` —
    /// scans occurrence list, checks `count == 1` for single-satisfier detection.
    #[inline]
    pub(super) fn compute_break_value(&self, var_idx: usize) -> usize {
        let current_val = self.values[var_idx];
        // The literal that is currently TRUE and would become FALSE
        let true_lit_idx = if current_val {
            2 * var_idx
        } else {
            2 * var_idx + 1
        };

        let occurs = &self.occurs[true_lit_idx];
        let mut break_count = 0;
        for &clause_idx in occurs {
            // If this clause has exactly 1 satisfier, flipping would break it
            if self.sat_count[clause_idx] == 1 {
                break_count += 1;
            }
        }

        break_count
    }

    /// Flip a variable and incrementally update broken list.
    /// O(degree) - only updates affected clauses.
    ///
    /// Reference: CaDiCaL `walk_full_occs.cpp:walk_full_occs_flip_lit()` —
    /// make_clauses (increment count, remove from broken) then break_clauses
    /// (decrement count, add to broken).
    pub(super) fn flip(&mut self, var_idx: usize) {
        debug_assert!(
            var_idx < self.values.len(),
            "BUG: flip var {var_idx} out of bounds"
        );
        let old_val = self.values[var_idx];
        self.values[var_idx] = !old_val;

        // The literal that was TRUE and is now FALSE
        let was_true_idx = if old_val {
            2 * var_idx
        } else {
            2 * var_idx + 1
        };
        // The literal that was FALSE and is now TRUE
        let now_true_idx = if old_val {
            2 * var_idx + 1
        } else {
            2 * var_idx
        };

        // Make phase: clauses containing the now-TRUE literal gain a satisfier.
        // Reference: CaDiCaL walk_full_occs.cpp:make_clauses_along_occurrences()
        let now_true_len = self.occurs[now_true_idx].len();
        self.ticks += 1 + (now_true_len as u64 / 8); // cache line estimate
        for i in 0..now_true_len {
            let clause_idx = self.occurs[now_true_idx][i];
            if self.sat_count[clause_idx] == 0 {
                // Was broken, now satisfied — remove from broken list
                let pos = self.broken_pos[clause_idx];
                if pos >= 0 {
                    let pos = pos as usize;
                    let last = self.broken.len() - 1;
                    if pos != last {
                        let last_clause = self.broken[last];
                        self.broken[pos] = last_clause;
                        self.broken_pos[last_clause] = pos as i32;
                    }
                    self.broken.pop();
                    self.broken_pos[clause_idx] = -1;
                }
                self.ticks += 1;
            }
            self.sat_count[clause_idx] += 1;
        }

        // Break phase: clauses containing the now-FALSE literal lose a satisfier.
        // Reference: CaDiCaL walk_full_occs.cpp:break_clauses()
        let was_true_len = self.occurs[was_true_idx].len();
        self.ticks += 1 + (was_true_len as u64 / 8); // cache line estimate
        for i in 0..was_true_len {
            let clause_idx = self.occurs[was_true_idx][i];
            self.sat_count[clause_idx] -= 1;
            if self.sat_count[clause_idx] == 0 {
                // Now broken — add to broken list
                if self.broken_pos[clause_idx] < 0 {
                    self.broken_pos[clause_idx] = self.broken.len() as i32;
                    self.broken.push(clause_idx);
                }
                self.ticks += 1;
            }
        }
    }

    /// Record a flip on the trail for lazy best-model tracking.
    /// Reference: CaDiCaL `walk.cpp:push_flipped()`.
    pub(super) fn push_flipped(&mut self, var_idx: usize) {
        if self.best_trail_pos < 0 {
            return; // trail invalidated
        }

        if self.flips_trail.len() < self.trail_limit {
            self.flips_trail.push(var_idx);
            return;
        }

        // Trail reached limit — flush best portion
        if self.best_trail_pos > 0 {
            self.save_trail_prefix(true);
            self.flips_trail.push(var_idx);
        } else {
            // No best position set, invalidate trail
            self.flips_trail.clear();
            self.best_trail_pos = -1;
        }
    }

    /// Save the flips from 0..best_trail_pos into best_values, then
    /// optionally shift remaining flips to the front.
    /// Reference: CaDiCaL `walk.cpp:save_walker_trail()`.
    fn save_trail_prefix(&mut self, keep_remaining: bool) {
        debug_assert!(self.best_trail_pos >= 0);
        let best_pos = self.best_trail_pos as usize;
        debug_assert!(best_pos <= self.flips_trail.len());

        // Apply flips [0..best_pos) to best_values
        for &var_idx in &self.flips_trail[..best_pos] {
            self.best_values[var_idx] = !self.best_values[var_idx];
        }

        if !keep_remaining {
            return;
        }

        // Shift remaining flips to the front
        let remaining = self.flips_trail.len() - best_pos;
        self.flips_trail.copy_within(best_pos.., 0);
        self.flips_trail.truncate(remaining);
        self.best_trail_pos = 0;
    }

    /// Save the final minimum when walk completes.
    /// Reference: CaDiCaL `walk.cpp:save_final_minimum()`.
    pub(super) fn save_final_minimum(&mut self) {
        if self.best_trail_pos == -1 || self.best_trail_pos == 0 {
            // Already saved or invalidated
        } else {
            self.save_trail_prefix(false);
        }
    }

    /// Record a new minimum — mark the current trail position as best.
    /// Reference: CaDiCaL `walk.cpp:walk_save_minimum()`.
    pub(super) fn save_minimum(&mut self, num_vars: usize) {
        self.minimum = self.broken.len();

        if self.best_trail_pos == -1 {
            // No trail — copy the full model
            self.best_values[..num_vars].copy_from_slice(&self.values[..num_vars]);
            self.best_trail_pos = 0;
        } else {
            // Mark current trail position as best
            self.best_trail_pos = self.flips_trail.len() as i32;
        }
    }
}
