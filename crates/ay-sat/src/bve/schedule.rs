// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BVE scheduling, growth bounds, and elimination loop drivers.
//!
//! Extracted from eliminate.rs for code-health (500-line limit).
//! Contains: next_candidate, mark_failed, growth_bound management,
//! resolvent_budget, and the test-only run_elimination drivers.

use crate::clause_arena::ClauseArena;
use crate::literal::Literal;
use crate::literal::Variable;

#[cfg(test)]
use super::EliminationResult;
use super::{BVE, BVE_GROWTH_BOUND_MAX};

impl BVE {
    /// Mark all active variables as dirty elimination candidates.
    pub(crate) fn mark_all_candidates_dirty(&mut self) {
        for (var_idx, dirty) in self.candidate_dirty.iter_mut().enumerate() {
            *dirty = !self.eliminated[var_idx];
        }
    }

    /// Mark the variables in one irredundant clause as dirty BVE candidates.
    pub(crate) fn mark_candidates_dirty_clause(&mut self, literals: &[Literal]) {
        for &lit in literals {
            let var_idx = lit.variable().index();
            if var_idx < self.candidate_dirty.len() && !self.eliminated[var_idx] {
                self.candidate_dirty[var_idx] = true;
            }
        }
    }

    /// Returns whether an inprocessing BVE round has pending dirty candidates.
    pub(crate) fn has_dirty_candidates(&self) -> bool {
        self.candidate_dirty.iter().any(|&dirty| dirty)
    }

    /// Pop the next valid elimination candidate from the schedule.
    ///
    /// Returns `Some(var)` if a candidate is available, `None` if the schedule is
    /// exhausted. The caller can then query occurrence lists via `get_occs()` for
    /// gate detection before calling `try_eliminate_with_gate()`.
    ///
    /// With the ElimHeap, variables are dynamically re-inserted when clauses are
    /// removed (via `update_schedule_after_clause_removal`), so failed variables
    /// stay out unless clause removals push them back in with a new score.
    /// The `schedule_built` flag prevents infinite re-builds when the heap
    /// drains without successful eliminations (#3506).
    pub(crate) fn next_candidate(
        &mut self,
        _clauses: &ClauseArena,
        vals: &[i8],
        frozen: &[u32],
    ) -> Option<Variable> {
        // Lazy build: populate the heap on first call after rebuild().
        // Only build once per round — after the heap is drained, re-insertion
        // only happens via update_schedule_after_clause_removal.
        if self.schedule.is_empty() && !self.schedule_built {
            self.build_schedule(vals, frozen);
            self.schedule_built = true;
            if self.schedule.is_empty() {
                return None;
            }
        }

        loop {
            let var = self
                .schedule
                .pop(&self.occ, &self.schedule_gate_pair_credit)?;
            let var_idx = var.index();
            if var_idx < self.candidate_dirty.len() {
                self.candidate_dirty[var_idx] = false;
            }

            if self
                .candidate_occurrence_counts(var_idx, vals, frozen)
                .is_none()
            {
                continue;
            }

            debug_assert!(
                var_idx >= frozen.len() || frozen[var_idx] == 0,
                "BUG: next_candidate selected frozen variable {var:?}"
            );
            return Some(var);
        }
    }

    /// Record a failed elimination attempt.
    ///
    /// CaDiCaL does nothing on failure (elim.cpp:725-727). With the ElimHeap,
    /// the variable has already been popped and stays out of the heap unless
    /// a subsequent clause removal re-inserts it via `push_or_update`. This
    /// naturally prevents infinite loops without needing the old
    /// `schedule_exhausted` guard (#3506).
    pub(crate) fn mark_failed(&mut self, _var: Variable) {
        // No-op: variable was already popped from the heap.
    }

    /// Get the current adaptive growth bound.
    ///
    /// Used by the factoring engine to match CaDiCaL's `bound = lim.elimbound`
    /// guard (factor.cpp:118, :888): factoring only fires when clause reduction
    /// exceeds the current elimination bound, ensuring BVE can never profitably
    /// undo the factoring.
    pub(crate) fn growth_bound(&self) -> usize {
        self.growth_bound
    }

    /// Increment the adaptive growth bound after a successful BVE phase.
    ///
    /// CaDiCaL elim.cpp:968-971 transitions 0 -> 1 and then doubles via
    /// `lim.elimbound *= 2`. The bound starts at 0 (CaDiCaL `elimboundmin`)
    /// and then grows as 0, 1, 2, 4, 8, 16.
    ///
    /// When transitioning from fastelim (preprocessing) to additive mode
    /// (inprocessing), the growth bound is RESET to 0. CaDiCaL uses separate
    /// `fastelimbound` (preprocessing, typically 8) and `elimbound` (inprocessing,
    /// starts at 0) fields. AY conflates them into one `growth_bound` field with
    /// `fastelim_mode` selecting semantics. Without the reset, preprocessing's
    /// bound (8) leaks into inprocessing's additive formula, allowing up to
    /// `clauses_removed + 16` resolvents on the first inprocessing call — far
    /// too loose for high-degree formulas like clique graphs (#7178).
    ///
    /// ENSURES: growth_bound <= BVE_GROWTH_BOUND_MAX
    pub(crate) fn increment_growth_bound(&mut self) {
        if self.fastelim_mode {
            // Transitioning from preprocessing to inprocessing.
            // Reset to inprocessing starting bound (CaDiCaL: elimboundmin=0).
            self.fastelim_mode = false;
            self.growth_bound = 0;
            self.mark_all_candidates_dirty();
            return;
        }

        if self.growth_bound >= BVE_GROWTH_BOUND_MAX {
            return;
        }
        // CaDiCaL elim.cpp: exponential doubling.
        // Sequence: 0 -> 1 -> 2 -> 4 -> 8 -> 16.
        if self.growth_bound == 0 {
            self.growth_bound = 1;
        } else {
            self.growth_bound = (self.growth_bound * 2).min(BVE_GROWTH_BOUND_MAX);
        }

        debug_assert!(
            self.growth_bound <= BVE_GROWTH_BOUND_MAX,
            "BUG: growth_bound {} exceeds max {}",
            self.growth_bound,
            BVE_GROWTH_BOUND_MAX
        );
        self.mark_all_candidates_dirty();
    }

    /// Compute the maximum allowed resolvent count for an elimination.
    ///
    /// CaDiCaL fastelim (elimfast.cpp:71-88):
    ///   `bound = min(fastelimbound, pos + neg)`
    ///   `resolvents <= bound`
    /// This caps resolvents at fastelimbound (default 8), even when
    /// pos+neg is larger. Variables with many occurrences produce
    /// at most 8 resolvents, preventing clause database bloat during
    /// preprocessing. Ref: elimfast.cpp lines 71-88, 118.
    ///
    /// CaDiCaL inprocessing (elim.cpp:480-517): resolvents <= pos_count +
    /// neg_count + adaptive_bound (`elimboundmin` growing with rounds).
    ///
    /// - preprocessing fastelim: min(clauses_removed, growth_bound)
    /// - inprocessing elimination: clauses_removed + growth_bound
    ///
    /// Lever `AY_AB_BVE_ADDITIVE_FASTELIM` (wf_eab7d219, banded wf_e2bdf6e1):
    /// when armed, the Pass-1 fastelim budget (`fastelim_mode && !quick_elim_mode`)
    /// adopts kissat's ADDITIVE `clauses_removed + growth_bound`
    /// (resolve.c:283-294) instead of CaDiCaL's no-growth `min`. The no-growth
    /// cap rejects EVERY variable whose elimination grows the clause DB at all
    /// (resolvents > removed); post-fast-inner-fix each elimination is ~30x
    /// cheaper, so the cap is now the binding constraint of the d0298807-class
    /// coverage gap (measured 3,165 -> 24,898 eliminated, 84% of kissat).
    /// Pass-0 quick (`quick_elim_mode`) stays no-growth so the free-elimination
    /// pre-pass is unaffected. Default: BAND-GATED — active iff
    /// `num_vars > AY_BVE_ADDITIVE_MIN_VARS` (200K); see
    /// `additive_fastelim_default` / `additive_fastelim_override`.
    pub(crate) fn resolvent_budget(&self, clauses_removed: usize) -> usize {
        if self.fastelim_mode {
            if self.additive_fastelim && !self.quick_elim_mode {
                // Kissat additive budget for Pass-1 fastelim (lever ON).
                clauses_removed + self.growth_bound
            } else {
                // CaDiCaL fastelim: bound = min(fastelimbound, pos+neg).
                // Caps resolvents at fastelimbound (typically 8) to prevent
                // clause bloat on high-occurrence variables (#6926).
                clauses_removed.min(self.growth_bound)
            }
        } else {
            clauses_removed + self.growth_bound
        }
    }

    /// Set the growth bound directly (for preprocessing).
    ///
    /// CaDiCaL's preprocessing uses `fastelimbound = 8`
    /// (`options.hpp:128`), which is more permissive than the default
    /// inprocessing bound of 0.
    pub(crate) fn set_growth_bound(&mut self, bound: usize) {
        self.growth_bound = bound.min(BVE_GROWTH_BOUND_MAX);
        self.fastelim_mode = true;
        self.mark_all_candidates_dirty();
        debug_assert!(
            self.growth_bound <= BVE_GROWTH_BOUND_MAX,
            "BUG: growth_bound {} > max {} after set",
            self.growth_bound,
            BVE_GROWTH_BOUND_MAX,
        );
    }

    /// Restore a caller's BVE budget mode after a bounded private route.
    pub(crate) fn restore_budget_mode(
        &mut self,
        growth_bound: usize,
        fastelim_mode: bool,
        quick_elim_mode: bool,
    ) {
        self.growth_bound = growth_bound.min(BVE_GROWTH_BOUND_MAX);
        self.fastelim_mode = fastelim_mode;
        self.quick_elim_mode = quick_elim_mode;
        self.mark_all_candidates_dirty();
        debug_assert!(
            self.growth_bound <= BVE_GROWTH_BOUND_MAX,
            "BUG: growth_bound {} > max {} after restore",
            self.growth_bound,
            BVE_GROWTH_BOUND_MAX,
        );
    }

    /// Reset the growth bound to 0 after preprocessing.
    ///
    /// CaDiCaL keeps `fastelimbound` (default 8, options.hpp:128) and
    /// `elimbound` (starts at elimboundmin=0, options.hpp:88) as separate
    /// values. AY uses a single `growth_bound` field. Without this reset,
    /// preprocessing's fastelim bound=8 leaks into `increment_growth_bound()`
    /// which doubles it to 16 (BVE_GROWTH_BOUND_MAX), making the first
    /// inprocessing BVE round allow pos+neg+16 resolvents per elimination.
    /// This causes massive clause explosion on structured formulas (#7178).
    pub(crate) fn reset_growth_bound_for_inprocessing(&mut self) {
        self.growth_bound = 0;
        self.fastelim_mode = false;
    }

    /// Run BVE elimination loop on an isolated `BVE` + `ClauseArena`.
    ///
    /// This is a self-contained elimination driver without solver-level state
    /// (watches, trail, reconstruction stack). Production uses `Solver::bve()`
    /// which orchestrates BVE through the full solver state machine.
    ///
    /// The `frozen` slice contains reference counts - a variable is frozen if its count > 0.
    #[cfg(test)]
    pub(crate) fn run_elimination(
        &mut self,
        clauses: &mut ClauseArena,
        vals: &[i8],
        frozen: &[u32],
        max_eliminations: usize,
    ) -> Vec<EliminationResult> {
        self.run_elimination_with_gate_provider(
            clauses,
            vals,
            frozen,
            max_eliminations,
            |_var, _pos_occs, _neg_occs, _clauses| None,
        )
    }

    /// Run BVE elimination loop with optional gate detection.
    ///
    /// Self-contained driver without solver state. Production uses
    /// `Solver::bve_body()` which adds effort limits, LRAT proof chains,
    /// reconstruction stack, backward subsumption cascades, and inter-round GC.
    ///
    /// REQUIRES: occurrence lists are up-to-date (rebuild() called before first use)
    /// ENSURES: all eliminated variables are marked in self.eliminated,
    ///          results.len() <= max_eliminations,
    ///          no variable is eliminated more than once,
    ///          no frozen variable is eliminated
    #[cfg(test)]
    pub(crate) fn run_elimination_with_gate_provider<F>(
        &mut self,
        clauses: &mut ClauseArena,
        vals: &[i8],
        frozen: &[u32],
        max_eliminations: usize,
        mut gate_provider: F,
    ) -> Vec<EliminationResult>
    where
        F: FnMut(Variable, &[usize], &[usize], &ClauseArena) -> Option<Vec<usize>>,
    {
        self.stats.rounds += 1;
        let mut results = Vec::new();
        let mut eliminations = 0;

        while eliminations < max_eliminations {
            // Find a candidate variable
            let Some(var) = self.next_candidate(clauses, vals, frozen) else {
                break;
            };

            let pos_lit = Literal::positive(var);
            let neg_lit = Literal::negative(var);
            // Pass occurrence slices directly to avoid allocation;
            // gate_provider only reads them
            let gate_defining =
                gate_provider(var, self.occ.get(pos_lit), self.occ.get(neg_lit), clauses);

            // Try to eliminate it
            let result =
                self.try_eliminate_with_gate(var, clauses, gate_defining.as_deref(), false);

            if result.eliminated {
                eliminations += 1;

                // Update occurrence lists for deleted clauses
                self.update_occs_after_elimination(&result.to_delete, clauses);
                // Delete clauses from the arena so subsequent eliminations don't
                // see clauses containing the just-eliminated variable (#7004).
                for &idx in &result.to_delete {
                    clauses.delete(idx);
                }

                results.push(result);
            } else {
                // Failed variables are not blacklisted and can be retried after
                // subsequent eliminations alter occurrence counts.
                self.mark_failed(var);
            }
        }

        // Post-condition: result count bounded by max_eliminations.
        debug_assert!(
            results.len() <= max_eliminations,
            "BUG: eliminated {} variables but max was {}",
            results.len(),
            max_eliminations
        );
        // Post-condition: no variable eliminated twice.
        debug_assert!(
            {
                let mut seen = crate::kani_compat::DetHashSet::default();
                results
                    .iter()
                    .filter(|r| r.eliminated)
                    .all(|r| seen.insert(r.variable))
            },
            "BUG: a variable was eliminated more than once in a single round"
        );
        // Post-condition: no frozen variable was eliminated.
        debug_assert!(
            results.iter().filter(|r| r.eliminated).all(|r| {
                let vi = r.variable.index();
                vi >= frozen.len() || frozen[vi] == 0
            }),
            "BUG: frozen variable was eliminated"
        );

        results
    }
}
