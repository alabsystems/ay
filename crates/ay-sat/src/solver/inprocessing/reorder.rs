// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause-weighted variable reorder (port of Kissat `reorder.c`).
//!
//! Periodically reorder the VMTF decision queue (focused mode) or boost EVSIDS
//! scores (stable mode) based on clause-weighted variable importance. For each
//! irredundant clause, weight halves per clause size. Each variable accumulates
//! per-polarity weights from participating clauses, then combined:
//!   `score = max(pos, neg) + 2 * min(pos, neg)`
//!
//! In focused mode: rebuild VMTF queue in score order (highest at front).
//! In stable mode: add scores to EVSIDS activities (Kissat `reorder_stable`).
//!
//! Reference: Kissat `reorder.c` (218 lines). Kissat-only technique (not in CaDiCaL).

use super::super::*;

/// Maximum clause size considered for weight computation.
/// Kissat: `reordermaxsize` option (default 100). Clauses larger than this
/// are skipped to avoid O(1/2^n) underflow and to focus on structurally
/// important short clauses. AY uses 20 (2^-20 ≈ 1e-6 is effectively zero).
const REORDER_MAX_SIZE: usize = 20;

impl Solver {
    /// Reorder decision queue by clause-weighted variable importance.
    ///
    /// Port of Kissat `reorder.c`. Runs at decision level 0 after restarts.
    /// In focused mode, rebuilds the VMTF queue; in stable mode, adds weights
    /// to EVSIDS activity scores.
    ///
    /// Does NOT modify clauses — this is a pure decision heuristic adjustment.
    pub(in crate::solver) fn reorder_variables(&mut self) {
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: reorder_variables at decision level {}",
            self.decision_level,
        );

        let n = self.num_vars;
        if n == 0 {
            return;
        }

        // Phase 1: compute per-literal weights from irredundant clauses.
        // Kissat reorder.c:24-101 `compute_weights`.
        // Weight table: weight[size] = 1.0 / 2^(size-2) for size in 2..=max_size.
        // size=2 → weight=1.0, size=3 → 0.5, size=4 → 0.25, etc.
        let mut weight_table = [0.0f64; REORDER_MAX_SIZE + 1];
        {
            let mut w = 1.0f64;
            for entry in weight_table.iter_mut().take(REORDER_MAX_SIZE + 1).skip(2) {
                *entry = w;
                w /= 2.0;
            }
        }

        // Per-literal weights: index by literal index (2*var for pos, 2*var+1 for neg).
        let num_lits = n * 2;
        let mut lit_weights = vec![0.0f64; num_lits];

        // Walk ALL irredundant clauses in the arena (including binary) and
        // accumulate weights.
        //
        // NOTE: Unlike Kissat where binary clauses live only in watch lists
        // (requiring a separate walk at reorder.c:62-84), AY stores all clauses
        // including binary in the arena. The arena walk covers all clause sizes.
        //
        // Kissat reorder.c:39-59: skips satisfied clauses, counts only unassigned
        // literals for effective size. AY: at level 0, all uneliminated variables
        // are unassigned, but we check anyway for robustness.
        // Reuse persistent buffer to avoid arena-proportional allocation (#8599).
        self.cold.reduce_indices_buf.clear();
        self.cold
            .reduce_indices_buf
            .extend(self.arena.active_indices());
        for i in 0..self.cold.reduce_indices_buf.len() {
            let offset = self.cold.reduce_indices_buf[i];
            if self.arena.is_learned(offset) {
                continue;
            }
            let lits = self.arena.literals(offset);
            // Compute effective size: count of non-false literals.
            // Skip satisfied clauses (any literal true at level 0).
            let mut effective_size = 0usize;
            let mut satisfied = false;
            for &lit in lits {
                let val = self.lit_val(lit);
                if val > 0 {
                    satisfied = true;
                    break;
                }
                if val == 0 {
                    effective_size += 1;
                    if effective_size >= REORDER_MAX_SIZE {
                        break;
                    }
                }
            }
            if satisfied || effective_size < 2 {
                continue;
            }
            let size = effective_size.min(REORDER_MAX_SIZE);
            let weight = weight_table[size];
            for &lit in lits {
                let li = lit.index();
                if li < num_lits && self.lit_val(lit) == 0 {
                    lit_weights[li] += weight;
                }
            }
        }

        // Phase 2: combine per-literal weights into per-variable scores.
        // Kissat reorder.c:85-99: score = max(pos, neg) + 2 * min(pos, neg).
        let mut var_scores: Vec<(u32, f64)> = (0..n as u32)
            .map(|v| {
                let pos = lit_weights[v as usize * 2];
                let neg = lit_weights[v as usize * 2 + 1];
                let score = 2.0f64.mul_add(pos.min(neg), pos.max(neg));
                (v, score)
            })
            .collect();

        // Phase 3: apply reorder based on mode.
        if self.stable_mode {
            // Stable mode (Kissat reorder_stable): rescale then add weights to
            // EVSIDS scores. Kissat reorder.c:180: `kissat_rescale_scores(solver)`
            // normalizes activities before adding clause weights so that the small
            // weight values (0.0–1.0) are meaningful relative to activities.
            self.vsids.rescale_for_reorder();
            for &(v, weight) in &var_scores {
                if weight > 0.0 {
                    self.vsids.add_to_activity(Variable(v), weight);
                }
            }
        } else {
            // Focused mode (Kissat reorder_focused): rebuild VMTF queue by weight.
            // Sort ascending by score (ties broken by existing stamp via stable sort).
            // Kissat reorder.c:103-112 `less_focused_order`: lower weight = earlier
            // in sorted order. After move_to_front loop, highest weight at front.
            var_scores.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal));

            let sorted_vars: Vec<u32> = var_scores.iter().map(|&(v, _)| v).collect();
            self.vsids.reorder_vmtf_queue(&sorted_vars, &self.vals);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::*;

    #[test]
    fn test_reorder_variables_focused_mode() {
        // Build a small formula where variable 2 appears in many short clauses.
        // After reorder, variable 2 should be at the front of the VMTF queue.
        let mut solver = Solver::new(4);

        // Short binary clauses involving variable 2:
        // (x2 ∨ x0), (x2 ∨ x1), (x2 ∨ x3), (¬x2 ∨ x0)
        let x0p = Literal::positive(Variable(0));
        let x1p = Literal::positive(Variable(1));
        let x2p = Literal::positive(Variable(2));
        let x2n = Literal::negative(Variable(2));
        let x3p = Literal::positive(Variable(3));

        solver.add_clause_db(&[x2p, x0p], false);
        solver.add_clause_db(&[x2p, x1p], false);
        solver.add_clause_db(&[x2p, x3p], false);
        solver.add_clause_db(&[x2n, x0p], false);
        // One longer clause not involving variable 2 (lower weight):
        solver.add_clause_db(&[x0p, x1p, x3p], false);

        // Solver starts in focused mode (stable_mode = false).
        assert!(!solver.stable_mode);

        solver.reorder_variables();

        // After reorder, variable 2 should be at the front of VMTF
        // (vmtf_last = most recently bumped = first decision candidate).
        let front = solver.vsids.vmtf_last();
        assert_eq!(front, 2, "Expected variable 2 at VMTF front, got {front}");
    }

    #[test]
    fn test_reorder_variables_stable_mode() {
        let mut solver = Solver::new(3);
        let x0n = Literal::negative(Variable(0));
        let x1p = Literal::positive(Variable(1));
        let x1n = Literal::negative(Variable(1));
        let x2p = Literal::positive(Variable(2));

        // Binary clauses with variable 1 having high weight.
        solver.add_clause_db(&[x1p, x0n], false);
        solver.add_clause_db(&[x1n, x2p], false);

        // Force stable mode.
        solver.stable_mode = true;

        let activity_before = solver.vsids.activity(Variable(1));
        solver.reorder_variables();
        let activity_after = solver.vsids.activity(Variable(1));

        // Variable 1 appears in both clauses → its activity should increase.
        assert!(
            activity_after > activity_before,
            "Expected activity increase for var 1: before={activity_before}, after={activity_after}"
        );
    }

    #[test]
    fn test_reorder_variables_empty() {
        // Empty solver should not panic.
        let mut solver = Solver::new(0);
        solver.reorder_variables();
    }

    #[test]
    fn test_reorder_variables_skips_learned_clauses() {
        // Learned clauses should NOT contribute to reorder weights.
        let mut solver = Solver::new(3);
        let x0p = Literal::positive(Variable(0));
        let x1p = Literal::positive(Variable(1));
        let x2p = Literal::positive(Variable(2));

        // Only irredundant clause involves var 0.
        solver.add_clause_db(&[x0p, x1p], false);
        // Learned clauses involving var 2 — should be ignored.
        solver.add_clause_db(&[x2p, x0p], true);
        solver.add_clause_db(&[x2p, x1p], true);

        solver.reorder_variables();

        // Variable 0 (in the only irredundant clause alongside var 1) should
        // be scored equally with var 1. Variable 2 (only in learned clauses)
        // should have zero weight and not be at the VMTF front.
        let front = solver.vsids.vmtf_last();
        assert_ne!(
            front, 2,
            "Variable 2 (only in learned clauses) should not be at VMTF front"
        );
    }

    #[test]
    fn test_reorder_variables_binary_clause_weights_from_arena() {
        // Binary clauses in AY are stored in the arena (unlike Kissat where
        // they live only in watch lists). Verify that the arena walk correctly
        // weights binary clauses (size 2 → weight 1.0, the highest weight).
        //
        // Setup: variable 1 appears in 3 binary clauses, variable 2 in 1.
        // After reorder (stable mode), variable 1's activity should increase
        // more than variable 2's.
        let mut solver = Solver::new(4);
        let x0p = Literal::positive(Variable(0));
        let x1p = Literal::positive(Variable(1));
        let x1n = Literal::negative(Variable(1));
        let x2p = Literal::positive(Variable(2));
        let x3p = Literal::positive(Variable(3));

        // Binary clauses (stored in both arena and watch lists):
        // Var 1 appears in 3 binary clauses (highest weight class):
        solver.add_clause_db(&[x1p, x0p], false); // (x1, x0)
        solver.add_clause_db(&[x1n, x2p], false); // (~x1, x2)
        solver.add_clause_db(&[x1p, x3p], false); // (x1, x3)

        solver.stable_mode = true;
        let activity_v1_before = solver.vsids.activity(Variable(1));
        let activity_v2_before = solver.vsids.activity(Variable(2));

        solver.reorder_variables();

        let activity_v1_after = solver.vsids.activity(Variable(1));
        let activity_v2_after = solver.vsids.activity(Variable(2));

        let v1_delta = activity_v1_after - activity_v1_before;
        let v2_delta = activity_v2_after - activity_v2_before;

        // Variable 1 (3 binary clause occurrences) should have a larger
        // activity increase than variable 2 (1 binary clause occurrence).
        assert!(
            v1_delta > v2_delta,
            "Variable 1 (3 binary clauses) should get more weight than var 2 (1 binary clause): \
             v1_delta={v1_delta}, v2_delta={v2_delta}"
        );

        // Variable 1 should have nonzero activity increase.
        assert!(
            v1_delta > 0.0,
            "Variable 1 should have nonzero activity increase from binary clause weights: \
             v1_delta={v1_delta}"
        );
    }

    #[test]
    fn test_reorder_stable_mode_rescale() {
        // Verify that rescale_for_reorder normalizes activities before adding
        // clause weights (Kissat reorder.c:180). Without rescaling, adding
        // small weights (0-1) to large activities (1e98) is a no-op.
        let mut solver = Solver::new(3);
        let x0p = Literal::positive(Variable(0));
        let x1p = Literal::positive(Variable(1));
        let _x2p = Literal::positive(Variable(2));

        // One binary clause involving var 1.
        solver.add_clause_db(&[x1p, x0p], false);

        solver.stable_mode = true;

        // Inflate activities to a large value to simulate long search.
        for v in 0..3 {
            solver.vsids.add_to_activity(Variable(v as u32), 1e80);
        }

        let _activity_v1_before = solver.vsids.activity(Variable(1));
        let _activity_v2_before = solver.vsids.activity(Variable(2));

        solver.reorder_variables();

        let activity_v1_after = solver.vsids.activity(Variable(1));
        let activity_v2_after = solver.vsids.activity(Variable(2));

        // After rescale + reorder, var 1 (in binary clause) should have
        // higher activity than var 2 (not in any clause).
        // Without rescale, the weight addition would be lost to fp precision.
        assert!(
            activity_v1_after > activity_v2_after,
            "After rescale, var 1 (in binary clause) should have higher activity than var 2: \
             v1={activity_v1_after}, v2={activity_v2_after}"
        );
    }

    #[test]
    fn test_should_reorder_allows_focused_mode_only_for_small_dense() {
        // Focused-mode reorder remains suppressed for normal formulas, but
        // small-dense Main-track formulas use the existing VMTF reorder path.
        let mut solver = Solver::new(4);
        let x0p = Literal::positive(Variable(0));
        let x1p = Literal::positive(Variable(1));
        solver.add_clause_db(&[x0p, x1p], false);

        solver.set_reorder_enabled(true);
        // Force the scheduling interval to 0 so the technique is "due".
        solver.inproc_ctrl.reorder.reset_interval(0);

        // In focused mode (default), a normal-density formula must not reorder.
        assert!(!solver.stable_mode, "solver starts in focused mode");
        assert!(
            !solver.should_reorder(),
            "normal-density focused mode should keep reorder suppressed"
        );

        // Small-dense Main formulas may run focused VMTF reorder. The
        // predicate excludes IC3 internally, matching learned-reduction policy.
        solver.num_original_clauses = solver.num_vars.max(1) * 10 + 1;
        assert!(
            solver.should_reorder(),
            "small-dense focused mode should allow proof-safe reorder"
        );

        solver.cold.ic3_mode = true;
        assert!(
            !solver.should_reorder(),
            "small-dense focused reorder must stay disabled for IC3"
        );
        solver.cold.ic3_mode = false;

        // Stable mode remains allowed regardless of the small-dense gate.
        solver.num_original_clauses = 1;
        solver.stable_mode = true;
        assert!(
            solver.should_reorder(),
            "should_reorder() must be true in stable mode when interval has elapsed"
        );
    }
}
