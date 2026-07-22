// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lookahead and cube generation for cube-and-conquer parallel solving.
//!
//! Implements the CaDiCaL-style lookahead algorithm:
//! - For each unassigned variable, probe both polarities
//! - Count propagation trail sizes to score variable "informativeness"
//! - Detect failed literals (backbone) as a side effect
//! - Return the best splitting variable for decision or cube generation
//!
//! Cube generation iteratively applies lookahead at increasing depth,
//! splitting the search space into non-overlapping cubes suitable for
//! parallel solving (cube-and-conquer).
//!
//! ## References
//!
//! - CaDiCaL `lookahead.cpp` (Biere et al.)
//! - Heule & van Maaren, "Look-Ahead Based SAT Solvers" (2009)
//! - Heule et al., "Cube and Conquer: Guiding CDCL SAT Solvers by Lookaheads" (2012)

use super::*;

/// Statistics for lookahead operations.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct LookaheadStats {
    /// Total probe attempts (one per literal per round).
    pub probes: u64,
    /// Failed literals discovered (one polarity leads to immediate conflict).
    pub failed: u64,
    /// Lookahead rounds completed.
    pub rounds: u64,
}

/// Result of probing a single literal: either a propagation count or
/// a failed-literal indication.
enum ProbeResult {
    /// Successful propagation; value is trail length after propagation.
    PropCount(usize),
    /// The literal is a failed literal (conflict under this polarity).
    Failed,
}

impl Solver {
    /// Perform lookahead to find the best decision literal for splitting.
    ///
    /// Probes every unassigned, non-eliminated variable in both polarities,
    /// scoring each by the product of positive and negative propagation counts
    /// (the standard balanced heuristic from Heule & van Maaren 2009).
    ///
    /// Failed literals are detected as a side effect: when one polarity leads
    /// to an immediate conflict, the negation is forced as a level-0 unit.
    ///
    /// Returns `Some(literal)` with the best splitting literal, or `None` if
    /// all variables are assigned or the formula is determined to be UNSAT.
    ///
    /// REQUIRES: `decision_level == 0`
    /// ENSURES: `decision_level == 0` on return
    ///
    /// Reference: CaDiCaL `lookahead_probing()` in `lookahead.cpp:286-402`.
    pub fn lookahead(&mut self) -> Option<Literal> {
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: lookahead() called at decision_level {}",
            self.decision_level
        );

        if self.has_empty_clause {
            return None;
        }

        // Propagate any pending level-0 units before probing.
        if self.search_propagate().is_some() {
            // Conflict at level 0 — formula is UNSAT.
            return None;
        }

        let mut base_trail_len = self.trail.len();
        let mut best_score: u64 = 0;
        let mut best_literal: Option<Literal> = None;

        // When LRAT/DRAT proof generation is enabled, we cannot use the
        // bare `enqueue(lit, None)` path for failed-literal forcing because
        // it emits no proof line, sets no `unit_proof_id`, and does not mark
        // the variable as fixed in `var_lifecycle`. The proper fix would be
        // to collect LRAT hints from the conflict and call
        // `learn_derived_unit`, but that is complex. Instead, we simply skip
        // the failed-literal optimisation when proofs are active. The unit
        // will be discovered later by normal probing or search. Lookahead is
        // a heuristic — skipping this optimisation does not affect
        // correctness.
        let proof_active = self.proof_manager.is_some();

        // Effort budget (#8322): bound lookahead propagations per round.
        // Without a budget, probing all ~35K variables on FmlaEquivChain
        // costs 3+ seconds per round, dominating total solve time (~12s of
        // 21s). The propagation budget keeps each round under ~500ms while
        // still scanning enough variables for a meaningful splitting decision.
        let props_start = self.num_propagations;
        let prop_budget = LOOKAHEAD_MAX_PROPAGATIONS;
        let wall_start = ay_core::time::Instant::now();

        for var_idx in 0..self.num_vars {
            if self.is_interrupted() {
                break;
            }
            // Propagation budget check: stop probing when budget is exhausted.
            // Check every 64 variables to amortize the overhead of
            // num_propagations reads.
            if var_idx & 63 == 0 {
                let props_used = self.num_propagations.saturating_sub(props_start);
                if props_used >= prop_budget {
                    break;
                }
            }
            // (#8448) Wall-clock check every 4 variables. Each probe pair
            // costs milliseconds on large formulas, and on ecarev-110
            // (127K vars) the previous 8-variable granularity allowed
            // rounds to exceed 5s despite a 500ms wall limit. 4-variable
            // granularity catches these cases with minimal overhead
            // (~0.1us per Instant::now()).
            if var_idx & 3 == 0
                && wall_start.elapsed().as_millis() as u64 >= LOOKAHEAD_WALL_LIMIT_MS
            {
                break;
            }
            if self.var_is_assigned(var_idx) || self.var_lifecycle.is_removed(var_idx) {
                continue;
            }

            let var = Variable(var_idx as u32);
            let pos_lit = Literal::positive(var);
            let neg_lit = Literal::negative(var);

            // Probe positive polarity.
            let pos_result = self.lookahead_probe(pos_lit, base_trail_len);
            match pos_result {
                ProbeResult::Failed => {
                    // pos_lit is a failed literal; neg_lit must be true.
                    // backtrack already done inside lookahead_probe.
                    if proof_active {
                        // Cannot enqueue without proof justification — skip
                        // and let normal probing discover this unit later.
                        continue;
                    }
                    self.enqueue(neg_lit, None);
                    if self.search_propagate().is_some() {
                        // Propagating the forced unit caused UNSAT.
                        return None;
                    }
                    // Update base_trail_len after forcing a unit so that
                    // subsequent probe scores are not inflated.
                    base_trail_len = self.trail.len();
                    // (#8448) Check wall time after each failed literal BCP.
                    // Failed literal chains (FmlaEquivChain: 772 in one round)
                    // accumulate BCP costs that the top-of-loop wall check
                    // misses because `continue` skips it for the current var.
                    if wall_start.elapsed().as_millis() as u64 >= LOOKAHEAD_WALL_LIMIT_MS {
                        break;
                    }
                    continue;
                }
                ProbeResult::PropCount(pos_props) => {
                    // Variable might have become assigned due to failed literal
                    // detection from a previous iteration propagating units.
                    if self.var_is_assigned(var_idx) {
                        continue;
                    }

                    // Probe negative polarity.
                    let neg_result = self.lookahead_probe(neg_lit, base_trail_len);
                    match neg_result {
                        ProbeResult::Failed => {
                            // neg_lit is a failed literal; pos_lit must be true.
                            if proof_active {
                                // Cannot enqueue without proof justification.
                                continue;
                            }
                            self.enqueue(pos_lit, None);
                            if self.search_propagate().is_some() {
                                return None;
                            }
                            // Update base_trail_len after forcing a unit.
                            base_trail_len = self.trail.len();
                            // (#8448) Wall check after failed literal BCP.
                            if wall_start.elapsed().as_millis() as u64 >= LOOKAHEAD_WALL_LIMIT_MS {
                                break;
                            }
                            continue;
                        }
                        ProbeResult::PropCount(neg_props) => {
                            // Both succeeded. Score = product of propagation counts.
                            // Use (props - base) as the actual number of new propagations.
                            let p = (pos_props.saturating_sub(base_trail_len)) as u64;
                            let n = (neg_props.saturating_sub(base_trail_len)) as u64;
                            // Product heuristic with +1 to avoid zero scores.
                            let score = (p + 1) * (n + 1);

                            if score > best_score {
                                best_score = score;
                                // Choose the polarity with fewer propagations as the
                                // decision literal. The solver explores the more
                                // constrained side first, leaving the easier side for
                                // the other branch. CaDiCaL returns the probe with the
                                // largest trail; we follow the balanced convention.
                                best_literal = Some(if p <= n { pos_lit } else { neg_lit });
                            }
                        }
                    }
                }
            }

            // base_trail_len is updated inline after each failed-literal
            // enqueue+propagate so that subsequent scores are not inflated.
        }

        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: lookahead() leaving at decision_level {}",
            self.decision_level
        );

        best_literal
    }

    /// Probe a single literal: decide it, propagate, record trail size, backtrack.
    ///
    /// Returns `ProbeResult::PropCount(trail_len)` on success, or
    /// `ProbeResult::Failed` if propagation discovered a conflict
    /// (meaning `lit` is a failed literal).
    ///
    /// REQUIRES: `decision_level == 0`, `lit` is unassigned
    /// ENSURES: `decision_level == 0` on return
    fn lookahead_probe(&mut self, lit: Literal, _base_trail_len: usize) -> ProbeResult {
        debug_assert_eq!(self.decision_level, 0);
        debug_assert!(
            !self.var_is_assigned(lit.variable().index()),
            "BUG: lookahead_probe on assigned variable"
        );

        self.decide(lit);
        let result = if self.search_propagate().is_some() {
            // Conflict: failed literal.
            self.backtrack(0);
            ProbeResult::Failed
        } else {
            let trail_len = self.trail.len();
            self.backtrack(0);
            ProbeResult::PropCount(trail_len)
        };

        debug_assert_eq!(self.decision_level, 0);
        result
    }

    /// Generate cubes for cube-and-conquer parallel solving.
    ///
    /// Produces a set of non-overlapping cubes (partial assignments) that
    /// partition the remaining search space. Each cube is a `Vec<Literal>`
    /// representing conjunctive assumptions. A solver instance can solve one
    /// cube by adding its literals as assumptions.
    ///
    /// The algorithm iteratively applies `lookahead()` at increasing depth:
    /// at each level, each existing cube is split into two sub-cubes by the
    /// best splitting variable found by lookahead.
    ///
    /// Returns `vec![vec![]]` (single empty cube) if `depth == 0`.
    /// Returns `vec![]` (no cubes) if the formula is UNSAT.
    ///
    /// REQUIRES: `decision_level == 0`
    /// ENSURES: `decision_level == 0` on return
    ///
    /// Reference: CaDiCaL `generate_cubes()` in `lookahead.cpp:404-518`.
    pub fn generate_cubes(&mut self, depth: usize) -> Vec<Vec<Literal>> {
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: generate_cubes() called at decision_level {}",
            self.decision_level
        );

        if depth == 0 {
            return vec![vec![]];
        }

        if self.has_empty_clause {
            return vec![];
        }

        let mut cubes: Vec<Vec<Literal>> = vec![vec![]];

        for _level in 0..depth {
            if self.is_interrupted() {
                break;
            }

            let prev_cubes = std::mem::take(&mut cubes);
            cubes = Vec::with_capacity(prev_cubes.len() * 2);

            for cube in prev_cubes {
                // Apply cube literals as decisions.
                let cube_ok = self.apply_cube_decisions(&cube);

                if !cube_ok {
                    // This cube leads to a conflict under its assumptions.
                    // It is pruned from the output (UNSAT sub-space).
                    self.backtrack(0);
                    continue;
                }

                // Run lookahead to find the best splitting variable.
                // We need to be at level 0 for lookahead, but we have cube
                // decisions on the trail. Instead, use a simplified inline
                // probe that works at the current decision level.
                let split_lit = self.lookahead_at_current_level();

                self.backtrack(0);

                match split_lit {
                    Some(lit) => {
                        // Split into two sub-cubes.
                        let mut cube1 = cube.clone();
                        cube1.push(lit);
                        let mut cube2 = cube;
                        cube2.push(lit.negated());
                        cubes.push(cube1);
                        cubes.push(cube2);
                    }
                    None => {
                        // No split variable found (all assigned or UNSAT).
                        // Keep the cube as-is.
                        cubes.push(cube);
                    }
                }
            }

            if cubes.is_empty() {
                break;
            }
        }

        self.backtrack(0);

        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: generate_cubes() leaving at decision_level {}",
            self.decision_level
        );

        cubes
    }

    /// Apply cube literals as sequential decisions. Returns `true` if all
    /// decisions + propagations succeeded, `false` if a conflict occurred.
    ///
    /// On conflict, the caller is responsible for calling `backtrack(0)`.
    fn apply_cube_decisions(&mut self, cube: &[Literal]) -> bool {
        for &lit in cube {
            // Skip already-assigned literals (may have been propagated by
            // earlier cube decisions at level 0).
            if self.var_is_assigned(lit.variable().index()) {
                // Check if the assigned value is consistent with the cube literal.
                let val = self.lit_val(lit);
                if val < 0 {
                    // Cube literal is falsified — this cube is UNSAT.
                    return false;
                }
                // val > 0: already true, skip the decision.
                continue;
            }

            self.decide(lit);
            if self.search_propagate().is_some() {
                return false;
            }
        }
        true
    }

    /// Perform lookahead probing at the current decision level (possibly > 0).
    ///
    /// This is a variant of `lookahead()` that works when cube decisions are
    /// on the trail. It probes unassigned variables by deciding at
    /// `decision_level + 1` and backtracking to `decision_level`.
    ///
    /// Failed literals at this level are NOT permanently enqueued (they would
    /// need to be part of the cube instead).
    fn lookahead_at_current_level(&mut self) -> Option<Literal> {
        if self.has_empty_clause {
            return None;
        }

        let save_level = self.decision_level;
        let base_trail_len = self.trail.len();
        let mut best_score: u64 = 0;
        let mut best_literal: Option<Literal> = None;

        for var_idx in 0..self.num_vars {
            if self.is_interrupted() {
                break;
            }
            if self.var_is_assigned(var_idx) || self.var_lifecycle.is_removed(var_idx) {
                continue;
            }

            let var = Variable(var_idx as u32);
            let pos_lit = Literal::positive(var);
            let neg_lit = Literal::negative(var);

            // Probe positive.
            self.decide(pos_lit);
            let pos_result = if self.search_propagate().is_some() {
                self.backtrack(save_level);
                None // failed literal under current cube
            } else {
                let count = self.trail.len();
                self.backtrack(save_level);
                Some(count)
            };

            // Variable may have become assigned from propagation at save_level.
            if self.var_is_assigned(var_idx) {
                continue;
            }

            // Probe negative.
            self.decide(neg_lit);
            let neg_result = if self.search_propagate().is_some() {
                self.backtrack(save_level);
                None
            } else {
                let count = self.trail.len();
                self.backtrack(save_level);
                Some(count)
            };

            // Score: only if both polarities succeed.
            if let (Some(pos_props), Some(neg_props)) = (pos_result, neg_result) {
                let p = pos_props.saturating_sub(base_trail_len) as u64;
                let n = neg_props.saturating_sub(base_trail_len) as u64;
                let score = (p + 1) * (n + 1);

                if score > best_score {
                    best_score = score;
                    best_literal = Some(if p <= n { pos_lit } else { neg_lit });
                }
            } else if pos_result.is_none() && neg_result.is_some() {
                // Positive polarity failed: neg_lit would be forced under this cube.
                // For cubing, we can still use neg_lit as a split decision.
                // But it's better to just pick it as forced.
                // Skip: let the cube consumer discover this.
            } else if pos_result.is_some() && neg_result.is_none() {
                // Negative polarity failed: pos_lit forced under this cube.
            }
            // Both failed: cube is UNSAT — caller will detect this.
        }

        debug_assert_eq!(
            self.decision_level, save_level,
            "BUG: lookahead_at_current_level changed decision_level"
        );

        best_literal
    }
}
