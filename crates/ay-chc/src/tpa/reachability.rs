// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Reachability queries for TPA.
//!
//! Implements the recursive reachability decomposition for both exact
//! (T^{=n}) and less-than (T^{<n}) power abstractions.
//!
//! Reference: Golem TPA.cc:reachabilityQueryExact (484-575),
//!            Golem TPA.cc:reachabilityQueryLessThan (583-714)

use ay_core::kani_compat::DetHashMap as FxHashMap;

use crate::transition_system::TransitionSystem;
use crate::{ChcExpr, SmtResult, SmtValue};

use super::solver::{PowerKind, ReachResult, TpaSolver};

impl TpaSolver {
    /// Check reachability in exactly 2^{power+1} steps.
    ///
    /// Uses recursive decomposition following Golem TPA.cc:reachabilityQueryExact:
    /// - On SAT, extract midpoint and recursively verify both halves
    /// - If either half is unreachable, the abstraction is strengthened and we retry
    /// - On UNSAT, compute interpolant to strengthen the power abstraction
    ///
    /// Reference: Golem TPA.cc:reachabilityQueryExact (line 484-575)
    ///
    /// `ts` is passed by reference to avoid cloning the TransitionSystem on every
    /// recursive call (#5574). The caller (`check_power`) extracts it once.
    pub(super) fn reachability_exact(
        &mut self,
        from: &ChcExpr,
        to: &ChcExpr,
        power: u32,
        ts: &TransitionSystem,
    ) -> ReachResult {
        const MAX_ITERATIONS: u32 = 100;

        if let Some(cached) = self.lookup_exact_query_cache(power, from, to) {
            if self.config.verbose_level > 2 {
                safe_eprintln!("TPA: reachability_exact cache hit power={power}");
            }
            return cached;
        }

        for iteration in 0..MAX_ITERATIONS {
            // SOUNDNESS (#3704): cancellation → inconclusive, not unreachable
            if self.is_cancelled() {
                return ReachResult::Unknown;
            }

            if self.config.verbose_level > 2 {
                safe_eprintln!(
                    "TPA: reachability_exact power={} iteration={}",
                    power,
                    iteration
                );
            }

            let exact_power = match self.get_exact_power(power, ts) {
                Some(ep) => ep,
                None => return ReachResult::Unknown, // Level not learned yet
            };
            let shifted_to = self.shift_expr(to, 2, ts);
            let shifted_power = self.shift_and_freshen(&exact_power, 1, ts);

            // Two-step query: from(0) ∧ exact[n](0→1) ∧ exact[n](1→2) ∧ to(2)
            // The two-step composition lives only in the query, NOT in the
            // cached exact power — this keeps exact powers pure.
            let query = ChcExpr::and(
                from.clone(),
                ChcExpr::and(
                    exact_power.clone(),
                    ChcExpr::and(shifted_power.clone(), shifted_to.clone()),
                ),
            );

            let result = self
                .smt
                .check_sat_with_timeout(&query, self.config.timeout_per_power);

            match result {
                SmtResult::Sat(model) => {
                    if power == 0 {
                        // Base case: truly reachable in 2 steps
                        let refined = self.refine_two_step_target(&model, ts);
                        let result = ReachResult::Reachable {
                            steps: 2,
                            model,
                            refined_target: Some(refined),
                        };
                        self.store_exact_query_cache(power, from, to, &result);
                        return result;
                    }

                    // Extract midpoint for recursive verification
                    let midpoint = self.extract_midpoint_from_model(&model, ts);

                    // Verify first half: from -> midpoint
                    let first_half = self.reachability_exact(from, &midpoint, power - 1, ts);
                    match self.verify_halves(first_half, &midpoint, to, power - 1, "Exact", ts) {
                        Some(result) => {
                            self.store_exact_query_cache(power, from, to, &result);
                            return result;
                        }
                        None => continue,
                    }
                }
                // SOUNDNESS FIX (#2654): Unknown does not imply Unreachable.
                // Returning Unreachable here could cause false Safe verdicts.
                SmtResult::Unknown => {
                    return ReachResult::Unknown;
                }
                // UNSAT (any variant): strengthen and return unreachable
                _ => {
                    self.strengthen_power_from_unsat(PowerKind::Exact, power, from, to, ts);
                    let result = ReachResult::Unreachable;
                    self.store_exact_query_cache(power, from, to, &result);
                    return result;
                }
            }
        }

        if self.config.verbose_level > 0 {
            safe_eprintln!(
                "TPA: reachability_exact max iterations ({}) at power={}",
                MAX_ITERATIONS,
                power
            );
        }
        // SOUNDNESS (#3704): iteration exhaustion → inconclusive, not unreachable.
        // Returning Unreachable here would allow check_power() to enter the
        // fixed-point check path, potentially yielding a false Safe verdict.
        ReachResult::Unknown
    }

    /// Check reachability in less than 2^{power+1} steps.
    ///
    /// Uses recursive decomposition following Golem TPA.cc:reachabilityQueryLessThan.
    /// Reference: Golem TPA.cc:reachabilityQueryLessThan (line 583-714)
    ///
    /// `ts` is passed by reference to avoid cloning the TransitionSystem on every
    /// recursive call (#5574). The caller (`check_power`) extracts it once.
    pub(super) fn reachability_less_than(
        &mut self,
        from: &ChcExpr,
        to: &ChcExpr,
        power: u32,
        ts: &TransitionSystem,
    ) -> ReachResult {
        // Trivial case: from == to means reachable in 0 steps
        if from == to {
            return ReachResult::Reachable {
                steps: 0,
                model: FxHashMap::default(),
                refined_target: Some(to.clone()),
            };
        }

        const MAX_ITERATIONS: u32 = 100;

        for iteration in 0..MAX_ITERATIONS {
            // SOUNDNESS (#3704): cancellation → inconclusive, not unreachable
            if self.is_cancelled() {
                return ReachResult::Unknown;
            }

            if self.config.verbose_level > 2 {
                safe_eprintln!(
                    "TPA: reachability_less_than power={} iteration={}",
                    power,
                    iteration
                );
            }

            let less_than_power = match self.get_less_than_power(power, ts) {
                Some(lt) => lt,
                None => return ReachResult::Unknown, // Level not learned yet
            };
            let exact_power = match self.get_exact_power(power, ts) {
                Some(ep) => ep,
                None => return ReachResult::Unknown, // Level not learned yet
            };
            let goal = self.shift_expr(to, 2, ts);
            let direct_less_than = self.shift_only_next_vars(&less_than_power, ts);
            let shifted_exact = self.shift_and_freshen(&exact_power, 1, ts);
            let composed = ChcExpr::and(less_than_power.clone(), shifted_exact.clone());
            let two_step = ChcExpr::or(direct_less_than.clone(), composed.clone());
            let query = ChcExpr::and(from.clone(), ChcExpr::and(two_step, goal.clone()));

            let result = self
                .smt
                .check_sat_with_timeout(&query, self.config.timeout_per_power);

            match result {
                SmtResult::Sat(model) => {
                    // Determine which disjunct was satisfied
                    let direct_satisfied = self.evaluate_in_model(&model, ts);

                    if direct_satisfied {
                        if power == 0 {
                            let refined = ChcExpr::and(from.clone(), to.clone());
                            return ReachResult::Reachable {
                                steps: 0,
                                model,
                                refined_target: Some(refined),
                            };
                        }

                        let sub_result = self.reachability_less_than(from, to, power - 1, ts);
                        match sub_result {
                            ReachResult::Reachable { .. } => return sub_result,
                            ReachResult::Unreachable | ReachResult::Unknown => {
                                if self.config.verbose_level > 2 {
                                    safe_eprintln!(
                                        "TPA: Direct path spurious, retrying power={}",
                                        power
                                    );
                                }
                                continue;
                            }
                        }
                    } else {
                        // Composed path satisfied
                        if power == 0 {
                            let refined = self.refine_two_step_target(&model, ts);
                            return ReachResult::Reachable {
                                steps: 1,
                                model,
                                refined_target: Some(refined),
                            };
                        }

                        let midpoint = self.extract_midpoint_from_model(&model, ts);
                        let first_half =
                            self.reachability_less_than(from, &midpoint, power - 1, ts);
                        match self.verify_halves(
                            first_half,
                            &midpoint,
                            to,
                            power - 1,
                            "Less-than",
                            ts,
                        ) {
                            Some(result) => return result,
                            None => continue,
                        }
                    }
                }
                // SOUNDNESS FIX (#2654): Unknown does not imply Unreachable.
                SmtResult::Unknown => return ReachResult::Unknown,
                // UNSAT (any variant): strengthen and return unreachable
                _ => {
                    self.strengthen_power_from_unsat(PowerKind::LessThan, power, from, to, ts);
                    return ReachResult::Unreachable;
                }
            }
        }

        if self.config.verbose_level > 0 {
            safe_eprintln!(
                "TPA: reachability_less_than max iterations ({}) at power={}",
                MAX_ITERATIONS,
                power
            );
        }
        // SOUNDNESS (#3704): iteration exhaustion → inconclusive, not unreachable.
        // Returning Unreachable here would allow check_power() to enter the
        // fixed-point check path, potentially yielding a false Safe verdict.
        ReachResult::Unknown
    }

    /// Verify a recursive half-decomposition of a reachability query.
    ///
    /// Given the result of checking the first half (from → midpoint), verifies
    /// the second half (midpoint → to) using exact reachability. Returns `None`
    /// if either half was spurious (caller should retry), or `Some(result)` with
    /// the combined reachability result.
    pub(super) fn verify_halves(
        &mut self,
        first_half: ReachResult,
        midpoint: &ChcExpr,
        to: &ChcExpr,
        power: u32,
        label: &str,
        ts: &TransitionSystem,
    ) -> Option<ReachResult> {
        let (first_steps, second_half_from, fallback_model) = match first_half {
            ReachResult::Unreachable | ReachResult::Unknown => {
                if self.config.verbose_level > 2 {
                    safe_eprintln!(
                        "TPA: {} first half spurious, retrying power={}",
                        label,
                        power
                    );
                }
                return None;
            }
            ReachResult::Reachable {
                steps,
                refined_target: Some(refined_mid),
                ..
            } => (steps, refined_mid, None),
            ReachResult::Reachable {
                steps,
                model,
                refined_target: None,
            } => (steps, midpoint.clone(), Some(model)),
        };

        let second_half = self.reachability_exact(&second_half_from, to, power, ts);
        match second_half {
            ReachResult::Unreachable | ReachResult::Unknown => {
                if self.config.verbose_level > 2 {
                    safe_eprintln!(
                        "TPA: {} second half spurious, retrying power={}",
                        label,
                        power
                    );
                }
                None
            }
            ReachResult::Reachable {
                steps: second_steps,
                model: second_model,
                refined_target,
            } => {
                let model = match fallback_model {
                    Some(fm) if second_model.is_empty() => fm,
                    _ => second_model,
                };
                Some(ReachResult::Reachable {
                    steps: first_steps + second_steps,
                    model,
                    refined_target,
                })
            }
        }
    }

    /// Determine which disjunct was satisfied based on model variables.
    /// Returns true if the direct path was used, false if the composed path.
    ///
    /// Heuristic: The direct path T^{<n}(v0, v2) doesn't use time-1 variables,
    /// while the composed path T^{<n}(v0, v1) ∧ T^{=n}(v1, v2) does.
    fn evaluate_in_model(
        &self,
        model: &FxHashMap<String, SmtValue>,
        ts: &TransitionSystem,
    ) -> bool {
        // Check if any time-1 state variables have values in the model.
        // The composed path requires these as intermediate states.
        for var in ts.state_vars() {
            let time_1_name = format!("{}_1", var.name);
            if model.contains_key(&time_1_name) {
                return false; // Composed path used time-1 variables
            }
        }
        true // Direct path (no time-1 state variables)
    }
}
