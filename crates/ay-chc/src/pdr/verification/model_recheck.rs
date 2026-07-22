// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Post-loop filtered-invariant re-verification for query clauses.
//!
//! Extracted from `model.rs` — handles the post-loop re-verification block
//! in `verify_model_impl` that fires when `used_filtered_invariant` is true.

use super::*;

impl PdrSolver {
    /// Re-verify all query clauses using the filtered invariant.
    ///
    /// Called after the main clause loop when `used_filtered_invariant` is true.
    /// Returns `Some(failure_tuple)` if any query clause fails with the
    /// filtered invariant. Returns `None` if all pass.
    pub(super) fn reverify_queries_with_filtered_invariant(
        &mut self,
        query_clause_info: &[QueryClauseInfo],
        verify_timeout: std::time::Duration,
        budget_start: Option<ay_core::time::Instant>,
        budget: Option<std::time::Duration>,
    ) -> Option<(PredicateId, ChcExpr, PredicateId, ChcExpr)> {
        // #73 SOUNDNESS FIX: If any transition clause used filtered invariant,
        // we must re-verify ALL query clauses with the same filtered invariant.
        // Otherwise, we have an inconsistent invariant - one that passes inductiveness
        // with filtering but may not exclude bad states.
        //
        // #74 FIX: Only filter the INVARIANT part, not the bad state constraint.
        // The bad state is part of the problem specification, not derived from frames.
        if self.config.verbose {
            safe_eprintln!(
                "PDR: verify_model: re-verifying {} query clauses with filtered invariant",
                query_clause_info.len()
            );
        }
        for (i, (pred_info, invariant_body, bad_state)) in query_clause_info.iter().enumerate() {
            // #3225: Check cooperative cancellation between re-verification queries.
            if self.is_cancelled() {
                return Some((
                    PredicateId::new(0),
                    ChcExpr::Bool(false),
                    PredicateId::new(0),
                    ChcExpr::Bool(false),
                ));
            }
            // FIX #74: Only filter the invariant part, keep bad state intact
            let filtered_invariant = Self::filter_blocking_lemmas_aggressive(invariant_body);
            // Reconstruct query body: filtered_invariant AND original_bad_state
            let query_body_filtered = ChcExpr::and(filtered_invariant.clone(), bad_state.clone());

            if self.config.verbose {
                safe_eprintln!("  query {}: invariant={}", i, invariant_body);
                safe_eprintln!("  query {}: bad_state={}", i, bad_state);
                safe_eprintln!("  query {}: filtered_invariant={}", i, filtered_invariant);
            }

            // Check if the filtered invariant still excludes bad states
            self.smt.reset();
            let result = self.smt.check_sat_with_timeout(
                &query_body_filtered,
                self.current_verify_step_timeout(verify_timeout, budget_start, budget),
            );
            match result {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: verify_model: query clause {} passed with filtered invariant",
                            i
                        );
                    }
                }
                SmtResult::Sat(mut m) => {
                    // Best-effort: ensure we have enough bindings to reconstruct a state.
                    if m.is_empty() {
                        Self::extract_equalities_from_formula(&query_body_filtered, &mut m);
                    }
                    cube::augment_model_from_equalities(&query_body_filtered, &mut m);

                    if let Some((pred, args)) = pred_info {
                        if let Some(state) = self.extract_state_from_args(*pred, args, &m) {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: verify_model: query clause {} (filtered) SAT - extracted state: {}",
                                    i, state
                                );
                            }
                            return Some((*pred, state, *pred, ChcExpr::Bool(false)));
                        }
                    }

                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: verify_model: SOUNDNESS CHECK FAILED - query clause {} does NOT pass with filtered invariant",
                            i
                        );
                        safe_eprintln!("  filtered body: {}", query_body_filtered);
                    }
                    // The filtered invariant is inductive but doesn't exclude bad states.
                    // This is NOT a valid CHC solution. Return failure.
                    return Some((
                        PredicateId::new(0),
                        ChcExpr::Bool(false),
                        PredicateId::new(0),
                        ChcExpr::Bool(false),
                    ));
                }
                SmtResult::Unknown => {
                    // #2477/#5970/#7109/#7165: Executor fallback for QF_LIA queries.
                    // #5595: BV problems are NOT pure QF_LIA — Unknown is expected.
                    // #7165: mod/div gate removed — executor handles mod/div via
                    // theory propagation after CHC-level Euclidean decomposition.
                    if !self.problem.has_bv_sorts() && !query_body_filtered.contains_array_ops() {
                        self.smt.reset();
                        let verify_retry_timeout =
                            self.current_verify_retry_timeout(budget_start, budget);
                        let retry = self.smt.check_sat_with_executor_fallback_timeout(
                            &query_body_filtered,
                            verify_retry_timeout,
                        );
                        match retry {
                            SmtResult::Unsat
                            | SmtResult::UnsatWithCore(_)
                            | SmtResult::UnsatWithFarkas(_) => {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: verify_model: query clause {} passed with filtered invariant (QF_LIA retry)",
                                        i
                                    );
                                }
                                continue;
                            }
                            SmtResult::Sat(mut m) => {
                                if m.is_empty() {
                                    Self::extract_equalities_from_formula(
                                        &query_body_filtered,
                                        &mut m,
                                    );
                                }
                                cube::augment_model_from_equalities(&query_body_filtered, &mut m);
                                if let Some((pred, args)) = pred_info {
                                    if let Some(state) =
                                        self.extract_state_from_args(*pred, args, &m)
                                    {
                                        return Some((*pred, state, *pred, ChcExpr::Bool(false)));
                                    }
                                }
                                return Some((
                                    PredicateId::new(0),
                                    ChcExpr::Bool(false),
                                    PredicateId::new(0),
                                    ChcExpr::Bool(false),
                                ));
                            }
                            SmtResult::Unknown => {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: verify_model: filtered query clause {} still UNKNOWN after extended retry",
                                        i
                                    );
                                }
                            }
                        }
                    }
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: verify_model: SOUNDNESS CHECK UNKNOWN - query clause {} could not be checked with filtered invariant",
                            i
                        );
                        safe_eprintln!("  filtered body: {}", query_body_filtered);
                    }
                    return Some((
                        PredicateId::new(0),
                        ChcExpr::Bool(false),
                        PredicateId::new(0),
                        ChcExpr::Bool(false),
                    ));
                }
            }
        }
        None
    }
}
