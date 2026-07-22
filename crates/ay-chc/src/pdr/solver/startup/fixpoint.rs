// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Startup fixpoint discovery loop.
//!
//! Runs iterative discovery passes (bounds, equalities, BV ranges, etc.)
//! until frame[1] converges or a small cap is reached.

use super::super::{PdrResult, PdrSolver};

impl PdrSolver {
    fn should_run_early_conditional_invariant_probe(&self) -> bool {
        self.problem.predicates().len() == 1
            && !self.problem.has_bv_sorts()
            && !self.problem.has_array_sorts()
            && !self.problem.has_real_sorts()
            && !self.problem.has_datatype_sorts()
            && self
                .problem
                .predicates()
                .iter()
                .any(|pred| !self.extract_threshold_conditions(pred.id).is_empty())
    }

    /// Run the startup fixpoint discovery loop.
    ///
    /// Forward invariant discovery: find invariants proactively.
    /// This is more efficient than discovering them through blocking.
    ///
    /// STARTUP FIXPOINT LOOP (#1398): Some invariants are only self-inductive once
    /// prerequisite invariants are added to frame[1]. We iterate until convergence
    /// (or a small cap) to allow dependent invariants to be discovered.
    ///
    /// Example (gj2007_m_3): The init equality C=G is only self-inductive after
    /// the prerequisite equality A=B is discovered, because the loop's conditional
    /// update (C' = ite(B >= k*G, C+1, C)) is only a no-op when A=B forces B < k*G.
    ///
    /// The fixpoint loop runs: bounds -> fact conjuncts -> joint bounds -> multi-linear
    /// -> equalities -> error-implied. Error-implied is included because conditional
    /// invariants like (A >= 5*C) => (B = 5*C) often need prerequisite equalities.
    pub(in crate::pdr::solver) fn run_fixpoint_discovery(&mut self) -> Option<PdrResult> {
        let _t_fixpoint = ay_core::time::Instant::now();
        // Adaptive fixpoint depth (#1398): for multi-predicate phase-chains,
        // invariants must propagate hop-by-hop from init to the deepest predicate.
        // A chain of N predicates may need up to N-1 hops. Use max(3, num_preds)
        // so single-predicate problems still use 3 iterations.
        let num_preds = self.problem.predicates().len();
        let max_fixpoint_iters = num_preds.max(3);
        for fixpoint_iter in 0..max_fixpoint_iters {
            // inc-12: total-startup budget check (wide-var cap). Exhaustion is
            // NOT a failure — stop discovering and hand the remaining engine
            // window to the main PDR blocking loop.
            if self.startup_budget_exhausted() {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Startup fixpoint stopped at iter {} (wide-var startup budget exhausted)",
                        fixpoint_iter
                    );
                }
                break;
            }
            let frame1_before = self.frames.get(1).map_or(0, |f| f.lemmas.len());

            // Core discovery passes that can create dependent invariants.
            // Cancellation checks between each pass ensure cooperative timeouts
            // are respected even when individual passes are slow.

            // 1. Bound invariants: basic constraints like E >= 1 from init
            self.discover_bound_invariants();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // 1a. BV range invariants: extract BV comparison atoms from transition
            // clauses and test inductiveness (#5877). Runs after Int bounds so that
            // any Int-side lemmas are available for mixed-sort problems.
            self.discover_bv_range_invariants();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // 1a2. BV bit-group invariants (#7044): discover equality, constant,
            // per-bit bound, and ordering invariants over BV groups reconstructed
            // from BvToBool metadata. Runs after BV range invariants.
            if !self.config.bv_bit_groups.is_empty() {
                self.discover_bv_group_equalities();
                if self.is_cancelled() {
                    return Some(self.finish_with_result_trace(PdrResult::Unknown));
                }
                self.discover_bv_group_constants();
                if self.is_cancelled() {
                    return Some(self.finish_with_result_trace(PdrResult::Unknown));
                }
                self.discover_bv_group_bit_bounds();
                if self.is_cancelled() {
                    return Some(self.finish_with_result_trace(PdrResult::Unknown));
                }
                self.discover_bv_group_ordering();
                if self.is_cancelled() {
                    return Some(self.finish_with_result_trace(PdrResult::Unknown));
                }
            }

            // 1b. Edge summary invariants: MBP-projected entry constraints for derived predicates (#1429)
            // This runs after bound invariants so source predicates have frame lemmas to project.
            self.discover_edge_summary_invariants();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // 2. Promote inductive fact-constraint conjuncts (e.g., three_dots_moving_2)
            self.discover_fact_clause_conjunct_invariants();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // 3. Bootstrap mutually-inductive lower bounds (e.g., yz_plus_minus_2)
            self.discover_joint_init_shifted_lower_bounds();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // 4. Multi-linear invariants via CEX-guided refinement (#1525)
            self.discover_multi_linear_invariants();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // 5. Equality invariants: discovers prerequisites like A=B
            self.discover_equality_invariants();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // 5b. Propagate newly-discovered symbolic equalities to derived predicates (#2248).
            // This enables equalities discovered by discover_equality_invariants() to feed
            // into phase-chain benchmarks where derived predicates need the equality constraint.
            self.propagate_symbolic_equalities_to_derived_predicates();

            // #1402: Cross-predicate invariant propagation (linear head-arg mapping).
            // This runs inside the startup fixpoint loop so propagated prerequisites can
            // enable subsequent discovery passes in the same run.
            let _propagated = self.propagate_frame1_invariants_to_users();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // 5b2. Difference-bound invariants from self-loop step constants (#1362).
            // For transitions with a stepped variable (a' = a + c) and an unchanged
            // variable (b' = b), generate candidates like `a < b + c`. This discovers
            // relational invariants that standard bound/equality passes miss.
            self.discover_step_difference_bound_invariants();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // 5c. Retry deferred entry-inductive invariants (#5970).
            // After cross-predicate propagation, predecessor frames may now contain
            // upper bounds that enable previously-failed weakened inequalities.
            self.retry_deferred_entry_invariants();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // 5d. Retry deferred self-inductive invariants with frame strengthening.
            // Invariants like (>= p4 p1) from init may not be independently
            // self-inductive but become inductive relative to other frame lemmas.
            self.retry_deferred_self_inductive_invariants();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // 6. Error-implied invariants: conditional invariants from error clauses
            // e.g., (A >= 5*C) => (B = 5*C) needs A=B to be self-inductive
            self.discover_error_implied_invariants();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // Check convergence
            let frame1_after = self.frames.get(1).map_or(0, |f| f.lemmas.len());
            if frame1_after == frame1_before {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Startup fixpoint converged after {} iteration(s)",
                        fixpoint_iter + 1
                    );
                }
                self.startup_converged = true;
                // #4751: snapshot the frame[1] size — the convergence claim is
                // only valid while frame[1] is unchanged (later passes keep
                // adding lemmas post-convergence).
                self.startup_converged_frame1_len = Some(frame1_after);
                break;
            }
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Startup fixpoint iter {}: {} -> {} lemmas",
                    fixpoint_iter,
                    frame1_before,
                    frame1_after
                );
            }
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }
        }
        if self.config.verbose {
            safe_eprintln!(
                "PDR: Startup fixpoint loop took {:?}",
                _t_fixpoint.elapsed()
            );
        }

        // PERF (dt+CHC family, model_checker_consumer_dt_union_find 6.8s -> sub-second):
        // try the direct safety proof BEFORE the expensive O(n^2) bound passes
        // below. When the converged fixpoint frame already proves safety (e.g.
        // via an error-implied conditional invariant), the scaled-difference /
        // sum-bound floods (a) cost seconds of SMT generation and (b) bloat
        // frame[1] with ~100 redundant lemmas that the safety proof then
        // re-verifies one-by-one. This is purely an ordering change: the model
        // still goes through the identical check_invariants_prove_safety
        // admission core, finish_safe_with_result_trace strict validation, and
        // portfolio/certificate replay. If the early check fails we fall
        // through to today's behavior unchanged.
        // Kill switch: AY_CHC_DISABLE_EARLY_SAFETY_CHECK.
        if self.startup_converged
            && !self.skip_startup_direct_safety_proof()
            && std::env::var_os("AY_CHC_DISABLE_EARLY_SAFETY_CHECK").is_none()
        {
            let _t_early = ay_core::time::Instant::now();
            if let Some(model) = self.check_invariants_prove_safety() {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Pre-bound-discovery invariants prove safety directly ({:?})",
                        _t_early.elapsed()
                    );
                }
                // #4751: on strict-validation demotion, fall through to the
                // bound passes / nonfixpoint discovery instead of aborting.
                if let Some(result) = self.finish_safe_or_continue(
                    model,
                    "post-fixpoint startup model (pre-bound-discovery)",
                ) {
                    return Some(result);
                }
                // Demoted: the frame carries optimistically-admitted junk.
                // Houdini-prune it NOW and retry once, before the bound
                // floods burn the engine budget (gj2007_m_3, #4751).
                if let Some(result) =
                    self.demotion_prune_and_retry("post-prune startup model (pre-bound-discovery)")
                {
                    return Some(result);
                }
            }
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Pre-bound-discovery direct safety check not yet sufficient ({:?})",
                    _t_early.elapsed()
                );
            }
        }

        // Expensive O(n^2) bound passes (scaled difference, sum bounds, loop exit,
        // entry guard) that don't depend on other frame lemmas. Run once here
        // instead of per-fixpoint-iteration to avoid redundant SMT work.
        // inc-12: skipped when the wide-var total-startup budget is spent.
        if !self.startup_budget_exhausted() {
            self.discover_bound_invariants_post_fixpoint();
        }
        if self.is_cancelled() {
            return Some(self.finish_with_result_trace(PdrResult::Unknown));
        }

        // s_disj_ite-style simple loops need the phase conditional invariant
        // before the late non-fixpoint tail burns the focused PDR probe budget.
        // The early algebraic insertion is limited to self-loop-only predicates
        // and the candidate is still checked by strict final model validation.
        if self.should_run_early_conditional_invariant_probe() {
            let _t_cond = ay_core::time::Instant::now();
            let added = self.discover_conditional_invariants_early_probe();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: early discover_conditional_invariants probe took {:?} (added={})",
                    _t_cond.elapsed(),
                    added
                );
            }
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }
        }

        None
    }
}
