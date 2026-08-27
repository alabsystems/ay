// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Non-fixpoint startup discovery passes.
//!
//! These run once after the fixpoint loop converges: sum invariants, affine
//! kernel, difference invariants, parity, modular equality, conditional
//! invariants, relational invariants, and more.

use super::super::{PdrResult, PdrSolver};

include!("nonfixpoint/budget.rs");

impl PdrSolver {
    /// Run non-fixpoint discovery passes once after core fixpoint converges.
    ///
    /// STARTUP BUDGET (#3121): When running under a portfolio or solve_timeout,
    /// the non-fixpoint discovery passes (especially affine kernel synthesis and
    /// difference invariants) can consume the entire time budget on benchmarks
    /// with many variables or mod/div constraints. Cap total non-fixpoint
    /// discovery time to leave budget for the actual PDR solve loop.
    pub(in crate::pdr::solver) fn run_nonfixpoint_discovery(&mut self) -> Option<PdrResult> {
        let nonfixpoint_start = ay_core::time::Instant::now();
        let nonfixpoint_budget: Option<std::time::Duration> =
            if self.config.cancellation_token.is_some() || self.config.solve_timeout.is_some() {
                // Use 5 seconds or 40% of solve_timeout, whichever is smaller.
                let budget = self
                    .config
                    .solve_timeout
                    .map(|t| t.mul_f64(0.4).min(std::time::Duration::from_secs(5)))
                    .unwrap_or(std::time::Duration::from_secs(5));
                Some(budget)
            } else {
                None
            };
        // inc-12: clamp to whatever remains of the wide-var TOTAL startup
        // budget (fixpoint may have spent most of it). The thread-local SMT
        // deadline installed by run_startup_discovery additionally clamps
        // every query inside the passes, which previously ran to completion
        // because this budget was checked only between passes.
        let nonfixpoint_budget = match self.startup_deadline {
            Some(deadline) => {
                let remaining = deadline.saturating_duration_since(ay_core::time::Instant::now());
                Some(nonfixpoint_budget.map_or(remaining, |b| b.min(remaining)))
            }
            None => nonfixpoint_budget,
        };

        let _t2 = ay_core::time::Instant::now();
        self.discover_sum_invariants();
        if self.config.verbose {
            safe_eprintln!("PDR: discover_sum_invariants took {:?}", _t2.elapsed());
        }

        // After sum invariants, check for constant accumulators: variables whose
        // increment is provably zero given the newly-discovered sum equalities.
        // This derives stronger modular invariants (e.g., C mod 10 = 0) that
        // the parity pass (mod 2 only) cannot discover. (#8782)
        {
            let _t2_acc = ay_core::time::Instant::now();
            self.discover_constant_accumulator_modular_invariants();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_constant_accumulator_modular_invariants took {:?}",
                    _t2_acc.elapsed()
                );
            }
        }

        if self.is_cancelled() {
            return Some(self.finish_with_result_trace(PdrResult::Unknown));
        }
        if !self.nonfixpoint_budget_exceeded(nonfixpoint_start, nonfixpoint_budget) {
            let _t2a = ay_core::time::Instant::now();
            self.discover_sum_equals_var_invariants();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_sum_equals_var_invariants took {:?}",
                    _t2a.elapsed()
                );
            }
        }

        // Early safety check: sum invariants (including cross-predicate propagation)
        // are often sufficient to prove safety for multi-predicate linear problems
        // like s_multipl_*. Check immediately rather than running 15+ more discovery
        // passes that may get cancelled by the portfolio timeout. (#5425)
        //
        // Only do this under portfolio/timeout pressure (cancellation_token or
        // solve_timeout set). Without those, the full pipeline completes and the
        // safety check at the end of run_startup_discovery catches it anyway.
        //
        // For multi-predicate problems, use algebraic_fast mode: only try the
        // algebraic-only model (sum/affine invariants). Skip the expensive
        // inductive-subset computation (O(n) SMT calls, ~100ms each) which on
        // benchmarks like s_multipl_25 wastes 6-10s during startup when the
        // algebraic model is insufficient. The full inductive-subset check runs
        // after all discovery passes complete. (#5425)
        if (self.config.cancellation_token.is_some() || self.config.solve_timeout.is_some())
            && !self.skip_startup_direct_safety_proof()
            && self.frames.len() >= 2
            && !self.frames[1].lemmas.is_empty()
        {
            let is_multi_pred = self.problem.predicates().len() > 1;
            let _t_early = ay_core::time::Instant::now();
            if let Some(mut model) = self.check_invariants_prove_safety_impl(is_multi_pred) {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Early safety check after sum discovery succeeded ({:?})",
                        _t_early.elapsed()
                    );
                }
                // SOUNDNESS (#5922): Fresh-context confirmation.
                // When the model is convergence_proven (startup fixpoint
                // converged, frame[0]=frame[1], no conjuncts filtered),
                // the full frame conjunction is inductive by definition.
                // Use query-only fresh verification to avoid expensive
                // transition clause SMT checks that can return Unknown
                // on large invariants (e.g., dillig12_m with ~40 conjuncts
                // and 42 variables). This matches the pattern in
                // startup/mod.rs line 231-234.
                let fresh_full = if model.convergence_proven {
                    self.verify_model_fresh_query_only(&model)
                } else {
                    self.verify_model_fresh(&model)
                };
                // Sound fallback (#1362): For sum-discovery models that are
                // individually_inductive (each lemma self-inductive without
                // frame strengthening), accept even if full fresh check fails.
                // PDR algebraic verification already proved inductiveness.
                // Portfolio Step 4.5 provides the query-only soundness gate.
                let fresh_ok = fresh_full || model.individually_inductive;
                if !fresh_ok {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: sum-discovery model fails fresh-context \
                             verification (#5922); continuing"
                        );
                    }
                } else {
                    // SOUNDNESS (#5922): Save model before simplification.
                    let original_model = model.clone();
                    let simp = self.simplify_model(&mut model);
                    // Re-verify when simplification modified the model (#5805, #5922).
                    // (#8782): Skip re-verification for individually_inductive models.
                    // Each lemma was already proven self-inductive independently of the
                    // frame, so simplification (which only removes redundant lemmas)
                    // cannot introduce unsoundness. The expensive verify_model call
                    // can time out on models with multiplication-heavy invariants
                    // (e.g., s_mutants_16: (= (- C A) (* 3 B))).
                    let reverify_needed = simp.modified() && !model.individually_inductive;
                    if reverify_needed && !self.verify_model(&model) {
                        if simp.free_vars_sanitized {
                            // Free-var sanitization modified the model and re-verification
                            // failed. The original model already passed fresh verification
                            // (fresh_ok was true at line 655). Fall back to original model
                            // instead of discarding a valid proof. (#1362)
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: simplified sum-discovery model fails re-verification \
                                     after free-variable sanitization; falling back to original \
                                     model (fresh_ok already confirmed) (#1362)"
                                );
                            }
                            // #4751: continue the pipeline on strict-validation demotion.
                            if let Some(result) = self.finish_safe_or_continue(
                                original_model,
                                "sum-discovery pre-simplification fallback",
                            ) {
                                return Some(result);
                            }
                        } else {
                            // Only redundancy removal — fall back (#5922).
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: simplified sum-discovery model fails re-verification; \
                                     falling back to pre-simplification model"
                                );
                            }
                            // #4751: continue the pipeline on strict-validation demotion.
                            if let Some(result) = self.finish_safe_or_continue(
                                original_model,
                                "sum-discovery pre-simplification fallback",
                            ) {
                                return Some(result);
                            }
                        }
                    } else if let Some(result) =
                        self.finish_safe_or_continue(model, "sum-discovery model")
                    {
                        // #4751: continue the pipeline on strict-validation demotion.
                        return Some(result);
                    }
                }
            }
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Early safety check after sum discovery: not yet sufficient ({:?})",
                    _t_early.elapsed()
                );
            }
            // #4751 (gj2007_m_3): a strict-validation demotion above means the
            // frame carries optimistically-admitted junk. Prune it and retry
            // once; the len-guard inside makes this free when nothing was
            // demoted or nothing changed since the last sweep.
            if self.strict_validation_demotions > 0 {
                if let Some(result) =
                    self.demotion_prune_and_retry("post-prune sum-discovery model")
                {
                    return Some(result);
                }
            }
        }

        if self.is_cancelled() {
            return Some(self.finish_with_result_trace(PdrResult::Unknown));
        }
        if !self.nonfixpoint_budget_exceeded(nonfixpoint_start, nonfixpoint_budget) {
            let _t2b = ay_core::time::Instant::now();
            self.discover_affine_invariants();
            if self.config.verbose {
                safe_eprintln!("PDR: discover_affine_invariants took {:?}", _t2b.elapsed());
            }
        }
        if self.is_cancelled() {
            return Some(self.finish_with_result_trace(PdrResult::Unknown));
        }
        // Kernel discovery has its own internal budget (1500ms) so it runs
        // even when the nonfixpoint startup budget is exceeded (#5399). The
        // kernel discovers relatively-inductive equalities (e.g., D=2C given
        // A=B) that the simpler equality mechanism above cannot find, and
        // Phase B retry handles the layered inductiveness checking.
        {
            let _t2c = ay_core::time::Instant::now();
            self.discover_affine_invariants_via_kernel(None);
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_affine_invariants_via_kernel took {:?}",
                    _t2c.elapsed()
                );
            }
        }
        if self.is_cancelled() {
            return Some(self.finish_with_result_trace(PdrResult::Unknown));
        }
        if !self.nonfixpoint_budget_exceeded(nonfixpoint_start, nonfixpoint_budget) {
            let _t2d = ay_core::time::Instant::now();
            self.propagate_affine_invariants_to_derived_predicates();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: propagate_affine_invariants_to_derived_predicates took {:?}",
                    _t2d.elapsed()
                );
            }
        }
        if self.is_cancelled() {
            return Some(self.finish_with_result_trace(PdrResult::Unknown));
        }
        if !self.nonfixpoint_budget_exceeded(nonfixpoint_start, nonfixpoint_budget) {
            let _t2e = ay_core::time::Instant::now();
            let affine_hint_added = self.apply_affine_equality_propagation_hints();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: apply_affine_equality_propagation_hints took {:?} ({} added)",
                    _t2e.elapsed(),
                    affine_hint_added
                );
            }
        }
        if self.is_cancelled() {
            return Some(self.finish_with_result_trace(PdrResult::Unknown));
        }
        // #4751: post-kernel derived-predicate bound passes. The affine kernel
        // above can add relational source-frame equalities (dillig12_m's
        // D = 2*C) that entry-inductiveness checks for DERIVED predicates
        // needed but did not have during the fixpoint loop. Two cheap,
        // fully-admission-checked passes re-harvest what is now provable:
        //  (a) entry-value constant bounds on self-loop-constant arguments
        //      (SAD's first arg <= 2), and
        //  (b) a re-run of the step-difference bound pass whose candidates
        //      were rejected pre-kernel as not entry-inductive
        //      (SAD's A <= B + 2).
        if !self.nonfixpoint_budget_exceeded(nonfixpoint_start, nonfixpoint_budget) {
            let _t2f = ay_core::time::Instant::now();
            self.discover_derived_entry_value_bounds();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_derived_entry_value_bounds took {:?}",
                    _t2f.elapsed()
                );
            }
        }
        if self.is_cancelled() {
            return Some(self.finish_with_result_trace(PdrResult::Unknown));
        }
        if !self.nonfixpoint_budget_exceeded(nonfixpoint_start, nonfixpoint_budget) {
            let _t2g = ay_core::time::Instant::now();
            self.discover_step_difference_bound_invariants();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: post-kernel discover_step_difference_bound_invariants took {:?}",
                    _t2g.elapsed()
                );
            }
        }
        if self.is_cancelled() {
            return Some(self.finish_with_result_trace(PdrResult::Unknown));
        }
        if !self.nonfixpoint_budget_exceeded(nonfixpoint_start, nonfixpoint_budget) {
            let _t3 = ay_core::time::Instant::now();
            self.discover_triple_sum_invariants();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_triple_sum_invariants took {:?}",
                    _t3.elapsed()
                );
            }
        }
        if self.is_cancelled() {
            return Some(self.finish_with_result_trace(PdrResult::Unknown));
        }
        // #8782: Signed triple-sum invariants (a + b - c = d) for problems
        // where one variable is subtracted. Run after unsigned triple sum.
        // Example: bouncy_three_counters_merged needs D = A + C - B.
        // Accidentally removed in 8e9057446 (zone adoption revert).
        if !self.nonfixpoint_budget_exceeded(nonfixpoint_start, nonfixpoint_budget) {
            let _t3s = ay_core::time::Instant::now();
            self.discover_signed_triple_sum_invariants();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_signed_triple_sum_invariants took {:?}",
                    _t3s.elapsed()
                );
            }
        }
        if self.is_cancelled() {
            return Some(self.finish_with_result_trace(PdrResult::Unknown));
        }
        // #1362: Quad sum invariants (vi + vj + vk + vm = vl) for 4-way
        // nondeterministic branching (s_multipl_14). Run after triple sum.
        if !self.nonfixpoint_budget_exceeded(nonfixpoint_start, nonfixpoint_budget) {
            let _t3q = ay_core::time::Instant::now();
            self.discover_sum_invariants();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_sum_invariants (quad) took {:?}",
                    _t3q.elapsed()
                );
            }
        }
        if self.is_cancelled() {
            return Some(self.finish_with_result_trace(PdrResult::Unknown));
        }
        if !self.nonfixpoint_budget_exceeded(nonfixpoint_start, nonfixpoint_budget) {
            let _t4 = ay_core::time::Instant::now();
            self.discover_difference_invariants();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_difference_invariants took {:?}",
                    _t4.elapsed()
                );
            }
        }
        if self.is_cancelled() {
            return Some(self.finish_with_result_trace(PdrResult::Unknown));
        }
        if !self.nonfixpoint_budget_exceeded(nonfixpoint_start, nonfixpoint_budget) {
            let _t5 = ay_core::time::Instant::now();
            self.discover_scaled_difference_invariants();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_scaled_difference_invariants took {:?}",
                    _t5.elapsed()
                );
            }
        }
        if self.is_cancelled() {
            return Some(self.finish_with_result_trace(PdrResult::Unknown));
        }
        if !self.nonfixpoint_budget_exceeded(nonfixpoint_start, nonfixpoint_budget) {
            let _t6 = ay_core::time::Instant::now();
            self.discover_scaled_sum_invariants();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_scaled_sum_invariants took {:?}",
                    _t6.elapsed()
                );
            }
        }
        if self.is_cancelled() {
            return Some(self.finish_with_result_trace(PdrResult::Unknown));
        }
        if !self.nonfixpoint_budget_exceeded(nonfixpoint_start, nonfixpoint_budget) {
            let _t7 = ay_core::time::Instant::now();
            // Cap parity at 500ms: probes involve individual SMT queries per
            // (var, modulus) pair. On problems without modular structure (e.g.,
            // dillig12_m J=1), ALL probes return Unknown and waste seconds that
            // the PDR solve loop needs for cross-predicate propagation (#1306).
            let parity_cap = std::time::Duration::from_millis(500);
            let parity_deadline = nonfixpoint_budget.map(|b| {
                let nonfixpoint_end = nonfixpoint_start + b;
                let capped = ay_core::time::Instant::now() + parity_cap;
                nonfixpoint_end.min(capped)
            });
            self.discover_parity_invariants(parity_deadline);
            if self.config.verbose {
                safe_eprintln!("PDR: discover_parity_invariants took {:?}", _t7.elapsed());
            }
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // #425: Some loop-exit bounds are only inductive once parity lemmas
            // land. Retry the deferred self-inductive queue immediately so
            // bounds like `counter <= 16` can enable a second, short parity pass.
            let frame1_before_parity_retry = self.frames.get(1).map_or(0, |f| f.lemmas.len());
            self.retry_deferred_self_inductive_invariants();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }
            let frame1_after_parity_retry = self.frames.get(1).map_or(0, |f| f.lemmas.len());
            if frame1_after_parity_retry > frame1_before_parity_retry
                && !self.nonfixpoint_budget_exceeded(nonfixpoint_start, nonfixpoint_budget)
            {
                let rerun_cap = std::time::Duration::from_millis(150);
                let rerun_deadline = nonfixpoint_budget.map(|b| {
                    let nonfixpoint_end = nonfixpoint_start + b;
                    let capped = ay_core::time::Instant::now() + rerun_cap;
                    nonfixpoint_end.min(capped)
                });
                let _t7b = ay_core::time::Instant::now();
                self.discover_parity_invariants(rerun_deadline);
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: discover_parity_invariants retry after deferred-self retry took {:?}",
                        _t7b.elapsed()
                    );
                }
                if self.is_cancelled() {
                    return Some(self.finish_with_result_trace(PdrResult::Unknown));
                }
            }

            // Parity-aware bound tightening: combine parity invariants with upper bounds
            // to compute tighter bounds. E.g., A % 16 = 0 AND A < 256 => A <= 240.
            let _t8 = ay_core::time::Instant::now();
            self.tighten_bounds_with_parity();
            if self.config.verbose {
                safe_eprintln!("PDR: tighten_bounds_with_parity took {:?}", _t8.elapsed());
            }
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }
            // Conditional parity invariants: discover threshold-based parity patterns
            // e.g., (A >= 1000) => (A mod 5 = 0) when increment changes at threshold
            let _t8b = ay_core::time::Instant::now();
            self.discover_conditional_parity_invariants();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_conditional_parity_invariants took {:?}",
                    _t8b.elapsed()
                );
            }

            // Toggle-parity invariants: discover relational (mod A 2) = B where
            // A increments by odd amount and B toggles via ite(B=0,1,0). (#3211)
            let _t8c = ay_core::time::Instant::now();
            self.discover_toggle_parity_invariants();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_toggle_parity_invariants took {:?}",
                    _t8c.elapsed()
                );
            }

            // Toggle-conditional equality: when a toggle variable C alternates 0/1
            // and two counters increment in opposite phases, discover
            // (C=0 → A=B) ∧ (C≠0 → A=B+1). Solves dillig32, s_multipl_24. (#8782)
            let _t8c2 = ay_core::time::Instant::now();
            self.discover_toggle_conditional_equality_invariants();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_toggle_conditional_equality_invariants took {:?}",
                    _t8c2.elapsed()
                );
            }

            // Increment-divisibility invariants: for self-loop transitions with constant
            // increment c (|c| >= 2), discover (mod var |c|) = (init mod |c|). (#1362)
            let _t8d = ay_core::time::Instant::now();
            self.discover_increment_divisibility_invariants();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_increment_divisibility_invariants took {:?}",
                    _t8d.elapsed()
                );
            }

            // Branch-accumulator parity invariants: for disjunctive self-loop
            // transitions where every branch changes the same set of K variables
            // by ±c (symmetric increment), discover that the sum's parity is
            // preserved, and that accumulators defined as base + sum(changed_vars)
            // also preserve parity. (#1362)
            let _t8e = ay_core::time::Instant::now();
            self.discover_branch_accumulator_parity_invariants();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_branch_accumulator_parity_invariants took {:?}",
                    _t8e.elapsed()
                );
            }
        } // end parity block

        // BUG FIX #3121: Re-attempt equality discovery AFTER parity invariants.
        // For multi-predicate problems with ITE(mod ...) transitions (e.g., dillig02_m),
        // equalities like D=E are init-valid but NOT SCC-inductive without parity support.
        // The startup fixpoint loop discovers equalities before parity, so the SCC check
        // correctly rejects them. Now that parity invariants are in the frame, re-running
        // equality discovery allows the SCC check to use them.
        if !self.nonfixpoint_budget_exceeded(nonfixpoint_start, nonfixpoint_budget) {
            let _t_eq_retry = ay_core::time::Instant::now();
            self.discover_equality_invariants();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: post-parity discover_equality_invariants took {:?}",
                    _t_eq_retry.elapsed()
                );
            }
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }
            // Propagate any newly-discovered equalities to derived predicates
            self.propagate_symbolic_equalities_to_derived_predicates();
            let _propagated = self.propagate_frame1_invariants_to_users();
        }

        // Check if problem contains mod/div
        let has_mod = self.problem.clauses().iter().any(|clause| {
            clause
                .body
                .constraint
                .as_ref()
                .is_some_and(Self::contains_mod_or_div)
                || clause
                    .body
                    .predicates
                    .iter()
                    .any(|(_, args)| args.iter().any(Self::contains_mod_or_div))
                || match &clause.head {
                    crate::ClauseHead::Predicate(_, args) => {
                        args.iter().any(Self::contains_mod_or_div)
                    }
                    crate::ClauseHead::False => false,
                }
        });
        // Modular equality discovery is expensive and only useful with mod/div
        if has_mod && !self.nonfixpoint_budget_exceeded(nonfixpoint_start, nonfixpoint_budget) {
            let _t9 = ay_core::time::Instant::now();
            self.discover_modular_equality_invariants();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_modular_equality_invariants took {:?}",
                    _t9.elapsed()
                );
            }
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }
        }
        if !self.nonfixpoint_budget_exceeded(nonfixpoint_start, nonfixpoint_budget) {
            // Conditional invariants: discover phase-transition patterns
            // (pivot <= threshold => other = init) AND (pivot > threshold => other = pivot)
            let _t10 = ay_core::time::Instant::now();
            self.discover_conditional_invariants();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_conditional_invariants took {:?}",
                    _t10.elapsed()
                );
            }
            // Guarded scaled equalities: `mode = g => B - k*A = c`, for
            // accumulators whose closed form depends on a mode fixed at entry.
            // Runs beside the threshold-based pass above because the guard is a
            // latch equality rather than a phase threshold, and the consequent
            // is a SCALED relation the unguarded difference pass cannot state.
            let _t10b = ay_core::time::Instant::now();
            self.discover_guarded_scaled_equalities();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_guarded_scaled_equalities took {:?}",
                    _t10b.elapsed()
                );
            }
        }
        if self.is_cancelled() {
            return Some(self.finish_with_result_trace(PdrResult::Unknown));
        }
        if !self.nonfixpoint_budget_exceeded(nonfixpoint_start, nonfixpoint_budget) {
            // Relational invariants: discover var1 <= var2 or var1 >= var2 relationships
            let _t11 = ay_core::time::Instant::now();
            self.discover_relational_invariants();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_relational_invariants took {:?}",
                    _t11.elapsed()
                );
            }
        }
        if self.is_cancelled() {
            return Some(self.finish_with_result_trace(PdrResult::Unknown));
        }
        if !self.nonfixpoint_budget_exceeded(nonfixpoint_start, nonfixpoint_budget) {
            // Step-bounded difference: discover var_i < var_j + step from loop guard + increment patterns
            let _t12 = ay_core::time::Instant::now();
            self.discover_step_bounded_difference_invariants();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_step_bounded_difference_invariants took {:?}",
                    _t12.elapsed()
                );
            }
        }
        if self.is_cancelled() {
            return Some(self.finish_with_result_trace(PdrResult::Unknown));
        }
        if !self.nonfixpoint_budget_exceeded(nonfixpoint_start, nonfixpoint_budget) {
            // Counting invariants: discover B = k*C relationships for chained predicates
            let _t13 = ay_core::time::Instant::now();
            self.discover_counting_invariants();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_counting_invariants took {:?}",
                    _t13.elapsed()
                );
            }
        }
        if self.is_cancelled() {
            return Some(self.finish_with_result_trace(PdrResult::Unknown));
        }
        // NOTE: discover_error_implied_invariants is now part of the startup fixpoint loop
        // (see #1398) so it runs earlier and can benefit from prerequisite equalities.

        if !self.nonfixpoint_budget_exceeded(nonfixpoint_start, nonfixpoint_budget) {
            // Three-variable difference bound invariants: discover d >= b - a patterns from init
            // e.g., for init D >= B - A, derive D + A >= B as an invariant
            let _t14b = ay_core::time::Instant::now();
            self.discover_three_var_diff_bound_invariants();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_three_var_diff_bound_invariants took {:?}",
                    _t14b.elapsed()
                );
            }

            // #8782: Same-delta constant-difference invariants.
            let _t14c_sd = ay_core::time::Instant::now();
            self.discover_same_delta_difference_invariants();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_same_delta_difference_invariants took {:?}",
                    _t14c_sd.elapsed()
                );
            }
        }
        if self.is_cancelled() {
            return Some(self.finish_with_result_trace(PdrResult::Unknown));
        }

        if !self.nonfixpoint_budget_exceeded(nonfixpoint_start, nonfixpoint_budget) {
            // ITE constant propagation: when a constant argument forces an ITE condition,
            // derive the resulting constant value as an invariant for the target predicate.
            // Essential for dillig12_m where mode=0 forces SAD's first arg to be 1.
            let _t14c = ay_core::time::Instant::now();
            self.discover_ite_constant_propagation();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_ite_constant_propagation took {:?}",
                    _t14c.elapsed()
                );
            }
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // Apply external lemma hints from registered providers
            let _t_hints = ay_core::time::Instant::now();
            self.apply_lemma_hints(crate::lemma_hints::HintStage::Startup);
            if self.config.verbose {
                safe_eprintln!("PDR: apply_lemma_hints took {:?}", _t_hints.elapsed());
            }
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // Fact-clause conjunctions: some init facts are only inductive together.
            // This matters on BV-to-Bool benchmarks where control-bit literals fail
            // self-inductiveness individually but succeed as a conjunction (#5877).
            let _t14d = ay_core::time::Instant::now();
            self.discover_conjunctive_fact_clause_invariants();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_conjunctive_fact_clause_invariants took {:?}",
                    _t14d.elapsed()
                );
            }
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // Conjunctive init inequalities: some init bounds are only inductive together.
            // This helps for benchmarks like `three_dots_moving_2` where individual init bounds
            // are not self-inductive, but their conjunction (plus simpler lemmas) is.
            let _t14e = ay_core::time::Instant::now();
            self.discover_conjunctive_init_inequality_invariants();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_conjunctive_init_inequality_invariants took {:?}",
                    _t14e.elapsed()
                );
            }
        } // end ITE/hints/conjunctive block guarded by nonfixpoint budget
        if self.is_cancelled() {
            return Some(self.finish_with_result_trace(PdrResult::Unknown));
        }

        // Array-content invariant synthesis (Increment 0 telemetry + Increment 1
        // candidate emission). Both layers are independently env-gated and DEFAULT
        // OFF: with no flag set these calls return immediately after one cheap
        // boolean check, proposing nothing, so the default verdict is unchanged.
        if !self.nonfixpoint_budget_exceeded(nonfixpoint_start, nonfixpoint_budget) {
            let _t_arr = ay_core::time::Instant::now();
            self.run_array_frontier_telemetry();
            self.discover_array_content_invariants();
            if self.config.verbose {
                safe_eprintln!("PDR: array-content discovery took {:?}", _t_arr.elapsed());
            }
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }
        }

        if self.config.verbose {
            safe_eprintln!(
                "PDR: Non-fixpoint startup discovery took {:?} total (budget: {:?})",
                nonfixpoint_start.elapsed(),
                nonfixpoint_budget
            );
        }

        None
    }
}
