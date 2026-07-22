// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg(test)]
std::thread_local! {
    /// Test hook (item 5a): force `ConvergenceHealth::Stuck` once the main
    /// loop reaches the given iteration. Genuine stagnation needs many
    /// wall-clock/iteration windows, which is too slow and load-sensitive for
    /// a unit test; this hook lets tests exercise the Stuck-arm policy
    /// (give_up_on_stuck vs. default log-and-continue) deterministically.
    pub(crate) static FORCE_CONVERGENCE_STUCK_AFTER_ITERATION:
        std::cell::Cell<Option<usize>> = const { std::cell::Cell::new(None) };
}

impl PdrSolver {
    pub(in crate::pdr::solver) const BV_DISCOVERY_RERUN_BLOCKED_STATE_THRESHOLD: usize = 4;

    pub(super) fn verification_progress_signature(&self) -> VerificationProgressSignature {
        VerificationProgressSignature {
            lemma_count: self.frames.iter().map(|frame| frame.lemmas.len()).sum(),
            must_summary_count: self.reachability.must_summaries.entry_count(),
            reach_fact_count: self.reachability.reach_facts.len(),
        }
    }

    pub(super) fn note_model_verification_failure(&mut self, reason: &str) {
        let progress = self.verification_progress_signature();
        if self.verification.consecutive_unlearnable > 0
            && progress != self.verification.last_unlearnable_progress
        {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Resetting consecutive_unlearnable after learning progress ({reason}): {} -> 0 \
                     [lemmas {}->{}, must_summaries {}->{}, reach_facts {}->{}]",
                    self.verification.consecutive_unlearnable,
                    self.verification.last_unlearnable_progress.lemma_count,
                    progress.lemma_count,
                    self.verification.last_unlearnable_progress.must_summary_count,
                    progress.must_summary_count,
                    self.verification.last_unlearnable_progress.reach_fact_count,
                    progress.reach_fact_count,
                );
            }
            self.verification.consecutive_unlearnable = 0;
        }
        self.verification.last_unlearnable_progress = progress;
        self.verification.consecutive_unlearnable += 1;
        self.verification.total_model_failures += 1;
    }

    /// De-escalate generalization on near-convergence signal (#7911).
    fn maybe_de_escalate_on_convergence_signal(&mut self, old_level: usize) {
        if self.frames.len() < 3 || old_level < 2 {
            return;
        }
        if self.generalization_strategy == GeneralizationStrategy::Default
            || self.generalization_strategy == GeneralizationStrategy::Conservative
        {
            return;
        }
        let cur = self.frames[old_level].lemmas.len();
        let prev = self.frames[old_level - 1].lemmas.len();
        if cur.abs_diff(prev) <= 3 {
            self.de_escalate_generalization_strategy();
        }
    }

    /// Solve the CHC problem
    pub fn solve(&mut self) -> PdrResult {
        // Hard wall-clock budget enforcement at the SMT boundary: every
        // check_sat on this thread (including startup discovery's deep
        // ITE/OR case-split recursion, which has no cancellation checks)
        // clamps to this deadline. Without it, a 3s engine budget can
        // overrun by an order of magnitude (lustre-class latency bug).
        let _smt_deadline_guard = self
            .config
            .solve_timeout
            .map(crate::smt::ScopedSmtDeadline::install);

        // Reset the SMT-layer no-progress circuit breaker for the duration of
        // this solve (restored on drop, so nested/sequential solves on the same
        // thread compose correctly). Without the reset a breaker that tripped in
        // a prior solve on a reused thread would wrongly cancel this fresh solve.
        let _no_progress_guard = crate::smt::ScopedNoProgressBreaker::new();

        // Initialization: validate problem, check init safety, set up must-summaries,
        // run startup discovery. Returns early if any phase proves safe/unsafe.
        if let Some(result) = self.solve_init() {
            return result;
        }

        // Main PDR loop
        //
        // Apply a tighter per-query SMT timeout during the main blocking loop. Startup
        // discovery already has a 10s per-query cap (above). The 5s cap here prevents
        // individual blocking queries from stalling the portfolio for minutes.
        let _smt_timeout_guard =
            if self.config.cancellation_token.is_some() || self.config.solve_timeout.is_some() {
                Some(
                    self.smt
                        .scoped_check_timeout(Some(std::time::Duration::from_secs(5))),
                )
            } else {
                None
            };
        // Reset convergence monitor at solve-loop entry (startup discovery may
        // have consumed wall-clock time that shouldn't count against frame stall).
        self.convergence = ConvergenceMonitor::new();
        self.terminated_by_stagnation = false;
        self.lemma_quality.reset_all();
        let has_budget =
            self.config.cancellation_token.is_some() || self.config.solve_timeout.is_some();

        let mut spurious_count = 0usize;
        while self.frames.len() <= self.config.max_frames {
            // Check cancellation or memory budget (#2769)
            if self.is_cancelled() {
                if self.config.verbose {
                    safe_eprintln!("PDR: Cancelled by portfolio or memory limit");
                }
                self.pdr_trace_conservative_fail(
                    "solve_cancelled",
                    serde_json::json!({
                        "iterations": self.iterations,
                        "frames": self.frames.len(),
                    }),
                    None,
                );
                return self.finish_with_result_trace(PdrResult::Unknown);
            }

            self.iterations += 1;

            // Frame structure invariant: frames[0] is init, frames[k] for k >= 1
            // are PDR levels. Must have at least 2 frames. (#4757)
            debug_assert!(
                self.frames.len() >= 2,
                "BUG: Main loop requires at least 2 frames, got {}",
                self.frames.len()
            );
            // Iteration counter should match actual loop count.
            debug_assert!(
                self.iterations > 0,
                "BUG: iterations counter should be positive in main loop"
            );

            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Iteration {}, {} frames",
                    self.iterations,
                    self.frames.len()
                );
            }
            // Convergence monitoring (#7906): graduated stagnation detection.
            let total_lemmas_now: usize = self.frames.iter().map(|f| f.lemmas.len()).sum();

            // Global memory GC (#8601): evict lemmas/must-summaries when over budget.
            self.gc_global_lemmas(total_lemmas_now);
            self.gc_global_must_summaries();

            // Update live progress snapshot for observer consumption (#8155).
            // The progress thread reads this on its 5-second cadence to emit
            // rich progress lines with frame count and lemma count.
            if let Some(snap) = &self.config.progress_snapshot {
                // Recompute after GC may have evicted lemmas.
                let total_after_gc: usize = self.frames.iter().map(|f| f.lemmas.len()).sum();
                snap.update_pdr_progress(self.frames.len() as u64, total_after_gc as u64);
            }

            let problem_hint = self.problem_size_hint;
            let stagnation_response = self.convergence.check_stagnation_graduated(
                self.iterations,
                total_lemmas_now,
                self.frames.len(),
                has_budget,
                &problem_hint,
            );
            if stagnation_response != StagnationResponse::None {
                self.lemma_quality.check_quality();
            }
            let health = self
                .convergence
                .assess_health(stagnation_response, &self.lemma_quality);
            #[cfg(test)]
            let health = FORCE_CONVERGENCE_STUCK_AFTER_ITERATION
                .with(std::cell::Cell::get)
                .filter(|&after| self.iterations >= after)
                .map_or(health, |_| {
                    // Model the robust window-based stagnation verdict the
                    // give-up arm requires (the wall-clock fast path leaves
                    // this at 0 and must NOT trigger an early give-up).
                    self.convergence.consecutive_stagnant_windows =
                        self.convergence.consecutive_stagnant_windows.max(2);
                    ConvergenceHealth::Stuck
                });
            match health {
                ConvergenceHealth::Healthy => {}
                ConvergenceHealth::Slowing => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Convergence slowing at iteration {} ({}s elapsed, stagnant_windows={}, low_quality_windows={})",
                            self.iterations, self.convergence.elapsed().as_secs(),
                            self.convergence.consecutive_stagnant_windows,
                            self.lemma_quality.consecutive_low_quality_windows,
                        );
                    }
                    if !self.restart.stuck_hints_applied {
                        self.restart.stuck_hints_applied = true;
                        self.apply_lemma_hints(crate::lemma_hints::HintStage::Stuck);
                    }
                }
                ConvergenceHealth::Stagnating => {
                    if self.escalate_generalization_strategy() {
                        self.convergence.note_generalization_escalation(
                            self.iterations,
                            total_lemmas_now,
                            self.frames.len(),
                        );
                        self.lemma_quality.reset_all();
                    } else if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Stagnating at max escalation level {} iter {}",
                            self.generalization_escalation_level,
                            self.iterations,
                        );
                    }
                }
                ConvergenceHealth::Stuck => {
                    self.terminated_by_stagnation = true;
                    // Opt-in early hopeless self-report (wishlist item 5a):
                    // only when a scheduler with another lane to try set
                    // give_up_on_stuck. Returning Unknown early releases the
                    // remaining budget to the next engine/stage instead of
                    // burning it on a provably stagnating search. SOUND: an
                    // early Unknown can never flip a Safe/Unsafe verdict.
                    // Honor Stuck only when BOTH hold: (a) the ITERATION-WINDOW
                    // stagnation verdict (consecutive_stagnant_windows >= 2 —
                    // measured in solver work, so valid under CPU starvation;
                    // the wall-clock frame-stall fast path leaves it at 0 and
                    // fires transiently on loaded machines), and (b) ZERO frame
                    // growth (never left the initial frame) — the same
                    // "provably redundant to retry" criterion the stage
                    // rotation uses (`predecessor_stage_stuck_no_growth`).
                    // Lemma-count windows legitimately stall mid-flight during
                    // heavy generalization on hard-but-solvable problems
                    // (pdr_s_multipl_12_safe went 54s-pass -> 120s-timeout when
                    // the give-up abandoned such a stage), so a search that has
                    // advanced frames keeps the default log-and-continue below.
                    if self.config.give_up_on_stuck
                        && self.convergence.consecutive_stagnant_windows >= 2
                        && self.frames.len() <= 2
                    {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Convergence monitor reports stuck at iteration {} ({}s elapsed, {} stagnant windows) — giving up (give_up_on_stuck)",
                                self.iterations, self.convergence.elapsed().as_secs(),
                                self.convergence.consecutive_stagnant_windows,
                            );
                        }
                        self.pdr_trace_conservative_fail(
                            "solve_stuck_gave_up",
                            serde_json::json!({
                                "iterations": self.iterations,
                                "frames": self.frames.len(),
                                "stagnant_windows": self.convergence.consecutive_stagnant_windows,
                                "elapsed_secs": self.convergence.elapsed().as_secs(),
                            }),
                            None,
                        );
                        return self.finish_with_result_trace(PdrResult::Unknown);
                    }
                    // DEFAULT: do NOT return Unknown early. The solve_timeout
                    // already enforces the total budget. Premature stagnation
                    // abort causes regressions under high system load where
                    // wall-clock stall detection fires before the solver has
                    // had enough CPU time. Log but continue — PDR may still
                    // converge once escalation strategies take effect.
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Convergence monitor reports stuck at iteration {} ({}s elapsed, {} stagnant windows) — continuing",
                            self.iterations, self.convergence.elapsed().as_secs(),
                            self.convergence.consecutive_stagnant_windows,
                        );
                    }
                    // Reset stagnation windows so we don't keep re-triggering
                    self.convergence.consecutive_stagnant_windows = 0;
                }
            }

            if self.iterations > self.config.max_iterations {
                if self.config.verbose {
                    safe_eprintln!("PDR: Exceeded max iterations");
                }
                self.pdr_trace_conservative_fail(
                    "solve_max_iterations_exceeded",
                    serde_json::json!({
                        "iterations": self.iterations,
                        "max_iterations": self.config.max_iterations,
                        "frames": self.frames.len(),
                    }),
                    None,
                );
                return self.finish_with_result_trace(PdrResult::Unknown);
            }

            // Luby restarts (#1270): when lemma growth stalls, restart to escape local minima
            if self.config.use_restarts
                && self.restart.lemmas_since_restart > self.restart.restart_threshold
            {
                // Pop queue until root (keep only level 0 obligations)
                // Z3 Spacer: while (!m_pob_queue.is_root(*m_pob_queue.top())) { m_pob_queue.pop(); }
                if self.config.use_level_priority {
                    // Priority heap: remove all non-root POBs
                    let root_pobs: Vec<_> = std::mem::take(&mut self.obligations.heap)
                        .into_vec()
                        .into_iter()
                        .filter(|p| p.0.level == 0)
                        .collect();
                    for pob in root_pobs {
                        self.obligations.heap.push(pob);
                    }
                } else {
                    // Deque: remove all non-root POBs
                    self.obligations.deque.retain(|pob| pob.level == 0);
                }

                // Update Luby index and threshold
                self.restart.luby_index += 1;
                self.restart.restart_threshold = (luby(self.restart.luby_index) as usize)
                    * self.config.restart_initial_threshold;
                self.restart.lemmas_since_restart = 0;
                self.restart.restart_count += 1;
                self.clear_restart_caches();

                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Restart #{} at iteration {} (next threshold: {})",
                        self.restart.restart_count,
                        self.iterations,
                        self.restart.restart_threshold
                    );
                }

                // #2393: On first restart, apply expanded Stuck-stage hints.
                // ModResidueHintProvider enumerates more residue values at Stuck
                // (20 vs 10 at Startup), which helps modular arithmetic benchmarks
                // like const_mod_3, dillig02_m, half_true_modif_m.
                if !self.restart.stuck_hints_applied {
                    self.restart.stuck_hints_applied = true;
                    self.apply_lemma_hints(crate::lemma_hints::HintStage::Stuck);
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Applied Stuck-stage lemma hints at restart #{}",
                            self.restart.restart_count
                        );
                    }
                }

                // Publish learned lemmas to cooperative blackboard (#7910).
                // At each restart, share our frame lemmas with other engines.
                self.publish_to_blackboard();
            }

            // Try to strengthen current frame
            let strengthen_result = self.strengthen();
            // Track strengthen outcome for convergence monitoring.
            let productive = matches!(
                strengthen_result,
                StrengthenResult::Safe | StrengthenResult::Continue
            );
            self.convergence.note_strengthen(productive);
            match strengthen_result {
                StrengthenResult::Safe => {
                    // Check for fixed point
                    if let Some(mut model) = self.check_fixed_point() {
                        // SOUNDNESS (#5745, #5970): Model verification before returning Safe.
                        //
                        // convergence_proven: Frame convergence proved inductiveness of the
                        // full frame conjunction. Use query-only verification (skip
                        // transition inductiveness, only check error blocking). Error
                        // blocking is NOT implied by convergence because
                        // propagate_tight_bound_constants can weaken the model formula
                        // by substituting away variables. (#5970, #7410)
                        //
                        // individually_inductive: Each lemma was verified self-inductive.
                        // Use query-only verification (checks error-blocking only). (#7410)
                        //
                        // Other models: full verify_model + verify_model_fresh.
                        let verified = if model.individually_inductive {
                            self.verify_model_query_only(&model)
                        } else {
                            self.verify_model(&model)
                        };
                        if !verified {
                            self.note_model_verification_failure("check_fixed_point verify_model");
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: check_fixed_point returned model that fails verify_model(); \
                                     consecutive_unlearnable={}, total_model_failures={}, continuing",
                                    self.verification.consecutive_unlearnable,
                                    self.verification.total_model_failures,
                                );
                            }
                            // Don't return Safe with invalid model - continue strengthening
                        } else if !{
                            if model.individually_inductive {
                                // #5970: query-only fresh verification for per-lemma proven models.
                                self.verify_model_fresh_query_only(&model)
                            } else {
                                // SOUNDNESS (#5922): Fresh-context confirmation.
                                self.verify_model_fresh(&model)
                            }
                        } {
                            self.note_model_verification_failure(
                                "check_fixed_point fresh-context verification",
                            );
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: model passes warm verify_model but fails fresh-context \
                                     verification (#5922); continuing"
                                );
                            }
                        } else {
                            // Reset consecutive counter on successful verification
                            self.verification.consecutive_unlearnable = 0;
                            // SOUNDNESS (#5922): Save verified model before simplification.
                            // The model was already verified at line 341. If simplification
                            // breaks it, we can fall back to this known-good version.
                            let verified_model = model.clone();
                            // Simplify the invariant (Z3 Spacer's unconditional solve-completion cleanup)
                            let simp = self.simplify_model(&mut model);
                            // Re-verify when simplification modified the model (#5805, #5922).
                            if simp.modified() && !self.verify_model(&model) {
                                if simp.free_vars_sanitized {
                                    // Free-var sanitization means the pre-simplification model
                                    // had undeclared variables — it may be fundamentally
                                    // invalid (#5805). Do NOT fall back; continue searching.
                                    self.note_model_verification_failure(
                                        "simplified fixed-point model free-var sanitization",
                                    );
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: simplified model fails re-verification after \
                                             free-variable sanitization; continuing"
                                        );
                                    }
                                } else {
                                    // Only redundancy removal — pre-simplification model is
                                    // known valid (verified at line 341). Fall back (#5922).
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: simplified model fails re-verification after \
                                             redundancy removal; falling back to pre-simplification model"
                                        );
                                    }
                                    // #4751: continue searching on strict-validation demotion.
                                    if let Some(result) = self.finish_safe_or_continue(
                                        verified_model,
                                        "fixed-point pre-simplification fallback",
                                    ) {
                                        return result;
                                    }
                                    self.note_model_verification_failure(
                                        "fixed-point model strict final validation",
                                    );
                                }
                            } else {
                                // #4751: continue searching on strict-validation demotion.
                                if let Some(result) =
                                    self.finish_safe_or_continue(model, "fixed-point model")
                                {
                                    return result;
                                }
                                self.note_model_verification_failure(
                                    "fixed-point model strict final validation",
                                );
                            }
                        }
                    }

                    // Part of #2059: If check_fixed_point fails (frames don't converge due to
                    // non-pushable lemmas like scaled bounds), try direct safety proof.
                    // The frame[1] invariants may already prove all error states unreachable
                    // even without frame convergence.
                    if let Some(mut model) = self.try_main_loop_direct_safety_proof() {
                        // #5877: For strictly self-inductive models, skip fresh-context
                        // verification. Each lemma was individually verified via strict
                        // self-inductiveness (no frame strengthening). The conjunction
                        // of strictly self-inductive lemmas is inductive by construction.
                        // Fresh-context verification can fail on complex disjunctive
                        // transitions where the SMT solver struggles with the full
                        // conjunction (ITE case-split handles these per-lemma).
                        let skip_fresh = model.individually_inductive;
                        // SOUNDNESS (#5922): Fresh-context confirmation (unless strictly self-inductive).
                        if !skip_fresh && !self.verify_model_fresh(&model) {
                            self.note_model_verification_failure(
                                "direct-proof fresh-context verification",
                            );
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: direct-proof model passes warm verify but fails \
                                     fresh-context verification (#5922); continuing"
                                );
                            }
                        } else {
                            // SOUNDNESS (#5922): Save model before simplification.
                            let original_model = model.clone();
                            // Simplify the invariant (Z3 Spacer's unconditional solve-completion cleanup)
                            let simp = self.simplify_model(&mut model);
                            // Re-verify when simplification modified the model (#5805, #5922).
                            if simp.modified() && !self.verify_model(&model) {
                                if simp.free_vars_sanitized {
                                    // Free-var sanitization — pre-simplification model may be
                                    // fundamentally invalid (#5805). Continue searching.
                                    self.note_model_verification_failure(
                                        "simplified direct-proof model free-var sanitization",
                                    );
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: simplified direct-proof model fails re-verification \
                                             after free-variable sanitization; continuing"
                                        );
                                    }
                                } else {
                                    // Only redundancy removal — fall back to original (#5922).
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: simplified direct-proof model fails re-verification; \
                                             falling back to pre-simplification model"
                                        );
                                    }
                                    // #4751: continue searching on strict-validation demotion.
                                    if let Some(result) = self.finish_safe_or_continue(
                                        original_model,
                                        "direct-proof pre-simplification fallback",
                                    ) {
                                        return result;
                                    }
                                    self.note_model_verification_failure(
                                        "direct-proof model strict final validation",
                                    );
                                }
                            } else {
                                // #4751: continue searching on strict-validation demotion.
                                if let Some(result) =
                                    self.finish_safe_or_continue(model, "direct-proof model")
                                {
                                    return result;
                                }
                                self.note_model_verification_failure(
                                    "direct-proof model strict final validation",
                                );
                            }
                        }
                    }
                    // Check if we're stuck in model verification failures without
                    // learning progress. This catches retry-without-learning loops
                    // while allowing continued search when frames/must-summaries keep
                    // growing between failed verification attempts.
                    const MAX_UNLEARNABLE_FAILURES: usize = 10;
                    if self.verification.consecutive_unlearnable >= MAX_UNLEARNABLE_FAILURES {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Giving up after {} consecutive unlearnable verification failures",
                                self.verification.consecutive_unlearnable
                            );
                        }
                        self.pdr_trace_conservative_fail(
                            "solve_consecutive_unlearnable_failures",
                            serde_json::json!({
                                "consecutive_unlearnable_failures": self.verification.consecutive_unlearnable,
                                "max_unlearnable_failures": MAX_UNLEARNABLE_FAILURES,
                                "iterations": self.iterations,
                                "frames": self.frames.len(),
                                "verification_progress": {
                                    "lemmas": self.verification.last_unlearnable_progress.lemma_count,
                                    "must_summaries": self.verification.last_unlearnable_progress.must_summary_count,
                                    "reach_facts": self.verification.last_unlearnable_progress.reach_fact_count,
                                },
                            }),
                            None,
                        );
                        return self.finish_with_result_trace(PdrResult::Unknown);
                    }
                    // Add new frame and continue
                    let old_level = self.frames.len() - 1;
                    self.push_frame();
                    self.convergence.note_frame_advance();
                    self.maybe_de_escalate_on_convergence_signal(old_level);
                    // Propagate must-summaries forward to the new level
                    self.propagate_must_summaries_forward(old_level - 1, old_level);
                    // Re-run kernel-based affine discovery after must-summaries accumulate.
                    //
                    // Some affine invariants are only visible after a few loop iterations
                    // (reachable states), not from degenerate init samples. (#1995)
                    if !self.is_quick_check_mode()
                        && old_level > 0
                        && old_level <= 5
                        && (old_level.is_multiple_of(3) || old_level == 5)
                    {
                        let max_check = old_level.min(5);
                        let has_reachable_summaries = (1..=max_check)
                            .any(|l| self.reachability.must_summaries.has_any_at_level(l));
                        if has_reachable_summaries {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Re-running affine kernel discovery after must-summary propagation to level {}",
                                    old_level
                                );
                            }
                            self.discover_affine_invariants_via_kernel(None);
                            self.propagate_affine_invariants_to_derived_predicates();
                        }
                    }
                    // Periodically re-run ITE constant propagation to leverage learned invariants
                    // This enables proving ITE branch constants using newly-learned predicate invariants
                    if self.iterations.is_multiple_of(5) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Re-running ITE constant propagation at iteration {}",
                                self.iterations
                            );
                        }
                        self.discover_ite_constant_propagation();
                    }
                }
                StrengthenResult::Unsafe(cex) => {
                    if self.config.verbose {
                        safe_eprintln!("PDR: Found counterexample with {} steps", cex.steps.len());
                    }
                    // Verify counterexample is forward-reachable (soundness-critical #1288)
                    match self.verify_counterexample(&cex) {
                        CexVerificationResult::Valid => {
                            return self.finish_with_result_trace(PdrResult::Unsafe(cex));
                        }
                        CexVerificationResult::Unknown => {
                            // SOUNDNESS FIX (#1288): Cannot return Unsafe when verification
                            // is inconclusive. Return Unknown to avoid unsound results.
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Counterexample verification inconclusive (Unknown)"
                                );
                            }
                            self.pdr_trace_conservative_fail(
                                "solve_cex_verification_inconclusive",
                                serde_json::json!({
                                    "cex_steps": cex.steps.len(),
                                    "iterations": self.iterations,
                                    "frames": self.frames.len(),
                                }),
                                None,
                            );
                            return self.finish_with_result_trace(PdrResult::Unknown);
                        }
                        CexVerificationResult::Spurious => {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Counterexample failed verification (spurious)"
                                );
                            }
                            // Spurious counterexample handling with Z3 Spacer-style weakness mechanism (#1664).
                            // Instead of a simple global counter, we track weakness per (predicate, state).
                            // This allows retrying the same spurious state with different abstraction levels
                            // before giving up, mirroring Z3's POB weakness bump on derivation failure.

                            // Extract root state from witness for weakness tracking
                            let root_info = cex.witness.as_ref().and_then(|w| {
                                w.entries
                                    .first()
                                    .map(|e| (e.predicate, e.state.structural_hash()))
                            });

                            // Check/bump weakness for this specific (predicate, state) pair
                            let should_give_up = if let Some((pred, state_hash)) = root_info {
                                let key = (pred, state_hash);
                                let weakness = self.bump_spurious_cex_weakness(key);
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: Spurious CEX weakness for pred {} = {}",
                                        pred.index(),
                                        weakness
                                    );
                                }
                                // Give up on this (pred, state) after MAX_WEAKNESS retries
                                weakness > ProofObligation::MAX_WEAKNESS
                            } else {
                                // No witness info - fall back to global counter
                                true
                            };

                            if should_give_up {
                                spurious_count += 1;
                            }

                            // Global safety limit to prevent infinite loops
                            // Limit raised from 100 to 500 per the development design notes
                            if spurious_count > 500 {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: Too many spurious counterexamples ({}), giving up",
                                        spurious_count
                                    );
                                }
                                self.pdr_trace_conservative_fail(
                                    "solve_spurious_cex_limit",
                                    serde_json::json!({
                                        "spurious_count": spurious_count,
                                        "iterations": self.iterations,
                                        "frames": self.frames.len(),
                                    }),
                                    None,
                                );
                                return self.finish_with_result_trace(PdrResult::Unknown);
                            }

                            // Learn from the spurious CEX: bound negation, ITE blocking,
                            // affine discovery, concrete value blocking (see spurious_cex.rs).
                            self.learn_from_spurious_cex(&cex);
                            // Continue searching
                        }
                    }
                }
                StrengthenResult::Unknown => {
                    if self.config.verbose {
                        safe_eprintln!("PDR: Strengthen returned Unknown");
                    }
                    return self.finish_with_result_trace(PdrResult::Unknown);
                }
                StrengthenResult::Continue => {
                    // Increase the bound and continue. This is used when must-summary reachability
                    // is enabled and we can't block the root query state at the current level, but
                    // a concrete counterexample may appear at a deeper level.
                    let old_level = self.frames.len() - 1;
                    self.push_frame();
                    self.convergence.note_frame_advance();
                    self.maybe_de_escalate_on_convergence_signal(old_level);
                    self.propagate_must_summaries_forward(old_level - 1, old_level);
                    // Re-run kernel-based affine discovery after must-summaries accumulate
                    // (matches the `Safe` case).
                    if !self.is_quick_check_mode()
                        && old_level > 0
                        && old_level <= 5
                        && (old_level.is_multiple_of(3) || old_level == 5)
                    {
                        let max_check = old_level.min(5);
                        let has_reachable_summaries = (1..=max_check)
                            .any(|l| self.reachability.must_summaries.has_any_at_level(l));
                        if has_reachable_summaries {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Re-running affine kernel discovery after must-summary propagation to level {}",
                                    old_level
                                );
                            }
                            self.discover_affine_invariants_via_kernel(None);
                            self.propagate_affine_invariants_to_derived_predicates();
                        }
                    }
                    // Periodically re-run ITE constant propagation to leverage learned invariants
                    // (matches the `Safe` case).
                    if self.iterations.is_multiple_of(5) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Re-running ITE constant propagation at iteration {}",
                                self.iterations
                            );
                        }
                        self.discover_ite_constant_propagation();
                    }
                }
            }
        }

        if self.config.verbose {
            safe_eprintln!("PDR: Exceeded max frames");
        }
        self.pdr_trace_conservative_fail(
            "solve_max_frames_exceeded",
            serde_json::json!({
                "frames": self.frames.len(),
                "max_frames": self.config.max_frames,
                "iterations": self.iterations,
            }),
            None,
        );
        self.finish_with_result_trace(PdrResult::Unknown)
    }

    /// Global lemma budget GC (#8601): evict lemmas across all frames when
    /// total count exceeds `MAX_GLOBAL_LEMMAS`.
    ///
    /// Strategy (Z3 Spacer-inspired):
    /// 1. Run syntactic bound subsumption on each frame with >100 lemmas
    /// 2. If still over budget, evict oldest lemmas from the largest frames
    ///
    /// Skips frame[0] (init frame) which is typically small and critical.
    fn gc_global_lemmas(&mut self, total_lemmas: usize) {
        if total_lemmas <= MAX_GLOBAL_LEMMAS {
            return;
        }

        tracing::info!(
            total_lemmas,
            budget = MAX_GLOBAL_LEMMAS,
            over_budget = total_lemmas - MAX_GLOBAL_LEMMAS,
            "PDR: global lemma GC triggered"
        );
        if self.config.verbose {
            safe_eprintln!(
                "PDR: global lemma cap hit ({total_lemmas} > {MAX_GLOBAL_LEMMAS}); running sound GC"
            );
        }
        if self.is_cancelled() {
            tracing::warn!(
                total_lemmas,
                budget = MAX_GLOBAL_LEMMAS,
                "PDR: global lemma cap hit while cancellation/deadline is active"
            );
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: global lemma cap hit but cancellation/deadline is active; returning Unknown"
                );
            }
            return;
        }

        let over_budget = total_lemmas - MAX_GLOBAL_LEMMAS;
        let mut reclaimed = 0usize;

        // Phase 1: Syntactic subsumption on frames with >100 lemmas (cheap, no SMT).
        // Skip frame[0] (init constraints).
        for i in 1..self.frames.len() {
            if self.is_cancelled() {
                tracing::warn!(
                    frame = i,
                    "PDR: global lemma GC interrupted during subsumption phase"
                );
                return;
            }
            if self.frames[i].lemmas.len() > 100 {
                reclaimed += self.frames[i].subsume_redundant_bounds();
            }
        }

        if reclaimed >= over_budget {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Global lemma GC: reclaimed {reclaimed} via subsumption (budget: {MAX_GLOBAL_LEMMAS})"
                );
            }
            return;
        }

        // Phase 2: Evict oldest lemmas from the largest frames until under budget.
        // This is sound: removing learned lemmas weakens over-approximation frames
        // and may lose progress, but cannot create a false Safe/Unsafe result.
        // Build (frame_index, lemma_count) sorted by count descending.
        let mut remaining = over_budget - reclaimed;
        let mut frame_sizes: Vec<(usize, usize)> = self
            .frames
            .iter()
            .enumerate()
            .skip(1) // Skip frame[0]
            .map(|(i, f)| (i, f.lemmas.len()))
            .filter(|(_, len)| *len > 0)
            .collect();
        frame_sizes.sort_unstable_by_key(|frame| std::cmp::Reverse(frame.1));

        for (frame_idx, frame_len) in &frame_sizes {
            if remaining == 0 {
                break;
            }
            if self.is_cancelled() {
                tracing::warn!(
                    frame = *frame_idx,
                    remaining,
                    "PDR: global lemma GC interrupted during eviction phase"
                );
                return;
            }
            // Evict proportionally: larger frames give up more. At least 1.
            let share = (remaining * frame_len / total_lemmas.max(1))
                .max(1)
                .min(remaining);
            let evicted = self.frames[*frame_idx].evict_oldest_n(share);
            remaining = remaining.saturating_sub(evicted);
            reclaimed += evicted;
        }

        if self.config.verbose {
            safe_eprintln!(
                "PDR: Global lemma GC: reclaimed {reclaimed} lemmas (budget: {MAX_GLOBAL_LEMMAS})"
            );
        }
        if remaining > 0 {
            tracing::warn!(
                remaining,
                total_lemmas,
                budget = MAX_GLOBAL_LEMMAS,
                "PDR: global lemma GC could not reclaim enough non-init lemmas"
            );
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Global lemma GC: {remaining} lemmas remain over budget after sound eviction"
                );
            }
        }
    }

    /// Global must-summary GC (#8601): evict entries when total count exceeds
    /// the global cap.
    fn gc_global_must_summaries(&mut self) {
        let evicted = self.reachability.must_summaries.gc_if_over_global_budget();
        if evicted > 0 && self.config.verbose {
            safe_eprintln!("PDR: Global must-summary GC: evicted {evicted} entries");
        }
    }
}
