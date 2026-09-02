// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Alternative engine methods for the adaptive portfolio solver.
//!
//! Solve-trivial fast path, K-induction, structural synthesis, and
//! budget-aware alternative engine dispatch.

use crate::adaptive::AdaptivePortfolio;
use crate::adaptive_decision_log::DecisionEntry;
use crate::bmc::BmcConfig;
use crate::classifier::{ProblemClassifier, ProblemFeatures};
use crate::engine_config::ChcEngineConfig;
use crate::engine_result::ValidationEvidence;
use crate::failure_analysis::{FailureAnalysis, FailureGuide};
use crate::kind::{KindConfig, KindResult, KindSolver};
use crate::pdr::{InvariantModel, PdrConfig, PdrResult, PdrSolver, PredicateInterpretation};
use crate::portfolio::{EngineConfig, PortfolioConfig, PortfolioResult, PreprocessSummary};
use crate::single_loop::SingleLoopTransformation;
use crate::synthesis::{
    StructuralSynthesizer, SynthesisPattern, SynthesisResult, SynthesizedInvariant,
};
use crate::{ChcExpr, ChcVar};
use ay_core::time::Instant;
use ay_sat::TlaTraceable;
use std::time::Duration;

const SHALLOW_UNSAFE_BMC_MAX_DEPTH: usize = 8;

/// Extra allowance, beyond the direct-Kind probe budget, reserved for
/// validating a proof Kind already found (fresh cross-check, init/query
/// verification, original-clause validation). See `KindConfig::validation_grace`.
const KIND_VALIDATION_GRACE: Duration = Duration::from_secs(3);

/// Inc-16 S1b front-probe clamp parameters: stop the single-pred TS probe
/// once this depth has been verified cex-free...
const FRONT_PROBE_CLAMP_DEPTH: usize = 8;
/// ...AND this much wall-clock has elapsed. See `BmcConfig::ts_probe_clamp`.
const FRONT_PROBE_CLAMP_AFTER: Duration = Duration::from_secs(9);

/// Kill switch for the inc-16 S1b front-probe clamp: `AY_FRONT_PROBE_CLAMP=0`
/// restores the unclamped probe (full ~25%-of-remaining budget).
fn front_probe_clamp_enabled() -> bool {
    // B27: CLI-owned; env retired.
    crate::ab_switches::get().front_probe_clamp
}

impl AdaptivePortfolio {
    /// Try the ADT/array nullary-fact unsafe prepass.
    ///
    /// This route is intentionally narrower than the generic shallow BMC probe:
    /// it only handles a nullary query marker reached by a satisfiable
    /// ADT+array fact, and it validates the constructed witness with the
    /// standard PDR counterexample verifier before returning it.
    pub(crate) fn try_adt_array_nullary_unsafe_prepass(
        &self,
        deadline: Option<Instant>,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        if self.budget_exhausted(deadline) {
            return None;
        }

        let start = Instant::now();
        let remaining = self
            .remaining_budget(deadline)
            .unwrap_or(Duration::from_secs(5));
        let sat_budget = remaining.min(Duration::from_secs(2));
        if sat_budget < Duration::from_millis(10) {
            return None;
        }

        let candidate =
            match crate::adt_array_nullary::try_build_counterexample(&self.problem, sat_budget) {
                Ok(candidate) => candidate,
                Err(outcome) => {
                    if !matches!(
                        outcome,
                        crate::adt_array_nullary::NullaryAdtArrayOutcome::NotApplicable
                    ) {
                        self.decision_log.log_decision(DecisionEntry {
                            stage: "adt_array_nullary_unsafe_prepass",
                            gate_result: false,
                            gate_reason:
                                "ADT-array nullary fact/query route did not produce a witness"
                                    .to_string(),
                            budget_secs: sat_budget.as_secs_f64(),
                            elapsed_secs: start.elapsed().as_secs_f64(),
                            result: outcome.as_str(),
                            lemmas_learned: 0,
                            max_frame: 0,
                        });
                    }
                    return None;
                }
            };

        let validation_budget = self
            .remaining_budget(deadline)
            .unwrap_or(Duration::from_secs(5))
            .min(Duration::from_secs(5));
        let validated = crate::adt_array_nullary::validate_counterexample(
            &self.problem,
            &candidate.cex,
            validation_budget,
            self.config.verbose,
        );
        let result = if validated {
            crate::adt_array_nullary::NullaryAdtArrayOutcome::ValidationAccepted
        } else {
            crate::adt_array_nullary::NullaryAdtArrayOutcome::ValidationRejected
        };

        self.decision_log.log_decision(DecisionEntry {
            stage: "adt_array_nullary_unsafe_prepass",
            gate_result: validated,
            gate_reason: format!(
                "ADT/array DAG clause {} reaches query {} through predicate {}",
                candidate.source_clause,
                candidate.query_clause,
                candidate.predicate.index()
            ),
            budget_secs: (sat_budget + validation_budget).as_secs_f64(),
            elapsed_secs: start.elapsed().as_secs_f64(),
            result: result.as_str(),
            lemmas_learned: 0,
            max_frame: 0,
        });

        if validated {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: ADT/array DAG unsafe prepass validated clause {} -> query {}",
                    candidate.source_clause,
                    candidate.query_clause
                );
            }
            Some((
                PortfolioResult::Unsafe(candidate.cex),
                ValidationEvidence::CounterexampleVerification,
            ))
        } else {
            None
        }
    }

    /// Try a tiny constructive BMC probe for acyclic fact-to-query bugs.
    ///
    /// Several CHC-COMP front-end rows contain only a handful of Horn rules
    /// where a fact reaches `false` through a short acyclic relation chain. PDR can
    /// spend its entire small competition slice looking for an invariant, while
    /// BMC can produce a concrete derivation immediately. Keep this admission
    /// narrow: the prepass is bug-finding only, never claims safety, and any
    /// non-Unsafe result falls through to the normal adaptive portfolio.
    pub(crate) fn try_shallow_unsafe_bmc_prepass(
        &self,
        features: &ProblemFeatures,
        deadline: Option<Instant>,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        if features.num_queries == 0
            || features.num_facts == 0
            || features.has_cycles
            || features.num_clauses > 12
            || features.dag_depth > SHALLOW_UNSAFE_BMC_MAX_DEPTH
        {
            return None;
        }
        if self.budget_exhausted(deadline) {
            return None;
        }

        let remaining = self
            .remaining_budget(deadline)
            .unwrap_or(Duration::from_millis(250));
        let budget = remaining.min(Duration::from_millis(250));
        if budget < Duration::from_millis(5) {
            return None;
        }

        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: trying shallow BMC unsafe prepass ({} clauses, depth {}, budget {:.3}s)",
                features.num_clauses,
                features.dag_depth.min(SHALLOW_UNSAFE_BMC_MAX_DEPTH),
                budget.as_secs_f64(),
            );
        }

        let max_depth = features
            .dag_depth
            .saturating_add(1)
            .clamp(1, SHALLOW_UNSAFE_BMC_MAX_DEPTH);
        let config = BmcConfig::default()
            .with_max_depth(max_depth)
            .with_time_budget(budget)
            .with_per_depth_timeout(budget)
            .with_verbose(self.config.verbose);
        let bmc = crate::bmc::BmcSolver::new(self.problem.clone(), config);
        let start = Instant::now();
        let result = bmc.solve();
        let result_label = Self::result_to_str(&result);
        self.decision_log.log_decision(DecisionEntry {
            stage: "shallow_bmc_unsafe_prepass",
            gate_result: matches!(result, PortfolioResult::Unsafe(_)),
            gate_reason: "small acyclic fact/query bug-finding probe".to_string(),
            budget_secs: budget.as_secs_f64(),
            elapsed_secs: start.elapsed().as_secs_f64(),
            result: result_label,
            lemmas_learned: 0,
            max_frame: 0,
        });

        match result {
            PortfolioResult::Unsafe(cex) => Some((
                PortfolioResult::Unsafe(cex),
                ValidationEvidence::BmcCounterexample,
            )),
            PortfolioResult::Safe(_)
            | PortfolioResult::Unknown
            | PortfolioResult::NotApplicable => None,
        }
    }

    /// Datatype-aware bounded BMC refutation pre-strategy route (#chc25-adt-bmc).
    ///
    /// AY's flat/level BMC bails on datatype sorts, so the CHC-COMP ADT-LIA
    /// unsafe instances (a finite constructor counterexample reaching a bad
    /// state, BMC-refutable in principle) degraded to Unknown. This route runs
    /// the dedicated [`crate::bmc::BmcSolver::solve_datatype_bounded_refutation`]
    /// lane: bounded derivation-tree unfolding whose datatype-carrying formula
    /// is decided by ay-dpll's native datatype theory (TOTAL model
    /// construction), with every reconstructed candidate — including concrete
    /// ADT constructor values — replayed against the ORIGINAL clauses.
    ///
    /// Bug-finding only: returns `Unsafe` (replay-validated) or `None` (any
    /// non-Unsafe result falls through to the normal safety pipeline). It can
    /// never emit a wrong answer — soundness rests entirely on the witness
    /// replay gate, not on the datatype model's fidelity. Kill switch
    /// `--chc-no-dt-bmc`.
    pub(crate) fn try_datatype_bounded_bmc_refutation(
        &self,
        features: &ProblemFeatures,
        deadline: Option<Instant>,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        if !crate::ab_switches::get().dt_bmc {
            return None;
        }
        if !self.problem.uses_datatype_features()
            || self.problem.has_real_sorts()
            || features.num_queries == 0
        {
            return None;
        }
        if self.budget_exhausted(deadline) {
            return None;
        }
        // Modest slice so safe ADT instances still reach their safety routes
        // (cata / native-ADT-MBP PDR). Shallow ADT counterexamples are found
        // well within this; competition budgets buy a deeper tree.
        let budget = self.scaled_probe_budget(
            deadline,
            Duration::from_secs(2),
            20,
            Duration::from_secs(30),
        );
        if budget < Duration::from_millis(50) {
            return None;
        }
        let competition = budget >= Duration::from_secs(20);
        let (max_tree_depth, node_cap) = if competition {
            (12, 24_000)
        } else {
            (8, 6_000)
        };
        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: trying datatype bounded BMC refutation (depth {}, budget {:.3}s)",
                max_tree_depth,
                budget.as_secs_f64(),
            );
        }
        let config = BmcConfig::default()
            .with_time_budget(budget)
            .with_verbose(self.config.verbose);
        let bmc = crate::bmc::BmcSolver::new(self.problem.clone(), config);
        let start = Instant::now();
        let result = bmc.solve_datatype_bounded_refutation(max_tree_depth, budget, node_cap);
        let result_label = Self::result_to_str(&result);
        self.decision_log.log_decision(DecisionEntry {
            stage: "datatype_bounded_bmc_refutation",
            gate_result: matches!(result, PortfolioResult::Unsafe(_)),
            gate_reason: "ADT-LIA bounded derivation-tree bug-finding".to_string(),
            budget_secs: budget.as_secs_f64(),
            elapsed_secs: start.elapsed().as_secs_f64(),
            result: result_label,
            lemmas_learned: 0,
            max_frame: 0,
        });

        match result {
            PortfolioResult::Unsafe(cex) => Some((
                PortfolioResult::Unsafe(cex),
                ValidationEvidence::BmcCounterexample,
            )),
            PortfolioResult::Safe(_)
            | PortfolioResult::Unknown
            | PortfolioResult::NotApplicable => None,
        }
    }

    /// Focused front BMC probe for cyclic linear CHC problems.
    ///
    /// Runs FIRST in the SimpleLoop and MultiPredLinear strategy arms,
    /// before the LIA/Farkas PDR route and the Kind probe. Rationale
    /// (lustre/svcomp-class latency): unsafe transition systems and CFG
    /// encodings usually have shallow counterexamples that BMC finds in
    /// well under a second, while invariant-directed routes burn their
    /// full budgets first. Bug-finding only: any non-Unsafe result falls
    /// through to the normal pipeline.
    pub(crate) fn try_front_bmc_probe(
        &self,
        features: &ProblemFeatures,
        deadline: Option<Instant>,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        if !(features.is_single_predicate || features.is_linear)
            || features.uses_arrays
            || self.problem.has_bv_sorts()
            || self.problem.has_datatype_sorts()
        {
            return None;
        }
        // Scaled with the global budget (#phase0c): a 1800s competition run
        // buys a deeper probe (up to 30s) than a 30s dev run (1.5s floor).
        //
        // Fix 1 follow-up (sat-side-model-search diagnosis): raised from 5%
        // to 25% of remaining. With LRA propagation off in the BMC TS lane,
        // DRAGON-class sat-type depth checks answer in ~1-2s and the flat
        // confirmation re-solve in ~3-5s, so an end-to-end shallow-cex find
        // needs ~5-7s — a 5%-of-30s probe (1.5s) starved it one depth short
        // of the counterexample. 25% keeps the competition-scale behavior
        // unchanged (25% of 1800s still hits the 30s cap) while letting
        // dev-scale (30-60s) runs complete depth-1/2 cex searches. Safe
        // instances are not stalled by the larger budget: their per-depth
        // UNSAT checks are fast in the eager arm, and the probe exits early
        // on exhaustion.
        let bmc_probe_budget = self.scaled_probe_budget(
            deadline,
            Duration::from_millis(1500),
            25,
            Duration::from_secs(30),
        );
        if bmc_probe_budget < Duration::from_millis(10) {
            return None;
        }
        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: front BMC probe (budget {:.1}s, direct)",
                bmc_probe_budget.as_secs_f64()
            );
        }
        // Child of the portfolio handle (item 5): budget timer stays lane-local,
        // external cancellation propagates in.
        let cancel = self.cancellation_token.child();
        // Inc-16 S1b: clamp the single-pred TS probe once depth 8 is verified
        // cex-free AND ~9s have elapsed (kill switch AY_FRONT_PROBE_CLAMP=0).
        // Attribution: on sat lustre residuals the probe burns its full
        // ~24%-of-wall budget reaching only depth 2-12 with no cex; unsafe TS
        // instances find their (shallow) cex long before the clamp point.
        // The clamp lives in the TS incremental lane only, so the multipred
        // SingleLoop lane (inc-9, where the probe historically wins deep
        // cexs) and all non-probe BMC runs keep their full budget.
        let ts_probe_clamp = front_probe_clamp_enabled()
            .then_some((FRONT_PROBE_CLAMP_DEPTH, FRONT_PROBE_CLAMP_AFTER))
            .filter(|(_, after)| bmc_probe_budget > *after);
        let bmc_config = BmcConfig {
            base: ChcEngineConfig {
                verbose: self.config.verbose,
                cancellation_token: Some(cancel.clone()),
            },
            max_depth: 50,
            per_depth_timeout: Some(bmc_probe_budget),
            time_budget: Some(bmc_probe_budget),
            ts_probe_clamp,
            ..BmcConfig::default()
        };
        let bmc_start = Instant::now();
        let _timeout_guard = cancel.cancel_after(bmc_probe_budget);
        let _smt_deadline_guard = crate::smt::ScopedSmtDeadline::install(bmc_probe_budget);
        let bmc_solver = crate::bmc::BmcSolver::new(self.problem.clone(), bmc_config);
        let bmc_result = bmc_solver.solve();
        let elapsed = bmc_start.elapsed();
        let found = matches!(bmc_result, crate::engine_result::ChcEngineResult::Unsafe(_));
        self.decision_log.log_decision(DecisionEntry {
            stage: "front_bmc_probe",
            gate_result: found,
            gate_reason: "shallow counterexample probe before invariant routes".to_string(),
            budget_secs: bmc_probe_budget.as_secs_f64(),
            elapsed_secs: elapsed.as_secs_f64(),
            result: Self::result_to_str(&bmc_result),
            lemmas_learned: 0,
            max_frame: 0,
        });
        match bmc_result {
            crate::engine_result::ChcEngineResult::Unsafe(cex) => {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: front BMC probe found counterexample in {:.2}s",
                        elapsed.as_secs_f64()
                    );
                }
                Some((
                    PortfolioResult::Unsafe(cex),
                    ValidationEvidence::BmcCounterexample,
                ))
            }
            _ => None,
        }
    }

    /// Solve entry-exit-only problems by delegating to portfolio.
    ///
    /// These problems have no predicates - all clauses are of the form:
    /// `constraint ⇒ false` (queries with no body predicates).
    ///
    /// Delegates to `PortfolioSolver` whose `try_solve_trivial()` handles
    /// predicate-free problems and routes Safe results through `validate_safe()`
    /// (#5794, #5745). Previously this method duplicated the SMT checking logic
    /// and returned Safe/Unsafe directly without portfolio validation.
    ///
    /// Reference: Golem's `solveTrivial()` in engine/Common.cc:6-36
    pub(crate) fn solve_entry_exit_only(&self, _features: &ProblemFeatures) -> PortfolioResult {
        // Route through portfolio which validates Safe results via try_solve_trivial().
        // Entry-exit-only problems are predicate-free: try_solve_trivial() handles
        // them directly with proper validate_safe() checks. Preprocessing is disabled
        // since the problem is already simple (no predicates to inline). One PDR engine
        // is included as fallback if try_solve_trivial() returns None (SMT Unknown).
        let config = PortfolioConfig {
            external_cancellation: Some(self.cancellation_token.clone()),
            engines: vec![EngineConfig::Pdr(PdrConfig::default())],
            enable_preprocessing: false,
            verbose: self.config.verbose,

            parallel: false,
            timeout: None,
            parallel_timeout: None,
            engine_budgets: ay_core::kani_compat::DetHashMap::default(),
            memory_budget: self.config.memory_budget,
            strict_proofs: self.config.strict_proofs,
        };
        self.run_portfolio(config)
    }

    /// Solve trivial problems - fast path with minimal overhead.
    ///
    /// Uses failure-guided retry: if first PDR attempt returns Unknown,
    /// analyze the failure and retry with adjusted configuration.
    pub(crate) fn solve_trivial(
        &self,
        _features: &ProblemFeatures,
        deadline: Option<Instant>,
    ) -> PortfolioResult {
        // Stage 0: Try structural synthesis (< 1ms overhead)
        let synth_start = Instant::now();
        if let Some(result) = self.try_synthesis() {
            if self.config.verbose {
                safe_eprintln!("Adaptive: Trivial problem solved by structural synthesis");
            }
            self.decision_log.log_decision(DecisionEntry {
                stage: "trivial_synthesis",
                gate_result: true,
                gate_reason: "pattern found".to_string(),
                budget_secs: 0.0,
                elapsed_secs: synth_start.elapsed().as_secs_f64(),
                result: Self::result_to_str(&result),
                lemmas_learned: 0,
                max_frame: 0,
            });
            return result;
        }
        self.decision_log.log_decision(DecisionEntry {
            stage: "trivial_synthesis",
            gate_result: false,
            gate_reason: "no pattern".to_string(),
            budget_secs: 0.0,
            elapsed_secs: synth_start.elapsed().as_secs_f64(),
            result: "skipped",
            lemmas_learned: 0,
            max_frame: 0,
        });

        if self.config.verbose {
            safe_eprintln!("Adaptive: Using trivial fast path (single-threaded PDR)");
        }

        // Single-threaded PDR with minimal config - no portfolio overhead
        let mut config = PdrConfig {
            max_frames: 50,
            max_iterations: 1000,
            verbose: self.config.verbose,
            ..PdrConfig::default()
        }
        .with_tla_trace_from_env();
        if !Self::cap_pdr_solve_timeout_to_budget(&mut config, self.remaining_budget(deadline)) {
            if self.config.verbose {
                safe_eprintln!("Adaptive: Budget exhausted before initial trivial PDR");
            }
            return PortfolioResult::Unknown;
        }
        // Apply after installing the finite timeout so the common helper can
        // attach an adaptive child cancellation token without changing truly
        // unbounded PDR semantics.
        self.apply_user_hints(&mut config);

        // Use solve_with_stats for failure analysis (#1870)
        let pdr_start = Instant::now();
        let result_with_stats = PdrSolver::solve_problem_with_stats(&self.problem, config.clone());
        self.accumulate_stats(&result_with_stats.stats);
        let pdr_elapsed = pdr_start.elapsed().as_secs_f64();

        // If solved, validate before returning (#5549 soundness fix)
        if !matches!(result_with_stats.result, PdrResult::Unknown) {
            let validated = self.validate_adaptive_result(result_with_stats.result);
            if !matches!(validated, PdrResult::Unknown) {
                self.decision_log.log_decision(DecisionEntry {
                    stage: "trivial_pdr",
                    gate_result: true,
                    gate_reason: "initial PDR".to_string(),
                    budget_secs: 0.0,
                    elapsed_secs: pdr_elapsed,
                    result: Self::result_to_str(&validated),
                    lemmas_learned: result_with_stats.learned_lemmas.len(),
                    max_frame: result_with_stats.stats.max_frame,
                });
                return validated;
            }
        }
        self.decision_log.log_decision(DecisionEntry {
            stage: "trivial_pdr",
            gate_result: true,
            gate_reason: "initial PDR returned unknown".to_string(),
            budget_secs: 0.0,
            elapsed_secs: pdr_elapsed,
            result: "unknown",
            lemmas_learned: result_with_stats.learned_lemmas.len(),
            max_frame: result_with_stats.stats.max_frame,
        });

        // Budget check before retry stages (#7034)
        if self.budget_exhausted(deadline) {
            if self.config.verbose {
                safe_eprintln!("Adaptive: Budget exhausted after initial PDR, skipping retry");
            }
            return PortfolioResult::Unknown;
        }

        // Analyze failure and guide retry
        let analysis = FailureAnalysis::from_stats(&result_with_stats.stats);
        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: PDR returned Unknown - {} (confidence {:.0}%)",
                analysis.mode,
                analysis.confidence * 100.0
            );
            safe_eprintln!("Adaptive: Diagnostic: {}", analysis.diagnostic);
        }

        let guide = FailureGuide::from_analysis(&analysis);

        // Try alternative engine with remaining budget (#7034)
        if let Some(ref alt_engine) = guide.try_alternative_engine {
            if let Some(result) = self.try_alternative_engine_budgeted(alt_engine, deadline) {
                return result;
            }
        }

        // Budget check before PDR retry (#7034)
        if self.budget_exhausted(deadline) {
            return PortfolioResult::Unknown;
        }

        // Retry PDR with guided config adjustments
        if !guide.adjustments.is_empty() {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: Retrying with {} config adjustments",
                    guide.adjustments.len()
                );
            }
            let retry_start = Instant::now();
            let mut retry_config = guide.apply_to_config(config);
            if !Self::cap_pdr_solve_timeout_to_budget(
                &mut retry_config,
                self.remaining_budget(deadline),
            ) {
                return PortfolioResult::Unknown;
            }
            retry_config
                .user_hints
                .extend(result_with_stats.learned_lemmas);
            let retry_result = PdrSolver::solve_problem_with_stats(&self.problem, retry_config);
            self.accumulate_stats(&retry_result.stats);
            let validated = self.validate_adaptive_result(retry_result.result);
            self.decision_log.log_decision(DecisionEntry {
                stage: "trivial_retry",
                gate_result: true,
                gate_reason: format!("{} adjustments", guide.adjustments.len()),
                budget_secs: 0.0,
                elapsed_secs: retry_start.elapsed().as_secs_f64(),
                result: Self::result_to_str(&validated),
                lemmas_learned: retry_result.learned_lemmas.len(),
                max_frame: retry_result.stats.max_frame,
            });
            return validated;
        }

        // No retry possible, return original Unknown
        PortfolioResult::Unknown
    }

    pub(crate) fn cap_pdr_solve_timeout_to_budget(
        config: &mut PdrConfig,
        remaining_budget: Option<Duration>,
    ) -> bool {
        match remaining_budget {
            Some(remaining) if remaining.is_zero() => false,
            Some(remaining) => {
                config.solve_timeout = Some(match config.solve_timeout {
                    Some(timeout) => timeout.min(remaining),
                    None => remaining,
                });
                true
            }
            None => true,
        }
    }

    fn direct_kind_remaining_budget(
        deadline: Instant,
        cancellation: &crate::cancellation::CancellationToken,
    ) -> Option<Duration> {
        if cancellation.is_cancelled() {
            return None;
        }
        let remaining = deadline.saturating_duration_since(Instant::now());
        (!remaining.is_zero()).then_some(remaining)
    }

    fn log_direct_kind_demotion(
        &self,
        reason: &'static str,
        budget: Duration,
        stage_start: Instant,
    ) {
        if self.config.verbose {
            safe_eprintln!("Adaptive: Direct Kind demoted result: {reason}");
        }
        self.decision_log.log_decision(DecisionEntry {
            stage: "direct_kind_post_validation",
            gate_result: false,
            gate_reason: reason.to_string(),
            budget_secs: budget.as_secs_f64(),
            elapsed_secs: stage_start.elapsed().as_secs_f64(),
            result: "unknown",
            lemmas_learned: 0,
            max_frame: 0,
        });
    }

    fn validate_kind_safe_result_full_with_budget(
        &self,
        model: InvariantModel,
        validation_budget: Duration,
    ) -> PdrResult {
        if validation_budget.is_zero() {
            return PdrResult::Unknown;
        }

        let mut verifier = PdrSolver::new(
            self.problem.clone(),
            PdrConfig {
                verbose: self.config.verbose,
                strict_proofs: true,
                solve_timeout: Some(validation_budget),
                disable_array_scalarization: true,
                ..PdrConfig::default()
            },
        );
        verifier.set_validation_deadline(validation_budget);
        let per_rule_budget = validation_budget.min(Duration::from_secs(2));
        if verifier.verify_model_per_rule(&model, per_rule_budget) {
            PdrResult::Safe(model)
        } else {
            tracing::debug!(
                "Adaptive: Kind Safe result failed budgeted original-clause validation, demoting to Unknown"
            );
            PdrResult::Unknown
        }
    }

    fn accept_direct_kind_safe_result(
        &self,
        model: InvariantModel,
        deadline: Instant,
        cancellation: &crate::cancellation::CancellationToken,
        budget: Duration,
        stage_start: Instant,
    ) -> Option<PortfolioResult> {
        let Some(validation_budget) = Self::direct_kind_remaining_budget(deadline, cancellation)
        else {
            self.log_direct_kind_demotion(
                "no remaining budget before original-clause validation",
                budget,
                stage_start,
            );
            return None;
        };

        let validated = self.validate_kind_safe_result_full_with_budget(model, validation_budget);
        let model = match validated {
            PdrResult::Safe(model) => model,
            PdrResult::Unknown | PdrResult::NotApplicable => {
                self.log_direct_kind_demotion(
                    "original-clause validation returned unknown",
                    budget,
                    stage_start,
                );
                return None;
            }
            PdrResult::Unsafe(_) => {
                unreachable!("Kind Safe original-clause validation cannot produce Unsafe")
            }
        };

        if Self::direct_kind_remaining_budget(deadline, cancellation).is_none() {
            self.log_direct_kind_demotion(
                "no remaining budget after original-clause validation",
                budget,
                stage_start,
            );
            return None;
        }

        Some(PortfolioResult::Safe(model))
    }

    /// Try an alternative engine with budget-aware timeout (#7034).
    ///
    /// Caps the alternative engine's timeout to the remaining budget instead of
    /// using a hardcoded 10s. Returns `None` if the budget is exhausted.
    pub(crate) fn try_alternative_engine_budgeted(
        &self,
        engine: &crate::failure_analysis::AlternativeEngine,
        deadline: Option<Instant>,
    ) -> Option<PortfolioResult> {
        if self.budget_exhausted(deadline) {
            return None;
        }
        use crate::failure_analysis::AlternativeEngine;
        match engine {
            AlternativeEngine::Bmc { suggested_depth } => {
                let timeout = match self.remaining_budget(deadline) {
                    Some(remaining) => remaining.min(Duration::from_secs(10)),
                    None => Duration::from_secs(10),
                };
                if timeout.is_zero() {
                    return None;
                }
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: Trying BMC (depth {}, budget {:.1}s) to verify deep CEX",
                        suggested_depth,
                        timeout.as_secs_f64()
                    );
                }
                let bmc_config = PortfolioConfig {
                    external_cancellation: Some(self.cancellation_token.clone()),
                    engines: vec![EngineConfig::Bmc(BmcConfig::with_engine_config(
                        *suggested_depth,
                        self.config.verbose,
                        None,
                    ))],
                    parallel: false,
                    timeout: None,
                    parallel_timeout: Some(timeout),
                    verbose: self.config.verbose,

                    enable_preprocessing: true,
                    engine_budgets: ay_core::kani_compat::DetHashMap::default(),
                    memory_budget: self.config.memory_budget,
                    strict_proofs: self.config.strict_proofs,
                };
                let result = self.run_portfolio(bmc_config);
                if matches!(
                    result,
                    PortfolioResult::Safe(_) | PortfolioResult::Unsafe(_)
                ) {
                    return Some(result);
                }
            }
        }
        None
    }

    /// Try K-Induction with forward and backward checks.
    ///
    /// K-Induction is a bounded model checking technique that:
    /// 1. Checks if bad state is reachable in ≤k steps (base case)
    /// 2. Checks if ¬bad is k-inductive (forward induction)
    /// 3. Checks if init is k-inductive backward (backward induction)
    ///
    /// For multi-predicate problems, applies SingleLoop encoding to produce
    /// a synthetic single-predicate transition system. Kind doesn't use
    /// interpolation during solving, so Bool location variables from
    /// SingleLoop are acceptable (unlike PDKind, #6500).
    ///
    /// This is Golem's approach per Kind.cc:44-133.
    pub(crate) fn try_kind(&self, budget: Duration) -> Option<PortfolioResult> {
        let stage_start = Instant::now();
        // Post-solve acceptance/validation gates use the grace-extended
        // deadline so a proof found at the probe edge is validated rather
        // than dropped (mirrors KindConfig::validation_grace below).
        let deadline = stage_start + budget + KIND_VALIDATION_GRACE;
        if budget.is_zero() {
            self.log_direct_kind_demotion("no direct Kind budget", budget, stage_start);
            return None;
        }

        // #5877: BV problems use non-incremental mode where each query rebuilds
        // the entire formula. At k>=2, the forward induction formula grows large
        // enough that preprocessing (propagate_constants, convert_expr, Tseitin)
        // consumes the entire per-query timeout before DPLL starts. Cap max_k
        // at 1 for BV: k=0 and k=1 are fast (~10ms each), k=2 is catastrophic.
        let has_bv = self.problem.has_bv_sorts();
        let max_k = if has_bv { 1 } else { 20 };
        // Pure LIA needs a wider per-query budget than the BV lane here.
        // The direct Kind probe should stay close to the portfolio Kind
        // defaults: 8s per query for LIA gives the multi-predicate canary
        // enough room to finish without overcommitting the fallback path.
        // BV remains capped at 1s because larger per-query budgets mostly
        // inflate bit-blast preprocessing without improving robustness.
        let query_timeout = if has_bv {
            budget.min(Duration::from_secs(1))
        } else {
            budget.min(Duration::from_secs(8))
        };
        // Proof-validation grace (#lustre): when induction finds a proof at
        // the probe-budget edge, validation (fresh cross-check, init/query
        // verification, original-clause validation) may draw on this extra
        // allowance instead of dropping the proof. Search stays bounded by
        // `budget` (KindConfig::total_timeout); the cancel timer and the
        // post-solve acceptance gates below extend by the same grace.
        let validation_grace = KIND_VALIDATION_GRACE;
        // Child of the portfolio handle (item 5).
        let cancellation = self.cancellation_token.child();
        let cancellation_observer = cancellation.clone();
        let _timeout_guard = cancellation.cancel_after(budget + validation_grace);
        let kind_config = KindConfig::with_engine_config(
            max_k,
            query_timeout, // Per-query timeout (capped by remaining budget)
            budget,
            self.config.verbose,
            Some(cancellation),
        )
        .with_validation_grace(validation_grace);

        // For multi-predicate problems, apply SingleLoop encoding so Kind
        // can operate on a synthetic single-predicate transition system.
        let problem = self.scalarized_problem();
        let mut kind_problem = problem.clone();
        if kind_problem.predicates().len() <= 1
            && !kind_problem.has_bv_sorts()
            && !kind_problem.has_array_sorts()
            && !kind_problem.has_real_sorts()
            && !kind_problem.has_datatype_sorts()
        {
            kind_problem.try_split_ites_in_clauses(32, self.config.verbose);
        }

        let (solver_problem, singleloop_ctx) = if kind_problem.predicates().len() > 1 {
            let mut tx = SingleLoopTransformation::new(kind_problem.clone());
            match tx.transform() {
                Some(sys) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: K-Induction using SingleLoop encoding ({} state vars)",
                            sys.state_vars.len()
                        );
                    }
                    let synthetic = sys.to_chc_problem();
                    let state_vars = sys.state_vars.clone();
                    (synthetic, Some((tx, state_vars)))
                }
                None => (kind_problem, None),
            }
        } else {
            (kind_problem, None)
        };

        let mut solver = KindSolver::new(solver_problem, kind_config);
        solver.maybe_enable_tla_trace_from_env();
        let result = solver.solve();

        match &result {
            KindResult::Safe(model) => {
                if Self::direct_kind_remaining_budget(deadline, &cancellation_observer).is_none() {
                    self.log_direct_kind_demotion(
                        "no remaining budget after Kind solve",
                        budget,
                        stage_start,
                    );
                    return None;
                }

                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: K-Induction found invariant with {} predicates",
                        model.len()
                    );
                }

                // If SingleLoop was used, back-translate to multi-predicate model.
                let final_model = if let Some((ref tx, ref state_vars)) = singleloop_ctx {
                    match crate::portfolio::singleloop_safe::SingleLoopSafeWitness::from_trl(
                        model, state_vars,
                    ) {
                        Some(witness) => {
                            crate::portfolio::singleloop_safe::translate_singleloop_safe(
                                problem, tx, &witness,
                            )
                        }
                        None => {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "Adaptive: K-Induction SingleLoop back-translation failed"
                                );
                            }
                            None
                        }
                    }
                } else {
                    Some(model.clone())
                };

                let Some(translated_model) = final_model else {
                    self.log_direct_kind_demotion(
                        "safe witness backtranslation failed",
                        budget,
                        stage_start,
                    );
                    return None;
                };

                if Self::direct_kind_remaining_budget(deadline, &cancellation_observer).is_none() {
                    self.log_direct_kind_demotion(
                        "no remaining budget after safe backtranslation",
                        budget,
                        stage_start,
                    );
                    return None;
                }

                // Correctness firewall: direct Kind Safe results bypass the
                // portfolio acceptor, so the returned invariant must validate
                // against the original CHC clauses before promotion. A merely
                // query-only k-induction result is useful search evidence but
                // not enough to expose `VerifiedChcResult::Safe`.
                self.accept_direct_kind_safe_result(
                    translated_model,
                    deadline,
                    &cancellation_observer,
                    budget,
                    stage_start,
                )
            }
            KindResult::Unsafe(cex) => {
                if Self::direct_kind_remaining_budget(deadline, &cancellation_observer).is_none() {
                    self.log_direct_kind_demotion(
                        "no remaining budget before unsafe acceptance",
                        budget,
                        stage_start,
                    );
                    return None;
                }

                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: K-Induction found counterexample ({} steps)",
                        cex.steps.len()
                    );
                }

                // SingleLoop encoding is an overapproximation of multi-predicate
                // problems. Counterexamples from the overapproximation are often
                // spurious — they represent paths through the synthetic merged
                // transition system that do not exist in the original multi-predicate
                // problem. Only Safe results transfer from overapproximation.
                //
                // Previously, spurious CEXs were returned as Unsafe, short-circuiting
                // the entire adaptive pipeline (non-inlined PDR, portfolio, retry).
                // Benchmarks like s_multipl_23, s_multipl_25, half_true_modif_m hit
                // this: Kind found a spurious CEX at k=2 in <0.1s, the final
                // validation rejected it, and the solver returned "unknown" with
                // 13+ seconds of unused budget.
                if singleloop_ctx.is_some() {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: Discarding Kind counterexample from SingleLoop overapproximation (spurious)"
                        );
                    }
                    None
                } else {
                    // Kind produces concrete counterexample traces via
                    // make_unsafe_with_trace (base case SAT + fresh cross-check).
                    // Return it as PortfolioResult::Unsafe for validation by
                    // finalize_verified_result. Part of #7897.
                    Some(PortfolioResult::Unsafe(cex.clone()))
                }
            }
            KindResult::Unknown => None,
            KindResult::NotApplicable => {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: K-Induction not applicable (not a transition system)"
                    );
                }
                None
            }
        }
    }

    /// Try structural synthesis for patterned problems.
    ///
    /// Returns Some(PortfolioResult::Safe) if synthesis succeeds and the adaptive
    /// validation path accepts the model, None otherwise.
    ///
    /// Unlike previous implementation that returned Safe without verification (#1949),
    /// we now route synthesized models through the same adaptive Safe-validation
    /// helper used by other direct-engine results.
    pub(crate) fn try_synthesis(&self) -> Option<PortfolioResult> {
        let synth = StructuralSynthesizer::new(&self.problem);
        match synth.try_synthesize() {
            SynthesisResult::Success(synthesized) => {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: Structural synthesis succeeded with pattern: {}",
                        synthesized.pattern
                    );
                }

                self.accept_synthesized_invariant(synthesized)
            }
            SynthesisResult::NotInductive => {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: Structural synthesis found pattern but not inductive"
                    );
                }
                self.try_threshold_ite_synthesis_fallback(&synth)
            }
            SynthesisResult::NoPattern => self.try_threshold_ite_synthesis_fallback(&synth),
        }
    }

    fn try_threshold_ite_synthesis_fallback(
        &self,
        synth: &StructuralSynthesizer<'_>,
    ) -> Option<PortfolioResult> {
        if let Some(synthesized) = synth.try_threshold_ite_candidate() {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: Trying threshold-ITE synthesis candidate through adaptive validation"
                );
            }
            if let Some(result) = self.accept_synthesized_invariant(synthesized) {
                return Some(result);
            }
        }

        for synthesized in synth.try_query_safety_candidates() {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: Trying query-safety synthesis candidate through adaptive validation"
                );
            }
            if let Some(result) = self.accept_synthesized_invariant(synthesized) {
                return Some(result);
            }
        }

        None
    }

    fn accept_synthesized_invariant(
        &self,
        synthesized: SynthesizedInvariant,
    ) -> Option<PortfolioResult> {
        // Build a TOTAL InvariantModel: all predicates get an interpretation.
        // Missing predicates are assigned `true` (universal relation), matching
        // synthesis inductiveness semantics (#1950).
        let mut model = InvariantModel::new();

        for pred in self.problem.predicates() {
            // Build PDR canonical vars (__p{pred}_a{i}) instead of synthesis vars (x{i}).
            // This matches the K-induction path and PDR's verify_model expectations.
            let synth_vars: Vec<_> = pred
                .arg_sorts
                .iter()
                .enumerate()
                .map(|(i, sort)| ChcVar::new(format!("x{i}"), sort.clone()))
                .collect();
            let pdr_vars: Vec<_> = pred
                .arg_sorts
                .iter()
                .enumerate()
                .map(|(i, sort)| {
                    ChcVar::new(format!("__p{}_a{}", pred.id.index(), i), sort.clone())
                })
                .collect();

            let formula = if let Some(expr) = synthesized.interpretations.get(&pred.id) {
                // Substitute x{i} -> __p{pred}_a{i}
                let subst: Vec<_> = synth_vars
                    .iter()
                    .cloned()
                    .zip(pdr_vars.iter().cloned().map(ChcExpr::var))
                    .collect();
                expr.substitute(&subst)
            } else {
                // Missing predicate -> true (universal relation)
                ChcExpr::bool_const(true)
            };

            let interp = PredicateInterpretation::new(pdr_vars, formula);
            model.set(pred.id, interp);
        }

        // SOUNDNESS POLICY: every Safe acceptance must pass full model
        // validation against the ORIGINAL clauses. Structural shape checks
        // (`structurally_validates_query_safety_candidate`) are pattern
        // recognizers, not proofs — accepting on them alone produced false
        // SAT answers. The only permitted fallback after the budgeted
        // `validate_adaptive_result` is a FULL per-rule re-validation with a
        // fresh strict verifier (larger per-clause budget, same obligations).
        let validated = {
            let fallback_model = model.clone();
            let validated = self.validate_adaptive_result(PdrResult::Safe(model));
            if matches!(validated, PdrResult::Unknown | PdrResult::NotApplicable)
                && synthesized.pattern == SynthesisPattern::QuerySafetyCondition
            {
                self.validate_query_safety_synthesized_model(fallback_model)
            } else {
                validated
            }
        };

        match validated {
            PdrResult::Safe(model) => {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: Structural synthesis model passed adaptive validation"
                    );
                }
                Some(PortfolioResult::Safe(model))
            }
            PdrResult::Unknown | PdrResult::NotApplicable => {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: Structural synthesis model failed adaptive validation, ignoring"
                    );
                }
                None
            }
            PdrResult::Unsafe(_) => {
                unreachable!("Safe synthesis candidate cannot validate to Unsafe")
            }
        }
    }

    /// Full per-rule re-validation fallback for query-safety synthesis models.
    ///
    /// This is NOT a structural shortcut: it re-checks every clause of the
    /// original problem with a fresh strict-proofs verifier and a larger
    /// per-rule budget than `validate_adaptive_result`'s shared budget.
    /// Structural shape acceptance was removed — it allowed unvalidated
    /// models through and produced false SAT answers (022c-horn_000).
    fn validate_query_safety_synthesized_model(&self, model: InvariantModel) -> PdrResult {
        let validation_budget = Duration::from_secs(10);
        let mut verifier = PdrSolver::new(
            self.problem.clone(),
            PdrConfig {
                verbose: self.config.verbose,
                strict_proofs: true,
                solve_timeout: Some(validation_budget),
                disable_array_scalarization: true,
                preserve_original_clauses: true,
                ..PdrConfig::default()
            },
        );
        verifier.set_validation_deadline(validation_budget);
        if verifier.verify_model_per_rule(&model, Duration::from_secs(2)) {
            PdrResult::Safe(model)
        } else {
            PdrResult::Unknown
        }
    }

    /// Run a BMC-only solve for proof cross-checking.
    ///
    /// Runs only the BMC engine (no PDR, no k-induction, no TPA) on the problem
    /// with the given configuration. Returns a `VerifiedChcResult`:
    ///
    /// - `Unsafe(cex)`: BMC found a counterexample within `max_depth` steps.
    ///   The counterexample is constructive (satisfying assignment to the BMC
    ///   encoding) and trusted without re-verification.
    /// - `Unknown`: BMC remained inconclusive. This may mean it exhausted a
    ///   fully discharged bounded search, hit a BMC time budget, or ended in
    ///   another inconclusive state such as an unresolved `unknown` at some
    ///   depth. This does NOT mean the system is safe -- BMC cannot prove
    ///   safety. Consumers can inspect `result.unknown_reason()` and
    ///   `result.unknown_marker()` for structured BMC metadata when available.
    /// - `Safe`: Only returned when `acyclic_safe` is set, max depth is
    ///   exhausted, and the original problem has scalar predicate state
    ///   (sound only for acyclic problems with bounded paths).
    ///
    /// This is designed for cross-checking PDR proofs: run BMC independently to
    /// search for counterexamples that would contradict a claimed PROOF result.
    /// If BMC finds Unsafe, the proof is likely spurious.
    ///
    /// Part of #8412: BMC-only mode for model-checker-consumer proof cross-checking.
    ///
    /// # Example
    ///
    /// ```rust,no_run
    /// use ay_chc::{AdaptiveConfig, AdaptivePortfolio, BmcConfig, ChcProblem};
    /// use std::time::Duration;
    ///
    /// let problem = ChcProblem::new();
    /// let solver = AdaptivePortfolio::new(problem, AdaptiveConfig::default());
    ///
    /// let bmc_config = BmcConfig::default()
    ///     .with_max_depth(100)
    ///     .with_time_budget(Duration::from_secs(30));
    ///
    /// let result = solver.solve_bmc_only(bmc_config);
    /// if result.is_unsafe() {
    ///     // PDR proof is contradicted by BMC counterexample
    /// } else if let Some(ay_chc::VerifiedUnknownReason::BmcExhaustedSearch) =
    ///     result.unknown_reason()
    /// {
    ///     // BMC searched up to max_depth without finding a counterexample
    /// }
    /// ```
    pub fn solve_bmc_only(&self, bmc_config: BmcConfig) -> crate::VerifiedChcResult {
        let solve_started = Instant::now();
        let requested_deadline = bmc_config.time_budget.map(|budget| solve_started + budget);
        // Resolve every caller-visible boundary before spawning: neither the
        // ambient thread-local deadline nor constructor-time one-shot context
        // is inherited by the BMC worker. The BMC-local budget may tighten an
        // enclosing boundary, never replace it with a later deadline.
        let solve_deadline = [requested_deadline, self.enclosing_subsolve_deadline()]
            .into_iter()
            .flatten()
            .min();
        let caller_cancellation = bmc_config.base.cancellation_token.clone();
        // Run on a dedicated thread with a large stack to prevent stack
        // overflow from deep Arc<ChcExpr> recursive Drop (#6847).
        let config_for_fallback = bmc_config.clone();
        let result = std::thread::scope(|scope| {
            match std::thread::Builder::new()
                .name("ay-bmc-only".to_string())
                .stack_size(crate::adaptive::ADAPTIVE_SOLVER_STACK_SIZE)
                .spawn_scoped(scope, || {
                    self.solve_bmc_only_internal(bmc_config, solve_deadline)
                }) {
                Ok(handle) => match handle.join() {
                    Ok(result) => result,
                    Err(payload) => std::panic::resume_unwind(payload),
                },
                Err(_) => {
                    // Fallback: run on calling thread if spawn fails
                    self.solve_bmc_only_internal(config_for_fallback, solve_deadline)
                }
            }
        });
        let boundary_closed = self.budget_exhausted(solve_deadline)
            || caller_cancellation
                .as_ref()
                .is_some_and(crate::CancellationToken::is_cancelled);
        if boundary_closed
            && matches!(
                &result,
                crate::VerifiedChcResult::Safe(_) | crate::VerifiedChcResult::Unsafe(_)
            )
        {
            crate::VerifiedChcResult::Unknown(crate::engine_result::VerifiedUnknownMarker::new())
        } else {
            result
        }
    }

    /// Internal BMC-only solve (runs on the solver thread).
    fn solve_bmc_only_internal(
        &self,
        mut bmc_config: BmcConfig,
        solve_deadline: Option<Instant>,
    ) -> crate::VerifiedChcResult {
        use crate::bmc::BmcSolver;
        use crate::engine_result::ValidationEvidence;

        let bmc_verbose = bmc_config.base.verbose;
        let config_for_evidence = bmc_config.clone();
        let mut route_cancellation = self.cancellation_token.child();
        if let Some(cancellation) = &bmc_config.base.cancellation_token {
            route_cancellation.link_upstream(cancellation);
        }
        let _route_timeout = solve_deadline.map(|deadline| {
            route_cancellation.cancel_after(deadline.saturating_duration_since(Instant::now()))
        });
        let _route_smt_deadline = solve_deadline.map(crate::smt::ScopedSmtDeadline::install_until);
        let boundary_open = || {
            !self.cancellation_token.is_cancelled()
                && !route_cancellation.is_cancelled()
                && solve_deadline.is_none_or(|deadline| Instant::now() < deadline)
        };
        let unknown = || {
            crate::VerifiedChcResult::Unknown(crate::engine_result::VerifiedUnknownMarker::new())
        };
        if !boundary_open() {
            return unknown();
        }
        // Every nested solver and final verifier observes this one linked
        // route token. Per-stage timers use children so they cannot cancel the
        // embedding caller's token.
        bmc_config.base.cancellation_token = Some(route_cancellation.clone());
        if self.config.verbose {
            safe_eprintln!(
                "BMC-only: Starting with max_depth={}, time_budget={:?}",
                bmc_config.max_depth,
                bmc_config.time_budget,
            );
        }

        // Item 4 (model-checker-consumer parity, heavy-memory "235-relation" class): run the
        // bounded-cost forwarding-only combination (ArrayStoreForwarder +
        // cost-bounded DeadParamEliminator) ahead of the BMC construction so
        // threaded-memory array relations are sliced before the exact DAG
        // encoding. Identity summaries (no arrays, kill switch
        // AY_CHC_DISABLE_ARRAY_STORE_FORWARDING, no-op forwarding) keep the
        // historical raw-problem behavior. Witnesses found on the transformed
        // problem are back-translated below; the final verified-result
        // boundary still replays Unsafe traces and validates Safe models
        // against the ORIGINAL clauses fail-closed.
        // Item 4 Stage 3 mirror (condense-first for the large acyclic
        // class): with >= 20s of budget, run the wall-bounded
        // CondenseSuperpass ahead of the BMC construction — identical gate
        // and bound to run_direct_acyclic_bmc_probe, so a 10s-budget call
        // (item-3 compliance) behaves exactly as before by construction.
        // Identity-grade / disabled condense falls through to the
        // forwarding-only combination unchanged.
        let condensed_first = if config_for_evidence
            .time_budget
            .is_some_and(|budget| budget >= Duration::from_secs(20))
            && crate::transform::condense_enabled()
        {
            if !boundary_open() {
                return unknown();
            }
            let features = ProblemClassifier::classify(&self.problem);
            if !boundary_open() {
                return unknown();
            }
            if Self::is_large_acyclic_linear_graph(&features) {
                let condense_budget = solve_deadline.map(|deadline| {
                    (deadline.saturating_duration_since(Instant::now()) / 3)
                        .min(Duration::from_secs(15))
                });
                if condense_budget.is_some_and(|budget| budget.is_zero()) {
                    return unknown();
                }
                let condense = crate::transform::CondenseSuperpass::new()
                    .with_verbose(self.config.verbose)
                    .with_wall_budget(condense_budget)
                    .with_caller_boundary(solve_deadline, route_cancellation.clone());
                let condensed = crate::transform::Transformer::transform(
                    Box::new(condense),
                    self.problem.clone(),
                );
                if !boundary_open() {
                    return unknown();
                }
                let memory = condensed.back_translator.transform_memory();
                if memory.is_identity_grade() {
                    None
                } else {
                    // Finish the (usually mean-node-gate-bailed) round with
                    // the bounded forwarding-only combination so dead table/
                    // memory array args are sliced (see the twin comment in
                    // run_direct_acyclic_bmc_probe).
                    let Some(post) = PreprocessSummary::build_array_forwarding_only_with_limits(
                        condensed.problem,
                        self.config.verbose,
                        solve_deadline,
                        &route_cancellation,
                    ) else {
                        return unknown();
                    };
                    if !boundary_open() {
                        return unknown();
                    }
                    let back: Box<dyn crate::transform::BackTranslator> =
                        Box::new(crate::transform::CompositeBackTranslator {
                            inner: vec![post.back_translator, condensed.back_translator],
                        });
                    let memory = back.transform_memory();
                    let scalarized_problem = post.transformed_problem;

                    // Item 4 BMC-only mirror of the converting adaptive lane:
                    // when condense + forwarding fully scalarized the state
                    // (DT-free + array-free, non-identity chain), run the SAME
                    // scalarized level-BMC probe + ground back-translation
                    // landing as `run_direct_acyclic_bmc_probe` (shared helper
                    // `run_scalarized_collapse_probe`). Historically this lane
                    // only got the condense mirror, so the heavy-memory class
                    // burned the whole BMC-shortcut guard slice in the exact
                    // DAG encoding, which structurally cannot convert it.
                    // SOUNDNESS: promotion inside the helper happens ONLY via
                    // `validate_ground_derivation` on the ORIGINAL clauses (or
                    // the fresh original-clause replay / validated-Safe
                    // anchors); the finalize boundary below re-validates once
                    // more. Every failure falls through to the pre-existing
                    // exact-DAG lane on the remaining budget. Budget posture
                    // is unchanged for short budgets: this whole branch is
                    // already gated on time_budget >= 20s (item-3 compliance).
                    let scalarized_scalar_state = !memory.is_identity_grade()
                        && !scalarized_problem.has_datatype_sorts()
                        && !scalarized_problem.has_array_sorts();
                    let probe_budget = solve_deadline
                        .map(|deadline| deadline.saturating_duration_since(Instant::now()))
                        .unwrap_or(Duration::ZERO);
                    if scalarized_scalar_state && !probe_budget.is_zero() {
                        let shared_back_translator: std::sync::Arc<
                            std::sync::Mutex<Box<dyn crate::transform::BackTranslator>>,
                        > = std::sync::Arc::new(std::sync::Mutex::new(back));
                        if let Some((result, evidence)) = self.run_scalarized_collapse_probe(
                            &scalarized_problem,
                            &shared_back_translator,
                            &features,
                            probe_budget,
                            "BMC-only",
                            self.config.verbose || bmc_verbose,
                            solve_deadline,
                            Some(&route_cancellation),
                        ) {
                            return self.finalize_verified_result_with_boundary(
                                result,
                                evidence,
                                solve_deadline,
                                &route_cancellation,
                            );
                        }
                        if !boundary_open() {
                            return unknown();
                        }
                        // Follow-on: the pre-existing exact-DAG BMC lane runs
                        // on whatever budget the probe left (never more than
                        // the caller's solve-wide budget).
                        bmc_config.time_budget = solve_deadline
                            .map(|deadline| deadline.saturating_duration_since(Instant::now()));
                        let back: Box<dyn crate::transform::BackTranslator> = Box::new(
                            crate::transform::SharedBackTranslator(shared_back_translator),
                        );
                        Some((scalarized_problem, back, memory))
                    } else {
                        Some((scalarized_problem, back, memory))
                    }
                }
            } else {
                None
            }
        } else {
            None
        };

        let (bmc_problem, forwarding_back) = if let Some((problem, back, memory)) = condensed_first
        {
            (problem, Some((back, memory)))
        } else if self.problem.has_array_sorts() {
            let Some(summary) = PreprocessSummary::build_array_forwarding_only_with_limits(
                self.problem.clone(),
                self.config.verbose,
                solve_deadline,
                &route_cancellation,
            ) else {
                return unknown();
            };
            if summary.transform_memory.is_identity_grade() {
                (self.problem.clone(), None)
            } else {
                let PreprocessSummary {
                    transformed_problem,
                    back_translator,
                    transform_memory,
                    ..
                } = summary;
                (
                    transformed_problem,
                    Some((back_translator, transform_memory)),
                )
            }
        } else {
            (self.problem.clone(), None)
        };
        if !boundary_open() {
            return unknown();
        }
        let empty_safe_transfer_is_equisat_grade = forwarding_back
            .as_ref()
            .map_or(true, |(_, memory)| memory.is_equisat_grade());

        if let Some(deadline) = solve_deadline {
            let remaining = deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() || !boundary_open() {
                return unknown();
            }
            bmc_config.time_budget = Some(remaining);
            bmc_config.per_depth_timeout = bmc_config
                .per_depth_timeout
                .map(|per_depth| per_depth.min(remaining));
        }
        bmc_config.base.cancellation_token = Some(route_cancellation.clone());
        let solver = BmcSolver::new(bmc_problem, bmc_config);
        if !boundary_open() {
            return unknown();
        }
        let result = solver.solve();
        let stats = solver.stats();
        if !boundary_open() {
            return unknown();
        }

        if self.config.verbose {
            safe_eprintln!("BMC-only: Result = {}", result);
        }

        // Map transformed-space results back into the original space before
        // classification (mirrors run_preprocessed_acyclic_bmc_probe).
        let result = match result {
            crate::ChcEngineResult::Unsafe(cex) => match &forwarding_back {
                // Ground-witness landing for the follow-on lane (item 4 BMC-only
                // mirror, second convert site): the exact-DAG/exhaustive arms
                // attach a concrete TRANSFORMED-space ground derivation to their
                // counterexamples; back-translate it through the chain and
                // validate it on the ORIGINAL clauses by pure ground evaluation.
                // Promotion happens ONLY on a validated ORIGINAL-clause
                // derivation (same kill switch and fail-closed posture as the
                // probe landing); every failure falls through to the
                // pre-existing mapping below unchanged.
                Some((back_translator, memory)) => {
                    if let Some((result, evidence)) = self.ground_backtranslate_landing(
                        &cex,
                        back_translator.as_ref(),
                        "BMC-only",
                        self.config.verbose || bmc_verbose,
                        solve_deadline,
                        &route_cancellation,
                    ) {
                        return self.finalize_verified_result_with_boundary(
                            result,
                            evidence,
                            solve_deadline,
                            &route_cancellation,
                        );
                    }
                    if !boundary_open() {
                        return unknown();
                    }
                    if !memory.unsafe_backtranslation_complete() {
                        if self.config.verbose {
                            safe_eprintln!(
                                "BMC-only: transformed Unsafe rejected before promotion; {}",
                                memory.diagnostic_summary()
                            );
                        }
                        crate::ChcEngineResult::Unknown
                    } else {
                        let translated = back_translator.translate_invalidity(cex);
                        if !boundary_open() {
                            return unknown();
                        }
                        crate::ChcEngineResult::Unsafe(translated)
                    }
                }
                None => crate::ChcEngineResult::Unsafe(cex),
            },
            crate::ChcEngineResult::Safe(model) => {
                let translated = match &forwarding_back {
                    Some((back_translator, _)) => back_translator.translate_validity(model),
                    None => model,
                };
                if !boundary_open() {
                    return unknown();
                }
                crate::ChcEngineResult::Safe(translated)
            }
            other => other,
        };

        let (result, evidence) = match result {
            // BMC counterexamples are source evidence. The final verified-result
            // boundary still replays the trace against the original CHC before
            // exposing Unsafe.
            crate::ChcEngineResult::Unsafe(cex) => (
                crate::ChcEngineResult::Unsafe(cex),
                ValidationEvidence::BmcCounterexample,
            ),
            crate::ChcEngineResult::Safe(model) => self.validate_bmc_only_safe_result(
                model,
                &config_for_evidence,
                &stats,
                empty_safe_transfer_is_equisat_grade,
                solve_deadline,
                &route_cancellation,
            ),
            crate::ChcEngineResult::Unknown => (
                crate::ChcEngineResult::Unknown,
                self.classify_bmc_only_unknown(&config_for_evidence, &stats),
            ),
            crate::ChcEngineResult::NotApplicable => (
                crate::ChcEngineResult::NotApplicable,
                ValidationEvidence::FullVerification,
            ),
        };

        self.finalize_verified_result_with_boundary(
            result,
            evidence,
            solve_deadline,
            &route_cancellation,
        )
    }

    fn validate_bmc_only_safe_result(
        &self,
        model: InvariantModel,
        bmc_config: &BmcConfig,
        stats: &crate::bmc::BmcStats,
        empty_safe_transfer_is_equisat_grade: bool,
        deadline: Option<Instant>,
        cancellation: &crate::CancellationToken,
    ) -> (
        crate::ChcEngineResult,
        crate::engine_result::ValidationEvidence,
    ) {
        use crate::engine_result::ValidationEvidence;

        if model.is_empty()
            && empty_safe_transfer_is_equisat_grade
            && self.bmc_only_safe_is_complete_bounded_proof(bmc_config, stats)
        {
            if self.bmc_only_empty_safe_is_proof_grade() {
                return (
                    crate::ChcEngineResult::Safe(model),
                    ValidationEvidence::ScalarAcyclicBmcExhaustive {
                        max_depth: bmc_config.max_depth,
                    },
                );
            }

            tracing::warn!(
                max_depth = bmc_config.max_depth,
                has_arrays = self.problem.has_array_sorts(),
                has_bv = self.problem.has_bv_sorts(),
                has_real = self.problem.has_real_sorts(),
                has_datatypes = self.problem.has_datatype_sorts(),
                "BMC-only: exhaustive acyclic empty-model Safe is not proof-grade for this signature; demoting to Unknown"
            );
            return (
                crate::ChcEngineResult::Unknown,
                ValidationEvidence::BmcExhaustedSearch {
                    max_depth: bmc_config.max_depth,
                },
            );
        }

        match self.validate_adaptive_result_with_boundary(
            crate::ChcEngineResult::Safe(model),
            deadline,
            cancellation,
        ) {
            crate::ChcEngineResult::Safe(validated_model) => (
                crate::ChcEngineResult::Safe(validated_model),
                ValidationEvidence::FullVerification,
            ),
            _ => (
                crate::ChcEngineResult::Unknown,
                ValidationEvidence::FullVerification,
            ),
        }
    }

    fn bmc_only_empty_safe_is_proof_grade(&self) -> bool {
        // Exhaustive acyclic BMC enumerates every path to every query and checks
        // each branch formula in the original theory. This proof-grade empty-model
        // shortcut is gated by `bmc_only_safe_is_complete_bounded_proof` (acyclic
        // + exhausted_search + !budget_exhausted + full depth), and the exhaustive
        // lanes set `exhausted_search` ONLY on a DEFINITE full-DAG UNSAT — SMT
        // "unknown" and SAT never set it (see solve_acyclic_exhaustive_once and
        // solve_acyclic_symbolic_reachability_once in bmc/mod.rs). A definite UNSAT
        // of the fully-unrolled acyclic query disjunction is therefore a COMPLETE
        // safety proof for any DECIDABLE finite-value theory: scalar Bool/Int,
        // BIT-VECTORS, and FINITE (non-recursive) datatypes over them. RECURSIVE
        // datatypes, reals, and arrays (unbounded value space) stay excluded —
        // bounded acyclic unroll is incomplete for them, so an empty-model Safe
        // there would be a false proof. (Cyclic BV still needs a rechecked
        // inductive invariant; that path is upstream and never reaches this gate,
        // which only fires under the acyclic+exhausted guard above.)
        !self.problem.has_array_sorts()
            && !self.problem.has_real_sorts()
            && !self.problem.has_recursive_datatype_sorts()
    }

    fn bmc_only_safe_is_complete_bounded_proof(
        &self,
        bmc_config: &BmcConfig,
        stats: &crate::bmc::BmcStats,
    ) -> bool {
        if !bmc_config.acyclic_safe
            || !stats.exhausted_search
            || stats.budget_exhausted
            || stats.max_depth_reached < bmc_config.max_depth
        {
            return false;
        }

        let features = ProblemClassifier::classify(&self.problem);
        !features.has_cycles
            || features
                .phase_bounded_depth
                .is_some_and(|depth| bmc_config.max_depth >= depth)
    }

    fn classify_bmc_only_unknown(
        &self,
        bmc_config: &BmcConfig,
        stats: &crate::bmc::BmcStats,
    ) -> crate::engine_result::ValidationEvidence {
        use crate::engine_result::ValidationEvidence;

        if self.problem.predicates().is_empty() || self.problem.queries().next().is_none() {
            return ValidationEvidence::FullVerification;
        }
        if bmc_config.base.is_cancelled() {
            return ValidationEvidence::FullVerification;
        }
        if stats.budget_exhausted {
            return ValidationEvidence::BmcBudgetExhausted {
                depth_reached: stats.max_depth_reached,
                max_depth: bmc_config.max_depth,
            };
        }
        if stats.exhausted_search {
            return ValidationEvidence::BmcExhaustedSearch {
                max_depth: bmc_config.max_depth,
            };
        }

        ValidationEvidence::FullVerification
    }
}

#[cfg(test)]
mod tests {
    use super::{AdaptivePortfolio, SHALLOW_UNSAFE_BMC_MAX_DEPTH};
    use crate::{
        bmc::BmcStats, engine_result::ValidationEvidence, AdaptiveConfig, BmcConfig, ChcExpr,
        ChcParser, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause,
        VerifiedUnknownReason,
    };
    use crate::{
        engine_result::ChcEngineResult,
        pdr::{InvariantModel, PredicateInterpretation},
    };

    fn make_bmc_unsafe_problem() -> ChcProblem {
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
            ClauseHead::Predicate(
                inv,
                vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
            ),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5))),
            ),
            ClauseHead::False,
        ));

        problem
    }

    fn make_bmc_exhausted_problem() -> ChcProblem {
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(3))),
            ),
            ClauseHead::Predicate(
                inv,
                vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
            ),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
            ),
            ClauseHead::False,
        ));

        problem
    }

    fn make_shallow_acyclic_unsafe_problem() -> ChcProblem {
        let mut problem = ChcProblem::new();
        let entry = problem.declare_predicate("Entry", vec![ChcSort::Int]);
        let bug = problem.declare_predicate("Bug", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
            ClauseHead::Predicate(entry, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(entry, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
            ),
            ClauseHead::Predicate(bug, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(bug, vec![ChcExpr::var(x)])]),
            ClauseHead::False,
        ));

        problem
    }

    fn make_direct_kind_guard_problem() -> ChcProblem {
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
            ClauseHead::Predicate(
                inv,
                vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
            ),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
            ),
            ClauseHead::False,
        ));

        problem
    }

    fn make_nonnegative_kind_model(problem: &ChcProblem) -> InvariantModel {
        let pred = problem.predicates()[0].id;
        let arg = ChcVar::new(format!("__p{}_a0", pred.index()), ChcSort::Int);
        let mut model = InvariantModel::new();
        model.set(
            pred,
            PredicateInterpretation::new(
                vec![arg.clone()],
                ChcExpr::ge(ChcExpr::var(arg), ChcExpr::int(0)),
            ),
        );
        model
    }

    #[test]
    fn shallow_unsafe_bmc_prepass_finds_acyclic_fact_to_query_bug() {
        let problem = make_shallow_acyclic_unsafe_problem();
        let features = crate::classifier::ProblemClassifier::classify(&problem);
        assert!(!features.has_cycles);
        assert_eq!(features.num_facts, 1);
        assert_eq!(features.num_queries, 1);

        let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
        let deadline = ay_core::time::Instant::now() + std::time::Duration::from_secs(1);

        let Some((result, evidence)) =
            adaptive.try_shallow_unsafe_bmc_prepass(&features, Some(deadline))
        else {
            panic!("small acyclic unsafe CHC should enter the shallow BMC prepass");
        };

        assert!(
            matches!(result, ChcEngineResult::Unsafe(_)),
            "prepass should only return when it has a concrete unsafe witness, got {result:?}"
        );
        assert!(matches!(evidence, ValidationEvidence::BmcCounterexample));
    }

    /// The marker-dag prepass only produces vacuous (all-`true`-state)
    /// witnesses, whose replay validation is unsound (it reduces to query
    /// satisfiability in isolation and emitted a FALSE UNSAFE on an
    /// expected-safe harness). `validate_counterexample` now rejects vacuous
    /// witnesses unconditionally, so the prepass must fail closed here even
    /// though this chain is genuinely unsafe — other (replay-validated)
    /// engines own this class now.
    #[test]
    fn adt_array_dag_prepass_fails_closed_on_array_chain() {
        let problem = ChcParser::parse(include_str!(
            "../../../tests/chc/regression/false_proof_array_chain.smt2"
        ))
        .expect("false_proof_array_chain.smt2 should parse");
        let features = crate::classifier::ProblemClassifier::classify(&problem);
        assert!(!features.has_cycles);
        assert_eq!(features.num_facts, 1);
        assert_eq!(features.num_queries, 1);
        assert!(
            features.dag_depth <= SHALLOW_UNSAFE_BMC_MAX_DEPTH,
            "sample chain depth {} must be admitted by the bounded bug prepass",
            features.dag_depth
        );

        let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
        let deadline = ay_core::time::Instant::now() + std::time::Duration::from_secs(1);

        assert!(
            adaptive
                .try_adt_array_nullary_unsafe_prepass(Some(deadline))
                .is_none(),
            "vacuous marker-dag witnesses must never be accepted as Unsafe"
        );
    }

    #[test]
    fn direct_kind_acceptance_demotes_safe_when_validation_deadline_exhausted() {
        let problem = make_direct_kind_guard_problem();
        let model = make_nonnegative_kind_model(&problem);
        let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
        let cancellation = crate::cancellation::CancellationToken::new();
        let now = ay_core::time::Instant::now();
        let expired_deadline = now
            .checked_sub(std::time::Duration::from_millis(1))
            .unwrap_or(now);

        let accepted = adaptive.accept_direct_kind_safe_result(
            model,
            expired_deadline,
            &cancellation,
            std::time::Duration::from_millis(1),
            ay_core::time::Instant::now(),
        );

        assert!(
            accepted.is_none(),
            "direct Kind Safe acceptance must fail closed after budget exhaustion"
        );
    }

    #[test]
    fn direct_kind_acceptance_demotes_safe_when_cancelled_before_validation() {
        let problem = make_direct_kind_guard_problem();
        let model = make_nonnegative_kind_model(&problem);
        let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
        let cancellation = crate::cancellation::CancellationToken::new();
        cancellation.cancel();

        let accepted = adaptive.accept_direct_kind_safe_result(
            model,
            ay_core::time::Instant::now() + std::time::Duration::from_secs(1),
            &cancellation,
            std::time::Duration::from_secs(1),
            ay_core::time::Instant::now(),
        );

        assert!(
            accepted.is_none(),
            "direct Kind Safe acceptance must fail closed after cancellation"
        );
    }

    #[test]
    fn direct_kind_acceptance_accepts_safe_with_remaining_validation_budget() {
        let problem = make_direct_kind_guard_problem();
        let model = make_nonnegative_kind_model(&problem);
        let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
        let cancellation = crate::cancellation::CancellationToken::new();

        let accepted = adaptive.accept_direct_kind_safe_result(
            model,
            ay_core::time::Instant::now() + std::time::Duration::from_secs(2),
            &cancellation,
            std::time::Duration::from_secs(2),
            ay_core::time::Instant::now(),
        );

        assert!(
            matches!(accepted, Some(ChcEngineResult::Safe(_))),
            "valid direct Kind Safe should still be accepted when validation budget remains"
        );
    }

    fn make_acyclic_safe_problem() -> ChcProblem {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::Int]);
        let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
            ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(p, vec![ChcExpr::var(x.clone())])]),
            ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(q, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(1))),
            ),
            ClauseHead::False,
        ));

        problem
    }

    fn make_acyclic_bv_safe_problem() -> ChcProblem {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::BitVec(8)]);
        let q = problem.declare_predicate("Q", vec![ChcSort::BitVec(8)]);
        let x = ChcVar::new("x", ChcSort::BitVec(8));

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(0, 8))),
            ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(p, vec![ChcExpr::var(x.clone())])]),
            ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(q, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(1, 8))),
            ),
            ClauseHead::False,
        ));

        problem
    }

    #[test]
    fn solve_bmc_only_marks_bounded_search_unknowns() {
        let adaptive =
            AdaptivePortfolio::new(make_bmc_exhausted_problem(), AdaptiveConfig::test_default());

        let result = adaptive.solve_bmc_only(BmcConfig::default().with_max_depth(10));
        let marker = result
            .unknown_marker()
            .expect("BMC-only safe benchmark should surface verified unknown details");

        assert!(result.is_unknown());
        assert_eq!(
            result.unknown_reason(),
            Some(VerifiedUnknownReason::BmcExhaustedSearch)
        );
        assert_eq!(marker.bmc_max_depth(), Some(10));
        assert_eq!(marker.bmc_depth_reached(), Some(10));
    }

    #[test]
    fn solve_bmc_only_validates_constructive_unsafe_without_trust_fallback() {
        let adaptive =
            AdaptivePortfolio::new(make_bmc_unsafe_problem(), AdaptiveConfig::test_default());

        let result = adaptive.solve_bmc_only(BmcConfig::default().with_max_depth(10));

        assert!(
            result.is_unsafe(),
            "constructive BMC counterexample should remain Unsafe after final replay: {result}"
        );
        assert_eq!(adaptive.statistics().trust_proof_fallbacks, 0);
    }

    #[test]
    fn solve_bmc_only_zero_budget_never_publishes_unsafe() {
        let adaptive =
            AdaptivePortfolio::new(make_bmc_unsafe_problem(), AdaptiveConfig::test_default());

        let result = adaptive.solve_bmc_only(
            BmcConfig::default()
                .with_max_depth(10)
                .with_time_budget(std::time::Duration::ZERO),
        );

        assert!(
            result.is_unknown(),
            "an already-expired absolute BMC-only deadline must fail closed: {result}"
        );
    }

    #[test]
    fn solve_bmc_only_inherits_expired_ambient_solve_deadline() {
        let adaptive =
            AdaptivePortfolio::new(make_bmc_unsafe_problem(), AdaptiveConfig::test_default());
        let _deadline = crate::smt::ScopedSolveDeadline::new(Some(ay_core::time::Instant::now()));

        let result = adaptive.solve_bmc_only(
            BmcConfig::default()
                .with_max_depth(10)
                .with_time_budget(std::time::Duration::from_secs(5)),
        );

        assert!(
            result.is_unknown(),
            "an expired enclosing solve deadline must not be reset by the BMC-local budget: {result}"
        );
    }

    #[test]
    fn solve_bmc_only_pre_cancelled_caller_never_publishes_safe() {
        let adaptive =
            AdaptivePortfolio::new(make_acyclic_safe_problem(), AdaptiveConfig::test_default());
        let cancellation = crate::CancellationToken::new();
        cancellation.cancel();

        let result = adaptive.solve_bmc_only(
            BmcConfig::default()
                .with_max_depth(2)
                .with_acyclic_safe(true)
                .with_cancellation(cancellation),
        );

        assert!(
            result.is_unknown(),
            "a pre-cancelled BMC-only caller must fail closed before preprocessing: {result}"
        );
    }

    #[test]
    fn solve_bmc_only_strict_proofs_accepts_replayed_constructive_unsafe() {
        let adaptive = AdaptivePortfolio::new(
            make_bmc_unsafe_problem(),
            AdaptiveConfig {
                strict_proofs: true,
                ..AdaptiveConfig::test_default()
            },
        );

        let result = adaptive.solve_bmc_only(BmcConfig::default().with_max_depth(10));

        assert!(
            result.is_unsafe(),
            "strict proofs should accept constructive BMC counterexamples after final replay: {result}"
        );
        assert_eq!(adaptive.statistics().trust_proof_fallbacks, 0);
    }

    #[test]
    fn solve_bmc_only_accepts_scalar_exhaustive_acyclic_empty_model_safe() {
        let adaptive =
            AdaptivePortfolio::new(make_acyclic_safe_problem(), AdaptiveConfig::test_default());

        let result = adaptive.solve_bmc_only(
            BmcConfig::default()
                .with_max_depth(2)
                .with_acyclic_safe(true),
        );

        assert!(
            result.is_safe(),
            "complete scalar acyclic BMC exhaustion is proof-grade: {result}"
        );
    }

    #[test]
    fn solve_bmc_only_accepts_bv_acyclic_empty_model_safe() {
        // Exhaustive acyclic BMC over a BV DAG that is UNSAT at every depth is a
        // COMPLETE decision procedure (bit-blasting is complete for BV), so the
        // empty-model Safe is proof-grade — same as the scalar case. exhausted_search
        // is only set on a definite full-DAG UNSAT, so this is sound.
        let adaptive = AdaptivePortfolio::new(
            make_acyclic_bv_safe_problem(),
            AdaptiveConfig::test_default(),
        );

        let result = adaptive.solve_bmc_only(
            BmcConfig::default()
                .with_max_depth(2)
                .with_acyclic_safe(true),
        );

        assert!(
            result.is_safe(),
            "complete BV acyclic BMC exhaustion is proof-grade: {result}"
        );
    }

    fn make_acyclic_bv_array_problem() -> ChcProblem {
        // Same acyclic DAG shape as make_acyclic_bv_safe_problem but with an ARRAY
        // sort in the predicate signature. Arrays have an unbounded value space, so
        // bounded acyclic unroll is INCOMPLETE — the empty-model Safe must stay
        // non-proof-grade (guard 4).
        let mut problem = ChcProblem::new();
        let arr = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::BitVec(8)));
        let p = problem.declare_predicate("P", vec![ChcSort::BitVec(8), arr.clone()]);
        let q = problem.declare_predicate("Q", vec![ChcSort::BitVec(8), arr.clone()]);
        let x = ChcVar::new("x", ChcSort::BitVec(8));
        let a = ChcVar::new("a", arr);

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(0, 8))),
            ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone()), ChcExpr::var(a.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(
                p,
                vec![ChcExpr::var(x.clone()), ChcExpr::var(a.clone())],
            )]),
            ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone()), ChcExpr::var(a.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(q, vec![ChcExpr::var(x.clone()), ChcExpr::var(a)])],
                Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(1, 8))),
            ),
            ClauseHead::False,
        ));

        problem
    }

    #[test]
    fn solve_bmc_only_demotes_array_acyclic_empty_model_safe() {
        // Guard 4: even a fully-exhausted acyclic empty-model Safe must be demoted
        // to Unknown when the signature carries an array sort (unbounded, bounded
        // unroll incomplete). Prevents an array false proof.
        let adaptive = AdaptivePortfolio::new(
            make_acyclic_bv_array_problem(),
            AdaptiveConfig::test_default(),
        );

        let result = adaptive.solve_bmc_only(
            BmcConfig::default()
                .with_max_depth(2)
                .with_acyclic_safe(true),
        );

        assert!(
            result.is_unknown(),
            "array acyclic BMC empty-model Safe must not be proof-grade: {result}"
        );
    }

    #[test]
    fn bmc_only_safe_demotes_cyclic_empty_model_even_if_caller_sets_acyclic_safe() {
        let adaptive =
            AdaptivePortfolio::new(make_bmc_exhausted_problem(), AdaptiveConfig::test_default());
        let config = BmcConfig::default()
            .with_max_depth(10)
            .with_acyclic_safe(true);
        let stats = BmcStats {
            max_depth_reached: 10,
            exhausted_search: true,
            ..BmcStats::default()
        };

        let cancellation = crate::CancellationToken::new();
        let (result, evidence) = adaptive.validate_bmc_only_safe_result(
            InvariantModel::new(),
            &config,
            &stats,
            true,
            None,
            &cancellation,
        );

        assert!(
            matches!(result, ChcEngineResult::Unknown),
            "cyclic empty-model BMC Safe must fail closed, got {result:?}"
        );
        assert!(
            matches!(evidence, ValidationEvidence::FullVerification),
            "demoted BMC Safe should not carry acyclic proof evidence: {evidence:?}"
        );
    }

    #[test]
    fn bmc_only_safe_demotes_incomplete_acyclic_empty_model() {
        let adaptive =
            AdaptivePortfolio::new(make_acyclic_safe_problem(), AdaptiveConfig::test_default());
        let config = BmcConfig::default()
            .with_max_depth(10)
            .with_acyclic_safe(true);
        let stats = BmcStats {
            max_depth_reached: 4,
            exhausted_search: true,
            ..BmcStats::default()
        };

        let cancellation = crate::CancellationToken::new();
        let (result, evidence) = adaptive.validate_bmc_only_safe_result(
            InvariantModel::new(),
            &config,
            &stats,
            true,
            None,
            &cancellation,
        );

        assert!(
            matches!(result, ChcEngineResult::Unknown),
            "incomplete BMC Safe must fail closed, got {result:?}"
        );
        assert!(
            matches!(evidence, ValidationEvidence::FullVerification),
            "incomplete BMC Safe should not carry acyclic proof evidence: {evidence:?}"
        );
    }

    #[test]
    fn bmc_only_safe_rejects_non_equisat_transformed_empty_model() {
        // Fabricate the result-side state reached after a non-equisat transform:
        // exhaustive transformed BMC reported an empty Safe model, but that model
        // does not validate on this acyclic unsafe original problem.  The complete
        // bounded-proof shortcut must not transfer across that transform.
        let adaptive = AdaptivePortfolio::new(
            make_shallow_acyclic_unsafe_problem(),
            AdaptiveConfig::test_default(),
        );
        let config = BmcConfig::default()
            .with_max_depth(10)
            .with_acyclic_safe(true);
        let stats = BmcStats {
            max_depth_reached: 10,
            exhausted_search: true,
            ..BmcStats::default()
        };

        let cancellation = crate::CancellationToken::new();
        let (result, evidence) = adaptive.validate_bmc_only_safe_result(
            InvariantModel::new(),
            &config,
            &stats,
            false,
            None,
            &cancellation,
        );

        assert!(
            matches!(result, ChcEngineResult::Unknown),
            "non-equisat transformed empty Safe must fail closed, got {result:?}"
        );
        assert!(
            matches!(evidence, ValidationEvidence::FullVerification),
            "rejected transformed Safe must not carry exhaustive evidence: {evidence:?}"
        );
    }

    #[test]
    fn classify_bmc_only_unknown_keeps_last_depth_unknown_inconclusive() {
        let adaptive =
            AdaptivePortfolio::new(make_bmc_exhausted_problem(), AdaptiveConfig::test_default());
        let evidence = adaptive.classify_bmc_only_unknown(
            &BmcConfig::default().with_max_depth(10),
            &BmcStats {
                max_depth_reached: 10,
                ..BmcStats::default()
            },
        );

        assert!(matches!(evidence, ValidationEvidence::FullVerification));
    }

    #[test]
    fn classify_bmc_only_unknown_keeps_legacy_fallback_inconclusive() {
        let adaptive =
            AdaptivePortfolio::new(make_bmc_exhausted_problem(), AdaptiveConfig::test_default());
        let evidence = adaptive.classify_bmc_only_unknown(
            &BmcConfig::default().with_max_depth(10),
            &BmcStats {
                max_depth_reached: 10,
                used_legacy_fallback: true,
                ..BmcStats::default()
            },
        );

        assert!(matches!(evidence, ValidationEvidence::FullVerification));
    }

    #[test]
    fn classify_bmc_only_unknown_prefers_budget_marker_over_exhausted_search() {
        let adaptive =
            AdaptivePortfolio::new(make_bmc_exhausted_problem(), AdaptiveConfig::test_default());
        let evidence = adaptive.classify_bmc_only_unknown(
            &BmcConfig::default().with_max_depth(10),
            &BmcStats {
                max_depth_reached: 4,
                budget_exhausted: true,
                exhausted_search: true,
                ..BmcStats::default()
            },
        );

        assert!(matches!(
            evidence,
            ValidationEvidence::BmcBudgetExhausted {
                depth_reached: 4,
                max_depth: 10
            }
        ));
    }
}
