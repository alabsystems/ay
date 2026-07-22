// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Adaptive portfolio validation methods.
//!
//! Extracted from adaptive.rs — these methods validate direct adaptive
//! results before returning them. Defense-in-depth for soundness when the
//! adaptive layer bypasses the portfolio acceptor (probe, retry, case-split,
//! structural synthesis, Kind).
//!
//! Safe and Unsafe validation are mandatory here, matching the portfolio
//! contract: adaptive direct-engine probes bypass the portfolio acceptor, so
//! they must not be able to return a false result just because
//! `config.validate` is off. If an adaptive Unsafe cannot be re-verified at
//! this internal boundary, it is demoted to Unknown instead of relying on the
//! final `VerifiedChcResult` wrapper to catch it later.

use crate::bmc::BmcConfig;
use crate::classifier::ProblemClassifier;
use crate::engine_config::ChcEngineConfig;
use crate::engine_result::ValidationEvidence;
use crate::pdr::{
    CexVerificationResult, Counterexample, InvariantModel, PdrConfig, PdrResult, PdrSolver,
    PredicateInterpretation,
};
use crate::portfolio::{PortfolioConfig, PortfolioResult, PortfolioSolver};
use crate::{BmcSolver, ChcExpr, ChcProblem, ChcSort, ChcVar, PredicateId};
use std::fmt::Write as _;
use std::time::Duration;

use crate::adaptive::AdaptivePortfolio;

const FINAL_VALIDATION_DIAGNOSTICS_ENV: &str = "AY_ADAPTIVE_FINAL_VALIDATION_DIAGNOSTICS";
const FINAL_VALIDATION_DIAGNOSTIC_HEAD_STEPS: usize = 3;

/// Budget cap for re-verifying a completed final Safe model on the original
/// problem (Fix B1). Capped at the remaining global budget when one exists.
const FINAL_SAFE_COMPLETION_VALIDATION_BUDGET: Duration = Duration::from_secs(30);

/// Budget cap for the Fix V1 independent acyclic-BMC safety re-proof on the
/// ORIGINAL problem. Capped at the remaining global budget when one exists.
const FINAL_SAFE_ACYCLIC_BMC_REPROOF_BUDGET: Duration = Duration::from_secs(10);

impl AdaptivePortfolio {
    /// Validate a non-portfolio adaptive result before returning it.
    ///
    /// The helper still uses `PdrResult` as the local result carrier, but it is
    /// used for any adaptive-layer result that bypasses the portfolio acceptor
    /// (for example direct PDR probes/retries and structural synthesis models).
    ///
    /// The portfolio solver validates all engine results internally (Safe via
    /// `verify_model_with_budget`, Unsafe via `verify_counterexample`). But when
    /// the adaptive layer handles results directly, those results bypass portfolio
    /// validation. This method provides the same defense-in-depth.
    ///
    /// SOUNDNESS FIX #5549: Without this, PDR's internal verify_model can accept
    /// invariants that fail external verification (e.g., switch_000.smt2 where
    /// PDR declares Safe but the invariant doesn't hold on the original problem).
    /// The adaptive layer returned this unvalidated Safe, producing false-SAT.
    ///
    /// Standard validation budget for 1-inductive engines (PDR, TPA, CEGAR).
    /// Matches portfolio's validate_safe budget (#5394).
    const VALIDATION_BUDGET_1INDUCTIVE: Duration = Duration::from_millis(1500);

    /// Build a fresh verifier for adaptive result validation.
    ///
    /// Validation must run in a clean solver instance rather than reusing any
    /// engine-local state from the candidate result we are checking.
    ///
    /// #8630: Wire solve_timeout so verification PdrSolvers bail
    /// cooperatively instead of hanging indefinitely.
    fn new_validation_solver(&self) -> PdrSolver {
        let config = PdrConfig {
            verbose: self.config.verbose,
            strict_proofs: true,
            solve_timeout: Some(Duration::from_secs(30)),
            disable_array_scalarization: true,
            preserve_original_clauses: true,
            ..PdrConfig::default()
        };
        PdrSolver::new(self.problem.clone(), config)
    }

    /// Build a fresh portfolio validator for the public verified-result boundary.
    ///
    /// The adaptive layer uses this only when converting a final candidate into
    /// `VerifiedChcResult`, so the config carries no engines and no preprocessing.
    fn new_verified_result_validator(
        &self,
        remaining_budget: Option<Duration>,
    ) -> Option<PortfolioSolver> {
        if remaining_budget.is_some_and(|budget| budget.is_zero()) {
            return None;
        }

        Some(PortfolioSolver::new(
            self.problem.clone(),
            PortfolioConfig {
                external_cancellation: Some(self.cancellation_token.clone()),
                engines: vec![],
                parallel: false,
                timeout: remaining_budget,
                parallel_timeout: remaining_budget,
                verbose: self.config.verbose,
                enable_preprocessing: false,
                engine_budgets: ay_core::kani_compat::DetHashMap::default(),
                memory_budget: self.config.memory_budget,
                strict_proofs: true,
            },
        ))
    }

    /// Validate an adaptive direct-engine counterexample with a fresh PDR solver.
    fn validate_direct_unsafe_counterexample(&self, cex: &Counterexample) -> bool {
        let mut verifier = self.new_validation_solver();
        matches!(
            verifier.verify_counterexample(cex),
            CexVerificationResult::Valid
        )
    }

    /// Validate a final Unsafe candidate at the public verified-result boundary.
    pub(crate) fn validate_final_unsafe_result(
        &self,
        cex: &Counterexample,
        remaining_budget: Option<Duration>,
    ) -> bool {
        let Some(validator) = self.new_verified_result_validator(remaining_budget) else {
            tracing::debug!(
                "Adaptive: final Unsafe result has no remaining validation budget, demoting to Unknown"
            );
            return false;
        };
        validator.validate_unsafe_for_verified_result_with_budget(cex, remaining_budget)
    }

    /// Cheap structural Safe guard for the public verified-result boundary.
    ///
    /// This does not replace full model verification in the producing path.
    /// It prevents unverifiable placeholder Safe results, such as BMC
    /// acyclic-exhaustion's empty model, from being wrapped as
    /// `VerifiedChcResult::Safe`.
    pub(crate) fn final_safe_model_has_required_interpretations(
        &self,
        model: &InvariantModel,
    ) -> bool {
        if model.is_empty() {
            return self.problem.predicates().is_empty();
        }

        self.problem.predicates().iter().all(|pred| {
            model.get(&pred.id).is_some()
                || !self.problem_references_predicate_for_final_safe(pred.id)
        })
    }

    fn problem_references_predicate_for_final_safe(&self, target: PredicateId) -> bool {
        self.problem.clauses().iter().any(|clause| {
            clause
                .body
                .predicates
                .iter()
                .any(|(pred_id, _)| *pred_id == target)
                || clause.head.predicate_id() == Some(target)
        })
    }

    /// Fix B1: complete a final Safe model that lacks interpretations for some
    /// referenced predicates, then fully re-verify it on the ORIGINAL problem.
    ///
    /// Preprocessing (e.g. `ClauseInliner`) can eliminate predicates, so an
    /// engine model that already passed full verification on the preprocessed
    /// problem only interprets the surviving predicates. The structural gate
    /// `final_safe_model_has_required_interpretations` would demote such a
    /// result to Unknown even though it is correct (O0_sendmail-class
    /// regressions). Instead, materialize constant interpretations for the
    /// missing predicates and run the full strict verifier against the
    /// original clauses. Verification — not the structural gate — is the
    /// soundness criterion:
    /// - consecutions INTO a `true` predicate are trivially satisfied, and
    ///   consecutions/queries FROM it become strictly harder obligations;
    /// - queries FROM a `false` predicate are trivially satisfied, and
    ///   consecutions INTO it become strictly harder obligations
    ///   (e.g. `Inv ∧ φ → error` must be refuted — the safety proof itself);
    /// - full clause verification checks every obligation on the original
    ///   problem, so no choice of constants can yield an unsound accept.
    ///
    /// Two candidate completions are tried in order:
    /// 1. `false` for missing predicates that feed a query clause
    ///    (`P ∧ ... → false`), `true` for the rest. This matches the
    ///    inlined-error-predicate shape (O0_sendmail).
    /// 2. `true` for every missing predicate.
    ///
    /// Returns the first completed model that fully verifies, or `None` when
    /// nothing was materialized or no candidate verifies within budget (the
    /// caller then demotes to Unknown exactly as before).
    pub(crate) fn try_complete_final_safe_model_with_constant_interpretations(
        &self,
        model: &InvariantModel,
        remaining_budget: Option<Duration>,
    ) -> Option<InvariantModel> {
        if remaining_budget.is_some_and(|budget| budget.is_zero()) {
            return None;
        }

        let missing: Vec<&crate::Predicate> = self
            .problem
            .predicates()
            .iter()
            .filter(|pred| {
                model.get(&pred.id).is_none()
                    && self.problem_references_predicate_for_final_safe(pred.id)
            })
            .collect();
        if missing.is_empty() {
            return None;
        }

        // Predicates appearing in the body of a query clause (head = false):
        // their natural completion is `false` (the proof that the query is
        // unreachable), not `true` (which would make the query trivially SAT).
        let feeds_query: Vec<bool> = missing
            .iter()
            .map(|pred| {
                self.problem.clauses().iter().any(|clause| {
                    clause.head.predicate_id().is_none()
                        && clause
                            .body
                            .predicates
                            .iter()
                            .any(|(pred_id, _)| *pred_id == pred.id)
                })
            })
            .collect();

        let candidates: Vec<Vec<bool>> = {
            let query_aware: Vec<bool> = feeds_query.iter().map(|feeds| !feeds).collect();
            let all_true: Vec<bool> = vec![true; missing.len()];
            if query_aware == all_true {
                vec![all_true]
            } else {
                vec![query_aware, all_true]
            }
        };

        for constants in candidates {
            let mut completed = model.clone();
            for (pred, value) in missing.iter().zip(constants.iter()) {
                let vars: Vec<ChcVar> = pred
                    .arg_sorts
                    .iter()
                    .enumerate()
                    .map(|(i, sort)| {
                        ChcVar::new(format!("__p{}_a{}", pred.id.index(), i), sort.clone())
                    })
                    .collect();
                completed.set(
                    pred.id,
                    PredicateInterpretation::new(vars, ChcExpr::Bool(*value)),
                );
            }

            // The completed model is a new artifact: engine-internal shortcut
            // flags from the source model no longer describe it.
            completed.individually_inductive = false;
            completed.convergence_proven = false;

            // Recompute the cap per attempt so a slow first candidate cannot
            // overdraw the remaining global budget.
            let validation_budget = remaining_budget
                .map_or(FINAL_SAFE_COMPLETION_VALIDATION_BUDGET, |remaining| {
                    remaining.min(FINAL_SAFE_COMPLETION_VALIDATION_BUDGET)
                });
            if validation_budget.is_zero() {
                return None;
            }
            let validation_config = PdrConfig {
                verbose: self.config.verbose,
                strict_proofs: true,
                solve_timeout: Some(validation_budget),
                disable_array_scalarization: true,
                preserve_original_clauses: true,
                ..PdrConfig::default()
            };
            let verified = crate::engines::validate_external_invariant_model(
                &self.problem,
                &completed,
                &validation_config,
            )
            .unwrap_or(false);

            tracing::debug!(
                materialized = missing.len(),
                model_predicates = model.len(),
                completed_predicates = completed.len(),
                verified,
                validation_budget_secs = validation_budget.as_secs_f64(),
                "Adaptive: final Safe model completion with constant interpretations"
            );

            if verified {
                return Some(completed);
            }
        }

        None
    }

    /// Fix V1: independently re-prove safety of the ORIGINAL problem by
    /// exhaustive bounded model checking of its acyclic predicate DAG.
    ///
    /// For CHC check-sat only the *verdict* is scored — the per-predicate
    /// witness is optional. A Safe result can therefore be accepted without a
    /// materialized invariant, provided the verdict itself is soundly
    /// established. This helper re-establishes that proof here, on the original
    /// clauses, instead of trusting the carried evidence label.
    ///
    /// SOUNDNESS — why the evidence label is NOT trusted: the `MultiPredComplex`
    /// strategy dispatch stamps `ValidationEvidence::FullVerification` on
    /// whatever `solve_multi_pred_complex` returns, *unconditionally*. The
    /// acyclic-BMC probe inside that route already produces the genuine
    /// `ScalarAcyclicBmcExhaustive` evidence, but it is discarded (the caller
    /// keeps only the `PortfolioResult` and drops the evidence) and then
    /// overwritten with the blanket `FullVerification`. So at the finalize gate
    /// a `FullVerification` + empty/partial model does NOT prove that full
    /// original-clause verification ran — it only proves *some* engine returned
    /// Safe. Per the soundness contract ("any path where FullVerification is set
    /// without actual original-clause verification must still validate or
    /// demote"), we re-derive the proof here rather than trust the label.
    ///
    /// Why an acyclic exhaustive BMC is a complete proof: for an ACYCLIC
    /// predicate dependency graph, unrolling every predicate to the longest
    /// condensation-DAG path is exhaustive. Once that bound is reached without a
    /// counterexample, no deeper unrolling can produce one, so the system is
    /// safe. This is exactly the proof the `ScalarAcyclicBmcExhaustive` admission
    /// gate already accepts for scalar empty models; here we simply re-run it.
    ///
    /// Restricted to scalar (Int/Bool) acyclic systems, mirroring that gate:
    /// array/real/datatype empty models are NOT proof-grade (a finite unrolling
    /// is not a complete decision procedure for those theories) and must keep
    /// demoting. Returns `true` only when the re-proof on the original problem
    /// returns Safe; an Unsafe/Unknown/NotApplicable BMC outcome (or a cyclic /
    /// non-scalar problem) yields `false`, so the caller demotes as before.
    pub(crate) fn final_safe_verdict_reproved_on_original(
        &self,
        remaining_budget: Option<Duration>,
    ) -> bool {
        // Decidable-finite acyclic only: mirrors `bmc_only_empty_safe_is_proof_grade`
        // (adaptive_engines.rs). A definite UNSAT of the fully-unrolled acyclic
        // query disjunction is a COMPLETE safety proof for any decidable
        // finite-value theory: scalar Bool/Int, BV, and FINITE (non-recursive)
        // datatypes over them (2026-07-13: was a blanket `has_datatype_sorts`
        // exclusion, which demoted the rust-horn ~Mut/%Point tuple family whose
        // acyclic probe proves Safe in milliseconds). RECURSIVE datatypes, reals,
        // and arrays (unbounded value space) stay excluded — bounded unroll is
        // incomplete for them.
        if self.problem.has_cycles()
            || self.problem.has_array_sorts()
            || self.problem.has_real_sorts()
            || self.problem.has_recursive_datatype_sorts()
        {
            return false;
        }

        let budget = remaining_budget.map_or(FINAL_SAFE_ACYCLIC_BMC_REPROOF_BUDGET, |remaining| {
            remaining.min(FINAL_SAFE_ACYCLIC_BMC_REPROOF_BUDGET)
        });
        if budget.is_zero() {
            return false;
        }

        // Re-derive features on the original problem and mirror the acyclic-BMC
        // probe's gating and depth exactly so we reproduce the same proof.
        let features = ProblemClassifier::classify(&self.problem);
        if features.has_cycles || features.num_predicates <= 1 {
            return false;
        }
        let depth = features.dag_depth.max(features.num_predicates).max(1);

        let bmc = BmcSolver::new(
            self.problem.clone(),
            BmcConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                max_depth: depth,
                // Declare Safe only on exhaustive acyclic unrolling — the
                // soundness-critical flag for this proof.
                acyclic_safe: true,
                prefer_exact_acyclic_first: false,
                per_depth_timeout: None,
                time_budget: Some(budget),
                enable_k_induction: false,
                enable_adaptive_stepping: false,
                proof_cross_check: false,
                ts_probe_clamp: None,
                sweep_past_spurious_sat: true,
            },
        );
        let reproved = matches!(bmc.solve(), PortfolioResult::Safe(_));
        tracing::debug!(
            depth,
            reproved,
            budget_secs = budget.as_secs_f64(),
            "Adaptive: Fix V1 acyclic-BMC safety re-proof on the original problem"
        );
        reproved
    }

    /// Returns true when bounded final-validation demotion diagnostics are enabled.
    pub(crate) fn final_validation_diagnostics_enabled(&self) -> bool {
        self.config.verbose || std::env::var_os(FINAL_VALIDATION_DIAGNOSTICS_ENV).is_some()
    }

    /// Build a bounded one-line summary for `Unsafe -> Unknown` demotions.
    pub(crate) fn format_final_validation_demotion_diagnostics(
        &self,
        stage: &'static str,
        source_evidence: &ValidationEvidence,
        cex: &Counterexample,
    ) -> String {
        let format_step = |idx: usize, step: &crate::pdr::CounterexampleStep| {
            let pred_name = self
                .problem
                .get_predicate(step.predicate)
                .map(|pred| pred.name.as_str())
                .unwrap_or("?");
            format!("{idx}:{pred_name}/vars={}", step.assignments.len())
        };
        let head = cex
            .steps
            .iter()
            .take(FINAL_VALIDATION_DIAGNOSTIC_HEAD_STEPS)
            .enumerate()
            .map(|(idx, step)| format_step(idx, step))
            .collect::<Vec<_>>()
            .join(", ");
        let tail = cex
            .steps
            .last()
            .map(|step| format_step(cex.steps.len().saturating_sub(1), step))
            .unwrap_or_else(|| "none".to_string());

        let mut message = format!(
            "Adaptive: final validation demoted Unsafe -> Unknown \
             (stage={stage}, source_evidence={source_evidence:?}, depth={}, witness={}, \
             head=[{head}], tail={tail}",
            cex.steps.len(),
            cex.witness.is_some(),
        );
        if cex.steps.len() > FINAL_VALIDATION_DIAGNOSTIC_HEAD_STEPS {
            let omitted = cex.steps.len() - FINAL_VALIDATION_DIAGNOSTIC_HEAD_STEPS;
            let _ = write!(message, ", omitted_steps={omitted}");
        }
        if let Some(witness) = &cex.witness {
            let _ = write!(message, ", witness_entries={}", witness.entries.len());
        }
        message.push(')');
        message
    }

    /// Emit bounded final-validation demotion diagnostics when explicitly enabled.
    pub(crate) fn emit_final_validation_demotion_diagnostics(
        &self,
        stage: &'static str,
        source_evidence: &ValidationEvidence,
        cex: &Counterexample,
    ) {
        if !self.final_validation_diagnostics_enabled() {
            return;
        }
        safe_eprintln!(
            "{}",
            self.format_final_validation_demotion_diagnostics(stage, source_evidence, cex)
        );
    }

    pub(crate) fn validate_adaptive_result(&self, result: PdrResult) -> PdrResult {
        match result {
            // #8782: Models with convergence_proven=true from the main PDR
            // blocking loop are inductive by the convergence theorem. However,
            // at the adaptive layer we cannot distinguish startup convergence
            // (heuristic, potentially unsound) from blocking-loop convergence
            // (sound). Use full validation with extended budget for convergence
            // models to catch startup-heuristic false proofs (#8578) while
            // still accepting correct convergence proofs.
            PdrResult::Safe(ref model) if model.convergence_proven => {
                // Extended budget: convergence models are typically from complex
                // multi-predicate problems where standard 1.5s may be tight.
                let budget = Duration::from_secs(3);
                self.validate_adaptive_result_with_budget(result, budget)
            }
            // Safe validation is mandatory: direct adaptive Safe results
            // bypass the portfolio's always-on Safe validation (#5382, #7688).
            //
            // #9227: Query-only validation is not a sound final gate for
            // `individually_inductive` or `convergence_proven` PDR models. It
            // only checks that the candidate blocks bad states; it does not
            // re-check initiation and transition clauses against the original
            // CHC system in a fresh context. If full validation cannot prove
            // those obligations within budget, demote to Unknown.
            PdrResult::Safe(_) => self
                .validate_adaptive_result_with_budget(result, Self::VALIDATION_BUDGET_1INDUCTIVE),
            // Unsafe validation is mandatory for EVERY adaptive Unsafe
            // (inc-9, gate g4). Previously, without `config.validate` /
            // `strict_proofs` the result was DROPPED without any
            // re-verification attempt; now it always goes through the same
            // fresh strict re-verification (witness replay, or the bounded
            // BMC cex replay for witness-free multipred counterexamples) and
            // is accepted ONLY when that verification confirms it — still
            // fail-closed, but no longer blind to genuine refutations.
            PdrResult::Unsafe(_) => self
                .validate_adaptive_result_with_budget(result, Self::VALIDATION_BUDGET_1INDUCTIVE),
            PdrResult::Unknown | PdrResult::NotApplicable => PdrResult::Unknown,
        }
    }

    /// Validate with a configurable budget for Safe model verification.
    ///
    /// For 1-inductive engines (PDR, TPA, CEGAR). Transition clauses are
    /// checked with the given budget — expiry means rejection (#5745).
    fn validate_adaptive_result_with_budget(
        &self,
        result: PdrResult,
        safe_budget: Duration,
    ) -> PdrResult {
        match &result {
            PdrResult::Safe(model) => {
                let mut verifier = self.new_validation_solver();
                if verifier.verify_model_with_budget(model, safe_budget) {
                    result
                } else {
                    tracing::debug!(
                        "Adaptive: direct Safe result failed external validation, demoting to Unknown"
                    );
                    PdrResult::Unknown
                }
            }
            PdrResult::Unsafe(cex) => {
                if self.validate_direct_unsafe_counterexample(cex) {
                    result
                } else {
                    tracing::debug!(
                        "Adaptive: direct Unsafe result failed external validation, demoting to Unknown"
                    );
                    PdrResult::Unknown
                }
            }
            // NotApplicable is an engine-internal signal; convert to Unknown
            // at the validation boundary so it never escapes the adaptive layer.
            PdrResult::Unknown | PdrResult::NotApplicable => PdrResult::Unknown,
        }
    }
}

/// Compute BV bit-group mapping from the original (pre-BvToBool) problem (#5877).
///
/// For each predicate, identifies which consecutive Bool argument ranges in the
/// transformed problem correspond to a single original BV argument. Returns groups
/// for the first predicate (single-predicate simple-loop problems have exactly one).
///
/// Example: original `P(Bool, BV32, Int)` → transformed `P(Bool, Bool*32, Int)`.
/// Returns `[(1, 32)]` — args 1..33 are bits of one BV32 variable.
///
/// Datatype predicate arguments are expanded the same way as `DtFlattener` before
/// BvToBool runs. This lets BV group equality discovery see constructor payloads
/// such as `Option<BV16>::Some(val)`, whose payload becomes a top-level Bool bit
/// group only after datatype flattening.
pub(crate) fn compute_bv_bit_groups(original_problem: &ChcProblem) -> Vec<(usize, u32)> {
    let mut groups = Vec::new();
    // Use the first predicate (simple-loop problems have exactly one).
    let Some(pred) = original_problem.predicates().first() else {
        return groups;
    };
    let mut expanded_idx = 0;
    for sort in &pred.arg_sorts {
        collect_bv_bit_groups_for_sort(sort, &mut expanded_idx, &mut groups, &mut Vec::new());
    }
    groups
}

fn collect_bv_bit_groups_for_sort(
    sort: &ChcSort,
    expanded_idx: &mut usize,
    groups: &mut Vec<(usize, u32)>,
    dt_stack: &mut Vec<String>,
) {
    match sort {
        // BvToBool currently expands predicate BV args up to 64 bits and leaves
        // wider vectors as a single BV argument for downstream lanes.
        ChcSort::BitVec(width) if *width <= 64 => {
            groups.push((*expanded_idx, *width));
            *expanded_idx += *width as usize;
        }
        ChcSort::Datatype { name, constructors }
            if dt_stack.iter().filter(|seen| *seen == name).count() >= 3 =>
        {
            // Match DtFlattener's recursive backedge cutoff: no scalar component
            // is emitted once the legacy recursive depth limit is reached.
        }
        ChcSort::Datatype { name, constructors } if constructors.len() == 1 => {
            dt_stack.push(name.clone());
            let ctor = &constructors[0];
            if ctor.selectors.is_empty() {
                *expanded_idx += 1;
                dt_stack.pop();
                return;
            }
            for selector in &ctor.selectors {
                collect_bv_bit_groups_for_sort(&selector.sort, expanded_idx, groups, dt_stack);
            }
            dt_stack.pop();
        }
        ChcSort::Datatype { name, constructors } => {
            // Multi-constructor datatypes flatten to an Int discriminant followed
            // by union payload slots in constructor order.
            dt_stack.push(name.clone());
            *expanded_idx += 1;
            let union_sorts = multi_ctor_union_flat_sorts(constructors, dt_stack);
            for field_sort in union_sorts {
                collect_bv_bit_groups_for_sort(&field_sort, expanded_idx, groups, dt_stack);
            }
            dt_stack.pop();
        }
        _ => {
            *expanded_idx += 1;
        }
    }
}

fn multi_ctor_union_flat_sorts(
    constructors: &[crate::ChcDtConstructor],
    dt_stack: &mut Vec<String>,
) -> Vec<ChcSort> {
    let max_fields = constructors
        .iter()
        .map(|ctor| {
            ctor.selectors
                .iter()
                .map(|selector| flattened_sort_count_for_groups(&selector.sort, dt_stack))
                .sum::<usize>()
        })
        .max()
        .unwrap_or(0);
    let mut union_sorts = vec![ChcSort::Int; max_fields];

    for ctor in constructors {
        let mut pos = 0;
        for selector in &ctor.selectors {
            let flat_sorts = flattened_sorts_for_groups(&selector.sort, dt_stack);
            for sort in flat_sorts {
                if pos < union_sorts.len() {
                    union_sorts[pos] = sort;
                }
                pos += 1;
            }
        }
    }

    union_sorts
}

fn flattened_sort_count_for_groups(sort: &ChcSort, dt_stack: &mut Vec<String>) -> usize {
    flattened_sorts_for_groups(sort, dt_stack).len()
}

fn flattened_sorts_for_groups(sort: &ChcSort, dt_stack: &mut Vec<String>) -> Vec<ChcSort> {
    match sort {
        ChcSort::Datatype { name, .. }
            if dt_stack.iter().filter(|seen| *seen == name).count() >= 3 =>
        {
            Vec::new()
        }
        ChcSort::Datatype { name, constructors } if constructors.len() == 1 => {
            dt_stack.push(name.clone());
            let ctor = &constructors[0];
            if ctor.selectors.is_empty() {
                dt_stack.pop();
                return vec![ChcSort::Bool];
            }
            let result = ctor
                .selectors
                .iter()
                .flat_map(|selector| flattened_sorts_for_groups(&selector.sort, dt_stack))
                .collect();
            dt_stack.pop();
            result
        }
        ChcSort::Datatype { name, constructors } => {
            dt_stack.push(name.clone());
            let mut result = vec![ChcSort::Int];
            result.extend(multi_ctor_union_flat_sorts(constructors, dt_stack));
            dt_stack.pop();
            result
        }
        _ => vec![sort.clone()],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ClauseBody, ClauseHead, HornClause};
    use std::sync::Arc;

    /// Two-predicate acyclic DAG `P -> Q`. `safe = true` makes the query
    /// unreachable; `safe = false` makes it reachable (genuine cex). Both are
    /// acyclic and scalar (Int), so an exhaustive acyclic BMC is a complete
    /// decision procedure.
    fn acyclic_dag_two_pred(safe: bool) -> ChcProblem {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::Int]);
        let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);
        let y = ChcVar::new("y", ChcSort::Int);

        // x = 0 => P(x)
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
            ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
        ));
        // P(x) /\ y = x + 1 => Q(y)   (acyclic edge P -> Q)
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(p, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::eq(
                    ChcExpr::var(y.clone()),
                    ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1)),
                )),
            ),
            ClauseHead::Predicate(q, vec![ChcExpr::var(y.clone())]),
        ));
        // Query: Q(y) /\ guard => false. y is always 1.
        // safe: guard `y < 0` is never reachable; unsafe: guard `y = 1` is.
        let guard = if safe {
            ChcExpr::lt(ChcExpr::var(y.clone()), ChcExpr::int(0))
        } else {
            ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(1))
        };
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(q, vec![ChcExpr::var(y)])], Some(guard)),
            ClauseHead::False,
        ));
        problem
    }

    /// Fix V1: a scalar acyclic SAFE multi-predicate problem is re-proved on the
    /// original clauses, so the finalize gate can accept the verdict without a
    /// materialized witness.
    #[test]
    fn v1_reproves_acyclic_scalar_safe_problem() {
        let adaptive = AdaptivePortfolio::new(
            acyclic_dag_two_pred(true),
            crate::AdaptiveConfig::test_default(),
        );
        assert!(
            adaptive.final_safe_verdict_reproved_on_original(Some(Duration::from_secs(5))),
            "exhaustive acyclic BMC must re-prove a safe scalar acyclic DAG"
        );
    }

    /// Fix V1 soundness: the re-proof must NOT report Safe on an UNSAFE problem,
    /// even though it is acyclic and scalar (BMC finds the counterexample).
    #[test]
    fn v1_does_not_reprove_acyclic_scalar_unsafe_problem() {
        let adaptive = AdaptivePortfolio::new(
            acyclic_dag_two_pred(false),
            crate::AdaptiveConfig::test_default(),
        );
        assert!(
            !adaptive.final_safe_verdict_reproved_on_original(Some(Duration::from_secs(5))),
            "re-proof must never accept an unsafe problem"
        );
    }

    /// Fix V1 soundness: cyclic problems are out of scope for an acyclic
    /// exhaustion proof and must be rejected by the guard (no false re-proof).
    #[test]
    fn v1_does_not_reprove_cyclic_problem() {
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);
        // x = 0 => Inv(x)
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
        ));
        // Inv(x) => Inv(x + 1)   (self-loop -> cyclic dependency graph)
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(inv, vec![ChcExpr::var(x.clone())])], None),
            ClauseHead::Predicate(
                inv,
                vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
            ),
        ));
        // Inv(x) /\ x < 0 => false   (safe but cyclic; re-proof must still bail)
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
            ),
            ClauseHead::False,
        ));

        let adaptive = AdaptivePortfolio::new(problem, crate::AdaptiveConfig::test_default());
        assert!(
            !adaptive.final_safe_verdict_reproved_on_original(Some(Duration::from_secs(5))),
            "cyclic problems must not be re-proved by acyclic exhaustion"
        );
    }

    #[test]
    fn default_mode_demotes_unverified_adaptive_unsafe() {
        #[allow(deprecated)]
        let config = crate::AdaptiveConfig {
            validate: false,
            strict_proofs: false,
            ..crate::AdaptiveConfig::test_default()
        };
        let adaptive = AdaptivePortfolio::new(ChcProblem::new(), config);

        let result =
            adaptive.validate_adaptive_result(PdrResult::Unsafe(Counterexample::new(Vec::new())));

        assert!(
            matches!(result, PdrResult::Unknown),
            "default-mode adaptive Unsafe without internal re-verification must fail closed"
        );
        // inc-9 (gate g4): the result is now RE-VERIFIED (and rejected on
        // failure) instead of being dropped as a trust-proof fallback, so
        // the fallback counter stays at zero.
        assert_eq!(adaptive.statistics().trust_proof_fallbacks, 0);
    }

    #[test]
    fn bv_bit_groups_include_datatype_payloads() {
        let option_bv16 = ChcSort::Datatype {
            name: "OptBV16".to_string(),
            constructors: Arc::new(vec![
                crate::ChcDtConstructor {
                    name: "none16".to_string(),
                    selectors: Vec::new(),
                },
                crate::ChcDtConstructor {
                    name: "some16".to_string(),
                    selectors: vec![crate::ChcDtSelector {
                        name: "val16".to_string(),
                        sort: ChcSort::BitVec(16),
                    }],
                },
            ]),
        };
        let mut problem = ChcProblem::new();
        problem.declare_predicate("inv", vec![option_bv16.clone(), option_bv16]);

        assert_eq!(compute_bv_bit_groups(&problem), vec![(1, 16), (18, 16)]);
    }

    #[test]
    fn bv_bit_groups_include_nested_datatype_payloads() {
        let result_bv8 = ChcSort::Datatype {
            name: "Result8".to_string(),
            constructors: Arc::new(vec![
                crate::ChcDtConstructor {
                    name: "ok".to_string(),
                    selectors: vec![crate::ChcDtSelector {
                        name: "ok_val".to_string(),
                        sort: ChcSort::BitVec(8),
                    }],
                },
                crate::ChcDtConstructor {
                    name: "err".to_string(),
                    selectors: vec![crate::ChcDtSelector {
                        name: "err_val".to_string(),
                        sort: ChcSort::BitVec(8),
                    }],
                },
            ]),
        };
        let state = ChcSort::Datatype {
            name: "State".to_string(),
            constructors: Arc::new(vec![crate::ChcDtConstructor {
                name: "mk_state".to_string(),
                selectors: vec![
                    crate::ChcDtSelector {
                        name: "tag".to_string(),
                        sort: result_bv8,
                    },
                    crate::ChcDtSelector {
                        name: "counter".to_string(),
                        sort: ChcSort::BitVec(8),
                    },
                ],
            }]),
        };
        let mut problem = ChcProblem::new();
        problem.declare_predicate("inv", vec![state]);

        assert_eq!(compute_bv_bit_groups(&problem), vec![(1, 8), (9, 8)]);
    }
}
