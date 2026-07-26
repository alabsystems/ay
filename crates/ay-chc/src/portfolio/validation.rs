// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Validation and engine-result conversion for the CHC portfolio.
//!
//! Soundness verification of Safe/Unsafe results and normalization of
//! per-engine result types into the unified `PortfolioResult`.

use super::preprocess::sort_contains_recursive_bv;
use super::{EngineResult, PortfolioResult, PortfolioSolver};
use crate::pdr::{
    CexVerificationResult, Counterexample, InvariantModel, PdrConfig, PdrSolver,
    PredicateInterpretation,
};
use crate::transform::{accept_profile_enabled, BackTranslator};
use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::time::Duration;

/// Hard timeout for validation sub-solvers (#8630).
///
/// Validation PdrSolvers (verify_counterexample, verify_model) are created
/// fresh in the acceptance pipeline. Without a timeout, they can hang
/// indefinitely — e.g., BV-domain confirmation creating a PdrSolver that
/// runs an expensive verify_counterexample on the original BV problem.
///
/// This is a safety cap; the cooperative cancellation token (from the
/// portfolio) normally stops them earlier.
const VALIDATION_TIMEOUT: Duration = Duration::from_secs(30);

/// Back-translate a counterexample and replace transformed ground evidence.
///
/// `BackTranslator::translate_invalidity` predates `GroundDerivation` and
/// remaps only the legacy step/witness representation. Clone-based
/// translators therefore leave a transformed clause-indexed ground proof
/// attached. This helper runs the proof through its separate fallible
/// translator, validates it against `original_problem`, and replaces (or
/// clears) the stale attachment.
///
/// The returned ground derivation is still only candidate evidence: every
/// acceptance site re-validates it on the clauses it owns.
pub(crate) fn backtranslate_counterexample_with_ground_evidence(
    back_translator: &dyn BackTranslator,
    original_problem: &ChcProblem,
    cex: &Counterexample,
) -> Counterexample {
    let mut translated = back_translator.translate_invalidity(cex.clone());
    let Some(transformed_derivation) = &cex.ground_derivation else {
        return translated;
    };

    let _witness_budget = crate::ground_derivation::witness::ScopedWitnessChainBudget::new();
    translated.ground_derivation = back_translator
        .translate_ground_derivation(transformed_derivation)
        .and_then(|candidate| {
            match crate::ground_derivation::validate_ground_derivation(original_problem, &candidate)
            {
                Ok(()) => Some(candidate),
                Err(err) => {
                    crate::ground_derivation::log_ground_translation_detail(format_args!(
                        "portfolio ground back-translation rejected on original clauses: {err}"
                    ));
                    None
                }
            }
        });
    translated
}

/// Validation result
#[derive(Debug, Clone)]
pub(super) enum ValidationResult {
    /// Result validated successfully
    Valid,
    /// Result failed validation - return Unknown instead
    Invalid(String),
}

/// Result of the query-only pre-check for Safe results (Step 4.5).
///
/// Distinguishes genuinely invalid models from the ambiguous case where
/// the invariant happens to equal `not(query)`. The latter cannot be
/// decided by query-only checking alone (#6789) — full per-rule
/// validation must decide it (#1306).
#[derive(Debug, Clone)]
pub(super) enum SafePrecheckResult {
    /// Model passes query-only validation — proceed to Step 5.
    Valid,
    /// Model is exactly `not(query)` for some predicate. Query-only
    /// validation is tautological for this model; defer to Step 5
    /// full validation to decide inductiveness. (#1306, #6789)
    ExactNegatedQuery(String),
    /// Model genuinely fails query-only validation — reject now.
    Invalid(String),
}

/// Budget for Safe model verification.
///
/// Replaces raw `Duration` in `validate_safe_with_budget` to make the intent
/// explicit. `Duration::ZERO` formerly had two incompatible meanings
/// ("skip transition clauses" vs "immediate reject") — the query-only path
/// is now structurally separate via `verify_model_query_only` (#5825).
///
/// Part of #5746: structural verification invariant Phase 2.
#[derive(Debug, Clone, Copy)]
pub(crate) enum ValidationBudget {
    /// Standard budget for 1-inductive engines (PDR, TPA, CEGAR, BMC).
    /// Checks init + transition + query clauses.
    /// Budget: 1.5s for LIA, 15s for BV problems.
    Standard,

    /// Per-rule independent budget: each clause gets its own budget allocation.
    /// Uses verify_model_per_rule instead of verify_model_with_budget.
    /// This prevents budget exhaustion where early complex clauses (mod/div)
    /// consume the shared budget, causing valid models to be rejected.
    /// Part of #5653: tiered verification design Phase 1.
    PerRule,
}

impl ValidationBudget {
    /// Resolve to a concrete Duration for verify_model_with_budget.
    pub(crate) fn to_duration(self, problem: &ChcProblem) -> Duration {
        match self {
            Self::Standard => {
                let has_bv = problem
                    .predicates()
                    .iter()
                    .any(|p| p.arg_sorts.iter().any(|s| matches!(s, ChcSort::BitVec(_))));
                if has_bv {
                    Duration::from_secs(15)
                } else {
                    Duration::from_millis(1500)
                }
            }
            Self::PerRule => Duration::from_secs(2), // per-rule budget (reverted from 5s #5970 D2)
        }
    }
}

impl PortfolioSolver {
    /// Validate a Safe result (model) using PDR's verify_model
    ///
    /// Returns Valid if the model is correct, Invalid if verification fails.
    /// This catches soundness bugs like #421 where engines return Safe
    /// with an invalid invariant.
    ///
    /// Note: We validate against the original problem, not the transformed one.
    /// The model is back-translated before validation if preprocessing was applied.
    pub(super) fn validate_safe(&self, model: &InvariantModel) -> ValidationResult {
        self.validate_safe_with_mode(model, ValidationBudget::Standard)
    }

    /// Validate a Safe result with a configurable verification budget.
    ///
    /// All engines use a non-zero budget that checks init, transition, and query
    /// clauses. There are no skip paths — portfolio always runs full verification
    /// (#5745). Budget determines max wall-clock time for transition clause checks.
    ///
    /// `ValidationBudget::Standard` resolves to 1.5s for LIA, 15s for BV problems.
    /// Part of #5746: replaces raw `Duration` parameter for audit clarity.
    pub(super) fn validate_safe_with_mode(
        &self,
        model: &InvariantModel,
        mode: ValidationBudget,
    ) -> ValidationResult {
        match self.validate_safe_with_mode_translating(model, mode) {
            Ok(_) => ValidationResult::Valid,
            Err(reason) => ValidationResult::Invalid(reason),
        }
    }

    /// Like [`validate_safe_with_mode`](Self::validate_safe_with_mode), but on
    /// success returns the back-translated model that actually passed
    /// verification against the ORIGINAL problem.
    ///
    /// Fix B1 (stop discarding verified Safe results): preprocessing (e.g.
    /// `ClauseInliner`) eliminates predicates, so the engine-space model only
    /// interprets the survivors. Validation back-translates the model —
    /// synthesizing interpretations for inlined predicates — and verifies the
    /// TRANSLATED model on the original clauses. Returning only a boolean and
    /// keeping the engine-space model made the downstream
    /// `final_safe_model_has_required_interpretations` gate demote the result
    /// to Unknown (O0_sendmail-class regressions). Callers that accept the
    /// Safe result must carry this translated model forward.
    pub(super) fn validate_safe_with_mode_translating(
        &self,
        model: &InvariantModel,
        mode: ValidationBudget,
    ) -> Result<InvariantModel, String> {
        let translated_model = self.back_translate_safe_model(model)?;
        self.validate_safe_with_mode_pre_translated(translated_model, mode)
    }

    /// Back-translate an engine-space Safe model to the ORIGINAL problem
    /// vocabulary, synthesizing interpretations for eliminated predicates.
    ///
    /// Split out of [`validate_safe_with_mode_translating`] so the acceptance
    /// pipeline translates ONCE and shares the result between the query-only
    /// pre-check (Step 4.5) and mandatory full validation (Step 5) — on
    /// 16-eliminated-predicate graph-collapse stacks each translation costs
    /// the full synthesized-interpretation construction.
    ///
    /// Fails closed: an empty or incomplete translation is an `Err`, which
    /// every caller maps to a rejected Safe result.
    pub(super) fn back_translate_safe_model(
        &self,
        model: &InvariantModel,
    ) -> Result<InvariantModel, String> {
        // Back-translate the model to the original problem vocabulary
        if self.config.verbose {
            for (pid, interp) in model.iter() {
                safe_eprintln!(
                    "Portfolio: validate_safe pre-backtranslate: pred {} vars={:?} formula={}",
                    pid.index(),
                    interp
                        .vars
                        .iter()
                        .map(|v| format!("{}:{}", v.name, v.sort))
                        .collect::<Vec<_>>(),
                    interp.formula,
                );
            }
        }
        let profile = accept_profile_enabled();
        let t_translate = ay_core::time::Instant::now();
        let mut translated_model = self.back_translator.translate_validity(model.clone());
        if profile {
            safe_eprintln!(
                "[ACCEPT-PROF] back_translate_safe_model dt={:.3}s",
                t_translate.elapsed().as_secs_f64()
            );
        }
        self.complete_unreferenced_predicate_interpretations(&mut translated_model);
        if self.config.verbose {
            for (pid, interp) in translated_model.iter() {
                safe_eprintln!(
                    "Portfolio: validate_safe post-backtranslate: pred {} vars={:?} formula={}",
                    pid.index(),
                    interp
                        .vars
                        .iter()
                        .map(|v| format!("{}:{}", v.name, v.sort))
                        .collect::<Vec<_>>(),
                    interp.formula,
                );
            }
        }
        if translated_model.is_empty() {
            if self.original_problem.predicates().is_empty() {
                // Truly predicate-free problem: no interpretations are required.
                return Ok(translated_model);
            }
            return Err(format!(
                "Empty Safe model after back-translation (no predicate interpretations); {}",
                self.transform_memory_diagnostic()
            ));
        }
        if self
            .original_problem
            .predicates()
            .iter()
            .any(|pred| translated_model.get(&pred.id).is_none())
        {
            return Err(format!(
                "Safe model back-translation left predicate interpretations missing; {}",
                self.transform_memory_diagnostic()
            ));
        }
        Ok(translated_model)
    }

    /// Verify an ALREADY-TRANSLATED Safe model against the ORIGINAL clauses.
    ///
    /// The model MUST come from [`back_translate_safe_model`] — it is verified
    /// as-is against `self.original_problem` with no further translation.
    pub(super) fn validate_safe_with_mode_pre_translated(
        &self,
        translated_model: InvariantModel,
        mode: ValidationBudget,
    ) -> Result<InvariantModel, String> {
        let profile = accept_profile_enabled();
        if translated_model.is_empty() && self.original_problem.predicates().is_empty() {
            // Truly predicate-free problem: no interpretations are required.
            return Ok(translated_model);
        }

        // Create a PDR solver for verification against the ORIGINAL problem.
        // Wire the portfolio's cancellation token and a hard timeout so that
        // validation bails cooperatively when the portfolio is cancelled or
        // its timeout expires (#8630).
        let config = PdrConfig {
            verbose: self.config.verbose,
            strict_proofs: true,
            cancellation_token: Some(self.cancellation_token.clone()),
            solve_timeout: Some(VALIDATION_TIMEOUT),
            disable_array_scalarization: true,
            ..PdrConfig::default()
        };
        let mut verifier = PdrSolver::new(self.original_problem.clone(), config);

        // Resolve the validation budget to a concrete Duration.
        // Standard budget is BV-aware: 15s for BV, 1.5s for LIA (#5595).
        //
        // Budget MUST match PDR's internal budget (1.5s in check_fixed_point,
        // solve.rs:1396). The per-clause VERIFY_INITIAL_TIMEOUT is 2s, so a
        // 3s budget allows one clause to return Unknown within budget, entering
        // the expensive fallback cascade instead of skipping. 1.5s ensures the
        // budget fires before the first clause's Unknown returns, matching PDR's
        // own acceptance behavior. Query clauses are always checked regardless
        // of budget (soundness-critical). (#5394)
        //
        // For k-inductive engines: the adaptive layer uses query-only validation
        // (verify_model_query_only) instead of Duration::ZERO. This validates that
        // the invariant excludes bad states without requiring 1-inductiveness. (#5211, #5825)
        let t_verify = ay_core::time::Instant::now();
        let verified = match mode {
            ValidationBudget::PerRule => {
                // #5653 Phase 1: Per-rule independent validation.
                // Each clause gets its own 2s budget instead of sharing 1.5s
                // across all clauses. This prevents budget exhaustion where
                // complex mod/div transitions steal budget from simple clauses.
                // Reverted from 5s to 2s: the 5s budget caused validation-budget
                // regressions (dillig05_m, s_multipl_13 timeout at 15s) because
                // mod/div transitions return Unknown regardless of budget, and
                // the extra 3s/clause is pure overhead.
                let per_rule = Duration::from_secs(2);
                verifier.verify_model_per_rule(&translated_model, per_rule)
            }
            _ => {
                let budget = mode.to_duration(&self.original_problem);
                verifier.verify_model_with_budget(&translated_model, budget)
            }
        };
        if profile {
            safe_eprintln!(
                "[ACCEPT-PROF] full-validation verify dt={:.3}s verified={}",
                t_verify.elapsed().as_secs_f64(),
                verified
            );
        }
        if verified {
            Ok(translated_model)
        } else {
            Err(format!(
                "Model failed PDR verification; {}",
                self.transform_memory_diagnostic()
            ))
        }
    }

    pub(super) fn complete_unreferenced_predicate_interpretations(
        &self,
        model: &mut InvariantModel,
    ) {
        let missing_unreferenced: Vec<_> = self
            .original_problem
            .predicates()
            .iter()
            .filter(|pred| model.get(&pred.id).is_none())
            .filter(|pred| !self.original_problem_references_predicate(pred.id))
            .cloned()
            .collect();

        for pred in missing_unreferenced {
            let vars = pred
                .arg_sorts
                .iter()
                .enumerate()
                .map(|(i, sort)| {
                    ChcVar::new(
                        format!("__unused_p{}_a{}", pred.id.index(), i),
                        sort.clone(),
                    )
                })
                .collect();
            model.set(
                pred.id,
                PredicateInterpretation::new(vars, ChcExpr::Bool(false)),
            );
        }
    }

    fn original_problem_references_predicate(&self, target: PredicateId) -> bool {
        self.original_problem.clauses().iter().any(|clause| {
            clause
                .body
                .predicates
                .iter()
                .any(|(pred_id, _)| *pred_id == target)
                || clause.head.predicate_id() == Some(target)
        })
    }

    /// SOUNDNESS GUARD (#6787): Mandatory query-only validation for all Safe results.
    ///
    /// Runs unconditionally for every Safe result accepted by the portfolio.
    /// Checks only query clauses — does the invariant actually exclude bad
    /// states? This is O(query_clauses) and catches false-Safe results where
    /// k-induction verification itself got a false UNSAT from the SMT solver.
    /// Full transition-clause validation is also always-on (#8585).
    pub(super) fn tautological_negated_query_reason(
        &self,
        model: &InvariantModel,
    ) -> Option<String> {
        for (pred_id, interp) in model.iter() {
            for clause in self.original_problem.queries() {
                let [(query_pred, query_args)] = clause.body.predicates.as_slice() else {
                    continue;
                };
                if *query_pred != *pred_id || query_args.len() != interp.vars.len() {
                    continue;
                }

                let mut substitutions = Vec::with_capacity(query_args.len());
                let mut binder_map = FxHashMap::default();
                let mut supported_query_shape = true;
                for (arg, model_var) in query_args.iter().zip(&interp.vars) {
                    match arg {
                        ChcExpr::Var(query_var) => {
                            if let Some(existing) = binder_map.get(query_var) {
                                if existing != model_var {
                                    supported_query_shape = false;
                                    break;
                                }
                                continue;
                            }
                            binder_map.insert(query_var.clone(), model_var.clone());
                            substitutions.push((query_var.clone(), ChcExpr::var(model_var.clone())))
                        }
                        _ => {
                            supported_query_shape = false;
                            break;
                        }
                    }
                }
                if !supported_query_shape {
                    continue;
                }

                let query_constraint = clause
                    .body
                    .constraint
                    .clone()
                    .unwrap_or(ChcExpr::Bool(true))
                    .substitute(&substitutions);
                let negated_query = ChcExpr::not(query_constraint.clone());
                let exact_false_query = matches!(query_constraint, ChcExpr::Bool(true))
                    && interp.formula == ChcExpr::Bool(false);

                // #6789: reject exact ¬query models before the SMT-level
                // query-only validator can accept them tautologically.
                if interp.formula == negated_query || exact_false_query {
                    let pred_name = self
                        .original_problem
                        .get_predicate(*pred_id)
                        .map_or_else(|| format!("P{}", pred_id.index()), |pred| pred.name.clone());
                    return Some(format!(
                        "Safe model for predicate {pred_name} is exact ¬query; query-only validation would be tautological (#6789)"
                    ));
                }
            }
        }

        None
    }

    /// Query-only pre-check that translates the model itself. Used by the
    /// algebraic-model debug assertion; the acceptance pipeline uses
    /// [`validate_safe_query_only_pre_translated`] with a shared translation.
    pub(super) fn validate_safe_query_only(&self, model: &InvariantModel) -> SafePrecheckResult {
        let translated_model = self.back_translator.translate_validity(model.clone());
        if translated_model.is_empty() {
            if self.original_problem.predicates().is_empty() {
                return SafePrecheckResult::Valid;
            }
            return SafePrecheckResult::Invalid(
                "Empty Safe model after back-translation (query-only check)".into(),
            );
        }
        self.validate_safe_query_only_pre_translated(&translated_model)
    }

    /// Query-only pre-check on an ALREADY-TRANSLATED Safe model.
    ///
    /// The model MUST come from [`back_translate_safe_model`]; the acceptance
    /// pipeline shares one translation between this pre-check and full
    /// validation.
    pub(super) fn validate_safe_query_only_pre_translated(
        &self,
        translated_model: &InvariantModel,
    ) -> SafePrecheckResult {
        let profile = accept_profile_enabled();
        if translated_model.is_empty() {
            if self.original_problem.predicates().is_empty() {
                return SafePrecheckResult::Valid;
            }
            return SafePrecheckResult::Invalid(
                "Empty Safe model after back-translation (query-only check)".into(),
            );
        }
        if let Some(reason) = self.tautological_negated_query_reason(translated_model) {
            return SafePrecheckResult::ExactNegatedQuery(reason);
        }
        // Wire the portfolio's cancellation token so query-only validation
        // bails when the portfolio is cancelled (#8630).
        let config = PdrConfig {
            verbose: self.config.verbose,
            strict_proofs: self.config.strict_proofs,
            cancellation_token: Some(self.cancellation_token.clone()),
            solve_timeout: Some(VALIDATION_TIMEOUT),
            disable_array_scalarization: true,
            ..PdrConfig::default()
        };
        let mut verifier = PdrSolver::new(self.original_problem.clone(), config);
        let t_verify = ay_core::time::Instant::now();
        let query_only_ok = verifier.verify_model_query_only(translated_model);
        if profile {
            safe_eprintln!(
                "[ACCEPT-PROF] query-only verify dt={:.3}s ok={}",
                t_verify.elapsed().as_secs_f64(),
                query_only_ok
            );
        }
        if query_only_ok {
            SafePrecheckResult::Valid
        } else {
            SafePrecheckResult::Invalid(
                "Safe model failed query-only validation — invariant does not exclude bad states"
                    .into(),
            )
        }
    }

    /// Validate an Unsafe result (counterexample) using PDR's verify_counterexample
    ///
    /// Returns Valid if the counterexample is correct, Invalid if verification fails.
    /// Look up the declared original sort of a canonical argument name like `__p0_a1`.
    /// Returns `None` if the name doesn't match the canonical pattern.
    fn canonical_arg_sort<'a>(name: &str, pred: &'a crate::Predicate) -> Option<&'a ChcSort> {
        // Canonical names are `__p<pred_idx>_a<arg_idx>`
        let after_a = name.rsplit_once("_a")?.1;
        let arg_idx: usize = after_a.parse().ok()?;
        pred.arg_sorts.get(arg_idx)
    }

    /// This catches spurious counterexamples from incomplete engines.
    ///
    /// Note: We validate against the original problem, not the transformed one.
    /// The counterexample is back-translated before validation if preprocessing was applied.
    pub(super) fn validate_unsafe(&self, cex: &crate::pdr::Counterexample) -> ValidationResult {
        self.validate_unsafe_with_timeout(cex, VALIDATION_TIMEOUT)
    }

    /// Like [`validate_unsafe`](Self::validate_unsafe), but on success returns
    /// the back-translated counterexample that actually passed verification
    /// against the ORIGINAL problem.
    ///
    /// Mirror of Fix B1 for Unsafe results: engines run on the preprocessed
    /// problem, so their counterexamples carry engine-space predicate ids and
    /// canonical names. Validation back-translates the cex and replays the
    /// TRANSLATED one on the original clauses. Returning the engine-space cex
    /// made the adaptive layer's final verified-result validation (which has
    /// `enable_preprocessing: false` and therefore an identity translator)
    /// replay transform-space metadata against the original problem and
    /// demote valid Unsafe results to Unknown (heap__swaparray-class, FM2b).
    pub(super) fn validate_unsafe_translating(
        &self,
        cex: &crate::pdr::Counterexample,
    ) -> Result<crate::pdr::Counterexample, String> {
        self.validate_unsafe_translating_with_timeout(cex, VALIDATION_TIMEOUT)
    }

    fn validate_unsafe_with_timeout(
        &self,
        cex: &crate::pdr::Counterexample,
        validation_timeout: Duration,
    ) -> ValidationResult {
        match self.validate_unsafe_translating_with_timeout(cex, validation_timeout) {
            Ok(_) => ValidationResult::Valid,
            Err(reason) => ValidationResult::Invalid(reason),
        }
    }

    fn validate_unsafe_translating_with_timeout(
        &self,
        cex: &crate::pdr::Counterexample,
        validation_timeout: Duration,
    ) -> Result<crate::pdr::Counterexample, String> {
        if !self.transform_memory.unsafe_backtranslation_complete() {
            return Err(format!(
                "Transform stack cannot reconstruct original Unsafe witnesses; {}",
                self.transform_memory_diagnostic()
            ));
        }
        let translated_cex = backtranslate_counterexample_with_ground_evidence(
            self.back_translator.as_ref(),
            &self.original_problem,
            cex,
        );

        // Defense in depth for #6047/#6293: after back-translation, witness instances for
        // BV/Array predicates must already use original-domain values. If Int-domain values
        // remain, the translator lost sort information and verification would become vacuous.
        if self.bv_abstracted {
            if let Some(witness) = &translated_cex.witness {
                let predicates = self.original_problem.predicates();
                for entry in &witness.entries {
                    let pred_idx = entry.predicate.index();
                    if pred_idx < predicates.len() {
                        let pred = &predicates[pred_idx];
                        for (name, value) in &entry.instances {
                            // Check the declared original sort of this specific argument,
                            // not a predicate-wide flag. Mixed-signature predicates like
                            // (Int, BitVec(8)) have legitimate Int arguments (#6293).
                            let arg_sort = Self::canonical_arg_sort(name, pred);
                            let expects_bv = arg_sort.map_or(false, sort_contains_recursive_bv);
                            if expects_bv && matches!(value, crate::smt::SmtValue::Int(_)) {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "Portfolio: BV-to-Int sort mismatch in counterexample: \
                                         instance '{}' has Int value but original sort is {:?}. \
                                         Rejecting as spurious (#6047).",
                                        name,
                                        arg_sort
                                    );
                                }
                                return Err("BV-to-Int counterexample has Int-domain values for \
                                     BV-sorted predicate arguments (spurious)"
                                    .into());
                            }
                        }
                    }
                }
            }
        }

        // Create a PDR solver for verification against the ORIGINAL problem.
        // Wire the portfolio's cancellation token and a hard timeout so that
        // BV-domain confirmation and other Unsafe validation bails when the
        // portfolio is cancelled or timed out (#8630).
        let config = PdrConfig {
            verbose: self.config.verbose,
            strict_proofs: self.config.strict_proofs,
            cancellation_token: Some(self.cancellation_token.clone()),
            solve_timeout: Some(validation_timeout),
            disable_array_scalarization: true,
            preserve_original_clauses: true,
            ..PdrConfig::default()
        };
        let mut verifier = PdrSolver::new(self.original_problem.clone(), config);
        verifier.set_validation_deadline(validation_timeout);

        match verifier.verify_counterexample(&translated_cex) {
            CexVerificationResult::Valid => Ok(translated_cex),
            CexVerificationResult::Spurious => Err("Counterexample is spurious (Unsat)".into()),
            CexVerificationResult::Unknown => {
                // SOUNDNESS FIX (#1288): Inconclusive verification cannot be trusted
                Err("Counterexample verification inconclusive (Unknown)".into())
            }
        }
    }

    /// Re-validate a counterexample before wrapping it in `VerifiedChcResult`.
    ///
    /// This is used at the public verified-result boundary. Both acceptance-time
    /// and verified-result-time validation are now always-on (#8585).
    pub(crate) fn validate_unsafe_for_verified_result_with_budget(
        &self,
        cex: &crate::pdr::Counterexample,
        remaining_budget: Option<Duration>,
    ) -> bool {
        if remaining_budget.is_some_and(|budget| budget.is_zero()) {
            return false;
        }

        let validation_timeout = remaining_budget
            .map(|budget| budget.min(VALIDATION_TIMEOUT))
            .unwrap_or(VALIDATION_TIMEOUT);
        matches!(
            self.validate_unsafe_with_timeout(cex, validation_timeout),
            ValidationResult::Valid
        )
    }

    /// Validate a result from any engine.
    ///
    /// All engines go through full verification (#5745). No skip paths.
    // Generic per-engine validation entry point exercised by `portfolio/tests/validation.rs`;
    // production callers currently dispatch through the more specific `validate_*` variants,
    // so this stays as the retained any-engine wrapper rather than being deleted.
    #[allow(dead_code)]
    pub(super) fn validate_result(
        &self,
        result: &PortfolioResult,
        engine_name: &str,
    ) -> ValidationResult {
        match result {
            PortfolioResult::Safe(model) => {
                // #5653 Phase 1: Per-rule independent validation for all engines.
                // Each clause gets its own 2s budget instead of sharing 1.5s across
                // all clauses. This fixes budget exhaustion where complex mod/div
                // transitions consumed the shared budget, causing valid models to be
                // rejected (#5653 regression from 53/55 to 34/55).
                //
                // Soundness: every clause is still checked (init + transition + query).
                // Safety: if any single clause fails (SAT), the model is rejected.
                // Performance: simple clauses resolve in ms; complex ones get 2s each.
                if self.config.verbose {
                    safe_eprintln!(
                        "Portfolio: validate_result: engine={}, method={:?}, per-rule verification",
                        engine_name,
                        model.verification_method,
                    );
                }
                let validation = self.validate_safe_with_mode(model, ValidationBudget::PerRule);
                if let ValidationResult::Invalid(reason) = &validation {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: {} Safe result failed validation: {}",
                            engine_name,
                            reason
                        );
                    }
                }
                validation
            }
            PortfolioResult::Unsafe(cex) => {
                let validation = self.validate_unsafe(cex);
                if let ValidationResult::Invalid(reason) = &validation {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: {} Unsafe result failed validation: {}",
                            engine_name,
                            reason
                        );
                    }
                }
                validation
            }
            PortfolioResult::Unknown | PortfolioResult::NotApplicable => ValidationResult::Valid,
        }
    }

    /// Convert an `EngineResult` to `(PortfolioResult, needs_validation, engine_name)`.
    ///
    /// Centralizes the result conversion logic previously duplicated across
    /// the parallel receive loop and sequential-threaded result handling.
    ///
    /// Portfolio-level validation policy (post #5376 soundness fix):
    /// - PDR, Decomposition: skip validation (complete internal checks).
    /// - PDKIND, Kind: skip validation (k-inductive invariants cannot be verified
    ///   by PDR's 1-inductive verify_model; doing so causes false rejections).
    /// - TPA, CEGAR, IMC, LAWI, DAR, TRL: validate Safe results (incomplete
    ///   internal checks; portfolio validation uses budgeted verify_model_with_budget).
    ///   TRL moved from trusted to validated after #5376 (spurious Safe on 3 UNSAT
    ///   benchmarks due to unsound diameter proof).
    /// - All engines: Unsafe results from trusted engines skip validation
    ///   (false Unsafe is less harmful than false Safe).
    pub(super) fn convert_engine_result(
        &self,
        result: EngineResult,
    ) -> (PortfolioResult, bool, &'static str) {
        match result {
            EngineResult::Unified(r, name) => {
                // Validate Safe results for engines whose internal checks may be
                // incomplete. PDKIND and Kind use k-induction which produces
                // k-inductive invariants; PDR's 1-inductive verify_model cannot
                // verify these, causing false rejections that regressed 13
                // benchmarks from 46/55 to 33/55. PDR performs its own internal
                // verification (unbounded verify_model on the fixed-point path).
                // TRL was previously trusted but moved to validated (#5376):
                // its diameter proof can produce spurious Safe results on
                // unsafe systems. Returns Inv=true which fails validation.
                // Decomposition delegates to PDR with full unbounded
                // verify_model of the merged model.
                //
                // Unsafe results from these trusted engines skip validation:
                // false-Unsafe is less harmful than false-Safe, and their
                // counterexample construction is well-tested.
                //
                // SOUNDNESS FIX #5380: PDR moved from trusted to validated.
                // Root cause was NOT(AND(...)) in verify_model formulas: mk_not's
                // De Morgan created complex boolean structure that the SAT solver
                // couldn't handle. Fixed by distributing De Morgan at the ChcExpr
                // level in normalize_negations. PDR stays validated as defense-in-depth.
                //
                // TRL was moved from trusted to validated after #5376: its
                // diameter-based proof can produce spurious Safe on unsafe
                // systems (returns Inv=true which is not inductively valid).
                //
                // SOUNDNESS FIX #5211: Kind/PDKind validated with query-only
                // checks (verify_model_query_only in adaptive layer, #5825). This
                // catches false Safes where the
                // invariant doesn't exclude bad states. KIND's deferred-safe path
                // now returns ¬query instead of `true` (#5595), so query-only
                // validation passes for valid k-inductive proofs while still
                // catching SMT false-UNSAT on base cases.
                // Decomposition: delegates to PDR — also needs validation now.
                let needs_val = true;
                (r, needs_val, name)
            }
            EngineResult::Tpa(r) => (PortfolioResult::from(r), true, "TPA"),
            EngineResult::Cegar(r) => (PortfolioResult::from(r), true, "CEGAR"),
        }
    }
}
