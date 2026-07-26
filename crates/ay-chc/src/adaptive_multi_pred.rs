// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Multi-predicate linear strategy methods for the adaptive portfolio solver.
//!
//! Contains multi-pred linear solving, failure-guided retry, portfolio config
//! building, and the non-inlined PDR gate.
//!
//! Companion: `adaptive_multi_pred_complex.rs` has `solve_complex_loop` and
//! `solve_multi_pred_complex`.

use crate::bmc::BmcConfig;
use crate::cegar::CegarConfig;
use crate::classifier::{ProblemClassifier, ProblemFeatures};
use crate::engine_config::ChcEngineConfig;
use crate::engine_result::ValidationEvidence;
use crate::failure_analysis::{FailureAnalysis, FailureGuide};
use crate::imc::ImcConfig;
use crate::kind::KindConfig;
use crate::lemma_pool::LemmaPool;
use crate::pdkind::PdkindConfig;
use crate::pdr::{Counterexample, InvariantModel, PdrConfig, PdrResult, PdrSolver};
use crate::portfolio::{
    EngineConfig, PortfolioConfig, PortfolioResult, PortfolioSolver, PreprocessSummary,
};
use crate::smt::SmtResult;
use crate::tpa::TpaConfig;
use crate::trl::TrlConfig;
use crate::{BmcSolver, ChcExpr, ChcProblem};
use ay_core::time::Instant;
use ay_core::TermStore;
use std::time::Duration;

use crate::adaptive::AdaptivePortfolio;
use crate::adaptive_decision_log::DecisionEntry;

/// Outcome of the query-only discharge on a fully-inlined preprocessed
/// problem: either every query body was refuted (Safe direction, carrying the
/// discharged clause count), or a satisfiable query body was replay-confirmed
/// on the ORIGINAL clauses as a verified counterexample (Unsafe direction).
pub(crate) enum QueryOnlyDischarge {
    Discharged(usize),
    VerifiedUnsafe(Counterexample),
}

impl AdaptivePortfolio {
    pub(crate) fn is_large_acyclic_linear_graph(features: &ProblemFeatures) -> bool {
        !features.has_cycles && features.is_linear && features.num_predicates > 128
    }

    fn is_large_acyclic_bv_array_graph(&self, features: &ProblemFeatures) -> bool {
        features.uses_arrays && Self::is_large_acyclic_linear_graph(features)
    }

    fn acyclic_bmc_depth(features: &ProblemFeatures) -> usize {
        features.dag_depth.max(features.num_predicates).max(1)
    }

    fn acyclic_bmc_probe_result(
        &self,
        result: PortfolioResult,
        features: &ProblemFeatures,
        depth: usize,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        match result {
            PortfolioResult::Safe(model) if model.is_empty() && features.uses_arrays => {
                tracing::warn!(
                    depth,
                    "Adaptive: preprocessed acyclic array DAG BMC returned empty-model Safe; \
                     rejecting as non-proof-grade (#9227)"
                );
                None
            }
            PortfolioResult::Safe(model) if model.is_empty() => Some((
                PortfolioResult::Safe(model),
                ValidationEvidence::ScalarAcyclicBmcExhaustive { max_depth: depth },
            )),
            PortfolioResult::Safe(model) => Some((
                PortfolioResult::Safe(model),
                ValidationEvidence::FullVerification,
            )),
            PortfolioResult::Unsafe(cex) => Some((
                PortfolioResult::Unsafe(cex),
                ValidationEvidence::FullVerification,
            )),
            PortfolioResult::Unknown | PortfolioResult::NotApplicable => None,
        }
    }

    fn discharge_preprocessed_query_only_problem(
        &self,
        problem: &ChcProblem,
        stage_budget: Duration,
        label: &'static str,
        replay_depth_hint: usize,
    ) -> Option<QueryOnlyDischarge> {
        if !problem.predicates().is_empty() {
            return None;
        }
        if problem.clauses().is_empty() {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: {label} preprocessing discharged all clauses; validating translated empty proof"
                );
            }
            return Some(QueryOnlyDischarge::Discharged(0));
        }
        let queries: Vec<_> = problem.queries().collect();
        if queries.is_empty() || queries.len() != problem.clauses().len() {
            return None;
        }
        if queries
            .iter()
            .any(|query| !query.body.predicates.is_empty())
        {
            return None;
        }

        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: {label} preprocessing collapsed to {} query-only clauses; checking bodies directly",
                queries.len()
            );
        }

        let deadline = Instant::now() + stage_budget;
        let mut smt = problem.make_smt_context();
        for (idx, query) in queries.iter().enumerate() {
            let body = query
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true))
                .simplify_constants();
            if matches!(body, ChcExpr::Bool(false)) {
                continue;
            }

            let remaining = deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                return None;
            }

            smt.reset();
            match smt.check_sat_with_executor_fallback_timeout(&body, remaining) {
                result if result.is_unsat() => {}
                SmtResult::Sat(_) => {
                    // A satisfiable query body in the fully-inlined problem is
                    // a counterexample CANDIDATE, not an Unknown. Previously
                    // this arm was lumped with Unknown and the computed
                    // verdict was discarded. Promote it only through the
                    // fail-closed bounded-BMC replay on the ORIGINAL clauses
                    // (fresh verified witness + strict PdrSolver replay via
                    // `replay_confirm_unsafe_on_problem`); the transformed
                    // model itself is never trusted. Anything unconfirmed
                    // keeps the historical fail-closed None.
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: {label} query-only clause {idx} is satisfiable; \
                             attempting bounded-BMC replay confirmation on original clauses \
                             (depth hint {replay_depth_hint})"
                        );
                    }
                    let replay_budget = deadline.saturating_duration_since(Instant::now());
                    if let Some(verified_cex) = BmcSolver::replay_confirm_unsafe_on_problem(
                        &self.problem,
                        replay_depth_hint,
                        replay_budget,
                        None,
                        self.config.verbose,
                    ) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "Adaptive: {label} query-only Unsafe replay-confirmed on \
                                 original clauses (verified witness)"
                            );
                        }
                        return Some(QueryOnlyDischarge::VerifiedUnsafe(verified_cex));
                    }
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: {label} query-only clause {idx} was not discharged \
                             (satisfiable, but bounded replay did not confirm)"
                        );
                    }
                    return None;
                }
                SmtResult::Unknown => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: {label} query-only clause {idx} was not discharged"
                        );
                    }
                    return None;
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    unreachable!("handled by is_unsat guard")
                }
            }
        }

        Some(QueryOnlyDischarge::Discharged(queries.len()))
    }

    /// Independent fresh-executor re-proof of a query-only discharge
    /// (item 4 Stage 0 acceptance fix).
    ///
    /// Re-checks EXACTLY the collapsed query bodies that
    /// [`Self::discharge_preprocessed_query_only_problem`] already proved
    /// UNSAT, on a FRESH `SmtContext` (fresh executor instance) per query.
    /// Returns `true` only when every body is re-proved UNSAT within
    /// `budget`; any SAT / Unknown / budget expiry fails closed.
    ///
    /// The first run and this run share no solver state, so a confirming
    /// recheck means two independent executor runs agreed on every UNSAT —
    /// the same trust baseline as any AY unsat verdict.
    pub(crate) fn recheck_query_only_discharge(
        &self,
        problem: &ChcProblem,
        budget: Duration,
    ) -> bool {
        if !problem.predicates().is_empty() || problem.clauses().is_empty() {
            return false;
        }
        let queries: Vec<_> = problem.queries().collect();
        if queries.is_empty()
            || queries.len() != problem.clauses().len()
            || queries
                .iter()
                .any(|query| !query.body.predicates.is_empty())
        {
            return false;
        }

        let deadline = Instant::now() + budget;
        for query in queries {
            let body = query
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true))
                .simplify_constants();
            if matches!(body, ChcExpr::Bool(false)) {
                continue;
            }
            let remaining = deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                return false;
            }
            // Fresh context (fresh executor) per query: no state is shared
            // with the first discharge run.
            let mut smt = problem.make_smt_context();
            if !smt
                .check_sat_with_executor_fallback_timeout(&body, remaining)
                .is_unsat()
            {
                return false;
            }
        }
        true
    }

    /// #9227 re-keyed empty-model acyclic BMC promotion (item 4 Stage 0).
    ///
    /// The default #9227 stance keys the empty-model Safe rejection on the
    /// ORIGINAL problem's array signature. Promote instead — through the
    /// dedicated [`ValidationEvidence::EquisatAcyclicBmcExhaustive`] variant —
    /// only when ALL of:
    /// (a) the TRANSFORMED problem is array-free AND datatype-free (bounded
    ///     acyclic exhaustion is complete for its value space),
    /// (b) the transform chain is equisat-grade
    ///     ([`crate::transform::TransformMemoryReport::is_equisat_grade`]:
    ///     fail-closed allowlist of equivalence-preserving passes), and
    /// (c) an INDEPENDENT fresh-executor BMC re-run of the same exhaustion
    ///     query (fresh `BmcSolver`, fresh SMT contexts) re-confirms the
    ///     empty-model Safe within a capped budget.
    /// Any failure returns `None` — exactly today's fail-closed rejection.
    pub(crate) fn try_promote_equisat_acyclic_exhaustion(
        &self,
        transformed_problem: &ChcProblem,
        transform_memory: &crate::transform::TransformMemoryReport,
        depth: usize,
        recheck_budget: Duration,
    ) -> Option<ValidationEvidence> {
        if transformed_problem.has_array_sorts() || transformed_problem.has_datatype_sorts() {
            tracing::warn!(
                depth,
                "Adaptive: preprocessed acyclic array DAG BMC returned empty-model Safe; \
                 rejecting as non-proof-grade (#9227: transformed problem still carries \
                 array/datatype state)"
            );
            return None;
        }
        if !transform_memory.is_equisat_grade() {
            tracing::warn!(
                depth,
                "Adaptive: preprocessed acyclic array DAG BMC returned empty-model Safe; \
                 rejecting as non-proof-grade (#9227: transform chain is not equisat-grade: {})",
                transform_memory.diagnostic_summary()
            );
            return None;
        }
        if recheck_budget.is_zero() {
            return None;
        }
        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: empty-model acyclic exhaustion on equisat-grade array-free transform; \
                 re-running exhaustion query on a fresh executor ({:.1}s budget)",
                recheck_budget.as_secs_f64()
            );
        }
        let recheck = BmcSolver::new(
            transformed_problem.clone(),
            BmcConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                max_depth: depth,
                acyclic_safe: true,
                prefer_exact_acyclic_first: false,
                per_depth_timeout: None,
                time_budget: Some(recheck_budget),
                enable_k_induction: false,
                enable_adaptive_stepping: false,
                proof_cross_check: false,
                ts_probe_clamp: None,
                sweep_past_spurious_sat: true,
            },
        );
        match recheck.solve() {
            PortfolioResult::Safe(model) if model.is_empty() => {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: fresh-executor exhaustion re-run confirmed empty-model Safe \
                         (equisat-grade chain); promoting via EquisatAcyclicBmcExhaustive"
                    );
                }
                Some(ValidationEvidence::EquisatAcyclicBmcExhaustive { max_depth: depth })
            }
            other => {
                tracing::warn!(
                    depth,
                    recheck = %other,
                    "Adaptive: fresh-executor exhaustion re-run did NOT confirm empty-model \
                     Safe; keeping #9227 fail-closed rejection"
                );
                None
            }
        }
    }

    fn validate_preprocessed_safe_model(
        &self,
        model: &InvariantModel,
        label: &'static str,
    ) -> bool {
        if !self.final_safe_model_has_required_interpretations(model) {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: {label} translated Safe model lacks required original predicate interpretations"
                );
            }
            return false;
        }

        let mut verifier = PdrSolver::new(
            self.problem.clone(),
            PdrConfig {
                verbose: self.config.verbose,
                strict_proofs: true,
                solve_timeout: Some(Duration::from_secs(30)),
                disable_array_scalarization: true,
                preserve_original_clauses: true,
                ..PdrConfig::default()
            },
        );
        if verifier.verify_model_per_rule(model, Duration::from_millis(1500)) {
            if self.config.verbose {
                safe_eprintln!("Adaptive: {label} translated Safe model validated");
            }
            true
        } else {
            if self.config.verbose {
                safe_eprintln!("Adaptive: {label} translated Safe model failed validation");
            }
            false
        }
    }

    pub(crate) fn run_preprocessed_acyclic_bmc_probe(
        &self,
        summary: PreprocessSummary,
        features: &ProblemFeatures,
        stage_budget: Duration,
        label: &'static str,
        prefer_exact_acyclic_first: bool,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        let PreprocessSummary {
            transformed_problem,
            back_translator,
            transform_memory,
            ..
        } = summary;
        let bmc_features = ProblemClassifier::classify(&transformed_problem);
        let bmc_is_acyclic = !bmc_features.has_cycles && bmc_features.num_predicates > 0;
        let depth = if bmc_is_acyclic {
            Self::acyclic_bmc_depth(&bmc_features)
        } else {
            Self::acyclic_bmc_depth(features)
        };
        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: Trying {label} acyclic BMC probe (depth={}, dag_depth={} -> {}, preds={} -> {}, timeout={:.1}s, per-depth=unbounded)",
                depth,
                features.dag_depth,
                bmc_features.dag_depth,
                features.num_predicates,
                bmc_features.num_predicates,
                stage_budget.as_secs_f64()
            );
        }

        let probe_deadline = Instant::now() + stage_budget;
        match self.discharge_preprocessed_query_only_problem(
            &transformed_problem,
            stage_budget,
            label,
            depth,
        ) {
            Some(QueryOnlyDischarge::Discharged(query_count)) => {
                let transformed_model = InvariantModel::default();
                let translated_model =
                    back_translator.translate_validity(transformed_model.clone());
                if self.validate_preprocessed_safe_model(&translated_model, label) {
                    return Some((
                        PortfolioResult::Safe(translated_model),
                        ValidationEvidence::FullVerification,
                    ));
                }
                // Item 4 Stage 0 acceptance fix: per-rule validation of the
                // TRANSLATED model can fail purely because back-translation
                // cannot reconstruct interpretations for the inlined original
                // predicates — a witness-completeness gap, not evidence
                // against safety. For an ORIGINALLY ACYCLIC problem the
                // collapsed query bodies cover every derivation path exactly,
                // so re-prove each of them UNSAT on a FRESH executor
                // (budget-capped): two independent executor runs agreeing is
                // the same trust baseline as any AY unsat. On confirmation,
                // promote through the dedicated CheckedQueryOnlyDischarge
                // evidence (explicitly accepted at both promotion
                // boundaries); on recheck failure or budget expiry, fall
                // through to the transformed-BMC step below instead of
                // aborting the probe.
                // Item 4 Stage 4 soundness gate: CheckedQueryOnlyDischarge
                // trusts the TRANSFORM CHAIN for the Safe direction (the
                // re-proof runs on the transformed query bodies). A DT
                // flattening that made ANY approximation (wrong-variant EUF
                // reads, default-filled constructor columns, recursive-depth
                // truncation) reports the approximation obligation and must
                // not be trusted here — fail closed to the transformed-BMC
                // step whose Safe path validates on the ORIGINAL clauses.
                let chain_trustworthy_for_safe = !transform_memory
                    .has_obligation(crate::transform::DT_FLATTEN_APPROX_OBLIGATION);
                if !chain_trustworthy_for_safe && self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: {label} query-only discharge NOT promoted: transform chain \
                         carries datatype-flatten approximations (fail-closed)"
                    );
                }
                if !features.has_cycles && query_count > 0 && chain_trustworthy_for_safe {
                    let recheck_budget = probe_deadline
                        .saturating_duration_since(Instant::now())
                        .min(Duration::from_secs(10));
                    if self.recheck_query_only_discharge(&transformed_problem, recheck_budget) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "Adaptive: {label} query-only discharge re-proved all {} query \
                                 bodies UNSAT on a fresh executor; promoting Safe via \
                                 CheckedQueryOnlyDischarge",
                                query_count
                            );
                        }
                        // Ship the HONEST empty certificate, not the
                        // back-translated model we just found does not
                        // per-rule validate (its inlined-predicate
                        // interpretations are unreconstructable — the
                        // witness-completeness gap noted above). The proof is
                        // the query-only exhaustive discharge, so mirror the
                        // ScalarAcyclicBmcExhaustive contract: an empty model
                        // routes the downstream discharge gate to the acyclic
                        // BMC re-validation (complete for this acyclic
                        // scalar/BV/finite-DT DAG) instead of re-checking a
                        // known-incomplete invariant and spuriously demoting a
                        // genuinely-proved Safe to unknown.
                        return Some((
                            PortfolioResult::Safe(InvariantModel::default()),
                            ValidationEvidence::CheckedQueryOnlyDischarge { query_count },
                        ));
                    }
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: {label} query-only discharge fresh-executor recheck did \
                             not confirm; falling through to transformed BMC"
                        );
                    }
                }
                tracing::debug!(
                    query_count,
                    "Adaptive: {label} query-only discharge failed original validation; \
                     rejecting transformed Safe evidence and continuing with transformed BMC"
                );
                // Fall through to the transformed-BMC step (A Part D) instead
                // of aborting the probe.
            }
            Some(QueryOnlyDischarge::VerifiedUnsafe(verified_cex)) => {
                // The counterexample was replay-confirmed on the ORIGINAL
                // clauses inside `replay_confirm_unsafe_on_problem` (fresh
                // witness + strict PdrSolver replay), so it needs no
                // back-translation from the transformed space.
                return Some((
                    PortfolioResult::Unsafe(verified_cex),
                    ValidationEvidence::FullVerification,
                ));
            }
            None => {}
        }

        // Retain a handle on the transformed problem for the #9227 re-keyed
        // promotion recheck below (Arc-shared expression trees: cheap).
        let rekey_probe_problem = features.uses_arrays.then(|| transformed_problem.clone());
        let bmc = BmcSolver::new(
            transformed_problem,
            BmcConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                max_depth: depth,
                acyclic_safe: true,
                prefer_exact_acyclic_first,
                // For bounded acyclic DAGs, the deepest exact query is
                // usually the expensive one. Let the stage timeout enforce
                // the budget instead of cutting off each depth early.
                per_depth_timeout: None,
                time_budget: Some(stage_budget),
                enable_k_induction: false,
                enable_adaptive_stepping: false,
                proof_cross_check: false,
                ts_probe_clamp: None,
                sweep_past_spurious_sat: true,
            },
        );

        let result = bmc.solve();
        match result {
            PortfolioResult::Safe(model) => {
                let translated_model = back_translator.translate_validity(model.clone());
                if self.validate_preprocessed_safe_model(&translated_model, label) {
                    return Some((
                        PortfolioResult::Safe(translated_model),
                        ValidationEvidence::FullVerification,
                    ));
                }
                if model.is_empty() {
                    // #9227 re-keyed gated promotion (item 4 Stage 0): for
                    // array-sorted ORIGINALS, promote only when the
                    // TRANSFORMED problem is array/datatype-free, the chain
                    // is equisat-grade, and an independent fresh-executor
                    // re-run confirms. Any failure keeps today's fail-closed
                    // rejection.
                    if let Some(probe_problem) = rekey_probe_problem.as_ref() {
                        let recheck_budget = probe_deadline
                            .saturating_duration_since(Instant::now())
                            .min(Duration::from_secs(10));
                        return self
                            .try_promote_equisat_acyclic_exhaustion(
                                probe_problem,
                                &transform_memory,
                                depth,
                                recheck_budget,
                            )
                            .map(|evidence| (PortfolioResult::Safe(model), evidence));
                    }
                    self.acyclic_bmc_probe_result(PortfolioResult::Safe(model), features, depth)
                } else {
                    None
                }
            }
            PortfolioResult::Unsafe(cex) => {
                if !transform_memory.unsafe_backtranslation_complete() {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: {label} transformed Unsafe rejected before promotion; {}",
                            transform_memory.diagnostic_summary()
                        );
                    }
                    None
                } else {
                    Some((
                        PortfolioResult::Unsafe(back_translator.translate_invalidity(cex)),
                        ValidationEvidence::FullVerification,
                    ))
                }
            }
            PortfolioResult::Unknown | PortfolioResult::NotApplicable => None,
        }
    }

    /// Ground-witness back-translation landing: turn a counterexample found on
    /// a TRANSFORMED problem into a verdict about the ORIGINAL problem without
    /// any theory search.
    ///
    /// The transformed counterexample carries a concrete
    /// [`crate::ground_derivation::GroundDerivation`] over the transformed
    /// clauses. `back_translator` maps that derivation, step by step, into one
    /// over the original clauses; the result is then validated by pure ground
    /// evaluation against `self.problem`. Only a derivation that passes THAT
    /// check is promoted, so transformed evidence is never trusted and a
    /// buggy/stale translation can only produce a rejection.
    ///
    /// Returns `None` for every failure — no attached derivation, a pass that
    /// cannot map it, or a mapped derivation that does not validate — leaving
    /// the caller's pre-existing search-replay fallback to run unchanged.
    ///
    /// `lane` is a log prefix only ("Adaptive" for the adaptive probe,
    /// "BMC-only" for the BMC-only mirror); `verbose` gates the log lines so
    /// the BMC-only entry can honor its own `BmcConfig` verbosity.
    pub(crate) fn ground_backtranslate_landing(
        &self,
        cex: &Counterexample,
        back_translator: &dyn crate::transform::BackTranslator,
        lane: &'static str,
        verbose: bool,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        if !crate::ground_derivation::ground_backtranslation_enabled() {
            return None;
        }
        let started = Instant::now();
        let transformed = cex.ground_derivation.as_ref()?;
        // Give this back-translation its own witness-solve chain budget.
        let _witness_budget = crate::ground_derivation::witness::ScopedWitnessChainBudget::new();
        let translated = back_translator.translate_ground_derivation(transformed);
        let Some(translated) = translated else {
            if verbose {
                safe_eprintln!(
                    "{lane}: ground back-translation of the transformed derivation \
                     ({} steps) is not available for this transform chain; \
                     falling back to original-clause replay",
                    transformed.len()
                );
            }
            return None;
        };
        if let Err(err) =
            crate::ground_derivation::validate_ground_derivation(&self.problem, &translated)
        {
            if verbose {
                safe_eprintln!(
                    "{lane}: back-translated derivation ({} steps) REJECTED on ORIGINAL \
                     clauses by ground validation ({err}); falling back to original-clause replay",
                    translated.len()
                );
            }
            return None;
        }
        if verbose {
            safe_eprintln!(
                "{lane}: transformed derivation back-translated to {} ORIGINAL-clause steps and \
                 GROUND-VALIDATED on the ORIGINAL clauses in {:.2}s (no theory search); \
                 promoting Unsafe",
                translated.len(),
                started.elapsed().as_secs_f64()
            );
        }
        let promoted = Counterexample::new(cex.steps.clone()).with_ground_derivation(translated);
        Some((
            PortfolioResult::Unsafe(promoted),
            ValidationEvidence::FullVerification,
        ))
    }

    fn is_high_arity_acyclic_bv_proof_shape(&self, features: &ProblemFeatures) -> bool {
        features.is_linear
            && !features.has_cycles
            && !features.uses_arrays
            && self.problem.has_bv_sorts()
            && (features.num_predicates >= 32 || features.dag_depth >= 32 || features.has_ite)
    }

    /// Scalarized graph-collapse + level-BMC probe with the ground-witness
    /// back-translation landing (item 4, heavy-memory "235-relation" class).
    ///
    /// Shared by the adaptive direct acyclic probe
    /// (`run_direct_acyclic_bmc_probe`) and the BMC-only lane
    /// (`solve_bmc_only_internal`), so BOTH entries convert the condensed,
    /// fully scalarized (DT-free + array-free) class the same way instead of
    /// only the adaptive one.
    ///
    /// Preconditions the callers establish: `scalarized_problem` is the
    /// non-identity condense+forwarding result, it is datatype-free and
    /// array-free, and `shared_back_translator` composes back to the ORIGINAL
    /// clauses (`self.problem`).
    ///
    /// SOUNDNESS: nothing found on the transformed problem is promoted
    /// directly. The Unsafe landing is `ground_backtranslate_landing`
    /// (derivation mapped through the chain, then validated by pure ground
    /// evaluation against the ORIGINAL clauses; kill switch
    /// `AY_CHC_DISABLE_GROUND_BACKTRANSLATION`), with the fresh
    /// original-clause search replay as fallback; the query-only-discharge
    /// branch validates through `run_preprocessed_acyclic_bmc_probe`'s
    /// original-clause anchors. Every failure returns `None`, leaving the
    /// caller's pre-existing lanes to run unchanged.
    ///
    /// `lane` is a log prefix only; `verbose` gates the log lines (the
    /// BMC-only entry honors its `BmcConfig` verbosity through it).
    pub(crate) fn run_scalarized_collapse_probe(
        &self,
        scalarized_problem: &ChcProblem,
        shared_back_translator: &std::sync::Arc<
            std::sync::Mutex<Box<dyn crate::transform::BackTranslator>>,
        >,
        features: &ProblemFeatures,
        condensed_budget: Duration,
        lane: &'static str,
        verbose: bool,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        let collapse_start = Instant::now();
        // Golem-style graph collapse: MultiEdgeMerger folds the
        // per-predicate parallel definitions into disjunctive
        // single edges, NodeEliminator then inlines nodes out
        // under its own hard caps (MAX_COLLAPSE_CLAUSES etc.),
        // matching the check_wrap_offset landing machinery. The
        // plain portfolio ClauseInliner is useless here (every
        // condensed basic-block predicate has multiple
        // definitions), and LocalVarEliminator wedges on the
        // 3000+-node condensed constraints.
        let collapse = crate::transform::TransformationPipeline::new()
            .with(crate::transform::MultiEdgeMerger::new())
            .with(crate::transform::NodeEliminator::new().with_verbose(verbose))
            .transform(scalarized_problem.clone());
        if collapse.problem.predicates().is_empty() {
            // Fully collapsed to query-only clauses: the
            // discharge machinery (query-body UNSAT proofs for
            // Safe / body-SAT + original-clause replay for
            // Unsafe) applies directly.
            let collapse_budget = (condensed_budget / 4).min(Duration::from_secs(30));
            let collapse_bt: Box<dyn crate::transform::BackTranslator> =
                Box::new(crate::transform::CompositeBackTranslator {
                    inner: vec![
                        collapse.back_translator,
                        Box::new(crate::transform::SharedBackTranslator(
                            shared_back_translator.clone(),
                        )),
                    ],
                });
            let collapse_memory = collapse_bt.transform_memory();
            let collapse_summary = PreprocessSummary {
                original_problem: self.problem.clone(),
                transformed_problem: collapse.problem,
                back_translator: collapse_bt,
                bv_abstracted: false,
                transform_memory: collapse_memory,
            };
            if let Some(result) = self.run_preprocessed_acyclic_bmc_probe(
                collapse_summary,
                features,
                collapse_budget,
                "scalarized inline-collapse",
                false,
            ) {
                return Some(result);
            }
        } else {
            // The scalarized DAG keeps multi-definition
            // predicates (basic-block branching), so full
            // inline-collapse is structurally unreachable and
            // the exact path-expansion encoding explodes
            // (measured on iterator_count). The standard
            // LEVEL-ENCODED BMC loop is the engine that finds
            // the transformed bug (measured: Unsafe at depth 2
            // in ~70s on the scalarized iterator_count).
            // SOUNDNESS: its Unsafe verdict is used ONLY as a
            // trigger — the promoted counterexample comes from
            // the ground back-translation landing (validated on
            // the ORIGINAL clauses) or, failing that, from
            // `replay_confirm_unsafe_on_problem`, a fresh
            // bounded search on the ORIGINAL clauses whose
            // witness is strict-replayed by PdrSolver. Safe /
            // Unknown fall through to the exact-DAG lane.
            let level_problem = collapse.problem;
            // The collapse translator maps the level problem's
            // clause indices back into the scalarized problem;
            // composed with the scalarized chain it reaches the
            // ORIGINAL clauses. It used to be dropped here because
            // the only landing path was a fresh search that needed
            // no translation at all.
            let level_back_translator: Box<dyn crate::transform::BackTranslator> =
                Box::new(crate::transform::CompositeBackTranslator {
                    inner: vec![
                        collapse.back_translator,
                        Box::new(crate::transform::SharedBackTranslator(
                            shared_back_translator.clone(),
                        )),
                    ],
                });
            // Diagnostic: dump the collapsed level problem for offline
            // standalone solving (companion to the scalarized dump in
            // run_direct_acyclic_bmc_probe).
            if let Some(dir) = std::env::var_os("AY_CHC_DUMP_SCALARIZED") {
                let dir = std::path::PathBuf::from(dir);
                let _ = std::fs::create_dir_all(&dir);
                let script =
                    crate::transform::cata_abstract::dump_abstract_lia_problem(&level_problem);
                let _ = std::fs::write(dir.join("level.smt2"), script);
            }
            let level_features = ProblemClassifier::classify(&level_problem);
            let level_depth = Self::acyclic_bmc_depth(&level_features);
            let level_budget = (condensed_budget / 2).min(Duration::from_secs(90));
            if verbose {
                safe_eprintln!(
                    "{lane}: Trying scalarized level BMC probe (preds={}, depth={}, timeout={:.1}s; unsafe-only, landing via original-clause replay)",
                    level_problem.predicates().len(),
                    level_depth,
                    level_budget.as_secs_f64()
                );
            }
            let level_bmc = BmcSolver::new(
                level_problem,
                BmcConfig {
                    base: ChcEngineConfig {
                        verbose,
                        ..ChcEngineConfig::default()
                    },
                    max_depth: level_depth,
                    acyclic_safe: false,
                    prefer_exact_acyclic_first: false,
                    per_depth_timeout: None,
                    time_budget: Some(level_budget),
                    enable_k_induction: false,
                    enable_adaptive_stepping: false,
                    proof_cross_check: false,
                    ts_probe_clamp: None,
                    sweep_past_spurious_sat: true,
                },
            );
            if let PortfolioResult::Unsafe(level_cex) = level_bmc.solve() {
                // FIRST landing attempt: back-translate the concrete
                // transformed DERIVATION through the transform chain
                // and validate it on the ORIGINAL clauses by pure
                // ground evaluation. This never trusts transformed
                // evidence — the promoted derivation is checked
                // clause-by-clause against `self.problem` — but it
                // also never re-enters the theory search that makes
                // the replay below return Unknown on this class.
                if let Some(result) = self.ground_backtranslate_landing(
                    &level_cex,
                    level_back_translator.as_ref(),
                    lane,
                    verbose,
                ) {
                    return Some(result);
                }
                let replay_budget = condensed_budget.saturating_sub(collapse_start.elapsed());
                let replay_depth_hint = Self::acyclic_bmc_depth(features);
                if verbose {
                    safe_eprintln!(
                        "{lane}: scalarized level BMC found transformed Unsafe; \
                         replaying on ORIGINAL clauses (depth hint {}, {:.1}s budget)",
                        replay_depth_hint,
                        replay_budget.as_secs_f64()
                    );
                }
                if let Some(verified_cex) = BmcSolver::replay_confirm_unsafe_on_problem(
                    &self.problem,
                    replay_depth_hint,
                    replay_budget,
                    None,
                    verbose,
                ) {
                    if verbose {
                        safe_eprintln!(
                            "{lane}: scalarized level BMC Unsafe replay-confirmed \
                             on original clauses (verified witness)"
                        );
                    }
                    return Some((
                        PortfolioResult::Unsafe(verified_cex),
                        ValidationEvidence::FullVerification,
                    ));
                }
                if verbose {
                    safe_eprintln!(
                        "{lane}: scalarized level BMC Unsafe NOT confirmed by \
                         original-clause replay; discarding (fail-closed)"
                    );
                }
            }
        }
        None
    }

    fn run_direct_acyclic_bmc_probe(
        &self,
        features: &ProblemFeatures,
        stage_budget: Duration,
        label: &'static str,
        prefer_exact_acyclic_first: bool,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        // Item 4 (model-checker-consumer parity, heavy-memory "235-relation" class): the
        // direct probe historically ran on the RAW problem, so acyclic
        // BV+array DAGs with threaded-memory relations (full arity ~235) hit
        // the exact DAG encoding at full width and burned the whole stage
        // budget. Run the bounded-cost forwarding-only combination
        // (ArrayStoreForwarder + cost-bounded DeadParamEliminator) first and,
        // when it actually rewrites something, probe the slimmed problem via
        // the preprocessed lane — which back-translates witnesses and
        // validates Safe models on the ORIGINAL clauses fail-closed. The raw
        // probe still runs afterwards on any leftover budget, so behavior can
        // only improve. Kill switch AY_CHC_DISABLE_ARRAY_STORE_FORWARDING and
        // the no-array / no-op cases yield an identity summary and skip
        // straight to the raw probe.
        let mut stage_budget = stage_budget;

        // Item 4 Stage 3 (condense-first for the large acyclic class): the
        // CondenseSuperpass collapses generated basic-block DAGs by an order
        // of magnitude (iterator_count: 377 preds / 454 clauses -> ~37/114),
        // but historically ran only inside the build* pipelines — too late
        // for this direct probe. Run it FIRST, wall-bounded to
        // min(stage_budget/3, 15s) (it polls between constituents; any
        // prefix is exact), and feed a non-identity result to the
        // preprocessed probe, which back-translates witnesses and validates
        // fail-closed on the ORIGINAL clauses. Identity-grade or timed-out
        // condense falls back to the forwarding-only lane below unchanged.
        // Gated on >= 20s remaining so short-budget behavior (item-3
        // compliance) is untouched.
        if Self::is_large_acyclic_linear_graph(features)
            && stage_budget >= Duration::from_secs(20)
            && crate::transform::condense_enabled()
        {
            let condense_start = Instant::now();
            let condense_budget = (stage_budget / 3).min(Duration::from_secs(15));
            let condense = crate::transform::CondenseSuperpass::new()
                .with_verbose(self.config.verbose)
                .with_wall_budget(Some(condense_budget));
            let condensed =
                crate::transform::Transformer::transform(Box::new(condense), self.problem.clone());
            let condense_memory = condensed.back_translator.transform_memory();
            if !condense_memory.is_identity_grade() {
                // The mean-node gate typically bails the condense round
                // BEFORE its trailing DeadParamEliminator (composed
                // constraints blow past 2048 nodes), leaving the
                // now-unconstrained table/memory array arguments in the
                // (wide) predicate signatures. Finish the job with the
                // bounded forwarding-only combination on the CONDENSED
                // problem — forwarder + ground-table concretizer + one
                // cost-bounded arity slicer — and compose the translators.
                let post = PreprocessSummary::build_array_forwarding_only(
                    condensed.problem,
                    self.config.verbose,
                );
                let back_translator: Box<dyn crate::transform::BackTranslator> =
                    Box::new(crate::transform::CompositeBackTranslator {
                        inner: vec![post.back_translator, condensed.back_translator],
                    });
                let transform_memory = back_translator.transform_memory();
                let scalarized_problem = post.transformed_problem;
                let mut condensed_budget = stage_budget.saturating_sub(condense_start.elapsed());

                // Item 4 Stage 4 probe reorder: when the scalarization
                // summary is non-identity AND the transformed problem is
                // DT-free + array-free (condense + concretizer + per-variant
                // DT flattening fully scalarized the state), run the
                // inline-collapse probe FIRST with a bounded stage split —
                // ClauseInliner collapse -> query-only discharge -> body SAT
                // -> replay_confirm_unsafe_on_problem on the ORIGINAL
                // clauses. Historically the exact-DAG lane consumed the
                // ENTIRE remaining budget for this shape
                // (acyclic_bmc_stage_budget), so the split must bound the
                // first lane; the exact-DAG probe runs after on the
                // remainder. The collapse lane shares the scalarized
                // back-translator (SharedBackTranslator) so both lanes
                // back-translate/validate against the ORIGINAL problem.
                // Diagnostic: dump the scalarized problem for offline
                // standalone solving (AY_CHC_DUMP_SCALARIZED=<dir>).
                if let Some(dir) = std::env::var_os("AY_CHC_DUMP_SCALARIZED") {
                    let dir = std::path::PathBuf::from(dir);
                    let _ = std::fs::create_dir_all(&dir);
                    let script = crate::transform::cata_abstract::dump_abstract_lia_problem(
                        &scalarized_problem,
                    );
                    let _ = std::fs::write(dir.join("scalarized.smt2"), script);
                }
                let scalarized_scalar_state = !transform_memory.is_identity_grade()
                    && !scalarized_problem.has_datatype_sorts()
                    && !scalarized_problem.has_array_sorts();
                let shared_back_translator: std::sync::Arc<
                    std::sync::Mutex<Box<dyn crate::transform::BackTranslator>>,
                > = std::sync::Arc::new(std::sync::Mutex::new(back_translator));

                if scalarized_scalar_state && !condensed_budget.is_zero() {
                    let collapse_start = Instant::now();
                    if let Some(result) = self.run_scalarized_collapse_probe(
                        &scalarized_problem,
                        &shared_back_translator,
                        features,
                        condensed_budget,
                        "Adaptive",
                        self.config.verbose,
                    ) {
                        return Some(result);
                    }
                    condensed_budget = condensed_budget.saturating_sub(collapse_start.elapsed());
                }

                if !condensed_budget.is_zero() {
                    let summary = PreprocessSummary {
                        original_problem: self.problem.clone(),
                        transformed_problem: scalarized_problem,
                        back_translator: Box::new(crate::transform::SharedBackTranslator(
                            shared_back_translator,
                        )),
                        bv_abstracted: false,
                        transform_memory,
                    };
                    if let Some(result) = self.run_preprocessed_acyclic_bmc_probe(
                        summary,
                        features,
                        condensed_budget,
                        "condensed direct",
                        prefer_exact_acyclic_first,
                    ) {
                        return Some(result);
                    }
                }
            }
            stage_budget = stage_budget.saturating_sub(condense_start.elapsed());
            if stage_budget.is_zero() {
                return None;
            }
        }

        if self.problem.has_array_sorts() {
            let forward_start = Instant::now();
            let summary = PreprocessSummary::build_array_forwarding_only(
                self.problem.clone(),
                self.config.verbose,
            );
            if !summary.transform_memory.is_identity_grade() {
                if let Some(result) = self.run_preprocessed_acyclic_bmc_probe(
                    summary,
                    features,
                    stage_budget,
                    "array-forwarded direct",
                    prefer_exact_acyclic_first,
                ) {
                    return Some(result);
                }
                stage_budget = stage_budget.saturating_sub(forward_start.elapsed());
                if stage_budget.is_zero() {
                    return None;
                }
            }
        }

        let depth = Self::acyclic_bmc_depth(features);
        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: Trying {label} acyclic BMC probe (preds={}, dag_depth={}, depth={}, timeout={:.1}s, per-depth=unbounded)",
                features.num_predicates,
                features.dag_depth,
                depth,
                stage_budget.as_secs_f64()
            );
        }
        let bmc = BmcSolver::new(
            self.problem.clone(),
            BmcConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                max_depth: depth,
                acyclic_safe: true,
                prefer_exact_acyclic_first,
                per_depth_timeout: None,
                time_budget: Some(stage_budget),
                enable_k_induction: false,
                enable_adaptive_stepping: false,
                proof_cross_check: false,
                ts_probe_clamp: None,
                sweep_past_spurious_sat: true,
            },
        );
        let probe_start = Instant::now();
        let result = bmc.solve();
        if let Some(hit) = self.acyclic_bmc_probe_result(result, features, depth) {
            // This is the raw, untransformed `self.problem` probe. Cache an
            // empty-model scalar proof only here, after the exact exhaustive
            // BMC run itself returned Safe. Do not record from the generic
            // finalizer: `ValidationEvidence` is metadata and a fabricated
            // label must never manufacture a reusable proof.
            if matches!(
                &hit,
                (
                    PortfolioResult::Safe(model),
                    ValidationEvidence::ScalarAcyclicBmcExhaustive { .. }
                ) if model.is_empty()
            ) {
                crate::acyclic_cert_cache::record_acyclic_bmc_safe(&self.problem, depth);
            }
            return Some(hit);
        }

        // The exact acyclic safe-first pass can find a SAT branch it cannot
        // convert into a witness: branch formulas use per-path fresh variable
        // naming that model_derivation_witness's level-based lookup cannot
        // resolve, so the fail-closed plumbing keeps Unknown. The standard
        // level-encoded loop CAN extract and replay-validate the same
        // counterexample — spend the probe's remaining stage budget on an
        // unsafe-only standard pass before giving up. Only a replay-validated
        // Unsafe is promoted; bounded Safe/Unknown fall through to None
        // exactly as before.
        let leftover = stage_budget.saturating_sub(probe_start.elapsed());
        if leftover.is_zero() {
            return None;
        }
        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: {label} acyclic probe undischarged; trying standard-BMC unsafe pass (depth={depth}, timeout={:.1}s)",
                leftover.as_secs_f64()
            );
        }
        let fallback = BmcSolver::new(
            self.problem.clone(),
            BmcConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                max_depth: depth,
                acyclic_safe: false,
                prefer_exact_acyclic_first: false,
                per_depth_timeout: None,
                time_budget: Some(leftover),
                enable_k_induction: false,
                enable_adaptive_stepping: false,
                proof_cross_check: false,
                ts_probe_clamp: None,
                sweep_past_spurious_sat: true,
            },
        );
        match fallback.solve() {
            PortfolioResult::Unsafe(cex) => Some((
                PortfolioResult::Unsafe(cex),
                ValidationEvidence::FullVerification,
            )),
            _ => None,
        }
    }

    pub(crate) fn multi_pred_pdr_config(mut config: PdrConfig) -> PdrConfig {
        // Entry-CEGAR discharge can burn the whole adaptive budget on
        // multi-predicate arithmetic chains while repeatedly rejecting the same
        // near-inductive lemmas. Keep the entry check, but skip the expensive
        // discharge loop on these paths.
        config.use_entry_cegar_discharge = false;
        config
    }

    pub(crate) fn try_acyclic_bmc_probe(
        &self,
        features: &ProblemFeatures,
        deadline: Option<Instant>,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        // #8663: For acyclic multi-predicate dependency graphs, bounded
        // unrolling to the predicate count is complete. Keep the acyclic and
        // multi-predicate gates strict, but do not require BV or array sorts:
        // straight-line CHC DAGs over Ints benefit from the same probe.
        if features.has_cycles || features.num_predicates <= 1 || self.budget_exhausted(deadline) {
            return None;
        }

        let remaining = self
            .remaining_budget(deadline)
            .unwrap_or(Duration::from_secs(15));
        let stage_budget = Self::acyclic_bmc_stage_budget(features, remaining);
        if stage_budget.is_zero() {
            return None;
        }

        let high_arity_bv_proof_shape = self.is_high_arity_acyclic_bv_proof_shape(features);
        if high_arity_bv_proof_shape {
            let exact_stage_budget = remaining.min(Duration::from_secs(45)).max(stage_budget);
            if let Some(result) = self.run_direct_acyclic_bmc_probe(
                features,
                exact_stage_budget,
                "original BV-exact",
                true,
            ) {
                return Some(result);
            }
            if self.budget_exhausted(deadline) {
                return None;
            }
        }

        let source_exact_bool_int_dag = !self.problem.has_cycles()
            && !self.problem.has_bv_sorts()
            && !self.problem.has_array_sorts()
            && !self.problem.has_real_sorts()
            && !self.problem.has_datatype_sorts()
            // High-arity stress fixtures are better left to the existing
            // stack-safe adaptive path; exact BMC can spend the whole budget
            // materializing wide states without improving proof strength.
            && features.max_predicate_arity <= 8;
        if source_exact_bool_int_dag {
            if let Some(result) = self.run_direct_acyclic_bmc_probe(
                features,
                stage_budget,
                "direct Bool/Int DAG",
                false,
            ) {
                return Some(result);
            }
            if self.budget_exhausted(deadline) {
                return None;
            }
        }

        if Self::is_large_acyclic_linear_graph(features) {
            return self.run_direct_acyclic_bmc_probe(
                features,
                stage_budget,
                "direct large linear DAG",
                false,
            );
        }

        // Exact BvToInt keeps scalar BV DAGs out of the mixed BV+Int executor
        // bridge when the query contains bv2nat/int2bv arithmetic. This lane is
        // proof-admissible only when the transform stayed exact: if bitwise UF
        // fallback was used, the probe fails closed and the native lane below
        // remains the source of truth (#8865/#9604).
        if !high_arity_bv_proof_shape && !features.uses_arrays && self.problem.has_bv_sorts() {
            let exact_stage_budget = if features.num_predicates >= 32 || features.dag_depth >= 32 {
                remaining.min(Duration::from_secs(45)).max(stage_budget)
            } else {
                stage_budget
            };
            let int_summary =
                PreprocessSummary::build_int_only(self.problem.clone(), self.config.verbose);
            if int_summary.had_bitwise_uf_fallback() {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: Skipping exact-BvToInt acyclic BMC probe because BvToInt used bitwise UF fallback"
                    );
                }
            } else if let Some(result) = self.run_preprocessed_acyclic_bmc_probe(
                int_summary,
                features,
                exact_stage_budget,
                "exact-BvToInt",
                true,
            ) {
                return Some(result);
            }
        }

        if self.budget_exhausted(deadline) {
            return None;
        }
        let native_stage_budget = self
            .remaining_budget(deadline)
            .map_or(stage_budget, |budget| {
                if budget <= stage_budget {
                    budget
                } else {
                    stage_budget
                }
            });
        if native_stage_budget.is_zero() {
            return None;
        }

        // Build the BV-native summary before selecting the bound. Inlining can
        // collapse generated basic-block DAGs by hundreds of predicates, so the
        // exhaustive acyclic bound must follow the transformed graph.
        let summary = PreprocessSummary::build_bv_native(self.problem.clone(), self.config.verbose);
        let prefer_exact_native = self.problem.has_bv_sorts()
            && !features.uses_arrays
            && (features.num_predicates >= 32 || features.dag_depth >= 32 || features.has_ite);
        self.run_preprocessed_acyclic_bmc_probe(
            summary,
            features,
            native_stage_budget,
            "BV-native",
            prefer_exact_native,
        )
    }

    pub(crate) fn acyclic_bmc_stage_budget(
        features: &ProblemFeatures,
        remaining: Duration,
    ) -> Duration {
        if features.uses_arrays || Self::is_large_acyclic_linear_graph(features) {
            // Acyclic CHCs are common in model-checker-consumer basic-block encodings. Exhaustive
            // BMC is complete for these DAGs, while falling through to PDR/CEGAR
            // often spends the rest of the budget rediscovering path facts.
            // Give the complete proof lane the remaining budget, subject to the
            // caller's global deadline.
            return remaining;
        }

        if remaining <= Duration::from_secs(6) {
            remaining
        } else {
            remaining
                .mul_f64(0.85)
                .max(Duration::from_secs(6))
                .min(Duration::from_secs(13))
                .min(remaining)
        }
    }

    pub(crate) fn multi_pred_portfolio_timeout(remaining: Duration) -> Duration {
        const MIN_PORTFOLIO_BUDGET: Duration = Duration::from_secs(3);
        // `PortfolioSolver` permits a two-second cooperative grace period after
        // its parallel timeout. Reserve that time here so the nested stage does
        // not overrun the adaptive solver's absolute deadline.
        const COOPERATIVE_GRACE_RESERVE: Duration = Duration::from_secs(2);

        let desired = if remaining <= MIN_PORTFOLIO_BUDGET {
            remaining
        } else {
            remaining
                .mul_f64(0.7)
                .max(MIN_PORTFOLIO_BUDGET)
                .min(remaining)
        };
        desired.min(remaining.saturating_sub(COOPERATIVE_GRACE_RESERVE))
    }

    pub(crate) fn multi_pred_probe_timeout(&self, deadline: Option<Instant>) -> Duration {
        match self.remaining_budget(deadline) {
            Some(remaining) => remaining.min(Duration::from_secs(5)),
            None => Duration::from_secs(5),
        }
    }

    pub(crate) fn multi_pred_retry_timeout(&self, deadline: Option<Instant>) -> Option<Duration> {
        self.remaining_budget(deadline)
            .or(Some(Duration::from_secs(10)))
    }

    /// Solve multi-predicate linear problems - PDR focused.
    ///
    /// Uses failure-guided retry: if portfolio returns Unknown, run a quick PDR
    /// probe with stats collection, analyze the failure, and retry with adjusted
    /// configuration.
    ///
    /// Part of #2082 - Extend failure-guided retry to multi-predicate paths.
    pub(super) fn solve_multi_pred_linear(
        &self,
        features: &ProblemFeatures,
        deadline: Option<Instant>,
    ) -> (PortfolioResult, ValidationEvidence) {
        if self.config.verbose {
            safe_eprintln!("Adaptive: Using multi-pred linear strategy (PDR focused)");
        }

        // Stage 0: Try structural synthesis (< 1ms overhead on extra-small-lia)
        if let Some(result) = self.try_synthesis() {
            if self.config.verbose {
                safe_eprintln!("Adaptive: MultiPredLinear problem solved by structural synthesis");
            }
            return (result, ValidationEvidence::FullVerification);
        }

        // Stage 0.15: early shallow BV bounded-refutation probe (CHC-COMP
        // BV-Lin). Sound-by-construction (validated Unsafe only); catches
        // shallow BV counterexamples the contended dual-lane BMC misses.
        if let Some(result) = self.try_bv_shallow_bmc_refutation(deadline) {
            if self.config.verbose {
                safe_eprintln!("Adaptive: MultiPredLinear early BV shallow-BMC found Unsafe");
            }
            return (result, ValidationEvidence::FullVerification);
        }

        // Stage 0.5: Exact BMC probe for acyclic DAGs.
        // model-checker-consumer-style CHC often encode bounded basic-block chains. These
        // problems are acyclic, so a short BV-native inlined BMC probe can
        // prove safety or find a bug before the heavier non-inlined PDR and
        // portfolio stages.
        if let Some((result, evidence)) = self.try_acyclic_bmc_probe(features, deadline) {
            if self.config.verbose {
                safe_eprintln!("Adaptive: Acyclic BMC probe solved the problem");
            }
            return (result, evidence);
        }

        // Stage 0.6: relational ARRAY-equality Houdini (#chc25-array-relational).
        // The llreve two-copy relational-equivalence family WITH an explicit
        // `CHC_COMP_FALSE` query predicate (memset/memmove/memccpy/strncmp/…)
        // classifies as MultiPredLinear rather than a single-predicate
        // ComplexLoop. Its safety proof is a relational array equality
        // `arrₐ = arr_b` plus scalar copy equalities — try that certified lane
        // before the heavy PDR portfolio. Gated on `has_array_sorts` so it is a
        // zero-cost skip for the (dominant) non-array MultiPredLinear corpus, and
        // it re-verifies per-rule on the ORIGINAL clauses before any Safe.
        if self.problem.has_array_sorts() && !self.budget_exhausted(deadline) {
            let arr_start = Instant::now();
            if let Some(result) = self.try_relational_equality_houdini_lane(deadline) {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: MultiPredLinear relational array-equality Houdini solved the problem"
                    );
                }
                self.decision_log.log_decision(DecisionEntry {
                    stage: "multi_pred_linear_array_relational_houdini",
                    gate_result: true,
                    gate_reason: "relational array-equality invariant certified".to_string(),
                    budget_secs: self
                        .remaining_budget(deadline)
                        .map_or(0.0, |d| d.as_secs_f64()),
                    elapsed_secs: arr_start.elapsed().as_secs_f64(),
                    result: Self::result_to_str(&result),
                    lemmas_learned: 0,
                    max_frame: 0,
                });
                return (result, ValidationEvidence::FullVerification);
            }
            self.decision_log.log_decision(DecisionEntry {
                stage: "multi_pred_linear_array_relational_houdini",
                gate_result: false,
                gate_reason: "no certified relational array-equality invariant".to_string(),
                budget_secs: self
                    .remaining_budget(deadline)
                    .map_or(0.0, |d| d.as_secs_f64()),
                elapsed_secs: arr_start.elapsed().as_secs_f64(),
                result: "unknown",
                lemmas_learned: 0,
                max_frame: 0,
            });
        }

        // Stage 1: Case-split preprocessing (#1306).
        // For problems with unconstrained constant arguments (like dillig12_m),
        // case-split can simplify the problem by partitioning based on mode
        // values. Keep the dedicated limit narrow so it cannot starve the later
        // PDR lane on longer phase chains.
        if self.config.verbose {
            safe_eprintln!("Adaptive: Trying case-split preprocessing (Stage 0)");
        }
        let case_split_budget = self
            .remaining_budget(deadline)
            .unwrap_or(Duration::from_secs(8))
            .min(Duration::from_secs(8));
        let mut case_split_config = Self::multi_pred_pdr_config(PdrConfig {
            max_iterations: 1000,
            max_obligations: 500_000,
            max_frames: 100,
            verbose: self.config.verbose,
            max_escalation_level: if features.uses_datatypes { 0 } else { 3 },
            // Cap case-split so the portfolio still gets the bulk of the budget.
            // Case-split either finds a simple decomposition quickly or not at all;
            // spending more time here steals from TPA/PDKIND which need the budget
            // to converge on harder multi-predicate problems (#4751).
            // 8s budget: branches are individually capped at 4s (case_split/mod.rs)
            // and the dillig12_m branches now solve in ~3.2s (E=1) + ~1.2s
            // (E!=1); the remaining time covers merged-model verification which
            // needs SMT checks on complex guarded formulas (e.g., dillig12_m's
            // quadratic invariant).
            solve_timeout: Some(case_split_budget),
            ..PdrConfig::default()
        })
        .with_tla_trace_from_env();
        self.apply_user_hints(&mut case_split_config);
        let case_split_start = Instant::now();
        if let Some(result) = PdrSolver::try_case_split_solve(&self.problem, case_split_config) {
            // Validate case-split result (#5549 soundness fix)
            let validated = self.validate_adaptive_result(result);
            if !matches!(validated, PdrResult::Unknown) {
                self.decision_log.log_decision(DecisionEntry {
                    stage: "multi_pred_linear_case_split",
                    gate_result: true,
                    gate_reason: "case-split solved".to_string(),
                    budget_secs: case_split_budget.as_secs_f64(),
                    elapsed_secs: case_split_start.elapsed().as_secs_f64(),
                    result: Self::result_to_str(&validated),
                    lemmas_learned: 0,
                    max_frame: 0,
                });
                return (validated, ValidationEvidence::FullVerification);
            }
        }
        self.decision_log.log_decision(DecisionEntry {
            stage: "multi_pred_linear_case_split",
            gate_result: true,
            gate_reason: "case-split returned none/unknown".to_string(),
            budget_secs: case_split_budget.as_secs_f64(),
            elapsed_secs: case_split_start.elapsed().as_secs_f64(),
            result: "unknown",
            lemmas_learned: 0,
            max_frame: 0,
        });
        if self.config.verbose {
            safe_eprintln!("Adaptive: Case-split returned None, continuing to portfolio");
        }

        // Stage 1.25: direct Kind pre-pass.
        //
        // Kind candidates are validated against the original clauses before
        // leaving the adaptive layer. Run this probe after case-split so it
        // cannot starve the rest of the multi-predicate pipeline on long
        // phase-chain benchmarks.
        let allow_direct_kind_prepass = features.num_predicates <= 2 && features.dag_depth <= 2;
        if allow_direct_kind_prepass && !self.budget_exhausted(deadline) {
            // Cap the Kind prepass at 3s. Kind either converges quickly
            // (k=0,1,2) or it stalls indefinitely unrolling long transitions.
            // The portfolio already runs Kind in parallel with other engines,
            // so the prepass only needs to catch the easy wins. Previous cap
            // of 20s starved TPA/PDR/DAR on benchmarks like half_true_modif_m
            // and dillig12_m where Kind cannot converge but TPA can.
            //
            // ITE/mod-div multi-predicate cases get only a smoke-test budget:
            // direct Kind uses executor-backed incremental queries whose timeout
            // is cooperative. On dillig12_m, the 3s pre-pass can enter k=1 and
            // overrun the caller timeout before downstream PDR/TPA runs.
            let direct_kind_cap = if features.has_ite || features.has_mod_div {
                Duration::from_millis(500)
            } else {
                Duration::from_secs(3)
            };
            let kind_budget = self
                .remaining_budget(deadline)
                .unwrap_or(direct_kind_cap)
                .min(direct_kind_cap);
            if !kind_budget.is_zero() {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: Trying direct Kind before non-inlined PDR ({:.1}s budget)",
                        kind_budget.as_secs_f64()
                    );
                }
                if let Some(result) = self.try_kind(kind_budget) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: Direct Kind solved the multi-pred linear problem"
                        );
                    }
                    let evidence = if matches!(result, PortfolioResult::Unsafe(_)) {
                        ValidationEvidence::CounterexampleVerification
                    } else {
                        ValidationEvidence::FullVerification
                    };
                    return (result, evidence);
                }
            }
        } else if self.config.verbose && !allow_direct_kind_prepass {
            safe_eprintln!(
                "Adaptive: Skipping direct Kind pre-pass for long multi-predicate chain (preds={}, dag_depth={})",
                features.num_predicates,
                features.dag_depth
            );
        }

        // Cross-engine lemma transfer pool (#7919). Populated by non-inlined PDR
        // when it returns Unknown, consumed by portfolio engines and retry.
        let mut transferred_pool: Option<LemmaPool> = None;
        // Stage rotation (item 5): true when the non-inlined PDR stage gave up
        // Stuck with zero frame growth — the same-family retry PDR probe on
        // the same problem is then provably redundant and skipped.
        let mut non_inlined_pdr_stuck_no_growth = false;

        // Stage 1.5: Run PDR on the original non-inlined problem for modular,
        // ITE-heavy, or long multi-predicate chains. Clause inlining can erase
        // the per-predicate structure these problems need for invariant discovery.
        //
        // self.problem is the ORIGINAL non-inlined problem. PdrSolver::new() on it
        // bypasses the portfolio's ClauseInliner preprocessing entirely.
        if self.should_try_non_inlined_pdr(features) && !self.budget_exhausted(deadline) {
            let stage_budget = self.non_inlined_pdr_stage_budget(features, deadline);
            if !stage_budget.is_zero() {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: Trying non-inlined PDR before portfolio ({} predicates, {:.1}s budget)",
                        features.num_predicates,
                        stage_budget.as_secs_f64()
                    );
                }

                let mut pdr_config = Self::multi_pred_pdr_config(PdrConfig {
                    verbose: self.config.verbose,
                    solve_timeout: Some(stage_budget),
                    // #7930: Cap escalation for DT problems.
                    max_escalation_level: if features.uses_datatypes { 0 } else { 3 },
                    ..PdrConfig::default()
                })
                .with_tla_trace_from_env();
                // Re-enable Entry-CEGAR for deep multi-predicate chains in the
                // non-inlined PDR stage. multi_pred_pdr_config disables it to
                // avoid burning unbounded portfolio budget, but the non-inlined
                // stage already has a bounded solve_timeout.
                // Item 5a: subsequent stages (portfolio, retry) exist, so let
                // this stage self-report hopeless stagnation and release its
                // budget to them instead of burning the full stage share.
                pdr_config.give_up_on_stuck = true;
                // Gate: dag_depth >= 4 or num_predicates >= 4. Deep chains like
                // gj2007_m_2 (5 preds, dag_depth=5) need CEGAR to propagate
                // invariants across predicate boundaries. Shallower chains
                // (s_multipl_13: 3 preds) solve faster without it.
                if features.dag_depth >= 4 || features.num_predicates >= 4 {
                    pdr_config.use_entry_cegar_discharge = true;
                }
                self.apply_user_hints(&mut pdr_config);
                let non_inlined_start = Instant::now();
                let mut pdr = PdrSolver::new(self.problem.clone(), pdr_config);
                pdr.enable_tla_trace_from_config();
                let result = pdr.solve();
                // Feed the live progress snapshot, then consult it for stage
                // rotation (item 5): a Stuck-with-zero-frame-growth stage
                // makes the same-family retry probe provably redundant.
                let stage_stats = pdr.extract_stats();
                self.accumulate_stats(&stage_stats);
                non_inlined_pdr_stuck_no_growth =
                    self.predecessor_stage_stuck_no_growth(&stage_stats);
                let validated = self.validate_adaptive_result(result);
                if !matches!(validated, PdrResult::Unknown) {
                    if self.config.verbose {
                        safe_eprintln!("Adaptive: Non-inlined PDR solved the problem");
                    }
                    self.decision_log.log_decision(DecisionEntry {
                        stage: "multi_pred_linear_non_inlined_pdr",
                        gate_result: true,
                        gate_reason: format!("{} predicates", features.num_predicates),
                        budget_secs: stage_budget.as_secs_f64(),
                        elapsed_secs: non_inlined_start.elapsed().as_secs_f64(),
                        result: Self::result_to_str(&validated),
                        lemmas_learned: 0,
                        max_frame: 0,
                    });
                    return (validated, ValidationEvidence::FullVerification);
                }
                self.decision_log.log_decision(DecisionEntry {
                    stage: "multi_pred_linear_non_inlined_pdr",
                    gate_result: true,
                    gate_reason: format!("{} predicates, unknown", features.num_predicates),
                    budget_secs: stage_budget.as_secs_f64(),
                    elapsed_secs: non_inlined_start.elapsed().as_secs_f64(),
                    result: "unknown",
                    lemmas_learned: 0,
                    max_frame: 0,
                });
                // Export learned lemmas for cross-engine transfer (#7919).
                // Non-inlined PDR may have discovered useful lemmas even
                // though it could not prove safety within its budget.
                let pool = pdr.export_lemmas();
                if self.config.verbose && !pool.is_empty() {
                    safe_eprintln!(
                        "Adaptive: Exported {} lemmas from non-inlined PDR for cross-engine transfer",
                        pool.len()
                    );
                }
                transferred_pool = Some(pool);
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: Non-inlined PDR returned Unknown, continuing to portfolio"
                    );
                }
            }
        }

        // Stage 2: Run mixed portfolio
        // Multi-predicate linear problems use PDR for joint invariant discovery,
        // plus PDKind via SingleLoop encoding for k-induction (Golem-style).
        // PDKind runs in parallel with other engines to avoid consuming budget
        // sequentially on spurious results (#2750).
        //
        // Budget check before portfolio (#7034)
        if self.budget_exhausted(deadline) {
            if self.config.verbose {
                safe_eprintln!("Adaptive: Budget exhausted after case-split, skipping portfolio");
            }
            return (
                PortfolioResult::Unknown,
                ValidationEvidence::FullVerification,
            );
        }

        // BV routing (linear): cyclic word-level BV problems get the dedicated
        // BV dual-lane (Lane C = BV-native PDR/BMC at the full remaining budget)
        // before the generic linear portfolio, which bit-blasts BV to hundreds
        // of Bool vars where PDR generalization collapses. Acyclic BV is already
        // handled by the BV-native BMC probe above (hence the has_cycles guard),
        // so this targets the cyclic multi-pred-linear BV that dominates the
        // CHC-COMP BV-Lin track. Every lane self-validates (Safe re-verified
        // per-rule on the original; Unsafe by counterexample), preserving 0-wrong;
        // an unhandled shape returns Unknown and falls through to the generic
        // portfolio. Arrays/datatypes excluded — the dual-lane is BV-scalar.
        if self.problem.has_bv_sorts()
            && !self.problem.has_array_sorts()
            && !self.problem.has_datatype_sorts()
            && features.has_cycles
            && !self.budget_exhausted(deadline)
        {
            if let Some(remaining) = self.remaining_budget(deadline) {
                let result = self.solve_bv_dual_lane(remaining);
                if !matches!(result, PortfolioResult::Unknown) {
                    if self.config.verbose {
                        safe_eprintln!("Adaptive: MultiPredLinear BV dual-lane solved the problem");
                    }
                    return (result, ValidationEvidence::FullVerification);
                }
            }
        }

        // Use deadline-based remaining budget (#7034, supersedes #4751).
        // Propagate verbose flag to PDR engine configs (#1969)
        // Seed portfolio PDR engines with transferred lemma pool (#7919).
        //
        // #7930: For DT problems, cap escalation at level 0. PDR generalization
        // escalation is unproductive for Datatype sorts — DT needs SMT-level
        // constructor/selector reasoning, not LIA lemma generalization. Without
        // this cap, PDR spends 4x longer stagnating through escalation levels,
        // starving other engines of budget.
        let max_esc = if features.uses_datatypes { 0 } else { 3 };
        let mut pdr1 = Self::multi_pred_pdr_config(PdrConfig {
            verbose: self.config.verbose,
            max_escalation_level: max_esc,
            ..PdrConfig::default()
        });
        // inc-12: the second (duplicate) portfolio PDR runs the spacer-mode
        // variant on the MultiPredLinear arm (startup off, interpolant-as-
        // lemma, executor-first checks); pdr1 keeps the full default pipeline.
        let mut pdr2 = Self::multi_pred_pdr_config(PdrConfig {
            verbose: self.config.verbose,
            max_escalation_level: max_esc,
            ..PdrConfig::portfolio_spacer_variant()
        });
        if let Some(ref pool) = transferred_pool {
            if !pool.is_empty() {
                pdr1.lemma_hints = Some(pool.clone());
                pdr2.lemma_hints = Some(pool.clone());
            }
        }

        let mut config = self.multi_pred_linear_portfolio_config(pdr1, pdr2, features);

        // Use deadline for portfolio timeout (#7034).
        if let Some(ref mut timeout) = config.parallel_timeout {
            if let Some(remaining) = self.remaining_budget(deadline) {
                *timeout = Self::multi_pred_portfolio_timeout(remaining);
                if timeout.is_zero() {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: Skipping mixed portfolio because only its cooperative grace window remains"
                        );
                    }
                    return (
                        PortfolioResult::Unknown,
                        ValidationEvidence::FullVerification,
                    );
                }
            }
        }
        let portfolio_budget_secs = config
            .parallel_timeout
            .map_or(0.0, |timeout| timeout.as_secs_f64());

        let portfolio_start = Instant::now();
        let portfolio_result = if self.is_large_acyclic_bv_array_graph(features) {
            // The standard portfolio constructor would run BvToBool/BvToInt
            // preprocessing before engines start. On large acyclic model-checker-consumer
            // BV+array DAGs that preprocessing can dominate the remaining
            // budget after the exact BV-native BMC lane. Keep any fallback
            // portfolio BV-native unless the exact lane has already produced
            // definitive evidence.
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: Running BV-native fallback portfolio for large acyclic BV+array graph"
                );
            }
            let summary =
                PreprocessSummary::build_bv_native(self.problem.clone(), self.config.verbose);
            PortfolioSolver::from_summary(summary, config).solve()
        } else {
            self.run_portfolio(config)
        };

        self.decision_log.log_decision(DecisionEntry {
            stage: "multi_pred_linear_portfolio",
            gate_result: true,
            gate_reason: "mixed portfolio".to_string(),
            budget_secs: portfolio_budget_secs,
            elapsed_secs: portfolio_start.elapsed().as_secs_f64(),
            result: Self::result_to_str(&portfolio_result),
            lemmas_learned: 0,
            max_frame: 0,
        });

        // If solved, return immediately
        if !matches!(portfolio_result, PortfolioResult::Unknown) {
            if !features.has_cycles
                && features.num_predicates > 1
                && matches!(&portfolio_result, PortfolioResult::Safe(model) if model.is_empty())
            {
                if !features.uses_arrays {
                    return (
                        portfolio_result,
                        ValidationEvidence::ScalarAcyclicBmcExhaustive {
                            max_depth: Self::acyclic_bmc_depth(features),
                        },
                    );
                }

                tracing::warn!(
                    max_depth = Self::acyclic_bmc_depth(features),
                    "Adaptive: mixed portfolio returned acyclic array empty-model Safe; \
                     demoting to Unknown (#9227)"
                );
                return (
                    PortfolioResult::Unknown,
                    ValidationEvidence::BmcExhaustedSearch {
                        max_depth: Self::acyclic_bmc_depth(features),
                    },
                );
            }
            return (portfolio_result, ValidationEvidence::FullVerification);
        }

        // Check global memory budget before starting retry stages (#2771)
        if TermStore::global_memory_exceeded() {
            return (
                PortfolioResult::Unknown,
                ValidationEvidence::FullVerification,
            );
        }

        // Budget check before failure-guided retry (#7034)
        if self.budget_exhausted(deadline) {
            if self.config.verbose {
                safe_eprintln!("Adaptive: Budget exhausted after portfolio, skipping retry");
            }
            return (
                PortfolioResult::Unknown,
                ValidationEvidence::FullVerification,
            );
        }

        // Stage rotation (item 5): skip the same-family retry PDR probe when
        // the non-inlined PDR stage already gave up Stuck with zero frame
        // growth on this very problem — the probe would replay the identical
        // stagnating search. Completeness-only (returns the portfolio Unknown).
        if non_inlined_pdr_stuck_no_growth {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: Skipping failure-guided retry — non-inlined PDR was stuck with zero frame growth"
                );
            }
            self.decision_log.log_decision(DecisionEntry {
                stage: "multi_pred_linear_retry",
                gate_result: false,
                gate_reason: "skipped: predecessor PDR stage stuck with zero frame growth"
                    .to_string(),
                budget_secs: self
                    .remaining_budget(deadline)
                    .map_or(0.0, |d| d.as_secs_f64()),
                elapsed_secs: 0.0,
                result: "unknown",
                lemmas_learned: 0,
                max_frame: 0,
            });
            return (portfolio_result, ValidationEvidence::FullVerification);
        }

        // Stage 3: Failure-guided retry (with transferred lemma pool).
        let retry_budget = self
            .remaining_budget(deadline)
            .map_or(0.0, |duration| duration.as_secs_f64());
        let retry_start = Instant::now();
        let retry_result = self.failure_guided_retry(deadline, transferred_pool.as_ref());
        let retry_solved = retry_result.as_ref().is_some_and(|candidate| {
            !matches!(
                candidate,
                PortfolioResult::Unknown | PortfolioResult::NotApplicable
            )
        });
        let result = retry_result.unwrap_or(portfolio_result);
        self.decision_log.log_decision(DecisionEntry {
            stage: "multi_pred_linear_retry",
            gate_result: retry_solved,
            gate_reason: if retry_solved {
                "failure-guided retry produced a result"
            } else {
                "failure-guided retry exhausted or remained unknown"
            }
            .to_string(),
            budget_secs: retry_budget,
            elapsed_secs: retry_start.elapsed().as_secs_f64(),
            result: Self::result_to_str(&result),
            lemmas_learned: 0,
            max_frame: 0,
        });
        (result, ValidationEvidence::FullVerification)
    }

    /// Failure-guided retry: probe PDR, analyze the failure, and retry with
    /// adjusted configuration. Returns `Some(result)` if retry solves or
    /// `None` to fall through to the original portfolio Unknown.
    pub(super) fn failure_guided_retry(
        &self,
        deadline: Option<Instant>,
        transferred_pool: Option<&LemmaPool>,
    ) -> Option<PortfolioResult> {
        if self.budget_exhausted(deadline) {
            if self.config.verbose {
                safe_eprintln!("Adaptive: Budget exhausted, skipping failure-guided retry");
            }
            return None;
        }
        if self.config.verbose {
            safe_eprintln!("Adaptive: Portfolio returned Unknown, running failure analysis probe");
        }

        let probe_timeout = self.multi_pred_probe_timeout(deadline);
        // #7930: Cap PDR escalation for DT problems in retry path too.
        let max_esc = if self.problem.has_datatype_sorts() {
            0
        } else {
            3
        };
        let mut probe_config = Self::multi_pred_pdr_config(PdrConfig {
            max_frames: 30,
            max_iterations: 500,
            verbose: self.config.verbose,
            solve_timeout: Some(probe_timeout),
            max_escalation_level: max_esc,
            ..PdrConfig::default()
        })
        .with_tla_trace_from_env();
        // Re-enable Entry-CEGAR for bounded probe when predicate count >= 4.
        if self.problem.predicates().len() >= 4 {
            probe_config.use_entry_cegar_discharge = true;
        }
        self.apply_user_hints(&mut probe_config);
        // Seed probe with transferred lemmas from non-inlined PDR (#7919).
        if let Some(pool) = transferred_pool {
            if !pool.is_empty() {
                probe_config.lemma_hints = Some(pool.clone());
            }
        }
        let probe_result = PdrSolver::solve_problem_with_stats(&self.problem, probe_config);
        self.accumulate_stats(&probe_result.stats);

        // Validate before returning (#5549 soundness fix)
        if !matches!(probe_result.result, PdrResult::Unknown) {
            let validated = self.validate_adaptive_result(probe_result.result);
            if !matches!(validated, PdrResult::Unknown) {
                return Some(validated);
            }
        }

        if self.budget_exhausted(deadline) {
            return None;
        }

        let analysis = FailureAnalysis::from_stats(&probe_result.stats);
        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: Probe analysis - {} (confidence {:.0}%)",
                analysis.mode,
                analysis.confidence * 100.0
            );
            safe_eprintln!("Adaptive: Diagnostic: {}", analysis.diagnostic);
        }

        let guide = FailureGuide::from_analysis(&analysis);

        if let Some(ref alt_engine) = guide.try_alternative_engine {
            if let Some(result) = self.try_alternative_engine_budgeted(alt_engine, deadline) {
                return Some(result);
            }
        }

        if self.budget_exhausted(deadline) {
            return None;
        }

        if !guide.adjustments.is_empty() {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: Retrying with {} config adjustments",
                    guide.adjustments.len()
                );
            }
            let mut retry_base = Self::multi_pred_pdr_config(PdrConfig {
                verbose: self.config.verbose,
                solve_timeout: self.multi_pred_retry_timeout(deadline),
                max_escalation_level: max_esc,
                ..PdrConfig::default()
            })
            .with_tla_trace_from_env();
            // Re-enable Entry-CEGAR for bounded retry when predicate count >= 4.
            if self.problem.predicates().len() >= 4 {
                retry_base.use_entry_cegar_discharge = true;
            }
            self.apply_user_hints(&mut retry_base);
            retry_base.user_hints.extend(probe_result.learned_lemmas);
            // Also seed retry with transferred lemmas from non-inlined PDR (#7919).
            if let Some(pool) = transferred_pool {
                if !pool.is_empty() {
                    retry_base.lemma_hints = Some(pool.clone());
                }
            }
            let retry_config = guide.apply_to_config(retry_base);
            let retry_result = PdrSolver::solve_problem_with_stats(&self.problem, retry_config);
            self.accumulate_stats(&retry_result.stats);
            let validated = self.validate_adaptive_result(retry_result.result);
            if !matches!(validated, PdrResult::Unknown) {
                return Some(validated);
            }
        }

        None
    }

    pub(crate) fn multi_pred_linear_portfolio_config(
        &self,
        pdr1: PdrConfig,
        pdr2: PdrConfig,
        features: &ProblemFeatures,
    ) -> PortfolioConfig {
        let mut engines = vec![EngineConfig::Pdr(pdr1), EngineConfig::Pdr(pdr2)];

        // #7930: Skip Kind for DT problems. Kind with SingleLoop encoding
        // produces huge flattened formulas for DT+BV problems (13+ predicates
        // with constructor/selector terms). This adds active CPU contention
        // without producing useful k-induction results. For non-DT problems,
        // Kind via SingleLoop replaces the no-op PDKind (#6500).
        if !features.uses_datatypes {
            engines.push(EngineConfig::Kind(KindConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                ..KindConfig::default()
            }));
        }

        engines.extend([
            // TPA closes mode-dispatch arithmetic cases (e.g., dillig12_m) that
            // often stall in PDR/TRL due heavy implication checks.
            EngineConfig::Tpa(TpaConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                ..TpaConfig::default()
            }),
            // PDKind via SingleLoop encoding: combines PDR frames with
            // k-induction. Golem's pdkind solves benchmarks like s_multipl_24
            // that pure PDR and Kind cannot handle individually.
            EngineConfig::Pdkind(PdkindConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                ..PdkindConfig::default()
            }),
            // IMC (interpolation-based model checking) via SingleLoop.
            // Solves multi-predicate problems with alternating counter
            // patterns (e.g., s_multipl_24) that PDR stalls on.
            EngineConfig::Imc(ImcConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                ..ImcConfig::default()
            }),
            // DAR's current implementation is a single-predicate transition-system
            // engine. The readiness preflight rejects multi-predicate problems, so
            // this hot path leaves the worker slot for engines that can enter.
            // TRL subsumes BMC (unrolling + transitive relation learning).
            // Replacing plain BMC with TRL to add loop summarization
            // capability without increasing engine count.
            EngineConfig::Trl(TrlConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                ..TrlConfig::default()
            }),
            EngineConfig::Cegar(CegarConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                ..CegarConfig::default()
            }),
        ]);

        // Array routing (#C-LAWI): LAWI (lazy abstraction with interpolants,
        // McMillan IMPACT) is AY's purpose-built array engine — previously dead
        // code for Int-array problems (only the SimpleLoop&&uses_real selector
        // path built it). Schedule it for array problems before the PDR-centric
        // roster collapses on opaque array values. Additive + self-validating
        // (Safe replayed per-rule on the original; Unsafe by counterexample),
        // preserving 0-wrong. (IMC is already in this roster.)
        if features.uses_arrays {
            engines.push(EngineConfig::Lawi(crate::lawi::LawiConfig::default()));
        }

        // Acyclic BMC completeness (#6047): For acyclic problems, add BMC with
        // acyclic_safe=true. After ClauseInliner collapses the predicate chain,
        // BMC on the preprocessed problem only needs depth = num_predicates to
        // achieve completeness (every execution path is bounded by chain length).
        // This handles the model-checker-consumer memory-tracking pattern: 27-predicate acyclic
        // basic-block chains where PDR can't initialize after inlining.
        if !features.has_cycles && !self.is_large_acyclic_bv_array_graph(features) {
            let depth = Self::acyclic_bmc_depth(features);
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: Adding acyclic BMC to portfolio (depth={}, dag_depth={}, preds={})",
                    depth,
                    features.dag_depth,
                    features.num_predicates
                );
            }
            engines.push(EngineConfig::Bmc(BmcConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                max_depth: depth,
                acyclic_safe: true,
                prefer_exact_acyclic_first: false,
                per_depth_timeout: None,
                time_budget: None,
                enable_k_induction: false,
                enable_adaptive_stepping: false,
                proof_cross_check: false,
                ts_probe_clamp: None,
                sweep_past_spurious_sat: true,
            }));
        } else if features.uses_arrays {
            // Fix C (#FM3): Cyclic array CHCs previously had NO
            // counterexample-finder in this lineup — TRL/CEGAR/PDR rarely
            // produce replayable witnesses for array transitions, so false
            // (Unsafe) verdicts were unreachable. Add bounded incremental BMC
            // with `acyclic_safe: false`: exhausting the depth bound returns
            // Unknown, so this engine can ONLY contribute Unsafe results.
            // Every counterexample still passes the standard witness replay
            // validation against the original clauses (div/mod replays
            // unblocked by #A3 executor axiomatization).
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: Adding Unsafe-only BMC for cyclic array problem (depth=30, preds={})",
                    features.num_predicates
                );
            }
            engines.push(EngineConfig::Bmc(BmcConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                max_depth: 30,
                acyclic_safe: false,
                prefer_exact_acyclic_first: false,
                per_depth_timeout: None,
                time_budget: None,
                enable_k_induction: false,
                enable_adaptive_stepping: false,
                proof_cross_check: false,
                ts_probe_clamp: None,
                sweep_past_spurious_sat: true,
            }));
        } else if features.is_linear && features.num_predicates >= 2 {
            // inc-9: cyclic LINEAR multipred problems previously had no
            // bounded counterexample-finder in this lineup (the eldarica
            // reve/llreve unsat-cex-suppression family): CEGAR/TRL Unsafe
            // results were suppressed by gates g1/g3 and the invariant
            // engines rarely reach the refutation. Add Unsafe-only
            // incremental BMC (acyclic_safe=false ⇒ depth exhaustion returns
            // Unknown, so this engine can ONLY contribute Unsafe): the
            // SingleLoop persistent-executor lane discharges shallow depths
            // quickly, and every counterexample still passes derivation
            // witness replay validation against the original clauses.
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: Adding Unsafe-only BMC for cyclic linear multipred problem \
                     (depth=50, preds={})",
                    features.num_predicates
                );
            }
            engines.push(EngineConfig::Bmc(BmcConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                max_depth: 50,
                acyclic_safe: false,
                prefer_exact_acyclic_first: false,
                per_depth_timeout: None,
                time_budget: None,
                enable_k_induction: false,
                enable_adaptive_stepping: false,
                proof_cross_check: false,
                ts_probe_clamp: None,
                sweep_past_spurious_sat: true,
            }));
        } else if features.has_cycles {
            // Cyclic bug-finding BMC on the original (non-SingleLoop) clauses.
            //
            // Without this lane, cyclic multi-predicate linear systems have NO
            // sound bounded bug-finder in the portfolio: Kind/PDKind/TRL/TPA
            // all run on the SingleLoop overapproximation, whose Unsafe
            // results are suppressed (spurious-prone, no back-translation),
            // and the acyclic BMC lanes are gated on `!has_cycles`. Shallow,
            // trivially reachable counterexamples (e.g. a two-phase
            // accumulator reaching the query after ~17 steps) were therefore
            // missed entirely while PDR stalled on invariant search.
            //
            // `acyclic_safe` stays false, so exhausting `max_depth` yields
            // Unknown (never Safe) — sound for cyclic systems. Unsafe results
            // carry a concrete witness and pass through the portfolio's
            // mandatory counterexample validation.
            engines.push(EngineConfig::Bmc(BmcConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    ..ChcEngineConfig::default()
                },
                ..BmcConfig::default()
            }));
        }

        PortfolioConfig {
            external_cancellation: Some(self.cancellation_token.clone()),
            engines,
            parallel: true,
            timeout: None,
            parallel_timeout: if self.config.time_budget.is_zero() {
                None
            } else {
                Some(self.config.time_budget)
            },
            verbose: self.config.verbose,

            enable_preprocessing: true,
            engine_budgets: ay_core::kani_compat::DetHashMap::default(),
            memory_budget: self.config.memory_budget,
            strict_proofs: self.config.strict_proofs,
        }
    }

    pub(crate) fn non_inlined_pdr_stage_budget(
        &self,
        features: &ProblemFeatures,
        deadline: Option<Instant>,
    ) -> Duration {
        // Budget scaling (#1398): 5s base + scaling per predicate beyond 3.
        // For 5 preds (gj2007_m_2): 5 + 3*2 = 11s. For 2-3 preds: 5s.
        // Cap at 15s to avoid starving the portfolio. push_lemmas requires
        // O(predicates × lemmas) SMT calls per level — 5s is insufficient
        // for 5+ predicate chains where invariants are discovered at level 1
        // but convergence needs multiple push rounds.
        let num_preds = features.num_predicates as u64;
        let base_budget_secs = if num_preds >= 5 {
            // #1362 D2: 3s per predicate beyond 3 for long chains.
            // gj2007_m_2 (5 preds) needs ~15s (Z3 needs 15.4s).
            5 + 3 * num_preds.saturating_sub(3)
        } else if num_preds >= 4 {
            5 + 2 * num_preds.saturating_sub(3)
        } else {
            5
        };
        let max_budget = Duration::from_secs(base_budget_secs.min(15));
        let remaining = self.remaining_budget(deadline).unwrap_or(max_budget);

        if self.is_large_acyclic_bv_array_graph(features) {
            // model-checker-consumer accumulator-style generated CHCs are large acyclic
            // basic-block DAGs with BV-indexed arrays. The generic array cap
            // below leaves native PDR with only a startup probe, then falls into
            // broad BvToBool preprocessing across hundreds of predicates. Give
            // native PDR a bounded first-class slice while preserving the global
            // deadline.
            return remaining
                .mul_f64(0.85)
                .max(Duration::from_secs(10))
                .min(Duration::from_secs(30))
                .min(remaining);
        }

        if features.uses_arrays {
            // #7897: Array-heavy model-checker-consumer memory-tracking harnesses spend the whole
            // external 15s cap in non-inlined PDR and never reach the portfolio.
            // Keep a short probe here, but reserve most of the budget for the
            // downstream array-aware portfolio (persistent-array sessions,
            // BvToBool/BvToInt, CEGAR/BMC/TRL).
            return (remaining / 4).min(Duration::from_secs(4)).min(max_budget);
        }

        // #7457: Cap non-inlined PDR to a fraction of remaining budget.
        // Without this cap, discover_counting_invariants can consume the
        // entire budget via O(n^2 * k) SMT checks, leaving zero for the
        // portfolio. dillig22_m regressed from <0.1s to ~5s because of this.
        // #1362 D2: Relax to 66% for 5+ predicate chains where non-inlined
        // PDR is the primary strategy and portfolio has lower expected yield.
        // For 2-3 predicates, use 50% of remaining budget.
        if num_preds >= 5 {
            (remaining * 2 / 3).min(max_budget)
        } else {
            (remaining / 2).min(max_budget)
        }
    }

    pub(crate) fn should_try_non_inlined_pdr(&self, features: &ProblemFeatures) -> bool {
        // Always try non-inlined PDR for 2+ predicate problems.
        // Clause inlining destroys per-predicate structure that PDR needs
        // for modular invariant discovery. The zone/chc-hard-tail peak (53/55)
        // was achieved with this wide gate; narrowing it to mod/div/ITE-only
        // caused the s_multipl_* regression from 53 to 42.
        if features.num_predicates <= 1 {
            if self.config.verbose {
                safe_eprintln!("should_try_non_inlined_pdr: false (single predicate)");
            }
            return false;
        }
        if self.config.verbose {
            safe_eprintln!(
                "should_try_non_inlined_pdr: true ({} predicates)",
                features.num_predicates
            );
        }
        true
    }
}
