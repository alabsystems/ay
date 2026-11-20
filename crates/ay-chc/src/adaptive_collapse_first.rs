// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Classify-after-preprocess for collapsible nonlinear problems (CH4/K3 of
//! the development design notes at `9598c4206`, §3.5).
//!
//! The kind2 family (823/1287 of LIA-Nonlin) is emitted as a nonlinear
//! multi-predicate system — `MAIN ← top_step ∧ MAIN`, 10–24 predicates, 12–26
//! clauses — that the classifier reads as `MultiPredComplex` on the RAW
//! clauses. That arm pays the non-inlined PDR pre-stage (≈15 s at 60 s) and
//! the other multi-predicate stages first, and only THEN does the portfolio's
//! own preprocessing inline the system to a 1-predicate / 3-clause transition
//! system ("Preprocessing reduced 12 clauses -> 3, 10 predicates -> 1") and
//! hand it to twelve engines with ≈12 s left. z3 answers the collapsed system
//! in 0.02 s; AY answered 1/65 in the LIA 100-sample.
//!
//! This route runs the SAME sound, already-validated preprocessing FIRST
//! (`PreprocessSummary::build_with_limits`, the pipeline the portfolio would
//! run anyway), and if the collapse is COMPLETE — one predicate, linear, the
//! witness back-translation complete — dispatches the collapsed problem down
//! the whole adaptive ladder as a nested portfolio with the full remaining
//! budget: it re-classifies as `SimpleLoop`, so it gets the front BMC probe
//! with the transition-system witness, the query-flag candidate race, Kind,
//! the solo PDR probe and the SimpleLoop roster. The ORIGINAL problem stays
//! authoritative: a nested `Safe` is back-translated and re-verified per
//! ORIGINAL rule (`verify_model_per_rule`, strict), a nested `Unsafe` is
//! back-translated and replayed against the ORIGINAL clauses
//! (`try_verify_counterexample`), and anything that does not verify falls
//! through to today's `MultiPredComplex` ladder with whatever budget is left.
//! An incomplete collapse (predicates remain) never enters the route.
//!
//! The verified verdict then passes through the bounded finalization boundary like
//! every other adaptive answer, and the CLI's own validation battery on top of
//! that is unchanged.

use std::time::Duration;

use ay_core::time::Instant;

use crate::adaptive::{AdaptiveConfig, AdaptiveExecutionMode, AdaptivePortfolio};
use crate::adaptive_decision_log::DecisionEntry;
use crate::classifier::{ProblemClass, ProblemClassifier, ProblemFeatures};
use crate::engine_result::ValidationEvidence;
use crate::lemma_pool::{LemmaPool, SharedLemma};
use crate::pdr::InvariantModel;
use crate::portfolio::{
    backtranslate_counterexample_with_ground_evidence, PortfolioResult, PreprocessSummary,
};
use crate::{ChcExpr, ChcVar};

/// Below this remaining budget the route is not attempted.
const COLLAPSE_FIRST_MIN_BUDGET: Duration = Duration::from_millis(500);
/// Share of the remaining budget the nested portfolio may use; the rest stays
/// for the original-problem re-verification and, on failure, the fallback
/// ladder. At 60 s this leaves ~6 s; the re-verification of a 3-clause
/// transition-system invariant against 12–26 original rules takes well under
/// a second on every kind2 instance measured.
const COLLAPSE_FIRST_NESTED_SHARE: f64 = 0.90;
/// Per-rule cap for the original-problem re-verification of a nested `Safe`.
const COLLAPSE_FIRST_SAFE_VERIFY_CAP: Duration = Duration::from_secs(10);
/// Cap for the original-problem replay of a nested `Unsafe`.
const COLLAPSE_FIRST_UNSAFE_VERIFY_CAP: Duration = Duration::from_secs(10);
const STAGE: &str = "collapse_first_nonlinear";
/// Bound on the seeds one solve keeps for a continuing caller.
const MAX_SEARCH_SEEDS: usize = 512;

impl AdaptivePortfolio {
    /// Whether the RAW problem is a candidate: nonlinear multi-predicate, no
    /// theory the SimpleLoop ladder guards against, not the deterministic mode
    /// (which keeps its fixed-budget schedule). Cheap syntactic checks only;
    /// the decisive test (does it collapse completely?) is the preprocessing
    /// itself.
    pub(crate) fn collapse_first_candidate(&self, features: &ProblemFeatures) -> bool {
        self.config.execution_mode != AdaptiveExecutionMode::DeterministicSequential
            && features.class == ProblemClass::MultiPredComplex
            && !features.is_linear
            && !features.is_single_predicate
            && !features.uses_arrays
            && !features.uses_datatypes
            && !self.problem.has_bv_sorts()
            && !self.problem.has_array_sorts()
            && !self.problem.has_datatype_sorts()
            && !self.problem.has_stripped_body_forall()
    }

    /// Preprocess first; if the collapse is complete, solve the collapsed
    /// problem with the full ladder and re-verify on the original. `None`
    /// falls through to today's `MultiPredComplex` ladder.
    pub(crate) fn try_collapse_first_nonlinear(
        &self,
        features: &ProblemFeatures,
        deadline: Option<Instant>,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        if !self.collapse_first_candidate(features) {
            return None;
        }
        let route_start = Instant::now();
        let budget = self
            .remaining_budget(deadline)
            .unwrap_or(self.config.time_budget);
        if budget < COLLAPSE_FIRST_MIN_BUDGET {
            return None;
        }

        // The standard pipeline, bounded by the outer deadline/cancellation.
        let summary = PreprocessSummary::build_with_limits(
            self.problem.clone(),
            self.config.verbose,
            deadline,
            &self.cancellation_token,
        )?;
        let collapsed = &summary.transformed_problem;
        let n_preds = collapsed.predicates().len();
        let n_clauses = collapsed.clauses().len();
        let linear = collapsed
            .clauses()
            .iter()
            .all(|c| c.body.predicates.len() <= 1);
        let complete = n_preds == 1
            && linear
            && summary.transform_memory.unsafe_backtranslation_complete()
            && !summary.bv_abstracted;
        if !complete {
            self.log_collapse_first(
                false,
                format!(
                    "collapse incomplete: {} -> {n_preds} predicates, {} -> {n_clauses} clauses, linear={linear}, unsafe_backtranslation_complete={}",
                    self.problem.predicates().len(),
                    self.problem.clauses().len(),
                    summary.transform_memory.unsafe_backtranslation_complete()
                ),
                budget,
                route_start,
                "skipped",
            );
            // The fallback reuses the pipeline's output instead of re-running it.
            self.stash_collapse_fallback(summary, None);
            return None;
        }
        let collapsed_features = ProblemClassifier::classify(collapsed);
        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: nonlinear problem collapses completely ({} preds / {} clauses -> {n_preds} / {n_clauses}, reclassified {}); solving the collapsed system first with the full ladder",
                self.problem.predicates().len(),
                self.problem.clauses().len(),
                collapsed_features.class
            );
        }

        // Nested portfolio on the collapsed problem with most of the budget.
        let nested_budget = self
            .remaining_budget(deadline)
            .unwrap_or(budget)
            .mul_f64(COLLAPSE_FIRST_NESTED_SHARE);
        if nested_budget < COLLAPSE_FIRST_MIN_BUDGET {
            self.stash_collapse_fallback(summary, None);
            return None;
        }
        let mut nested_config = AdaptiveConfig::with_budget(nested_budget, self.config.verbose);
        nested_config.strict_proofs = self.config.strict_proofs;
        nested_config.memory_budget = self.config.memory_budget;
        nested_config.progress_enabled = self.config.progress_enabled;
        nested_config.collapse_first_nested = true;
        // Child of this route's lane token (the nested solve runs on its own
        // thread): external and ladder-race cancellation propagate in.
        let nested = AdaptivePortfolio::new_for_solve_with_cancellation(
            collapsed.clone(),
            nested_config,
            &self.lane_token(),
        );
        let nested_start = Instant::now();
        let nested_result = nested.solve();
        let nested_elapsed = nested_start.elapsed();

        let remaining_after = self.remaining_budget(deadline).unwrap_or(Duration::MAX);
        // CH4b: whatever the nested run learned without deciding is kept for
        // the fallback (collapsed-problem vocabulary; the fallback portfolio
        // runs on this very collapsed problem via the handed-off summary).
        let seeds = Self::collapse_seeds_from(&nested, collapsed);
        let outcome = self.verify_collapsed_verdict(
            nested_result,
            &summary,
            budget,
            route_start,
            nested_elapsed,
            remaining_after,
        );
        if outcome.is_none() {
            self.stash_collapse_fallback(summary, seeds);
        }
        outcome
    }

    /// Establish a nested verdict on the ORIGINAL clauses (fail-closed).
    fn verify_collapsed_verdict(
        &self,
        nested_result: crate::VerifiedChcResult,
        summary: &PreprocessSummary,
        budget: Duration,
        route_start: Instant,
        nested_elapsed: Duration,
        remaining_after: Duration,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        match nested_result {
            crate::VerifiedChcResult::Safe(verified) => {
                // Back-translate to the ORIGINAL vocabulary and re-verify per
                // ORIGINAL rule with the strict validator (fail-closed).
                let collapsed_model = verified.into_inner();
                let original_model = summary.back_translator.translate_validity(collapsed_model);
                let per_rule = remaining_after.min(COLLAPSE_FIRST_SAFE_VERIFY_CAP);
                if self.validate_translated_safe_model_on_original(&original_model, per_rule) {
                    self.log_collapse_first(
                        true,
                        format!(
                            "collapsed system Safe in {:.2}s; back-translated invariant verified on every original rule",
                            nested_elapsed.as_secs_f64()
                        ),
                        budget,
                        route_start,
                        "safe",
                    );
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: collapse-first Safe verified on the original clauses ({:.2}s)",
                            route_start.elapsed().as_secs_f64()
                        );
                    }
                    return Some((
                        PortfolioResult::Safe(original_model),
                        ValidationEvidence::FullVerification,
                    ));
                }
                self.log_collapse_first(
                    false,
                    format!(
                        "collapsed system Safe in {:.2}s but the back-translated invariant did not verify on the original rules; falling back",
                        nested_elapsed.as_secs_f64()
                    ),
                    budget,
                    route_start,
                    "unknown",
                );
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: collapse-first Safe REJECTED by original-clause verification; falling back to the multi-predicate ladder"
                    );
                }
                None
            }
            crate::VerifiedChcResult::Unsafe(verified) => {
                // Back-translate and replay against the ORIGINAL clauses.
                // Back-translate WITH ground evidence — the portfolio's own
                // path (`validation.rs`): the plain `translate_invalidity`
                // remaps only the step/witness vocabulary, and the original
                // clauses' replay then cannot discharge the inlined body atoms
                // (`MAIN ∧ step ⇒ MAIN`) from a `MAIN`-only trace and returns
                // Unknown. The ground derivation carried through the inliner
                // is what lets the ORIGINAL-clause replay decide.
                let witness_start = Instant::now();
                let collapsed_cex = self.witnessed_collapsed_counterexample(
                    &summary.transformed_problem,
                    verified.into_inner(),
                    remaining_after.min(COLLAPSE_FIRST_UNSAFE_VERIFY_CAP),
                );
                let original_cex = backtranslate_counterexample_with_ground_evidence(
                    summary.back_translator.as_ref(),
                    &self.problem,
                    &collapsed_cex,
                    &self.cancellation_token,
                );
                let replay = remaining_after
                    .saturating_sub(witness_start.elapsed())
                    .min(COLLAPSE_FIRST_UNSAFE_VERIFY_CAP);
                if self.validate_original_counterexample_with_budget(&original_cex, replay) {
                    self.log_collapse_first(
                        true,
                        format!(
                            "collapsed system Unsafe in {:.2}s; back-translated counterexample replayed on the original clauses",
                            nested_elapsed.as_secs_f64()
                        ),
                        budget,
                        route_start,
                        "unsafe",
                    );
                    if self.config.verbose {
                        safe_eprintln!(
                            "Adaptive: collapse-first Unsafe replayed on the original clauses ({:.2}s)",
                            route_start.elapsed().as_secs_f64()
                        );
                    }
                    return Some((
                        PortfolioResult::Unsafe(original_cex),
                        ValidationEvidence::CounterexampleVerification,
                    ));
                }
                self.log_collapse_first(
                    false,
                    format!(
                        "collapsed system Unsafe in {:.2}s but the back-translated counterexample did not replay on the original clauses; falling back",
                        nested_elapsed.as_secs_f64()
                    ),
                    budget,
                    route_start,
                    "unknown",
                );
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: collapse-first Unsafe REJECTED by original-clause replay; falling back to the multi-predicate ladder"
                    );
                }
                None
            }
            crate::VerifiedChcResult::Unknown(_) => {
                self.log_collapse_first(
                    false,
                    format!(
                        "collapsed system unknown after {:.2}s; falling back",
                        nested_elapsed.as_secs_f64()
                    ),
                    budget,
                    route_start,
                    "unknown",
                );
                None
            }
        }
    }

    /// A collapsed-system counterexample the original-clause replay can decide.
    ///
    /// A witness-free counterexample (e.g. an IMC trace the nested portfolio
    /// accepted through its transition-system reachability check) carries no
    /// ground derivation, so the back-translation has nothing to map and the
    /// replay on the nonlinear ORIGINAL clauses — where the bounded BMC replay
    /// does not apply — is inconclusive. The collapsed system is linear with
    /// one predicate, so a bounded BMC replay THERE derives a witnessed
    /// counterexample cheaply. It is still only a candidate: the original-
    /// clause replay decides, fail-closed. Measured on kind2 durationThm_3
    /// (unsafe): IMC's witness-free trace won the nested SimpleLoop race at
    /// 1.3 s and was rejected, then the multi-predicate fallback timed out.
    fn witnessed_collapsed_counterexample(
        &self,
        collapsed: &crate::ChcProblem,
        cex: crate::pdr::Counterexample,
        budget: Duration,
    ) -> crate::pdr::Counterexample {
        if cex.witness.is_some() || cex.ground_derivation.is_some() {
            return cex;
        }
        let depth_hint = cex.steps.len().saturating_add(2);
        match crate::bmc::BmcSolver::replay_confirm_unsafe_on_problem(
            collapsed,
            depth_hint,
            budget,
            Some(self.lane_token()),
            self.config.verbose,
        ) {
            Some(witnessed) => {
                tracing::info!(
                    "Adaptive: collapse-first witness-free Unsafe re-derived with a ground witness on the collapsed system (depth hint {depth_hint})"
                );
                witnessed
            }
            None => cex,
        }
    }

    /// Hand the fallback ladder the collapse-first preprocessing (reused by
    /// its first preprocessing-enabled portfolio, `make_portfolio_solver`)
    /// and, if any, the nested run's seeds (applied to that portfolio's PDR
    /// engines, which run on the same collapsed problem).
    fn stash_collapse_fallback(&self, summary: PreprocessSummary, seeds: Option<LemmaPool>) {
        *self
            .handed_off_preprocess
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = Some(summary);
        if let Some(seeds) = seeds.filter(|pool| !pool.is_empty()) {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: collapse-first hands {} seed lemmas to the fallback portfolio",
                    seeds.len()
                );
            }
            *self
                .fallback_seed_pool
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner) = Some(seeds);
        }
    }

    /// The nested run's seeds, IF its problem is the collapsed problem the
    /// fallback portfolio will run on (same predicates, same argument sorts,
    /// in the same order) — the adaptive constructor may prune or scalarize,
    /// and a seed keyed to a shifted predicate id would only be noise.
    fn collapse_seeds_from(
        nested: &AdaptivePortfolio,
        collapsed: &crate::ChcProblem,
    ) -> Option<LemmaPool> {
        let signature = |problem: &crate::ChcProblem| {
            problem
                .predicates()
                .iter()
                .map(|p| (p.id, p.arg_sorts.clone()))
                .collect::<Vec<_>>()
        };
        (signature(&nested.problem) == signature(collapsed)).then(|| nested.take_search_seeds())
    }

    /// Whether the collapse-first route handed down a COMPLETE collapse (one
    /// linear predicate) that the fallback portfolio will run on.
    pub(crate) fn inherits_complete_collapse(&self) -> bool {
        self.handed_off_preprocess
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .as_ref()
            .is_some_and(|summary| {
                let collapsed = &summary.transformed_problem;
                collapsed.predicates().len() == 1
                    && collapsed
                        .clauses()
                        .iter()
                        .all(|c| c.body.predicates.len() <= 1)
            })
    }

    pub(crate) fn take_handed_off_preprocess(&self) -> Option<PreprocessSummary> {
        self.handed_off_preprocess
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .take()
    }

    pub(crate) fn take_fallback_seed_pool(&self) -> Option<LemmaPool> {
        self.fallback_seed_pool
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .take()
    }

    pub(crate) fn take_search_seeds(&self) -> LemmaPool {
        std::mem::take(
            &mut *self
                .search_seeds
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner),
        )
    }

    /// Record a PDR lemma pool learned on this problem (canonical vocabulary
    /// already) as seeds.
    pub(crate) fn record_search_seed_pool(&self, pool: LemmaPool) {
        let mut seeds = self
            .search_seeds
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        for lemma in pool.lemmas {
            if seeds.len() >= MAX_SEARCH_SEEDS {
                break;
            }
            seeds.lemmas.push(lemma);
        }
    }

    /// Record an invariant candidate that did NOT validate as seeds: each
    /// interpretation is renamed positionally onto PDR's canonical variables
    /// (`__p{id}_a{i}`) and split into top-level conjuncts, so PDR can keep
    /// the conjuncts that are inductive and drop the rest.
    pub(crate) fn record_search_seed_model(&self, model: &InvariantModel) {
        let mut lemmas = Vec::new();
        for (pid, interp) in model.iter() {
            let Some(pred) = self.problem.get_predicate(*pid) else {
                continue;
            };
            if interp.vars.len() != pred.arity()
                || interp
                    .vars
                    .iter()
                    .zip(&pred.arg_sorts)
                    .any(|(var, sort)| &var.sort != sort)
            {
                continue;
            }
            let subst: Vec<(ChcVar, ChcExpr)> = interp
                .vars
                .iter()
                .enumerate()
                .map(|(i, var)| {
                    (
                        var.clone(),
                        ChcExpr::var(ChcVar::new(
                            format!("__p{}_a{i}", pid.index()),
                            var.sort.clone(),
                        )),
                    )
                })
                .collect();
            let canonical = interp.formula.substitute(&subst);
            for conjunct in canonical.collect_conjuncts() {
                if matches!(conjunct.simplify_constants(), ChcExpr::Bool(_)) {
                    continue;
                }
                lemmas.push(SharedLemma {
                    formula: conjunct,
                    predicate: *pid,
                    source_frame: 0,
                });
            }
        }
        let mut seeds = self
            .search_seeds
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        for lemma in lemmas {
            if seeds.len() >= MAX_SEARCH_SEEDS {
                break;
            }
            if !seeds
                .lemmas
                .iter()
                .any(|l| l.predicate == lemma.predicate && l.formula == lemma.formula)
            {
                seeds.lemmas.push(lemma);
            }
        }
    }

    fn log_collapse_first(
        &self,
        gate_result: bool,
        gate_reason: String,
        budget: Duration,
        started: Instant,
        result: &'static str,
    ) {
        self.decision_log.log_decision(DecisionEntry {
            stage: STAGE,
            gate_result,
            gate_reason,
            budget_secs: budget.as_secs_f64(),
            elapsed_secs: started.elapsed().as_secs_f64(),
            result,
            lemmas_learned: 0,
            max_frame: 0,
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ChcParser;

    /// kind2 shape in miniature: MAIN ← step ∧ MAIN (nonlinear), a fact, a
    /// query on a Bool flag; `step` is a definitional predicate the inliner
    /// removes, so the system collapses to one predicate.
    const KIND2_LIKE_SAFE: &str = "(set-logic HORN)
(declare-fun step (Int Bool Int Bool) Bool)
(declare-fun MAIN (Int Bool) Bool)
(assert (forall ((x Int) (ok Bool) (x1 Int) (ok1 Bool))
  (=> (and (= x1 (+ x 1)) (= ok1 (and ok (>= x1 0)))) (step x ok x1 ok1))))
(assert (forall ((x Int) (ok Bool)) (=> (and (= x 0) ok) (MAIN x ok))))
(assert (forall ((x Int) (ok Bool) (x1 Int) (ok1 Bool))
  (=> (and (MAIN x ok) (step x ok x1 ok1)) (MAIN x1 ok1))))
(assert (forall ((x Int) (ok Bool)) (=> (and (MAIN x ok) (not ok)) false)))";

    /// Same shape, unsafe: the flag drops once x reaches 3.
    const KIND2_LIKE_UNSAFE: &str = "(set-logic HORN)
(declare-fun step (Int Bool Int Bool) Bool)
(declare-fun MAIN (Int Bool) Bool)
(assert (forall ((x Int) (ok Bool) (x1 Int) (ok1 Bool))
  (=> (and (= x1 (+ x 1)) (= ok1 (and ok (< x1 3)))) (step x ok x1 ok1))))
(assert (forall ((x Int) (ok Bool)) (=> (and (= x 0) ok) (MAIN x ok))))
(assert (forall ((x Int) (ok Bool) (x1 Int) (ok1 Bool))
  (=> (and (MAIN x ok) (step x ok x1 ok1)) (MAIN x1 ok1))))
(assert (forall ((x Int) (ok Bool)) (=> (and (MAIN x ok) (not ok)) false)))";

    /// Genuinely nonlinear: two recursive occurrences of the SAME predicate
    /// in one body; no definitional inlining can make it linear.
    const TRULY_NONLINEAR: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (P x) (P y) (= z (+ x y 1))) (P z))))
(assert (forall ((x Int)) (=> (and (P x) (< x 0)) false)))";

    fn portfolio(src: &str, secs: u64) -> AdaptivePortfolio {
        let problem = ChcParser::parse(src).expect("fixture parses");
        AdaptivePortfolio::new(
            problem,
            AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(secs)),
        )
    }

    #[test]
    fn kind2_like_raw_problem_is_a_candidate_and_collapses_to_safe() {
        let p = portfolio(KIND2_LIKE_SAFE, 20);
        let features = ProblemClassifier::classify(&p.problem);
        assert_eq!(features.class, ProblemClass::MultiPredComplex);
        assert!(!features.is_linear);
        assert!(p.collapse_first_candidate(&features));
        let result = p.try_collapse_first_nonlinear(&features, None);
        assert!(
            matches!(
                result,
                Some((
                    PortfolioResult::Safe(_),
                    ValidationEvidence::FullVerification
                ))
            ),
            "collapsed system must be proven and the invariant re-verified on the original"
        );
    }

    #[test]
    fn kind2_like_unsafe_collapses_and_replays_on_the_original() {
        let p = portfolio(KIND2_LIKE_UNSAFE, 20);
        let features = ProblemClassifier::classify(&p.problem);
        assert!(p.collapse_first_candidate(&features));
        let result = p.try_collapse_first_nonlinear(&features, None);
        assert!(
            matches!(
                result,
                Some((
                    PortfolioResult::Unsafe(_),
                    ValidationEvidence::CounterexampleVerification
                ))
            ),
            "collapsed system must be refuted and the counterexample replayed on the original"
        );
    }

    #[test]
    fn truly_nonlinear_problem_never_enters_the_route() {
        let p = portfolio(TRULY_NONLINEAR, 5);
        let features = ProblemClassifier::classify(&p.problem);
        // Single predicate already, so the candidate gate rejects it; and even
        // if it were multi-predicate the collapse could not be complete.
        assert!(!p.collapse_first_candidate(&features));
        assert!(p.try_collapse_first_nonlinear(&features, None).is_none());
    }

    /// Two mutually-dependent predicates in a self-product: the standard
    /// pipeline cannot inline this down to one linear predicate.
    const INCOMPLETE_COLLAPSE: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int)) (=> (= x 1) (Q x))))
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (P x) (Q y) (= z (+ x y))) (P z))))
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (Q x) (P y) (= z (+ x y 1))) (Q z))))
(assert (forall ((x Int)) (=> (and (P x) (< x 0)) false)))";

    #[test]
    fn fall_through_hands_its_preprocessing_to_the_next_portfolio() {
        let p = portfolio(INCOMPLETE_COLLAPSE, 5);
        let features = ProblemClassifier::classify(&p.problem);
        if !p.collapse_first_candidate(&features) {
            // Not this route's shape on this build; nothing to check.
            return;
        }
        assert!(p.try_collapse_first_nonlinear(&features, None).is_none());
        let summary = p
            .take_handed_off_preprocess()
            .expect("a fall-through must hand the pipeline's output to the fallback");
        assert!(
            summary.transformed_problem.predicates().len() > 1 || {
                summary
                    .transformed_problem
                    .clauses()
                    .iter()
                    .any(|c| c.body.predicates.len() > 1)
            }
        );
        assert!(
            p.take_handed_off_preprocess().is_none(),
            "taken exactly once"
        );
    }

    #[test]
    fn a_rejected_candidate_becomes_canonical_conjunct_seeds() {
        let p = portfolio(KIND2_LIKE_SAFE, 5);
        let main = p
            .problem
            .predicates()
            .iter()
            .find(|pred| pred.arity() == 2)
            .expect("MAIN");
        let x = ChcVar::new("x", crate::ChcSort::Int);
        let ok = ChcVar::new("ok", crate::ChcSort::Bool);
        let formula = ChcExpr::and(
            ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::var(ok.clone()),
        );
        let mut model = InvariantModel::new();
        model.set(
            main.id,
            crate::pdr::PredicateInterpretation::new(vec![x, ok], formula),
        );
        p.record_search_seed_model(&model);
        let seeds = p.take_search_seeds();
        assert_eq!(seeds.len(), 2, "one seed per top-level conjunct");
        let a0 = format!("__p{}_a0", main.id.index());
        let a1 = format!("__p{}_a1", main.id.index());
        for lemma in &seeds.lemmas {
            assert_eq!(lemma.predicate, main.id);
            let names: Vec<String> = lemma.formula.vars().into_iter().map(|v| v.name).collect();
            assert!(
                names.iter().all(|n| *n == a0 || *n == a1),
                "seed must be over PDR's canonical vars, got {names:?}"
            );
        }
        // An interpretation whose arity does not match is ignored, not guessed.
        let mut bad = InvariantModel::new();
        bad.set(
            main.id,
            crate::pdr::PredicateInterpretation::new(
                vec![ChcVar::new("only", crate::ChcSort::Int)],
                ChcExpr::ge(
                    ChcExpr::var(ChcVar::new("only", crate::ChcSort::Int)),
                    ChcExpr::int(0),
                ),
            ),
        );
        p.record_search_seed_model(&bad);
        assert!(p.take_search_seeds().is_empty());
    }

    #[test]
    fn deterministic_mode_keeps_the_fixed_schedule() {
        let problem = ChcParser::parse(KIND2_LIKE_SAFE).expect("fixture parses");
        let mut config = AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(5));
        config.execution_mode = AdaptiveExecutionMode::DeterministicSequential;
        let p = AdaptivePortfolio::new(problem, config);
        let features = ProblemClassifier::classify(&p.problem);
        assert!(!p.collapse_first_candidate(&features));
    }
}
