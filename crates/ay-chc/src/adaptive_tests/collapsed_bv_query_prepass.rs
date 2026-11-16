// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Admission and exact-source acceptance for the bounded native BV prepass.

use super::*;
use crate::ChcCheckedReplayObligation;

pub(super) enum QueryPolarity {
    Wrap,
    NoWrap,
}

pub(super) fn original_problem(polarity: QueryPolarity) -> ChcProblem {
    let mut input = String::from("(set-logic HORN)\n");
    for index in 0..40 {
        input.push_str(&format!(
            "(declare-rel P{index} ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64)))\n"
        ));
    }
    input.push_str(
        "(declare-rel error ())\n\
         (declare-var start (_ BitVec 64))\n\
         (declare-var end (_ BitVec 64))\n\
         (declare-var off (_ BitVec 64))\n\
         (rule (=> (and (bvule start end) (bvule end (_ bv5 64)) \
         (bvule off (_ bv4 64)) (bvule (bvadd start off) (_ bv4 64))) \
         (P0 start end off)))\n",
    );
    for index in 0..39 {
        input.push_str(&format!(
            "(rule (=> (P{index} start end off) (P{} start end off)))\n",
            index + 1
        ));
    }
    let wrap = "(bvult (bvadd start off) start)";
    let query = match polarity {
        QueryPolarity::Wrap => wrap.to_string(),
        QueryPolarity::NoWrap => format!("(not {wrap})"),
    };
    input.push_str(&format!(
        "(rule (=> (and (P39 start end off) {query}) error))\n(query error)\n"
    ));
    ChcParser::parse(&input).expect("original 40-relation BV64 query must parse")
}

fn assert_collapsed_summary(original: &ChcProblem) {
    let cancellation = crate::CancellationToken::new();
    let summary = PreprocessSummary::build_bv_native_with_limits(
        original.clone(),
        false,
        Some(Instant::now() + Duration::from_secs(10)),
        &cancellation,
    )
    .expect("bounded BV-native fixture preprocessing must finish");
    assert!(AdaptivePortfolio::is_fully_collapsed_query_problem(
        &summary.transformed_problem
    ));
}

fn assert_prepass_trace(
    trace: &crate::AdaptiveSolveTrace,
    outcome: crate::AdaptiveStrategyOutcome,
) {
    let observed = trace
        .observations()
        .iter()
        .find(|observation| observation.stage == "collapsed_bv_native_query_prepass")
        .expect("the original solve must actually use the collapsed native prepass");
    assert!(observed.gate_result);
    assert_eq!(observed.outcome, outcome);
    assert!(!trace
        .observations()
        .iter()
        .any(|observation| observation.stage == "original_bv_exact_acyclic_probe"));
}

#[test]
#[timeout(90_000)]
fn collapsed_safe_preserves_total_original_model_and_strict_replay() {
    let original = original_problem(QueryPolarity::Wrap);
    assert_collapsed_summary(&original);
    let adaptive = AdaptivePortfolio::new(
        original.clone(),
        AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(15)),
    );
    let trace_session = adaptive.decision_log.begin_trace();
    let run = adaptive.solve_proof_run();
    assert_prepass_trace(
        &trace_session.finish(),
        crate::AdaptiveStrategyOutcome::Safe,
    );
    let model = run
        .result()
        .safe_invariant()
        .expect("native prepass must produce verified Safe, not a refusal")
        .model();
    assert!(
        !model.is_empty(),
        "empty exhaustive evidence is not this test's acceptance"
    );
    for predicate in original.predicates() {
        assert!(
            model.get(&predicate.id).is_some(),
            "missing original {}",
            predicate.name
        );
    }
    assert!(crate::engines::validate_external_invariant_model(
        &original,
        model,
        &PdrConfig {
            strict_proofs: true,
            solve_timeout: Some(Duration::from_secs(10)),
            preserve_original_clauses: true,
            disable_array_scalarization: true,
            ..PdrConfig::default()
        },
    )
    .expect("the complete model must validate on the original clauses"));
    let checked = run
        .run_checked_replay(Duration::from_secs(20))
        .expect("every exact original-clause obligation must have strict replay");
    assert!(checked.proof_run().accepted_as_proof());
    assert!(checked.summary().obligations.len() >= original.clauses().len());
    assert!(checked
        .summary()
        .obligations
        .iter()
        .all(|row| row.strict_cert.is_some()));
    checked
        .recheck_with_fresh_ay(Duration::from_secs(20))
        .expect("strict retained bundles and exact original queries must recheck on fresh AY");
}

#[test]
#[timeout(90_000)]
fn collapsed_flipped_query_requires_original_unsafe_witness_and_replay() {
    let original = original_problem(QueryPolarity::NoWrap);
    assert_collapsed_summary(&original);
    let adaptive = AdaptivePortfolio::new(
        original,
        AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(15)),
    );
    let trace_session = adaptive.decision_log.begin_trace();
    let run = adaptive.solve_proof_run();
    assert_prepass_trace(
        &trace_session.finish(),
        crate::AdaptiveStrategyOutcome::Unsafe,
    );
    let witness = run
        .result()
        .unsafe_counterexample()
        .expect("negating the original query must produce verified Unsafe")
        .counterexample();
    assert!(
        witness
            .witness
            .as_ref()
            .is_some_and(|w| !w.entries.is_empty())
            || witness
                .ground_derivation
                .as_ref()
                .is_some_and(|d| !d.is_empty()),
        "Unsafe must carry original-source evidence, not only the transformed SAT model"
    );
    let checked = run
        .run_checked_replay(Duration::from_secs(20))
        .expect("the original Unsafe witness must pass checked replay");
    assert!(checked.proof_run().accepted_as_proof());
    assert_ne!(
        checked.summary().obligations,
        [] as [ChcCheckedReplayObligation; 0]
    );
    checked
        .recheck_with_fresh_ay(Duration::from_secs(20))
        .expect("original Unsafe replay payloads must independently recheck");

    // Matching IDs and declarations are not authority for a changed query.
    // Disable search-based replacement: decide this witness against the SAFE
    // original, not whether a fresh unrelated reachability search can answer.
    let deadline = Instant::now() + Duration::from_secs(10);
    let _solve = crate::smt::ScopedSolveDeadline::new(Some(deadline));
    let _smt = crate::smt::ScopedSmtDeadline::install_until(deadline);
    let mut verifier = crate::PdrSolver::new(
        original_problem(QueryPolarity::Wrap),
        PdrConfig {
            strict_proofs: true,
            solve_timeout: Some(Duration::from_secs(10)),
            preserve_original_clauses: true,
            disable_array_scalarization: true,
            disable_cex_replay: true,
            ..PdrConfig::default()
        },
    );
    assert!(verifier.confirm_counterexample(witness.clone()).is_err());
}

fn noncollapsed_problem() -> ChcProblem {
    let mut input = String::from("(set-logic HORN)\n(declare-var x (_ BitVec 8))\n");
    for index in 0..40 {
        input.push_str(&format!("(declare-rel P{index} ((_ BitVec 8)))\n"));
    }
    // More definitions than either the normal (8) or graph-collapse (64)
    // inliner cap: this recognized BV DAG must retain a real predicate.
    for value in 0..65 {
        input.push_str(&format!("(rule (P0 (_ bv{value} 8)))\n"));
    }
    for index in 0..39 {
        input.push_str(&format!("(rule (=> (P{index} x) (P{} x)))\n", index + 1));
    }
    input.push_str("(rule (=> (and (P39 x) (bvugt x (_ bv64 8))) false))\n(check-sat)\n");
    ChcParser::parse(&input).expect("noncollapsed acyclic BV fixture must parse")
}

#[test]
#[timeout(30_000)]
fn recognized_noncollapsed_summary_keeps_raw_original_fallback() {
    let original = noncollapsed_problem();
    let summary = PreprocessSummary::build_bv_native_with_limits(
        original.clone(),
        false,
        Some(Instant::now() + Duration::from_secs(10)),
        &crate::CancellationToken::new(),
    )
    .expect("bounded noncollapsed fixture preprocessing must finish");
    assert!(!summary.transformed_problem.predicates().is_empty());
    assert!(!AdaptivePortfolio::is_fully_collapsed_query_problem(
        &summary.transformed_problem
    ));
    let adaptive = AdaptivePortfolio::new(original, AdaptiveConfig::test_default());
    let features = adaptive.features();
    assert!(features.is_linear && !features.has_cycles && !features.uses_arrays);
    assert!(features.num_predicates >= 32 && adaptive.problem.has_bv_sorts());
    let trace_session = adaptive.decision_log.begin_trace();
    let result =
        adaptive.try_acyclic_bmc_probe(&features, Some(Instant::now() + Duration::from_secs(5)));
    let trace = trace_session.finish();
    assert!(!trace
        .observations()
        .iter()
        .any(|row| row.stage == "collapsed_bv_native_query_prepass"));
    assert!(trace
        .observations()
        .iter()
        .any(|row| row.stage == "original_bv_exact_acyclic_probe"));
    assert!(!matches!(result, Some((PortfolioResult::Unsafe(_), _))));
}

#[test]
fn full_collapse_gate_rejects_empty_surviving_and_malformed_query_shapes() {
    let empty = ChcProblem::new();
    assert!(!AdaptivePortfolio::is_fully_collapsed_query_problem(&empty));
    let mut query_only = empty;
    query_only.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
        true,
    ))));
    assert!(AdaptivePortfolio::is_fully_collapsed_query_problem(
        &query_only
    ));
    let mut surviving = query_only.clone();
    surviving.declare_predicate("surviving", vec![ChcSort::BitVec(8)]);
    assert!(!AdaptivePortfolio::is_fully_collapsed_query_problem(
        &surviving
    ));
    // Even a malformed dangling predicate must not pass this structural gate.
    let mut body_predicate = query_only.clone();
    body_predicate.clauses_mut()[0]
        .body
        .predicates
        .push((crate::PredicateId::new(0), vec![]));
    assert!(!AdaptivePortfolio::is_fully_collapsed_query_problem(
        &body_predicate
    ));
    query_only.clauses_mut()[0].head = ClauseHead::Predicate(crate::PredicateId::new(0), vec![]);
    assert!(!AdaptivePortfolio::is_fully_collapsed_query_problem(
        &query_only
    ));
}

#[test]
fn expired_caller_deadline_never_starts_native_preprocessing_or_raw_fallback() {
    let adaptive = AdaptivePortfolio::new(
        original_problem(QueryPolarity::Wrap),
        AdaptiveConfig::test_default(),
    );
    let trace_session = adaptive.decision_log.begin_trace();
    assert!(adaptive
        .try_acyclic_bmc_probe(&adaptive.features(), Some(Instant::now()))
        .is_none());
    assert_eq!(trace_session.finish().observations(), []);
}

#[test]
fn cancelled_caller_never_starts_native_preprocessing_or_raw_fallback() {
    let adaptive = AdaptivePortfolio::new(
        original_problem(QueryPolarity::Wrap),
        AdaptiveConfig::test_default(),
    );
    adaptive.cancellation_handle().cancel();
    let trace_session = adaptive.decision_log.begin_trace();
    assert!(adaptive
        .try_acyclic_bmc_probe(
            &adaptive.features(),
            Some(Instant::now() + Duration::from_secs(1))
        )
        .is_none());
    assert_eq!(trace_session.finish().observations(), []);
}

#[test]
fn expired_ambient_deadline_cannot_be_reopened_by_native_prefix() {
    let adaptive = AdaptivePortfolio::new(
        original_problem(QueryPolarity::Wrap),
        AdaptiveConfig::test_default(),
    );
    let trace_session = adaptive.decision_log.begin_trace();
    let _deadline = crate::smt::ScopedSolveDeadline::new(Some(Instant::now()));
    assert!(adaptive
        .try_acyclic_bmc_probe(
            &adaptive.features(),
            Some(Instant::now() + Duration::from_secs(1))
        )
        .is_none());
    assert_eq!(trace_session.finish().observations(), []);
}
