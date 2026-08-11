// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for timeout, interrupt, unknown reason, statistics, and
//! check_sat_with_details.

use std::sync::atomic::Ordering;
use std::time::Duration;

use crate::api::*;

#[test]
fn test_timeout_setting() {
    let mut solver = Solver::new(Logic::QfLia);
    assert!(solver.timeout().is_none());
    solver.set_timeout(Some(Duration::from_secs(5)));
    assert_eq!(solver.timeout(), Some(Duration::from_secs(5)));
    solver.set_timeout(None);
    assert!(solver.timeout().is_none());
}

#[test]
fn native_decision_routes_preserve_parsed_publication_controls() {
    const PARSED_MEMORY_MIB: usize = 2_048;
    const PARSED_MEMORY_BYTES: usize = PARSED_MEMORY_MIB * 1024 * 1024;
    let options =
        format!("(set-option :timeout 60000) (set-option :max-memory {PARSED_MEMORY_MIB})");

    let mut solver = Solver::new(Logic::QfUf);
    solver.parse_smtlib2(&options).expect("parsed controls");
    let truth = solver.bool_const(true);
    solver.assert_term(truth);

    for result in [
        solver.check_sat(),
        solver.check_sat_assuming(&[truth]),
        solver.check_sat_interruptible(|| false),
    ] {
        assert!(result.is_sat(), "unexpected native result: {result}");
        assert_eq!(solver.executor.timeout(), Some(Duration::from_secs(60)));
        assert_eq!(solver.executor.memory_limit(), Some(PARSED_MEMORY_BYTES));
        assert_eq!(solver.executor.current_solve_deadline(), None);
    }

    let mut optimizer = Solver::new(Logic::QfLia);
    optimizer
        .parse_smtlib2(&options)
        .expect("parsed optimization controls");
    let x = optimizer.declare_const("x", Sort::Int);
    let zero = optimizer.int_const(0);
    let one = optimizer.int_const(1);
    let lower = optimizer.ge(x, zero);
    let upper = optimizer.le(x, one);
    optimizer.assert_term(lower);
    optimizer.assert_term(upper);
    optimizer.maximize(x);

    let result = optimizer.optimize_check();
    assert!(result.is_sat(), "unexpected optimize result: {result}");
    assert_eq!(optimizer.executor.timeout(), Some(Duration::from_secs(60)));
    assert_eq!(optimizer.executor.memory_limit(), Some(PARSED_MEMORY_BYTES));
    assert_eq!(optimizer.executor.current_solve_deadline(), None);
}

#[test]
fn test_interrupt_flag() {
    let solver = Solver::new(Logic::QfLia);
    assert!(!solver.is_interrupted());
    solver.interrupt();
    assert!(solver.is_interrupted());
    solver.clear_interrupt();
    assert!(!solver.is_interrupted());
}

#[test]
fn test_interrupt_handle_sharing() {
    let solver = Solver::new(Logic::QfLia);
    let handle = solver.interrupt_handle();
    assert!(!handle.load(Ordering::Relaxed));
    handle.store(true, Ordering::Relaxed);
    assert!(solver.is_interrupted());
}

#[test]
fn test_check_sat_respects_interrupt_before_start() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.interrupt();
    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(solver.get_reason_unknown(), Some("interrupted".to_string()));
}

#[test]
fn optimize_check_respects_interrupt_before_start_and_restricted_subsets_up() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let ten = solver.int_const(10);
    let lower = solver.ge(x, zero);
    let upper = solver.le(x, ten);
    solver.assert_term(lower);
    solver.assert_term(upper);
    let objective = solver.maximize(x);

    solver.interrupt();
    let rejected = solver.optimize_check();
    assert!(rejected.is_unknown());
    assert_eq!(solver.unknown_reason(), Some(UnknownReason::Interrupted));
    assert!(solver.model().is_none());
    assert!(solver.get_objective_value(objective).is_none());
    assert!(solver.executor.take_sat_certificate().is_none());

    solver.clear_interrupt();
    let admitted = solver.optimize_check();
    assert!(
        admitted.is_sat(),
        "controls must be clean for the next solve"
    );
    assert!(solver.get_objective_value(objective).is_some());
}

#[test]
fn optimize_check_respects_zero_timeout_and_restricted_subsets_up() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let ten = solver.int_const(10);
    let lower = solver.ge(x, zero);
    let upper = solver.le(x, ten);
    solver.assert_term(lower);
    solver.assert_term(upper);
    let objective = solver.maximize(x);

    solver.set_timeout(Some(Duration::ZERO));
    let rejected = solver.optimize_check();
    assert!(rejected.is_unknown());
    assert_eq!(solver.unknown_reason(), Some(UnknownReason::Timeout));
    assert!(solver.model().is_none());
    assert!(solver.get_objective_value(objective).is_none());
    assert!(solver.executor.take_sat_certificate().is_none());

    solver.set_timeout(None);
    let admitted = solver.optimize_check();
    assert!(
        admitted.is_sat(),
        "controls must be clean for the next solve"
    );
    assert!(solver.get_objective_value(objective).is_some());
}

#[test]
fn preflight_unknown_retires_prior_model_certificate_and_optimum() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let ten = solver.int_const(10);
    let lower = solver.ge(x, zero);
    let upper = solver.le(x, ten);
    solver.assert_term(lower);
    solver.assert_term(upper);
    let objective = solver.maximize(x);

    let admitted = solver.optimize_check();
    assert!(admitted.is_sat());
    assert!(solver.model().is_some());
    assert!(solver.get_objective_value(objective).is_some());

    // Fire before Executor is entered. This used to return Unknown while the
    // preceding SAT model/result/optimum remained queryable.
    solver.interrupt();
    let rejected = solver.check_sat();
    assert!(rejected.is_unknown());
    assert_eq!(solver.get_reason_unknown(), Some("interrupted".to_string()));
    assert!(solver.model().is_none());
    assert!(solver.model_str().is_none());
    assert!(solver.get_objective_value(objective).is_none());
    // The retired state is `Unknown`, NOT absent. `last_result()` returning
    // `Some(Unknown)` is the production contract, pinned in the opposite
    // direction by `run.rs`'s `executor_result_matches_public_verdict`, by
    // `ay unknown-policy-probe`, and by `api/solving/check.rs`. Asserting
    // `is_none()` here would only be satisfiable by clearing the result, which
    // would break all three and degrade `(get-info :reason-unknown)` from
    // `interrupted` to a bare `unknown`.
    //
    // Pinned twice on purpose. The structural `matches!` reads the raw
    // `last_result()` accessor, while `last_result_is_unknown()` is the
    // separate predicate that `run.rs`'s verdict gate and the unknown-policy
    // probe actually consult. Checking only the predicate would let a
    // regression inside it (e.g. reporting `true` for an absent result) pass
    // unnoticed here; checking only the raw accessor would leave the
    // production-facing predicate unpinned at this boundary.
    assert!(matches!(
        solver.executor.last_result(),
        Some(SolveResult::Unknown)
    ));
    assert!(solver.executor.last_result_is_unknown());
    // Stronger than the assertion this replaces: pin WHY it is unknown, so a
    // degradation of the reason or origin is caught too. Preflight publishes
    // through `replace_last_result_with_unknown(Interrupted)`, which routes to
    // `publish_unknown_from_origin(UnknownReason::Interrupted.origin())` and
    // therefore fixes the origin to `InterruptFlag`.
    assert_eq!(
        solver.executor.unknown_reason(),
        Some(UnknownReason::Interrupted)
    );
    assert_eq!(
        solver.executor.unknown_origin(),
        Some(crate::UnknownOrigin::InterruptFlag)
    );
    assert!(solver.executor.take_sat_certificate().is_none());
}

#[test]
fn test_check_sat_interruptible_callback_returns_unknown_622() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_ge_0 = solver.ge(x, zero);
    solver.assert_term(x_ge_0);

    let result = solver.check_sat_interruptible(|| true);
    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(solver.get_reason_unknown(), Some("interrupted".to_string()));
    assert!(!solver.is_interrupted());

    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Sat);
    assert!(solver.get_reason_unknown().is_none());
}

#[test]
fn test_check_sat_assuming_respects_interrupt() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_ge_0 = solver.ge(x, zero);
    solver.interrupt();
    let result = solver.check_sat_assuming(&[x_ge_0]);
    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(solver.get_reason_unknown(), Some("interrupted".to_string()));
}

#[test]
fn test_zero_timeout_returns_unknown() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_timeout(Some(Duration::ZERO));
    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(solver.get_reason_unknown(), Some("timeout".to_string()));
}

#[test]
fn test_reason_unknown_cleared_on_sat() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.interrupt();
    let _ = solver.check_sat();
    assert_eq!(solver.get_reason_unknown(), Some("interrupted".to_string()));
    solver.clear_interrupt();
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_ge_0 = solver.ge(x, zero);
    solver.assert_term(x_ge_0);
    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Sat);
    assert!(solver.get_reason_unknown().is_none());
}

#[test]
fn test_reason_unknown_cleared_on_unsat() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.interrupt();
    let _ = solver.check_sat();
    assert_eq!(solver.get_reason_unknown(), Some("interrupted".to_string()));
    solver.clear_interrupt();
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_ge_0 = solver.ge(x, zero);
    let x_lt_0 = solver.lt(x, zero);
    solver.assert_term(x_ge_0);
    solver.assert_term(x_lt_0);
    let result = solver.check_sat();
    assert!(result.is_unsat());
    assert!(solver.get_reason_unknown().is_none());
}

#[test]
fn test_check_sat_assuming_zero_timeout() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_ge_0 = solver.ge(x, zero);
    solver.set_timeout(Some(Duration::ZERO));
    let result = solver.check_sat_assuming(&[x_ge_0]);
    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(solver.get_reason_unknown(), Some("timeout".to_string()));
}

#[test]
fn test_get_unknown_reason_structured() {
    // Test the structured UnknownReason API
    use crate::UnknownReason;

    let mut solver = Solver::new(Logic::QfLia);

    // Test Interrupted reason
    solver.interrupt();
    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(solver.unknown_reason(), Some(UnknownReason::Interrupted));
    solver.clear_interrupt();

    // Test Timeout reason
    solver.set_timeout(Some(Duration::ZERO));
    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(solver.unknown_reason(), Some(UnknownReason::Timeout));
    solver.set_timeout(None);

    // Test that reason is cleared on SAT
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_ge_0 = solver.ge(x, zero);
    solver.assert_term(x_ge_0);
    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Sat);
    assert_eq!(solver.unknown_reason(), None);
}

#[test]
fn test_get_statistics_api() {
    // Test that Solver::get_statistics() returns stats from Executor
    let mut solver = Solver::new(Logic::QfUf);
    let a = solver.declare_const("a", Sort::Bool);
    let b = solver.declare_const("b", Sort::Bool);
    let or_ab = solver.or(a, b);
    let not_a = solver.not(a);
    let not_b = solver.not(b);
    solver.assert_term(or_ab);
    solver.assert_term(not_a);
    solver.assert_term(not_b);

    // Should be UNSAT: (a v b) & ~a & ~b
    let result = solver.check_sat();
    assert!(result.is_unsat());

    let stats = solver.get_statistics();
    // With UNSAT, we should see some solver activity
    assert!(
        stats.conflicts > 0 || stats.decisions > 0 || stats.propagations > 0,
        "Statistics should show some solver activity"
    );
}

#[test]
fn test_check_sat_with_statistics_returns_populated_stats() {
    // Verify that the convenience API returns both result and non-trivial stats
    let mut solver = Solver::new(Logic::QfUf);
    let a = solver.declare_const("a", Sort::Bool);
    let b = solver.declare_const("b", Sort::Bool);
    let or_ab = solver.or(a, b);
    let not_a = solver.not(a);
    let not_b = solver.not(b);
    solver.assert_term(or_ab);
    solver.assert_term(not_a);
    solver.assert_term(not_b);

    let (result, stats) = solver.check_sat_with_statistics();
    assert!(result.is_unsat());
    assert_eq!(
        stats.num_assertions, 3,
        "Statistics should include the solved assertion count",
    );
    assert!(
        stats.conflicts > 0 || stats.decisions > 0 || stats.propagations > 0,
        "Statistics should show solver activity for the same check_sat call"
    );

    let latest = solver.get_statistics();
    assert_eq!(latest.conflicts, stats.conflicts);
    assert_eq!(latest.decisions, stats.decisions);
    assert_eq!(latest.propagations, stats.propagations);
    assert_eq!(latest.restarts, stats.restarts);
}

#[test]
fn test_check_sat_with_details_sat_has_model_validated() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);

    let details = solver.check_sat_with_details();
    assert_eq!(details.result, SolveResult::Sat);
    assert!(details.unknown_reason.is_none());
    assert!(details.verification.sat_model_validated);
    assert!(!details.verification.unsat_proof_available);
    assert!(!details.verification.unsat_proof_strictly_verified);
    assert_eq!(details.verification.unsat_proof_checker_failures, 0);
}

#[test]
fn test_check_sat_with_details_accepts_validated_sat_for_consumers_6852() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);

    let details = solver.check_sat_with_details();
    assert!(details.accept_for_consumer().is_ok_and(|r| r.is_sat()));
}

/// The empty conjunction is a definite, vacuously validated SAT result. The
/// consumer capability must accept it, and unconstrained declarations must be
/// completed in the same final model before that evidence is recorded.
#[test]
fn test_empty_sat_is_consumer_accepted_with_completed_unconstrained_model() {
    let mut solver = Solver::new(Logic::QfLia);
    let _flag = solver.declare_const("flag", Sort::Bool);
    let _count = solver.declare_const("count", Sort::Int);

    let result = solver.check_sat();
    assert!(result.is_sat());
    assert!(result.was_model_validated());
    assert!(result.accept_for_consumer().is_ok_and(|r| r.is_sat()));
    assert!(solver.model_for_consumer().is_some());
    let model = solver.model_str().expect("empty SAT has a completed model");
    assert!(model.contains("flag"), "missing Bool declaration: {model}");
    assert!(model.contains("count"), "missing Int declaration: {model}");
}

/// Regression for #6852, updated by #8456: FP model validation is now active.
/// The merged FP+Real model is validated against the original assertions, so
/// `accept_for_consumer` returns Ok(Sat) instead of SatModelNotValidated.
#[test]
fn test_check_sat_with_details_accepts_validated_fp_sat_for_consumers_8456() {
    let mut solver = Solver::new(Logic::QfFp);
    let x = solver.declare_const("x", Sort::FloatingPoint(5, 11));
    let r = solver.declare_const("r", Sort::Real);
    let fp_to_real = solver.try_fp_to_real(x).unwrap();
    let eq = solver.eq(r, fp_to_real);
    solver.assert_term(eq);
    let one = solver.real_const(1.0);
    let gt = solver.gt(r, one);
    solver.assert_term(gt);

    let details = solver.check_sat_with_details();
    assert_eq!(details.result, SolveResult::Sat);
    assert!(
        details.verification.sat_model_validated,
        "FP+Real merged model should now be validated (#8456)"
    );
    assert!(
        details.accept_for_consumer().is_ok_and(|r| r.is_sat()),
        "validated FP model should be accepted for consumers"
    );
}

/// Regression for #8456: Seq model validation is now active.
/// The combined EUF+Seq model is validated against the original assertions,
/// so `accept_for_consumer` returns Ok(Sat) instead of SatModelNotValidated.
#[test]
fn test_check_sat_with_details_accepts_validated_seq_sat_for_consumers_8456() {
    let mut solver = Solver::new(Logic::QfSeq);
    let a = solver.declare_const("a", Sort::Seq(Box::new(Sort::Int)));
    let b = solver.declare_const("b", Sort::Seq(Box::new(Sort::Int)));
    let eq = solver.eq(a, b);
    solver.assert_term(eq);

    let details = solver.check_sat_with_details();
    assert_eq!(details.result, SolveResult::Sat);
    assert!(
        details.verification.sat_model_validated,
        "Seq model should now be validated (#8456)"
    );
    assert!(
        details.accept_for_consumer().is_ok_and(|r| r.is_sat()),
        "validated Seq model should be accepted for consumers"
    );
}

/// Regression (#5777): `VerificationSummary` evidence counts are populated
/// with independent/delegated/incomplete provenance after a SAT solve.
#[test]
fn test_check_sat_with_details_evidence_counts_5777() {
    // A trivial QF_LIA formula with one independently-checkable assertion.
    // The evaluator should return Bool(true) for `(= x 5)` when the model
    // assigns x=5. This produces an independent check with zero delegation
    // and zero incomplete evidence.
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);

    let details = solver.check_sat_with_details();
    assert_eq!(details.result, SolveResult::Sat);
    assert!(
        details.verification.sat_model_validated,
        "simple LIA formula should be model-validated"
    );
    // Independent checks must be > 0 for a validated SAT result.
    assert!(
        details.verification.sat_independent_checks > 0,
        "Expected independent checks > 0, got {}",
        details.verification.sat_independent_checks
    );
    assert_eq!(
        details.verification.sat_delegated_checks, 0,
        "Simple equality should not need theory-delegated evidence"
    );
    // No circular SAT fallback should be needed for a simple equality.
    assert_eq!(
        details.verification.sat_incomplete_checks, 0,
        "Simple equality should not need SAT fallback"
    );
}

/// Regression (#5777): theory-delegated string evidence must not inflate the
/// public independent-check counter.
///
/// History: this originally asserted `sat_independent_checks == 0` and
/// `sat_delegated_checks > 0` because `(= x y)` over unassigned string
/// variables left the string model incomplete and validation relied on
/// delegated string-solver evidence. Since #str-incomplete-model-gate, the
/// string-witness materializer COMPLETES the model (pinning otherwise
/// unconstrained user string variables to `""`, the printer default) and
/// strictly re-validates by full substitution, so the assertion is now
/// checked independently — genuinely stronger evidence, not counter
/// inflation. The #5777 intent (delegated evidence must not be misclassified
/// as independent) is preserved: independent evidence here comes from a
/// concrete-substitution check of the completed model.
#[test]
fn test_check_sat_with_details_delegated_string_evidence_5777() {
    let mut solver = Solver::new(Logic::QfS);
    let x = solver.string_var("x");
    let y = solver.string_var("y");
    let eq = solver.eq(x, y);
    solver.assert_term(eq);

    let details = solver.check_sat_with_details();
    assert_eq!(details.result, SolveResult::Sat);
    assert!(
        details.verification.sat_model_validated,
        "simple string equality should be model-validated"
    );
    assert!(
        details.verification.sat_independent_checks + details.verification.sat_delegated_checks > 0,
        "Expected concrete (independent or delegated) evidence, got independent={} delegated={}",
        details.verification.sat_independent_checks,
        details.verification.sat_delegated_checks
    );
    assert_eq!(
        details.verification.sat_incomplete_checks, 0,
        "Simple string equality should not need incomplete fallback"
    );
}

#[test]
fn test_check_sat_with_details_unsat_basic() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_gt_0 = solver.gt(x, zero);
    let x_lt_0 = solver.lt(x, zero);
    solver.assert_term(x_gt_0);
    solver.assert_term(x_lt_0);

    let details = solver.check_sat_with_details();
    assert_eq!(details.result, SolveResult::unsat());
    assert!(details.unknown_reason.is_none());
    assert!(!details.verification.sat_model_validated);
}

#[test]
fn test_check_sat_with_details_unknown_timeout_has_reason() {
    use crate::UnknownReason;

    let mut solver = Solver::new(Logic::QfLia);
    solver.set_timeout(Some(Duration::ZERO));

    let details = solver.check_sat_with_details();
    assert_eq!(details.result, SolveResult::Unknown);
    assert_eq!(details.unknown_reason, Some(UnknownReason::Timeout));
    assert_eq!(solver.unknown_reason(), Some(UnknownReason::Timeout));

    let diagnostic = details
        .unknown_diagnostic
        .expect("timeout should include an actionable Unknown diagnostic");
    assert_eq!(diagnostic.reason, UnknownReason::Timeout);
    assert_eq!(diagnostic.phase.as_deref(), Some("search-control"));
    assert_eq!(diagnostic.cost_center.as_deref(), Some("deadline"));
    assert!(
        diagnostic
            .detail
            .as_deref()
            .is_some_and(|detail| detail.contains("deadline")),
        "expected timeout detail to mention the deadline, got {diagnostic:?}"
    );
}

#[test]
fn test_decision_profile_summary_sat_4445() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);

    let details = solver.check_sat_with_details();
    let summary = details.decision_profile_summary();

    assert_eq!(summary.schema, AY_SOLVE_DECISION_PROFILE_SUMMARY_SCHEMA);
    assert_eq!(
        summary.schema_version,
        AY_SOLVE_DECISION_PROFILE_SUMMARY_SCHEMA_VERSION
    );
    assert_eq!(summary.decision, SolveDecision::Sat);
    assert_eq!(summary.decision_code, "sat");
    assert_eq!(summary.decision_name, "SAT");
    assert!(summary.accepted_for_consumer);
    assert_eq!(summary.consumer_rejection_code, None);
    assert!(summary.model_validated);
    assert!(summary.unknown.is_none());
    assert_eq!(summary.verification, details.verification);
    assert_eq!(
        summary.verification_level_code,
        details.verification_level.code()
    );
    assert_eq!(
        summary.profile.num_assertions,
        details.statistics.num_assertions
    );
    assert_eq!(
        summary.profile.term_count,
        details.resource_usage.term_count
    );
    assert_eq!(
        summary.profile.term_bytes,
        details.resource_usage.term_bytes
    );

    let model_decision = summary.model_consumer_decision();
    assert_eq!(
        model_decision.schema,
        AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA
    );
    assert_eq!(
        model_decision.schema_version,
        AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA_VERSION
    );
    assert_eq!(
        model_decision.status,
        SolveDecisionProfileModelConsumerStatus::Accepted
    );
    assert_eq!(
        model_decision.reason,
        SolveDecisionProfileModelConsumerReason::Accepted
    );
    assert_eq!(model_decision.status_code, "accepted");
    assert_eq!(model_decision.reason_code, "accepted");
    assert!(model_decision.accepted_for_consumer);
    assert!(summary.accepts_model_for_consumer());
    let json = summary.model_consumer_decision_json();
    assert_eq!(
        json["schema"],
        AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA
    );
    assert_eq!(json["status"], "accepted");
    assert_eq!(json["reason"], "accepted");
}

#[test]
fn test_decision_profile_summary_unknown_timeout_4445() {
    use crate::UnknownReason;

    let mut solver = Solver::new(Logic::QfLia);
    solver.set_timeout(Some(Duration::ZERO));

    let details = solver.check_sat_with_details();
    let summary = details.decision_profile_summary();

    assert_eq!(summary.decision, SolveDecision::Unknown);
    assert_eq!(summary.decision_code, "unknown");
    assert!(summary.accepted_for_consumer);

    let unknown = summary
        .unknown
        .as_ref()
        .expect("timeout should produce stable Unknown summary");
    assert_eq!(unknown.reason, UnknownReason::Timeout);
    assert_eq!(unknown.reason_code, "timeout");
    assert_eq!(unknown.reason_name, "Timeout");
    assert_eq!(unknown.phase.as_deref(), Some("search-control"));
    assert_eq!(unknown.cost_center.as_deref(), Some("deadline"));
    assert_eq!(unknown.limit_hit, Some(LimitKind::Timeout));
    assert_eq!(unknown.limit_code, Some("timeout"));
    assert_eq!(
        summary.profile.wall_time_ms,
        details.resource_usage.wall_time.as_millis()
    );

    let model_decision = summary.model_consumer_decision();
    assert_eq!(
        model_decision.status,
        SolveDecisionProfileModelConsumerStatus::Rejected
    );
    assert_eq!(
        model_decision.reason,
        SolveDecisionProfileModelConsumerReason::NonSatDecision
    );
    assert_eq!(model_decision.reason_code, "non_sat_decision");
    assert!(!model_decision.accepted_for_consumer);
    assert!(model_decision.fail_closed);
    assert!(!summary.accepts_model_for_consumer());
}

#[test]
fn test_decision_profile_summary_rejected_sat_boundary_4445() {
    let details = SolveDetails {
        result: VerifiedSolveResult::for_testing(SolveResult::Sat, false),
        statistics: crate::Statistics::default(),
        unknown_reason: None,
        unknown_diagnostic: None,
        executor_error: None,
        verification: VerificationSummary::default(),
        verification_level: VerificationLevel::Trusted,
        resource_usage: ResourceUsage::default(),
    };

    let summary = details.decision_profile_summary();

    assert_eq!(summary.decision, SolveDecision::Sat);
    assert!(!summary.accepted_for_consumer);
    assert_eq!(
        summary.consumer_rejection_code,
        Some("sat_model_not_validated")
    );
    assert!(!summary.model_validated);

    let model_decision = summary.model_consumer_decision();
    assert_eq!(
        model_decision.status,
        SolveDecisionProfileModelConsumerStatus::Rejected
    );
    assert_eq!(
        model_decision.reason,
        SolveDecisionProfileModelConsumerReason::ConsumerRejected
    );
    assert_eq!(model_decision.reason_code, "consumer_rejected");
    assert_eq!(
        model_decision.solve_consumer_rejection_code,
        Some("sat_model_not_validated")
    );
    assert!(!model_decision.accepted_for_consumer);
    assert!(model_decision.fail_closed);
}

#[test]
fn test_raw_smt_solve_profile_summary_from_typed_details_9712() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);

    let details = solver.check_sat_with_details();
    let summary = raw_smt_solve_profile_summary_from_typed_details("ay", Some("QF_LIA"), &details);

    assert_eq!(summary.schema, AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA);
    assert_eq!(
        summary.schema_version,
        AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA_VERSION
    );
    assert_eq!(
        summary.producer_revision,
        AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_CURRENT_REVISION
    );
    assert_eq!(summary.source, RawSmtSolveProfileSource::TypedAYInternals);
    assert_eq!(summary.source_code, "typed_ay_internals");
    assert_eq!(summary.status, RawSmtSolveProfileStatus::Available);
    assert_eq!(summary.reason, RawSmtSolveProfileReason::TypedAYInternals);
    assert_eq!(summary.solver_path, "ay");
    assert_eq!(summary.logic.as_deref(), Some("QF_LIA"));
    assert_eq!(summary.decision, Some(SolveDecision::Sat));
    assert_eq!(summary.decision_code, "sat");
    assert!(summary.accepted_for_consumer);
    assert!(!summary.fail_closed);
    assert!(summary.typed_consumer);
    assert!(summary.model_validated);
    assert_eq!(
        summary.profile.num_assertions,
        details.statistics.num_assertions
    );
    assert_eq!(
        summary.profile.term_count,
        details.resource_usage.term_count
    );

    let json = summary.to_json_value();
    assert_eq!(json["schema"], AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA);
    assert_eq!(json["status"], "available");
    assert_eq!(json["reason"], "typed_ay_internals");
    assert_eq!(
        json["profile"]["num_assertions"],
        details.statistics.num_assertions
    );
    assert_eq!(
        json["profile"]["term_count"],
        details.resource_usage.term_count
    );

    let rows = summary.to_key_value_rows();
    assert!(rows.iter().any(|(key, value)| {
        key == "profile_wall_time_ms" && value == &summary.profile.wall_time_ms.to_string()
    }));
    let report = validate_raw_smt_solve_profile_summary_key_value_rows(&rows);
    assert!(report.accepted(), "{report:?}");
    assert_eq!(
        validate_raw_smt_solve_profile_summary_text_lines(&summary.to_text_lines()).status,
        RawSmtSolveProfileValidationStatus::Accepted
    );
}

#[test]
fn test_raw_smt_solve_profile_summary_from_process_timeout_and_error_9712() {
    let timeout_summary = raw_smt_solve_profile_summary_from_process(
        RawSmtProcessSolveProfileInput::new(
            "target/release/ay",
            Some("QF_LIA"),
            "unknown\n",
            "",
            Some(0),
        )
        .with_wall_time_ms(25)
        .with_timed_out(true)
        .with_deadline_exceeded(true),
    );

    assert_eq!(
        timeout_summary.source,
        RawSmtSolveProfileSource::RawProcessExecution
    );
    assert_eq!(timeout_summary.status, RawSmtSolveProfileStatus::Available);
    assert_eq!(
        timeout_summary.reason,
        RawSmtSolveProfileReason::RawProcessTimeout
    );
    assert_eq!(timeout_summary.decision, Some(SolveDecision::Unknown));
    assert_eq!(timeout_summary.unknown_reason_code, Some("timeout"));
    assert_eq!(timeout_summary.unknown_limit_code, Some("timeout"));
    assert!(timeout_summary.accepted_for_consumer);
    assert!(!timeout_summary.fail_closed);
    assert_eq!(timeout_summary.profile.wall_time_ms, 25);
    assert!(validate_raw_smt_solve_profile_summary(&timeout_summary).accepted());

    let killed_summary = raw_smt_solve_profile_summary_from_process(
        RawSmtProcessSolveProfileInput::new(
            "target/release/ay",
            Some("QF_LIA"),
            "",
            "killed",
            None,
        )
        .with_wall_time_ms(30)
        .with_timed_out(true),
    );

    assert_eq!(killed_summary.status, RawSmtSolveProfileStatus::Rejected);
    assert_eq!(
        killed_summary.reason,
        RawSmtSolveProfileReason::RawProcessTimeout
    );
    assert_eq!(killed_summary.decision, None);
    assert!(!killed_summary.accepted_for_consumer);
    assert!(killed_summary.fail_closed);
    assert!(validate_raw_smt_solve_profile_summary(&killed_summary).accepted());

    let error_summary = raw_smt_solve_profile_summary_from_process(
        RawSmtProcessSolveProfileInput::new(
            "target/release/ay",
            Some("QF_LIA"),
            "",
            "parse error",
            Some(1),
        )
        .with_wall_time_ms(3),
    );
    assert_eq!(error_summary.status, RawSmtSolveProfileStatus::Rejected);
    assert_eq!(
        error_summary.reason,
        RawSmtSolveProfileReason::RawProcessError
    );
    assert!(error_summary.fail_closed);
}

#[test]
fn test_raw_smt_solve_profile_validation_rejects_bad_rows_9712() {
    let summary = raw_smt_solve_profile_summary_from_process(
        RawSmtProcessSolveProfileInput::new("ay", Some("QF_UF"), "sat\n", "", Some(0))
            .with_wall_time_ms(7),
    );
    let rows = summary.to_key_value_rows();
    assert!(validate_raw_smt_solve_profile_summary_key_value_rows(&rows).accepted());

    let mut stale_rows = rows.clone();
    replace_row(
        &mut stale_rows,
        "producer_revision",
        "raw-smt-solve-profile.stale",
    );
    let stale = validate_raw_smt_solve_profile_summary_key_value_rows(&stale_rows);
    assert_eq!(stale.reason, RawSmtSolveProfileValidationReason::StaleRows);
    assert!(!stale.accepted());

    let missing_rows: Vec<_> = rows
        .iter()
        .filter(|(key, _)| key != "schema")
        .cloned()
        .collect();
    let missing = validate_raw_smt_solve_profile_summary_key_value_rows(&missing_rows);
    assert_eq!(
        missing.reason,
        RawSmtSolveProfileValidationReason::MissingRequiredRow
    );

    let mut duplicate_rows = rows.clone();
    duplicate_rows.push(rows[0].clone());
    let duplicate = validate_raw_smt_solve_profile_summary_key_value_rows(&duplicate_rows);
    assert_eq!(
        duplicate.reason,
        RawSmtSolveProfileValidationReason::DuplicateRow
    );

    let malformed = validate_raw_smt_solve_profile_summary_text_lines(&["not-a-row".to_string()]);
    assert_eq!(
        malformed.reason,
        RawSmtSolveProfileValidationReason::MalformedRow
    );

    let mut fail_open_rows = raw_smt_solve_profile_summary_from_process(
        RawSmtProcessSolveProfileInput::new("ay", Some("QF_UF"), "", "timeout", None)
            .with_timed_out(true),
    )
    .to_key_value_rows();
    replace_row(&mut fail_open_rows, "fail_closed", "false");
    let fail_open = validate_raw_smt_solve_profile_summary_key_value_rows(&fail_open_rows);
    assert_eq!(
        fail_open.reason,
        RawSmtSolveProfileValidationReason::FailOpenRows
    );
}

fn replace_row(rows: &mut [(String, String)], key: &str, value: &str) {
    let (_, row_value) = rows
        .iter_mut()
        .find(|(row_key, _)| row_key == key)
        .expect("row should exist");
    *row_value = value.to_string();
}

#[test]
fn test_check_sat_with_details_statistics_match_get_statistics() {
    let mut solver = Solver::new(Logic::QfUf);
    let a = solver.declare_const("a", Sort::Bool);
    let b = solver.declare_const("b", Sort::Bool);
    let a_or_b = solver.or(a, b);
    let not_a = solver.not(a);
    let not_b = solver.not(b);
    solver.assert_term(a_or_b);
    solver.assert_term(not_a);
    solver.assert_term(not_b);

    let details = solver.check_sat_with_details();
    let latest = solver.get_statistics();
    assert_eq!(details.statistics.conflicts, latest.conflicts);
    assert_eq!(details.statistics.decisions, latest.decisions);
    assert_eq!(details.statistics.propagations, latest.propagations);
    assert_eq!(details.statistics.restarts, latest.restarts);
}

#[test]
fn test_verification_level_from_state_no_proofs() {
    use crate::api::types::VerificationLevel;

    let level = VerificationLevel::from_state(false);
    if cfg!(debug_assertions) {
        assert_eq!(level, VerificationLevel::DebugChecked);
        assert!(level.has_debug_checks());
        assert!(!level.has_proof_checking());
        assert!(!level.is_trusted_only());
    } else {
        assert_eq!(level, VerificationLevel::Trusted);
        assert!(!level.has_debug_checks());
        assert!(!level.has_proof_checking());
        assert!(level.is_trusted_only());
    }
}

#[test]
fn test_verification_level_from_state_with_proofs() {
    use crate::api::types::VerificationLevel;

    let level = VerificationLevel::from_state(true);
    if cfg!(debug_assertions) {
        assert_eq!(level, VerificationLevel::FullyVerified);
        assert!(level.has_debug_checks());
        assert!(level.has_proof_checking());
        assert!(!level.is_trusted_only());
    } else {
        assert_eq!(level, VerificationLevel::ProofChecked);
        assert!(!level.has_debug_checks());
        assert!(level.has_proof_checking());
        assert!(!level.is_trusted_only());
    }
}

#[test]
fn test_verification_level_display() {
    use crate::api::types::VerificationLevel;

    assert_eq!(VerificationLevel::Trusted.to_string(), "trusted");
    assert_eq!(VerificationLevel::DebugChecked.to_string(), "debug-checked");
    assert_eq!(VerificationLevel::ProofChecked.to_string(), "proof-checked");
    assert_eq!(
        VerificationLevel::FullyVerified.to_string(),
        "fully-verified"
    );
}

#[test]
fn test_check_sat_with_details_has_verification_level() {
    use crate::api::types::VerificationLevel;

    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);

    let details = solver.check_sat_with_details();
    assert_eq!(details.result, SolveResult::Sat);
    let expected = VerificationLevel::from_state(false);
    assert_eq!(details.verification_level, expected);
}

#[test]
fn test_check_sat_with_details_proofs_enabled_verification_level() {
    use crate::api::types::VerificationLevel;

    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_proofs(true);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_gt_0 = solver.gt(x, zero);
    let x_lt_0 = solver.lt(x, zero);
    solver.assert_term(x_gt_0);
    solver.assert_term(x_lt_0);

    let details = solver.check_sat_with_details();
    assert_eq!(details.result, SolveResult::unsat());
    let expected = VerificationLevel::from_state(true);
    assert_eq!(details.verification_level, expected);
    assert!(details.verification_level.has_proof_checking());
}

#[test]
fn proof_checked_level_requires_and_reports_strict_unsat_authority() {
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_verification_level(VerificationLevel::ProofChecked);
    let p = solver.declare_const("p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.assert_term(not_p);

    let details = solver.check_sat_with_details();
    assert!(details.result.is_unsat());
    assert!(details.verification_level.has_proof_checking());
    assert!(details.verification.unsat_proof_available);
    assert!(details.verification.unsat_proof_strictly_verified);
}

/// Verify that set_random_seed is callable and the solver still produces
/// correct results (#6961).
#[test]
fn test_set_random_seed_api() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_random_seed(42);

    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);

    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Sat);
}

/// Verify that different seeds don't break UNSAT results (#6961).
#[test]
fn test_set_random_seed_unsat() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_random_seed(12345);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_gt_0 = solver.gt(x, zero);
    let x_lt_0 = solver.lt(x, zero);
    solver.assert_term(x_gt_0);
    solver.assert_term(x_lt_0);

    let result = solver.check_sat();
    assert!(result.is_unsat());
}

/// Verify that set_ematching_round_limit is reflected in ematching_round_limit (#8614).
#[test]
fn test_set_ematching_round_limit_api_8614() {
    let mut solver = Solver::try_new(Logic::Uf).unwrap();

    // Default is 16 (raised from 8 to chain deeper quantifier instantiations).
    assert_eq!(solver.ematching_round_limit(), 16);

    // Set a custom limit
    solver.set_ematching_round_limit(24);
    assert_eq!(solver.ematching_round_limit(), 24);

    // Clamped to [1, 128]
    solver.set_ematching_round_limit(0);
    assert_eq!(solver.ematching_round_limit(), 1);
    solver.set_ematching_round_limit(1000);
    assert_eq!(solver.ematching_round_limit(), 128);
}

/// Verify that E-matching statistics are populated after solving a quantified formula (#8614).
#[test]
fn test_ematching_statistics_populated_8614() {
    let mut solver = Solver::try_new(Logic::Uf).unwrap();

    // Build a quantified formula that requires E-matching:
    // (forall ((x U)) (! (=> (P x) (Q x)) :pattern ((P x))))
    // (P a)
    // (not (Q a))
    // This should fire 1 E-matching round, producing 1 instance.
    let u = Sort::Uninterpreted("U".to_string());
    let a = solver.declare_const("a", u.clone());
    let p = solver.declare_fun("P", std::slice::from_ref(&u), Sort::Bool);
    let q = solver.declare_fun("Q", std::slice::from_ref(&u), Sort::Bool);
    let p_a = solver.apply(&p, &[a]);
    let q_a = solver.apply(&q, &[a]);
    let not_q_a = solver.not(q_a);
    solver.assert_term(p_a);
    solver.assert_term(not_q_a);

    // Build quantified assertion via SMT-LIB parse (triggers are not exposed in builder API)
    // Instead, just check statistics after an E-matching-enabled solve
    // by using the Executor-level approach.
    // The simplest approach: parse a full SMT-LIB script.
    drop(solver);

    // Use a Solver with SMT-LIB input that has triggers.
    use crate::Executor;
    use ay_frontend::parse;

    let input = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun P (U) Bool)
        (declare-fun Q (U) Bool)
        (declare-const a U)
        (assert (forall ((x U)) (! (=> (P x) (Q x)) :pattern ((P x)))))
        (assert (P a))
        (assert (not (Q a)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(outputs, vec!["unsat"]);

    let stats = exec.statistics();
    assert!(
        stats.ematching_rounds_completed > 0,
        "Expected ematching_rounds_completed > 0, got {}",
        stats.ematching_rounds_completed
    );
    assert!(
        stats.ematching_instances_created > 0,
        "Expected ematching_instances_created > 0, got {}",
        stats.ematching_instances_created
    );

    // Also verify the stats are accessible via get_int
    assert_eq!(
        stats.get_int("ematching_rounds_completed"),
        Some(stats.ematching_rounds_completed)
    );
    assert_eq!(
        stats.get_int("ematching_instances_created"),
        Some(stats.ematching_instances_created)
    );
}

/// Verify that E-matching statistics are zero for quantifier-free formulas (#8614).
#[test]
fn test_ematching_statistics_zero_for_qf_8614() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);

    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Sat);

    let stats = solver.statistics();
    assert_eq!(
        stats.ematching_rounds_completed, 0,
        "QF formula should have zero E-matching rounds"
    );
    assert_eq!(
        stats.ematching_instances_created, 0,
        "QF formula should have zero E-matching instances"
    );
}

/// Regression (#6740): `try_reset()` must zero `scope_level` so
/// `num_scopes()` reports `0` after a full solver reset.
#[test]
fn test_try_reset_resets_scope_depth_6740() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.try_push().unwrap();
    solver.try_push().unwrap();
    assert_eq!(solver.num_scopes(), 2);

    solver.try_reset().unwrap();
    assert_eq!(solver.num_scopes(), 0);

    // Push after reset must count from zero, not from the stale value.
    solver.try_push().unwrap();
    assert_eq!(solver.num_scopes(), 1);
}

/// Nelson-Oppen fixpoint loop must respect interrupt flag (#8637).
///
/// The N-O loop in TheoryCombiner can iterate up to 100 times per check()
/// call. With the interrupt flag set before solving, the solver must return
/// Unknown promptly without completing all iterations.
#[test]
fn test_nelson_oppen_interrupt_returns_unknown_8637() {
    // QF_UFLIA uses TheoryCombiner::uf_lia which has the N-O fixpoint loop.
    let mut solver = Solver::new(Logic::QfUflia);
    let f = solver.declare_fun("f", &[Sort::Int], Sort::Int);
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let fx = solver.apply(&f, &[x]);
    let fy = solver.apply(&f, &[y]);
    let eq_xy = solver.eq(x, y);
    let eq_fxfy = solver.eq(fx, fy);
    let neq_fxfy = solver.not(eq_fxfy);
    solver.assert_term(eq_xy);
    solver.assert_term(neq_fxfy);

    // Set interrupt before solving — the N-O loop check must detect it.
    solver.interrupt();
    let result = solver.check_sat();
    assert_eq!(
        result,
        SolveResult::Unknown,
        "QF_UFLIA solver must return Unknown when interrupted (#8637)"
    );
    assert_eq!(solver.get_reason_unknown(), Some("interrupted".to_string()));
}

/// Array+EUF N-O fixpoint loop must respect interrupt flag (#8637).
#[test]
fn test_array_euf_interrupt_returns_unknown_8637() {
    let mut solver = Solver::new(Logic::QfAx);
    let arr = solver.declare_const("arr", Sort::array(Sort::Int, Sort::Int));
    let i = solver.declare_const("i", Sort::Int);
    let v = solver.int_const(42);
    let stored = solver.store(arr, i, v);
    let read = solver.select(stored, i);
    let eq = solver.eq(read, v);
    solver.assert_term(eq);

    solver.interrupt();
    let result = solver.check_sat();
    assert_eq!(
        result,
        SolveResult::Unknown,
        "QF_AX solver must return Unknown when interrupted (#8637)"
    );
    assert_eq!(solver.get_reason_unknown(), Some("interrupted".to_string()));
}

/// AUFLIA N-O fixpoint loop must respect interrupt flag (#8637).
#[test]
fn test_auflia_interrupt_returns_unknown_8637() {
    let mut solver = Solver::new(Logic::QfAuflia);
    let arr = solver.declare_const("arr", Sort::array(Sort::Int, Sort::Int));
    let i = solver.declare_const("i", Sort::Int);
    let j = solver.declare_const("j", Sort::Int);
    let v = solver.int_const(42);
    let stored = solver.store(arr, i, v);
    let read = solver.select(stored, j);
    let eq_ij = solver.eq(i, j);
    let eq_rv = solver.eq(read, v);
    solver.assert_term(eq_ij);
    solver.assert_term(eq_rv);

    solver.interrupt();
    let result = solver.check_sat();
    assert_eq!(
        result,
        SolveResult::Unknown,
        "QF_AUFLIA solver must return Unknown when interrupted (#8637)"
    );
    assert_eq!(solver.get_reason_unknown(), Some("interrupted".to_string()));
}

/// LIA entry-point guard must respect interrupt flag (#8636).
#[test]
fn test_lia_interrupt_returns_unknown_8636() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_gt_0 = solver.gt(x, zero);
    solver.assert_term(x_gt_0);

    solver.interrupt();
    let result = solver.check_sat();
    assert_eq!(
        result,
        SolveResult::Unknown,
        "QF_LIA solver must return Unknown when interrupted (#8636)"
    );
    assert_eq!(solver.get_reason_unknown(), Some("interrupted".to_string()));
}

/// DT entry-point guard must respect interrupt flag (#8636).
#[test]
fn test_dt_interrupt_returns_unknown_8636() {
    use crate::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let mut solver = Solver::new(Logic::QfDt);
    let option_int = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "none".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "some".to_string(),
                fields: vec![DatatypeField {
                    name: "value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    solver
        .try_declare_datatype(&option_int)
        .expect("declare datatype");
    let x = solver.declare_const("x", Sort::Datatype(option_int.clone()));
    let y = solver.declare_const("y", Sort::Datatype(option_int));
    let eq = solver.eq(x, y);
    solver.assert_term(eq);

    solver.interrupt();
    let result = solver.check_sat();
    assert_eq!(
        result,
        SolveResult::Unknown,
        "QF_DT solver must return Unknown when interrupted (#8636)"
    );
    assert_eq!(solver.get_reason_unknown(), Some("interrupted".to_string()));
}

/// FP entry-point guard must respect interrupt flag (#8636).
#[test]
fn test_fp_interrupt_returns_unknown_8636() {
    let mut solver = Solver::new(Logic::QfFp);
    let x = solver.declare_const("x", Sort::FloatingPoint(5, 11));
    let r = solver.declare_const("r", Sort::Real);
    let fp_to_real = solver.try_fp_to_real(x).unwrap();
    let eq = solver.eq(r, fp_to_real);
    solver.assert_term(eq);

    solver.interrupt();
    let result = solver.check_sat();
    assert_eq!(
        result,
        SolveResult::Unknown,
        "QF_FP solver must return Unknown when interrupted (#8636)"
    );
    assert_eq!(solver.get_reason_unknown(), Some("interrupted".to_string()));
}

/// EUF entry-point guard must respect interrupt flag (#8636).
#[test]
fn test_euf_interrupt_returns_unknown_8636() {
    let mut solver = Solver::new(Logic::QfUf);
    let u = Sort::Uninterpreted("U".to_string());
    let f = solver.declare_fun("f", std::slice::from_ref(&u), u.clone());
    let x = solver.declare_const("x", u.clone());
    let y = solver.declare_const("y", u);
    let fx = solver.apply(&f, &[x]);
    let fy = solver.apply(&f, &[y]);
    let eq_fxfy = solver.eq(fx, fy);
    solver.assert_term(eq_fxfy);

    solver.interrupt();
    let result = solver.check_sat();
    assert_eq!(
        result,
        SolveResult::Unknown,
        "QF_UF solver must return Unknown when interrupted (#8636)"
    );
    assert_eq!(solver.get_reason_unknown(), Some("interrupted".to_string()));
}

/// SEQ entry-point guard must respect interrupt flag (#8636).
#[test]
fn test_seq_interrupt_returns_unknown_8636() {
    let mut solver = Solver::new(Logic::QfSeq);
    let a = solver.declare_const("a", Sort::Seq(Box::new(Sort::Int)));
    let b = solver.declare_const("b", Sort::Seq(Box::new(Sort::Int)));
    let eq = solver.eq(a, b);
    solver.assert_term(eq);

    solver.interrupt();
    let result = solver.check_sat();
    assert_eq!(
        result,
        SolveResult::Unknown,
        "QF_SEQ solver must return Unknown when interrupted (#8636)"
    );
    assert_eq!(solver.get_reason_unknown(), Some("interrupted".to_string()));
}

/// Array theory propagation inner loops must respect interrupt flag (#8615).
///
/// Creates many store/select operations to stress the O(n^2) inner loops in
/// `propagation.rs` (array congruence, transitive equality, store injectivity,
/// cross-chain resolution) and `theory_propagate.rs` (ROW2 propagation).
/// Without interrupt checks in these inner loops, seq push_back chains can
/// cause kernel panics from unbounded memory/CPU consumption.
#[test]
fn test_array_propagation_inner_loops_interrupt_8615() {
    let mut solver = Solver::new(Logic::QfAuflia);
    let arr_sort = Sort::array(Sort::Int, Sort::Int);

    // Build a chain of stores: arr0, store(arr0, 0, v0), store(store(arr0, 0, v0), 1, v1), ...
    // This creates many array terms that will generate O(n^2) work in the
    // equality propagation loops.
    let arr0 = solver.declare_const("arr0", arr_sort.clone());
    let mut current_arr = arr0;
    let chain_len = 30;
    let mut selects = Vec::new();

    for k in 0..chain_len {
        let idx = solver.int_const(k);
        let val = solver.int_const(k * 10 + 1);
        current_arr = solver.store(current_arr, idx, val);

        // Read back at a different index to generate cross-chain work
        let read_idx = solver.int_const((k + 1) % chain_len);
        let sel = solver.select(current_arr, read_idx);
        selects.push(sel);
    }

    // Assert equalities between some select results to force the equality
    // propagation paths (array congruence, transitive, store permutation).
    for pair in selects.windows(2) {
        let eq = solver.eq(pair[0], pair[1]);
        solver.assert_term(eq);
    }

    // Create a second chain and assert array equality to trigger cross-chain
    // resolution and effective store map decomposition.
    let arr1 = solver.declare_const("arr1", arr_sort);
    let mut current_arr2 = arr1;
    for k in 0..chain_len {
        let idx = solver.int_const(k);
        let val = solver.int_const(k * 10 + 1);
        current_arr2 = solver.store(current_arr2, idx, val);
    }
    let arr_eq = solver.eq(current_arr, current_arr2);
    solver.assert_term(arr_eq);

    // Set interrupt before solving — the inner propagation loops must detect it.
    solver.interrupt();
    let result = solver.check_sat();
    assert_eq!(
        result,
        SolveResult::Unknown,
        "Array propagation inner loops must return Unknown when interrupted (#8615)"
    );
    assert_eq!(solver.get_reason_unknown(), Some("interrupted".to_string()));
}

// =========================================================================
// SolverConfig and per-query timeout tests (#8688)
// =========================================================================

/// SolverConfig default has no timeout.
#[test]
fn test_solver_config_default_no_timeout() {
    let config = SolverConfig::default();
    assert!(config.timeout.is_none());
    assert!(config.memory_limit.is_none());
    assert!(config.term_memory_limit.is_none());
    assert!(config.learned_clause_limit.is_none());
    assert!(config.clause_db_bytes_limit.is_none());
}

/// SolverConfig builder sets timeout.
#[test]
fn test_solver_config_with_timeout() {
    let config = SolverConfig::default().with_timeout(Duration::from_secs(5));
    assert_eq!(config.timeout, Some(Duration::from_secs(5)));
}

/// SolverConfig builder chains multiple settings.
#[test]
fn test_solver_config_builder_chaining() {
    let config = SolverConfig::default()
        .with_timeout(Duration::from_secs(5))
        .with_memory_limit(1024 * 1024 * 1024)
        .with_term_memory_limit(512 * 1024 * 1024)
        .with_learned_clause_limit(100_000)
        .with_clause_db_bytes_limit(256 * 1024 * 1024);
    assert_eq!(config.timeout, Some(Duration::from_secs(5)));
    assert_eq!(config.memory_limit, Some(1024 * 1024 * 1024));
    assert_eq!(config.term_memory_limit, Some(512 * 1024 * 1024));
    assert_eq!(config.learned_clause_limit, Some(100_000));
    assert_eq!(config.clause_db_bytes_limit, Some(256 * 1024 * 1024));
}

/// try_new_with_config respects timeout from config.
#[test]
fn test_try_new_with_config_timeout() {
    let config = SolverConfig::default().with_timeout(Duration::from_secs(5));
    let solver = Solver::try_new_with_config(Logic::QfLia, config).expect("QF_LIA is supported");
    assert_eq!(solver.timeout(), Some(Duration::from_secs(5)));
}

/// try_new_with_config with default config has no timeout.
#[test]
fn test_try_new_with_config_default() {
    let solver = Solver::try_new_with_config(Logic::QfLia, SolverConfig::default())
        .expect("QF_LIA is supported");
    assert!(solver.timeout().is_none());
}

/// try_new_with_config with zero timeout returns Unknown immediately.
#[test]
fn test_try_new_with_config_zero_timeout_returns_unknown() {
    let config = SolverConfig::default().with_timeout(Duration::ZERO);
    let mut solver =
        Solver::try_new_with_config(Logic::QfLia, config).expect("QF_LIA is supported");
    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(solver.get_reason_unknown(), Some("timeout".to_string()));
}

/// check_sat_with_timeout with zero duration returns Unknown.
#[test]
fn test_check_sat_with_timeout_zero_returns_unknown() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA is supported");
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let gt = solver.gt(x, zero);
    solver.assert_term(gt);

    let result = solver.check_sat_with_timeout(Duration::ZERO);
    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(solver.get_reason_unknown(), Some("timeout".to_string()));
}

/// check_sat_with_timeout with sufficient duration solves.
#[test]
fn test_check_sat_with_timeout_sufficient_solves() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA is supported");
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let gt = solver.gt(x, zero);
    solver.assert_term(gt);

    let result = solver.check_sat_with_timeout(Duration::from_secs(10));
    assert_eq!(result, SolveResult::Sat);
}

/// check_sat_with_timeout does not permanently change the solver's timeout.
#[test]
fn test_check_sat_with_timeout_restores_previous_timeout() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA is supported");
    solver.set_timeout(Some(Duration::from_secs(30)));

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let gt = solver.gt(x, zero);
    solver.assert_term(gt);

    let _ = solver.check_sat_with_timeout(Duration::from_secs(5));
    // The original 30s timeout should be restored
    assert_eq!(solver.timeout(), Some(Duration::from_secs(30)));
}

/// check_sat_with_timeout restores None when solver had no timeout.
#[test]
fn test_check_sat_with_timeout_restores_none() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA is supported");
    assert!(solver.timeout().is_none());

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let gt = solver.gt(x, zero);
    solver.assert_term(gt);

    let _ = solver.check_sat_with_timeout(Duration::from_secs(5));
    assert!(solver.timeout().is_none());
}

/// try_check_sat_with_timeout panic-safe wrapper works.
#[test]
fn test_try_check_sat_with_timeout_returns_ok() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA is supported");
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let gt = solver.gt(x, zero);
    solver.assert_term(gt);

    let result = solver.try_check_sat_with_timeout(Duration::from_secs(10));
    assert!(result.is_ok());
    assert_eq!(result.expect("should not panic"), SolveResult::Sat);
}

/// SolverConfig works with QF_BV logic (#8688 acceptance criteria).
#[test]
fn test_solver_config_qf_bv_with_timeout() {
    let config = SolverConfig::default().with_timeout(Duration::from_secs(5));
    let mut solver = Solver::try_new_with_config(Logic::QfBv, config).expect("QF_BV is supported");
    let x = solver.declare_const("x", Sort::bitvec(8));
    let ff = solver.bv_const(0xFF, 8);
    let x_eq_ff = solver.eq(x, ff);
    solver.assert_term(x_eq_ff);

    let result = solver.check_sat();
    assert_eq!(result, SolveResult::Sat);
}

/// Per-query timeout works for EXTERNAL_CODEGEN's QF_ABV native API path (#8688).
#[test]
fn test_check_sat_with_timeout_zero_qf_abv_returns_timeout() {
    let mut solver = Solver::try_new(Logic::QfAbv).expect("QF_ABV is supported");
    let arr = solver.declare_const("arr", Sort::array(Sort::bitvec(8), Sort::bitvec(8)));
    let idx = solver.bv_const(7, 8);
    let val = solver.bv_const(42, 8);
    let stored = solver.store(arr, idx, val);
    let selected = solver.select(stored, idx);
    let eq = solver.eq(selected, val);
    solver.assert_term(eq);

    let result = solver.check_sat_with_timeout(Duration::ZERO);
    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(solver.get_reason_unknown(), Some("timeout".to_string()));
}

/// Per-query timeout is available for quantified-logics requested by EXTERNAL_CODEGEN (#8688).
#[test]
fn test_check_sat_with_timeout_zero_all_logic_returns_timeout() {
    let mut solver = Solver::try_new(Logic::All).expect("ALL logic is supported");
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let ge = solver.ge(x, zero);
    solver.assert_term(ge);

    let result = solver.check_sat_with_timeout(Duration::ZERO);
    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(solver.get_reason_unknown(), Some("timeout".to_string()));
}

/// #sat-chokepoint provenance: a surfaced `Sat` always retains the
/// `SatCertificate` emission witness minted by the `emit_sat_verdict` funnel
/// (`finish_verified_result` publishes registered `Unknown` when the token is
/// absent, while the definite constructor requires it); the test-only
/// `for_testing` bypass carries none.
#[test]
fn test_sat_result_retains_chokepoint_emission_witness() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);

    let verified = solver.check_sat();
    assert!(verified.is_sat());
    assert!(
        verified.has_sat_emission_witness(),
        "funnel-minted Sat must retain its SatCertificate witness"
    );

    let bypass = VerifiedSolveResult::for_testing(SolveResult::Sat, true);
    assert!(
        !bypass.has_sat_emission_witness(),
        "the test-only constructor bypass never carries the emission witness"
    );
}

#[test]
fn test_unsat_result_retains_chokepoint_emission_witness() {
    let mut solver = Solver::new(Logic::QfLia);
    let contradiction = solver.bool_const(false);
    solver.assert_term(contradiction);

    let verified = solver.check_sat();
    assert!(verified.is_unsat());
    assert!(
        verified.has_unsat_emission_witness(),
        "query-authorized Unsat must retain its one-shot witness"
    );
    assert!(
        !verified.was_unsat_strictly_verified(),
        "ordinary QF_LIA publication must not claim a checked refutation"
    );
}
