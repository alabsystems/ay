// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::SmtContext;
use crate::{ChcExpr, ChcParser, ChcSort, ChcVar};

const COUNTER: &str = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (y Int)) (=> (and (Inv x) (= y (+ x 1))) (Inv y))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;

fn fixture() -> (ChcProblem, InvariantModel, PdrConfig) {
    let problem = ChcParser::parse(COUNTER).unwrap();
    let model =
        InvariantModel::parse_smtlib("(define-fun Inv ((x Int)) Bool (>= x 0))", &problem).unwrap();
    let config = PdrConfig {
        solve_timeout: Some(Duration::from_secs(20)),
        ..PdrConfig::default()
    }
    .with_memory_budget(Some(64 * 1024 * 1024));
    (problem, model, config)
}

#[test]
fn original_valid_model_is_valid_and_legacy_bool_remains_true() {
    let (problem, model, config) = fixture();
    assert_eq!(
        validate_external_invariant_model_typed(&problem, &model, &config).unwrap(),
        ExternalInvariantValidation::Valid
    );
    assert!(validate_external_invariant_model(&problem, &model, &config).unwrap());
}

#[test]
fn original_query_sat_refutes_candidate_not_the_chc_problem() {
    let (problem, model, config) = fixture();
    let bad = ChcParser::parse(&COUNTER.replace("(< x 0)", "(>= x 0)")).unwrap();
    assert_eq!(
        validate_external_invariant_model_typed(&bad, &model, &config).unwrap(),
        ExternalInvariantValidation::Refuted
    );
    assert!(!validate_external_invariant_model(&bad, &model, &config).unwrap());
    assert_eq!(
        validate_external_invariant_model_typed(&problem, &model, &config).unwrap(),
        ExternalInvariantValidation::Valid
    );
}

#[test]
fn original_transition_sat_refutes_the_submitted_interpretation() {
    let (problem, _, config) = fixture();
    let model =
        InvariantModel::parse_smtlib("(define-fun Inv ((x Int)) Bool (= x 0))", &problem).unwrap();
    assert_eq!(
        validate_external_invariant_model_typed(&problem, &model, &config).unwrap(),
        ExternalInvariantValidation::Refuted
    );
}

#[test]
fn missing_and_free_variable_models_are_rejected_not_refuted() {
    let (problem, mut model, config) = fixture();
    assert_eq!(
        validate_external_invariant_model_typed(&problem, &InvariantModel::new(), &config,)
            .unwrap(),
        ExternalInvariantValidation::Rejected
    );
    let pred = problem.predicates()[0].id;
    let mut interpretation = model.get(&pred).unwrap().clone();
    interpretation.formula = ChcExpr::eq(
        ChcExpr::var(ChcVar::new("outside_binder", ChcSort::Int)),
        ChcExpr::int(0),
    );
    model.set(pred, interpretation);
    assert_eq!(
        validate_external_invariant_model_typed(&problem, &model, &config).unwrap(),
        ExternalInvariantValidation::Rejected
    );
}

#[test]
fn unsupported_validation_false_is_inconclusive_not_a_refutation() {
    let problem = ChcParser::parse(
        r#"
(set-logic HORN)
(declare-fun Inv (Real) Bool)
(assert (forall ((x Real)) (=> (= x 0.0) (Inv x))))
(assert (forall ((x Real)) (=> (and (Inv x) (< x 0.0)) false)))
(check-sat)
"#,
    )
    .unwrap();
    let model =
        InvariantModel::parse_smtlib("(define-fun Inv ((x Real)) Bool true)", &problem).unwrap();
    assert_eq!(
        validate_external_invariant_model_typed(&problem, &model, &PdrConfig::default(),).unwrap(),
        ExternalInvariantValidation::Inconclusive
    );
    assert_eq!(
        from_completed(false),
        ExternalInvariantValidation::Inconclusive
    );
}

#[test]
fn original_zero_and_expired_ambient_walls_report_timeout_not_refuted() {
    let (problem, model, mut config) = fixture();
    config.solve_timeout = Some(Duration::ZERO);
    assert_eq!(
        validate_external_invariant_model_typed(&problem, &model, &config).unwrap(),
        ExternalInvariantValidation::Timeout
    );
    config.solve_timeout = Some(Duration::from_secs(20));
    let _ambient =
        crate::smt::ScopedSmtDeadline::install_until(Instant::now() - Duration::from_secs(1));
    assert_eq!(
        validate_external_invariant_model_typed(&problem, &model, &config).unwrap(),
        ExternalInvariantValidation::Timeout
    );
}

#[test]
fn precancel_is_typed_and_caller_reset_allows_only_a_fresh_attempt() {
    let (problem, model, config) = fixture();
    let caller = CancellationToken::new();
    let config = config.with_cancellation_token(Some(caller.clone()));
    caller.cancel();
    assert_eq!(
        validate_external_invariant_model_typed(&problem, &model, &config).unwrap(),
        ExternalInvariantValidation::Cancelled
    );
    caller.reset();
    assert_eq!(
        validate_external_invariant_model_typed(&problem, &model, &config).unwrap(),
        ExternalInvariantValidation::Valid
    );
}

#[test]
fn observed_active_cancellation_survives_reset_and_has_exact_cause() {
    let caller = CancellationToken::new();
    let control =
        ScopedReplayControl::install_until(Instant::now() + Duration::from_secs(20), Some(&caller));
    let observation = ScopedResourceObservation::install();
    let memory = Budget::capture(None, None);
    caller.cancel();
    let descendant = control.cancellation().unwrap().child();
    assert!(descendant.is_cancelled());
    caller.reset();
    assert_eq!(
        refusal(&control, memory, &observation),
        Some(ExternalInvariantValidation::Cancelled)
    );
    assert!(!caller.is_cancelled());
}

#[test]
fn zero_cap_and_inherited_tighter_cap_report_memory_and_restore_owner() {
    let (problem, model, config) = fixture();
    let zero = config.clone().with_memory_budget(Some(0));
    assert_eq!(
        validate_external_invariant_model_typed(&problem, &model, &zero).unwrap(),
        ExternalInvariantValidation::Memory
    );
    assert!(!validate_external_invariant_model(&problem, &model, &zero).unwrap());
    {
        let _ambient = SmtContext::scoped_thread_term_memory_budget(Some(1));
        for requested in [None, Some(usize::MAX)] {
            let config = config.clone().with_memory_budget(requested);
            assert_eq!(
                validate_external_invariant_model_typed(&problem, &model, &config,).unwrap(),
                ExternalInvariantValidation::Memory
            );
            assert_eq!(SmtContext::current_thread_term_memory_budget(), Some(1));
        }
    }
    assert_eq!(
        validate_external_invariant_model_typed(&problem, &model, &config).unwrap(),
        ExternalInvariantValidation::Valid
    );
}

fn empty_fixture() -> ChcProblem {
    ChcParser::parse(
        r#"
(set-logic HORN)
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (p x))))
(assert (forall ((x Int)) (=> (p x) (q x))))
(assert (forall ((x Int)) (=> (and (q x) (< x 0)) false)))
(check-sat)
"#,
    )
    .unwrap()
}

#[test]
fn genuine_empty_certificate_remains_independently_checked_with_finite_cap() {
    let (_, _, config) = fixture();
    let problem = empty_fixture();
    assert_eq!(
        validate_external_invariant_model_typed(&problem, &InvariantModel::new(), &config,)
            .unwrap(),
        ExternalInvariantValidation::Valid
    );
    assert_eq!(
        validate_external_invariant_model_typed(
            &problem,
            &InvariantModel::new(),
            &config.with_memory_budget(Some(0)),
        )
        .unwrap(),
        ExternalInvariantValidation::Memory
    );
}

#[test]
fn empty_memo_cannot_erase_zero_inherited_term_cap() {
    let problem = empty_fixture();
    let observation = ScopedResourceObservation::install();
    let _cap = SmtContext::scoped_thread_term_memory_budget(Some(0));
    assert!(!crate::empty_acyclic_safe_check::confirmed(
        &problem,
        Duration::from_secs(20),
        None,
    ));
    assert_eq!(observation.first(), Some(ResourceRefusal::Memory));
}

#[test]
fn default_pdr_config_retains_none_and_builder_does_not_mutate_other_limits() {
    let default = PdrConfig::default();
    let bounded = default.clone().with_memory_budget(Some(1234));
    assert_eq!(default.memory_budget(), None);
    assert_eq!(bounded.memory_budget(), Some(1234));
    assert_eq!(bounded.max_frames, default.max_frames);
    assert_eq!(bounded.max_iterations, default.max_iterations);
    assert_eq!(bounded.solve_timeout, default.solve_timeout);
}

#[test]
fn bare_original_interrupt_reports_cancelled_without_mutating_caller_token() {
    let (problem, model, config) = fixture();
    let caller = CancellationToken::new();
    let interrupt = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(true));
    let _lane = crate::smt::deadline::ScopedLaneCancellation::install(
        caller.clone(),
        Some(interrupt.clone()),
    );
    assert_eq!(
        validate_external_invariant_model_typed(&problem, &model, &config).unwrap(),
        ExternalInvariantValidation::Cancelled
    );
    assert!(!caller.is_cancelled());
    interrupt.store(false, std::sync::atomic::Ordering::Relaxed);
    assert_eq!(
        validate_external_invariant_model_typed(&problem, &model, &config).unwrap(),
        ExternalInvariantValidation::Valid
    );
}

#[test]
fn observed_memory_first_survives_nested_live_recovery_and_later_cancellation() {
    let (problem, model, config) = fixture();
    let caller = CancellationToken::new();
    let config = config.with_cancellation_token(Some(caller.clone()));
    {
        let owner = ScopedResourceObservation::install();
        {
            let _cap = SmtContext::scoped_thread_term_memory_budget(Some(1));
            let context = SmtContext::new();
            assert!(context.exact_term_memory_exceeded());
        }
        assert_eq!(owner.first(), Some(ResourceRefusal::Memory));
        caller.cancel();
        assert_eq!(
            validate_external_invariant_model_typed(&problem, &model, &config).unwrap(),
            ExternalInvariantValidation::Memory
        );
        caller.reset();
        assert_eq!(
            validate_external_invariant_model_typed(&problem, &model, &config).unwrap(),
            ExternalInvariantValidation::Memory
        );
    }
    assert_eq!(
        validate_external_invariant_model_typed(&problem, &model, &config).unwrap(),
        ExternalInvariantValidation::Valid
    );
}
