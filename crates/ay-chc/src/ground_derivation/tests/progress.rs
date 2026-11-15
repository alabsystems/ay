// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cooperative cancellation never becomes a successful or malformed witness.

use super::*;

fn validate_with_callback(
    problem: &ChcProblem,
    derivation: &GroundDerivation,
    callback: &mut dyn FnMut() -> bool,
) -> Result<(), GroundDerivationError> {
    validate_ground_derivation_with_control(
        problem,
        derivation,
        &mut GroundValidationControl::new(callback),
    )
}

fn refuse_every_validation_callback(problem: &ChcProblem, derivation: &GroundDerivation) {
    let mut callbacks = 0;
    assert_eq!(
        validate_with_callback(problem, derivation, &mut || {
            callbacks += 1;
            true
        }),
        Ok(())
    );
    assert!(callbacks > derivation.steps.len());
    // The last ordinal is inside the final step (#completed-check-accepted:
    // nothing polls after it), so a refusal there still interrupts the walk.
    // A fresh retry also detects leaked global state.
    for reject_at in 1..=callbacks {
        let mut seen = 0;
        assert_eq!(
            validate_with_callback(problem, derivation, &mut || {
                seen += 1;
                seen != reject_at
            }),
            Err(GroundDerivationError::Interrupted),
            "callback {reject_at} of {callbacks}"
        );
        assert_eq!(seen, reject_at, "refusal must remain terminal");
        assert_eq!(validate_ground_derivation(problem, derivation), Ok(()));
    }
}

#[test]
fn counting_derivation_refuses_every_callback_and_restricted_subsetly_retries() {
    refuse_every_validation_callback(&counting_problem(), &counting_derivation());
}

/// #completed-check-accepted — a check that decided its last step is
/// returned: no poll follows the final decision, so a stop that arrives after
/// it cannot turn an accepted derivation into `Interrupted` (it used to: one
/// trailing poll followed the step loop).
#[test]
fn a_stop_after_the_final_decision_cannot_undo_a_completed_check() {
    let problem = counting_problem();
    let valid = counting_derivation();
    // Identical to `valid` up to the final step's last comparison, which
    // fails: the query's premise head is P(2), its use reads P(3).
    let mut rejected_last = valid.clone();
    rejected_last.steps[3].env = env(&[("x", 3)]);
    let polls = |derivation: &GroundDerivation| {
        let mut calls = 0;
        let result = validate_with_callback(&problem, derivation, &mut || {
            calls += 1;
            true
        });
        (result, calls)
    };
    let (accepted, accepted_polls) = polls(&valid);
    assert_eq!(accepted, Ok(()));
    let (rejected, rejected_polls) = polls(&rejected_last);
    assert_eq!(
        rejected,
        Err(GroundDerivationError::ArgumentMismatch {
            step: 3,
            position: 0,
            argument: 0,
        })
    );
    // The final decision's poll is the last one either walk makes.
    assert_eq!(accepted_polls, rejected_polls);
    // A stop raised right after that poll is never observed...
    let mut seen = 0;
    assert_eq!(
        validate_with_callback(&problem, &valid, &mut || {
            seen += 1;
            seen <= accepted_polls
        }),
        Ok(())
    );
    assert_eq!(seen, accepted_polls);
    // ...while one raised AT it still interrupts (negative control).
    let mut seen = 0;
    assert_eq!(
        validate_with_callback(&problem, &valid, &mut || {
            seen += 1;
            seen < accepted_polls
        }),
        Err(GroundDerivationError::Interrupted)
    );
}

#[test]
fn always_continue_preserves_valid_and_malformed_derivation_reasons() {
    let problem = counting_problem();
    let valid = counting_derivation();
    let mut cases = vec![(valid.clone(), Ok(()))];
    cases.push((
        GroundDerivation::default(),
        Err(GroundDerivationError::Empty),
    ));
    let mut malformed = valid.clone();
    malformed.query_step = usize::MAX;
    cases.push((malformed, Err(GroundDerivationError::RootOutOfRange)));
    let mut malformed = valid.clone();
    malformed.steps[0].clause_index = 99;
    cases.push((
        malformed,
        Err(GroundDerivationError::ClauseOutOfRange {
            step: 0,
            clause_index: 99,
        }),
    ));
    let mut malformed = valid.clone();
    malformed.steps[1].premises = vec![1];
    cases.push((
        malformed,
        Err(GroundDerivationError::PremiseNotWellFounded {
            step: 1,
            premise: 1,
        }),
    ));
    let mut malformed = valid.clone();
    malformed.steps[1].env = env(&[("x", 0)]);
    cases.push((
        malformed,
        Err(GroundDerivationError::VariableBindingMissing {
            step: 1,
            variable: 1,
        }),
    ));
    let mut malformed = valid.clone();
    malformed.steps[1].env = env(&[("x", 0), ("y", 5)]);
    cases.push((
        malformed,
        Err(GroundDerivationError::ConstraintFalse { step: 1 }),
    ));
    let mut malformed = valid;
    malformed.steps[1].env = env(&[("x", 1), ("y", 2)]);
    cases.push((
        malformed,
        Err(GroundDerivationError::ArgumentMismatch {
            step: 1,
            position: 0,
            argument: 0,
        }),
    ));
    for (derivation, expected) in cases {
        assert_eq!(validate_ground_derivation(&problem, &derivation), expected);
        assert_eq!(
            validate_with_callback(&problem, &derivation, &mut || true),
            expected
        );
    }
}

#[test]
fn pre_cancelled_control_dominates_invalid_derivation_shape() {
    let problem = counting_problem();
    let mut malformed = counting_derivation();
    malformed.query_step = usize::MAX;
    for derivation in [GroundDerivation::default(), malformed] {
        let mut calls = 0;
        assert_eq!(
            validate_with_callback(&problem, &derivation, &mut || {
                calls += 1;
                false
            }),
            Err(GroundDerivationError::Interrupted)
        );
        assert_eq!(calls, 1);
    }
}

#[test]
fn reusing_a_stopped_control_cannot_resurrect_validation() {
    let problem = counting_problem();
    let derivation = counting_derivation();
    let mut calls = 0;
    let mut callback = || {
        calls += 1;
        calls != 1
    };
    let mut control = GroundValidationControl::new(&mut callback);
    for _ in 0..2 {
        assert_eq!(
            validate_ground_derivation_with_control(&problem, &derivation, &mut control),
            Err(GroundDerivationError::Interrupted)
        );
        assert!(control.is_stopped());
    }
    assert_eq!(calls, 1);
    assert_eq!(validate_ground_derivation(&problem, &derivation), Ok(()));
}

fn observed_uf_derivation() -> (ChcProblem, GroundDerivation) {
    let mut problem = ChcProblem::new();
    let predicate = problem.declare_predicate("Observed", vec![ChcSort::Int]);
    let fx = int_uf("observed_f", var("x"));
    let fy = int_uf("observed_f", var("y"));
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(fx.clone(), ChcExpr::Int(7))),
        ClauseHead::Predicate(predicate, vec![fx.clone()]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(predicate, vec![fy.clone()])],
        Some(ChcExpr::eq(fy.clone(), ChcExpr::Int(7))),
    )));
    let mut fact = env(&[("x", 0)]);
    install_observation(&mut fact, fx, 7);
    let mut query = env(&[("y", 0)]);
    install_observation(&mut query, fy, 7);
    let derivation = GroundDerivation {
        steps: vec![
            GroundDerivationStep {
                clause_index: 0,
                env: fact,
                premises: vec![],
            },
            GroundDerivationStep {
                clause_index: 1,
                env: query,
                premises: vec![0],
            },
        ],
        query_step: 1,
    };
    (problem, derivation)
}

#[test]
fn observed_uf_and_ground_argument_replay_share_the_same_control() {
    let (problem, derivation) = observed_uf_derivation();
    refuse_every_validation_callback(&problem, &derivation);
}

fn direct_store_read_expression() -> ChcExpr {
    let array = ChcExpr::var(ChcVar::new(
        "unbound_array",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    ));
    ChcExpr::select(
        ChcExpr::store(array, ChcExpr::Int(0), ChcExpr::Int(7)),
        ChcExpr::Int(0),
    )
}

fn normalization_retry_expression() -> ChcExpr {
    ChcExpr::ite(
        ChcExpr::var(ChcVar::new("unbound_condition", ChcSort::Bool)),
        ChcExpr::Int(7),
        ChcExpr::Int(7),
    )
}

fn refuse_every_evaluation_callback(
    expression: &ChcExpr,
    values: &FxHashMap<String, SmtValue>,
    expected: Option<SmtValue>,
) {
    let mut calls = 0;
    assert_eq!(
        eval_ground_with_control(
            expression,
            values,
            &mut GroundValidationControl::new(&mut || {
                calls += 1;
                true
            })
        ),
        Ok(expected.clone())
    );
    assert!(calls >= 2);
    for reject_at in 1..=calls {
        let mut seen = 0;
        assert_eq!(
            eval_ground_with_control(
                expression,
                values,
                &mut GroundValidationControl::new(&mut || {
                    seen += 1;
                    seen != reject_at
                })
            ),
            Err(GroundDerivationError::Interrupted),
            "evaluation callback {reject_at} of {calls} must not become None"
        );
        assert_eq!(seen, reject_at);
        assert_eq!(eval_ground(expression, values), expected);
    }
}

#[test]
fn direct_and_indeterminate_ground_evaluation_propagate_interrupted() {
    let values = env(&[("x", 3)]);
    refuse_every_evaluation_callback(
        &ChcExpr::add(var("x"), ChcExpr::Int(4)),
        &values,
        Some(SmtValue::Int(7)),
    );
    refuse_every_evaluation_callback(&var("unbound"), &values, None);
    let opaque = FxHashMap::from_iter([("x".to_string(), SmtValue::Opaque("placeholder".into()))]);
    refuse_every_evaluation_callback(&var("x"), &opaque, None);
}

#[test]
fn direct_store_read_preserves_exact_value_and_cooperative_cancellation() {
    let expression = direct_store_read_expression();
    let values = FxHashMap::default();
    assert_eq!(evaluate_expr(&expression, &values), Some(SmtValue::Int(7)));
    assert_eq!(eval_ground(&expression, &values), Some(SmtValue::Int(7)));
    refuse_every_evaluation_callback(&expression, &values, Some(SmtValue::Int(7)));
}

#[test]
fn normalization_retry_never_converts_interruption_to_none_or_success() {
    let expression = normalization_retry_expression();
    let values = FxHashMap::default();
    assert_eq!(
        evaluate_expr(&expression, &values),
        None,
        "the retry must actually run"
    );
    assert_eq!(eval_ground(&expression, &values), Some(SmtValue::Int(7)));
    refuse_every_evaluation_callback(&expression, &values, Some(SmtValue::Int(7)));
}

#[test]
fn cold_source_cache_refuses_every_callback_without_publishing_a_surface() {
    let problem = counting_problem();
    let mut legacy = GroundSourceSurfaceCache::new(&problem);
    let expected = legacy.charge_step_reuse(1).expect("legacy surface");
    let expected_work = legacy.work_used_for_test();
    let mut observed = GroundSourceSurfaceCache::new(&problem);
    let mut calls = 0;
    assert_eq!(
        observed.charge_step_reuse_with_control(
            1,
            &mut GroundValidationControl::new(&mut || {
                calls += 1;
                true
            })
        ),
        Ok(expected)
    );
    assert_eq!(observed.work_used_for_test(), expected_work);
    assert_eq!(observed.walked_clause_count(), 1);
    assert!(calls > 10, "must poll inside the source walk");
    for refused in 1..=calls {
        let mut cache = GroundSourceSurfaceCache::new(&problem);
        let mut seen = 0;
        assert_eq!(
            cache.charge_step_reuse_with_control(
                1,
                &mut GroundValidationControl::new(&mut || {
                    seen += 1;
                    seen != refused
                })
            ),
            Err(GroundSourceSurfaceError::Interrupted),
            "source callback {refused} of {calls}"
        );
        assert_eq!(seen, refused);
        let mut retry = GroundSourceSurfaceCache::new(&problem);
        assert_eq!(retry.charge_step_reuse(1), Ok(expected));
        assert_eq!(retry.work_used_for_test(), expected_work);
    }
}

#[test]
fn warm_source_cache_cannot_bypass_refusal_or_rewalk_the_clause() {
    let problem = counting_problem();
    let mut cache = GroundSourceSurfaceCache::new(&problem);
    cache.charge_step_reuse(1).expect("warm source surface");
    let work = cache.work_used_for_test();
    let mut calls = 0;
    let error = cache.surface_with_control(
        1,
        &mut GroundValidationControl::new(&mut || {
            calls += 1;
            false
        }),
    );
    assert!(matches!(error, Err(GroundSourceSurfaceError::Interrupted)));
    assert_eq!(calls, 1);
    assert_eq!(cache.work_used_for_test(), work);
    assert_eq!(cache.walked_clause_count(), 1);
}
