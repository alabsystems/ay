// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::engines::{ExternalInvariantValidation as Kind, ExternalInvariantValidationOwner};
use crate::{CancellationToken, ChcParser, PdrConfig};
use ay_core::resource::{enter_check_stop, ResourceGuard};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

fn configured() -> PdrConfig {
    PdrConfig {
        solve_timeout: Some(Duration::from_secs(3)),
        memory_budget: Some(64 * 1024 * 1024),
        ..PdrConfig::default()
    }
}

fn verifier() -> PdrSolver {
    let problem =
        ChcParser::parse("(set-logic HORN) (declare-rel p ()) (rule p) (query p)").unwrap();
    PdrSolver::new(problem, configured())
}

fn bv_var(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::BitVec(8)))
}

fn confirm(
    verifier: &mut PdrSolver,
    original: &ChcExpr,
    definitions: &[(ChcVar, ChcExpr)],
    model: FxHashMap<String, SmtValue>,
) -> SmtResult {
    verifier.confirm_original_validation_sat(
        original,
        definitions,
        model,
        Duration::from_secs(2),
        None,
        None,
    )
}

#[test]
fn a_genuine_original_model_is_confirmed_by_exact_evaluation() {
    let mut verifier = verifier();
    let original = ChcExpr::eq(bv_var("x"), ChcExpr::BitVec(7, 8));
    let mut model = FxHashMap::default();
    model.insert("x".into(), SmtValue::BitVec(7, 8));
    assert!(matches!(
        confirm(&mut verifier, &original, &[], model),
        SmtResult::Sat(_)
    ));
    assert_eq!(
        verifier.observed_model_validation_failure(),
        Some(Kind::Refuted)
    );
}

#[test]
fn reconstructed_definition_trail_is_replayed_against_the_original_formula() {
    let mut verifier = verifier();
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let y = ChcVar::new("y", ChcSort::BitVec(8));
    let original = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
        ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::BitVec(7, 8)),
    );
    let definitions = [(x, ChcExpr::var(y.clone())), (y, ChcExpr::BitVec(7, 8))];
    let SmtResult::Sat(model) =
        confirm(&mut verifier, &original, &definitions, FxHashMap::default())
    else {
        panic!("the actual original formula is satisfied by the reconstructed trail");
    };
    assert_eq!(evaluate_expr(&original, &model), Some(SmtValue::Bool(true)));
    assert_eq!(
        verifier.observed_model_validation_failure(),
        Some(Kind::Refuted)
    );
}

#[test]
fn partial_substitution_sat_cannot_refute_an_unsatisfiable_original() {
    let mut verifier = verifier();
    // A deliberately incomplete substituted view could drop one occurrence
    // and report SAT. Only the complete original contradiction is authority.
    let original = ChcExpr::and(
        ChcExpr::eq(bv_var("x"), ChcExpr::BitVec(1, 8)),
        ChcExpr::eq(bv_var("x"), ChcExpr::BitVec(2, 8)),
    );
    let mut candidate = FxHashMap::default();
    candidate.insert("x".into(), SmtValue::BitVec(1, 8));
    assert!(confirm(&mut verifier, &original, &[], candidate).is_unsat());
    assert_eq!(verifier.observed_model_validation_failure(), None);
}

#[test]
fn a_false_candidate_triggers_the_actual_original_query_not_a_false_refutation() {
    let mut verifier = verifier();
    let original = ChcExpr::eq(bv_var("x"), ChcExpr::BitVec(2, 8));
    let mut candidate = FxHashMap::default();
    candidate.insert("x".into(), SmtValue::BitVec(1, 8));
    let SmtResult::Sat(model) = confirm(&mut verifier, &original, &[], candidate) else {
        panic!("the real original query has the distinct satisfying value 2");
    };
    assert_eq!(evaluate_expr(&original, &model), Some(SmtValue::Bool(true)));
    assert_eq!(
        verifier.observed_model_validation_failure(),
        Some(Kind::Refuted)
    );
}

#[test]
fn missing_candidate_assignments_do_not_become_original_satisfaction() {
    let mut verifier = verifier();
    let original = ChcExpr::eq(bv_var("missing"), ChcExpr::BitVec(3, 8));
    let SmtResult::Sat(model) = confirm(&mut verifier, &original, &[], FxHashMap::default()) else {
        panic!("the actual original query supplies the missing assignment");
    };
    assert_eq!(evaluate_expr(&original, &model), Some(SmtValue::Bool(true)));
    assert_eq!(
        verifier.observed_model_validation_failure(),
        Some(Kind::Refuted)
    );
}

#[test]
fn original_expired_clause_clock_is_not_restarted_by_a_new_step_timeout() {
    let mut verifier = verifier();
    let expired = Instant::now() - Duration::from_secs(1);
    let result = verifier.confirm_original_validation_sat(
        &ChcExpr::Bool(true),
        &[],
        FxHashMap::default(),
        Duration::from_secs(60),
        Some(expired),
        Some(Duration::from_millis(1)),
    );
    assert!(matches!(result, SmtResult::Unknown));
    assert_eq!(verifier.observed_model_validation_failure(), None);
}

#[test]
fn actual_original_query_inherits_exact_clause_end_and_restores_enclosing_scope() {
    use crate::smt::{deadline::current_smt_deadline, ScopedSmtDeadline};

    let previous = current_smt_deadline();
    let start = Instant::now();
    let clause_budget = Duration::from_secs(1);
    let clause_end = start + clause_budget;
    let enclosing_end = start + Duration::from_secs(30);
    let mut verifier = verifier();
    {
        let _enclosing = ScopedSmtDeadline::install_until(enclosing_end);
        assert_eq!(current_smt_deadline(), Some(enclosing_end));
        let calls = Arc::new(AtomicUsize::new(0));
        let observed = Arc::clone(&calls);
        let _stop = enter_check_stop(Arc::new(move || {
            assert_eq!(current_smt_deadline(), Some(clause_end));
            // A descendant's later duration must not rebase the original end.
            let _nested = ScopedSmtDeadline::install_until(enclosing_end);
            assert_eq!(current_smt_deadline(), Some(clause_end));
            observed.fetch_add(1, Ordering::SeqCst);
            false
        }));
        let original = ChcExpr::eq(bv_var("x"), ChcExpr::BitVec(2, 8));
        // Missing x forces the real original SMT call, not the evaluator or
        // the forced-result seam used by the publication-only control.
        let SmtResult::Sat(model) = verifier.confirm_original_validation_sat(
            &original,
            &[],
            FxHashMap::default(),
            Duration::from_secs(60),
            Some(start),
            Some(clause_budget),
        ) else {
            panic!("the actual original query is satisfiable within its clause scope");
        };
        assert_eq!(evaluate_expr(&original, &model), Some(SmtValue::Bool(true)));
        assert!(calls.load(Ordering::SeqCst) > 0);
        assert_eq!(current_smt_deadline(), Some(enclosing_end));
    }
    assert_eq!(current_smt_deadline(), previous);
}

#[test]
fn inherited_cancel_and_zero_memory_refuse_even_a_true_original_formula() {
    let cancellation = CancellationToken::new();
    let mut verifier = verifier();
    verifier.config.cancellation_token = Some(cancellation.clone());
    cancellation.cancel();
    assert!(matches!(
        confirm(
            &mut verifier,
            &ChcExpr::Bool(true),
            &[],
            FxHashMap::default()
        ),
        SmtResult::Unknown
    ));
    assert_eq!(verifier.observed_model_validation_failure(), None);
    cancellation.reset();
    verifier.config.memory_budget = Some(0);
    assert!(matches!(
        confirm(
            &mut verifier,
            &ChcExpr::Bool(true),
            &[],
            FxHashMap::default()
        ),
        SmtResult::Unknown
    ));
    assert_eq!(verifier.observed_model_validation_failure(), None);
}

#[test]
fn every_original_observer_cut_withholds_refutation_before_publication() {
    let mut verifier = verifier();
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    {
        let _scope = enter_check_stop(Arc::new(move || {
            observed.fetch_add(1, Ordering::SeqCst);
            false
        }));
        assert!(matches!(
            confirm(
                &mut verifier,
                &ChcExpr::Bool(true),
                &[],
                FxHashMap::default()
            ),
            SmtResult::Sat(_)
        ));
    }
    let total = calls.load(Ordering::SeqCst);
    assert!(total >= 3);
    for cut in 1..=total {
        let mut verifier = self::verifier();
        let calls = Arc::new(AtomicUsize::new(0));
        let observed = Arc::clone(&calls);
        let _scope = enter_check_stop(Arc::new(move || {
            observed.fetch_add(1, Ordering::SeqCst) + 1 == cut
        }));
        assert!(
            matches!(
                confirm(
                    &mut verifier,
                    &ChcExpr::Bool(true),
                    &[],
                    FxHashMap::default()
                ),
                SmtResult::Unknown
            ),
            "cut {cut}"
        );
        assert_eq!(calls.load(Ordering::SeqCst), cut);
        assert_eq!(verifier.observed_model_validation_failure(), None);
    }
}

fn owned_confirmation(limit: Option<u64>) -> (Result<SmtResult, Kind>, u64) {
    let mut original = ResourceGuard::new();
    original.set_deadline(Some(Instant::now() + Duration::from_secs(3)));
    original.set_rlimit(limit);
    let owner = ExternalInvariantValidationOwner::capture(&original, &configured());
    let mut verifier = verifier();
    let result = owner
        .with_resources(|| {
            Ok(confirm(
                &mut verifier,
                &ChcExpr::Bool(true),
                &[],
                FxHashMap::default(),
            ))
        })
        .unwrap();
    (result, original.ticks())
}

#[test]
fn every_retained_original_work_cut_stays_worklimit_and_never_mints_a_grant() {
    let (healthy, used) = owned_confirmation(None);
    assert!(matches!(healthy, Ok(SmtResult::Sat(_))));
    assert!(used > 0);
    for limit in 0..=used {
        let (result, spent) = owned_confirmation(Some(limit));
        assert!(
            matches!(result, Err(Kind::WorkLimit)),
            "limit {limit}, spent {spent}"
        );
        assert!(spent <= limit);
    }
}

#[test]
fn late_original_stop_after_candidate_reconstruction_withholds_refutation() {
    let mut verifier = verifier();
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let _scope = enter_check_stop(Arc::new(move || {
        observed.fetch_add(1, Ordering::SeqCst) + 1 >= 3
    }));
    assert!(matches!(
        confirm(
            &mut verifier,
            &ChcExpr::Bool(true),
            &[],
            FxHashMap::default()
        ),
        SmtResult::Unknown
    ));
    assert_eq!(verifier.observed_model_validation_failure(), None);
}

#[test]
fn mismatched_or_noncanonical_scalar_bindings_cannot_authorize_the_evaluator() {
    let original = ChcExpr::eq(bv_var("x"), ChcExpr::BitVec(3, 8));
    for value in [
        SmtValue::Int(3),
        SmtValue::BitVec(3, 16),
        SmtValue::BitVec(259, 8),
        SmtValue::Opaque("x".into()),
    ] {
        let mut model = FxHashMap::default();
        model.insert("x".into(), value);
        assert!(!exact_scalar_assignments(&original, &model));
    }
}

#[test]
fn full_array_original_query_keeps_both_sat_and_unsat_authority() {
    let sort = ChcSort::Array(Box::new(ChcSort::BitVec(8)), Box::new(ChcSort::BitVec(8)));
    let array = ChcExpr::var(ChcVar::new("a", sort));
    let pinned = ChcExpr::eq(
        array.clone(),
        ChcExpr::const_array(ChcSort::BitVec(8), ChcExpr::BitVec(7, 8)),
    );
    for expected in [7, 8] {
        let original = ChcExpr::and(
            pinned.clone(),
            ChcExpr::eq(
                ChcExpr::select(array.clone(), ChcExpr::BitVec(3, 8)),
                ChcExpr::BitVec(expected, 8),
            ),
        );
        let mut model = FxHashMap::default();
        model.insert(
            "a".into(),
            SmtValue::ConstArray(Box::new(SmtValue::BitVec(7, 8))),
        );
        assert!(!exact_scalar_assignments(&original, &model));
        let mut verifier = verifier();
        let result = confirm(&mut verifier, &original, &[], model);
        if expected == 7 {
            assert!(matches!(result, SmtResult::Sat(_)));
            assert_eq!(
                verifier.observed_model_validation_failure(),
                Some(Kind::Refuted)
            );
        } else {
            assert!(result.is_unsat());
            assert_eq!(verifier.observed_model_validation_failure(), None);
        }
    }
}

#[test]
fn named_datatype_original_query_is_solved_with_its_actual_registry() {
    let problem = ChcParser::parse(
        "(set-logic HORN)
         (declare-datatypes ((Cell 0)) (((mkCell (payload (_ BitVec 8))))))
         (declare-var obj Cell)
         (rule (=> (= obj (mkCell #x07)) false))",
    )
    .unwrap();
    let original = problem.clauses()[0].body.constraint.clone().unwrap();
    assert!(original
        .vars()
        .iter()
        .any(|var| matches!(var.sort, ChcSort::Datatype { .. })));
    let mut verifier = PdrSolver::new(problem, configured());
    assert!(matches!(
        confirm(&mut verifier, &original, &[], FxHashMap::default()),
        SmtResult::Sat(_)
    ));
    assert_eq!(
        verifier.observed_model_validation_failure(),
        Some(Kind::Refuted)
    );
}

#[test]
fn cancelled_original_owner_preserves_the_exact_typed_cause() {
    let cancellation = CancellationToken::new();
    let config = configured().with_cancellation_token(Some(cancellation.clone()));
    let mut original = ResourceGuard::new();
    original.set_deadline(Some(Instant::now() + Duration::from_secs(3)));
    let owner = ExternalInvariantValidationOwner::capture(&original, &config);
    cancellation.cancel();
    let mut verifier = verifier();
    let result = owner
        .with_resources(|| {
            Ok(confirm(
                &mut verifier,
                &ChcExpr::Bool(true),
                &[],
                FxHashMap::default(),
            ))
        })
        .unwrap();
    assert!(matches!(result, Err(Kind::Cancelled)));
    assert_eq!(owner.check(), Some(Kind::Cancelled));
    assert_eq!(verifier.observed_model_validation_failure(), None);
}

#[test]
fn an_inconclusive_original_recheck_cannot_inherit_the_simplified_sat_marker() {
    let mut verifier = verifier();
    verifier
        .smt
        .push_forced_check_sat_result_for_tests(SmtResult::Unknown);
    let original = ChcExpr::eq(bv_var("x"), ChcExpr::BitVec(2, 8));
    assert!(matches!(
        confirm(&mut verifier, &original, &[], FxHashMap::default()),
        SmtResult::Unknown
    ));
    assert_eq!(verifier.observed_model_validation_failure(), None);
}

#[test]
fn refusal_after_completed_original_smt_withholds_its_sat_result() {
    let original = ChcExpr::eq(bv_var("x"), ChcExpr::BitVec(2, 8));
    let exercise = |cut: Option<usize>| {
        let mut verifier = verifier();
        let mut actual_model = FxHashMap::default();
        actual_model.insert("x".into(), SmtValue::BitVec(2, 8));
        assert_eq!(
            evaluate_expr(&original, &actual_model),
            Some(SmtValue::Bool(true))
        );
        // This existing test seam isolates the post-SMT publication fence;
        // separate controls above execute the actual original solver.
        verifier
            .smt
            .push_forced_check_sat_result_for_tests(SmtResult::Sat(actual_model));
        let calls = Arc::new(AtomicUsize::new(0));
        let observed = Arc::clone(&calls);
        let _scope = enter_check_stop(Arc::new(move || {
            let call = observed.fetch_add(1, Ordering::SeqCst) + 1;
            cut == Some(call)
        }));
        let result = confirm(&mut verifier, &original, &[], FxHashMap::default());
        (
            result,
            verifier.observed_model_validation_failure(),
            calls.load(Ordering::SeqCst),
        )
    };
    let (healthy, marker, calls) = exercise(None);
    assert!(matches!(healthy, SmtResult::Sat(_)));
    assert_eq!(marker, Some(Kind::Refuted));
    let (refused, marker, seen) = exercise(Some(calls));
    assert!(matches!(refused, SmtResult::Unknown));
    assert_eq!(marker, None);
    assert_eq!(seen, calls);
}
