// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fresh native qualification; prepared fixture metadata alone is not evidence.

use super::*;
use crate::quantified::QuantifiedChcResult;
use ntest::timeout;

const MEMORY: usize = 128 * 1024 * 1024;

fn remaining(deadline: Instant) -> Duration {
    deadline.saturating_duration_since(Instant::now())
}

fn scalar() -> QuantifiedChcProblem {
    QuantifiedChcProblem::parse_smtlib(
        "(set-logic HORN)
         (declare-fun P ((_ BitVec 2)) Bool)
         (declare-fun Marker () Bool)
         (assert (=> Marker false))
         (assert (forall ((x (_ BitVec 2)))
           (=> (forall ((i (_ BitVec 2))) (= x x)) (P x))))
         (assert (forall ((x (_ BitVec 2)) (y (_ BitVec 2)))
           (=> (and (P x) (P y) (distinct x y)) Marker)))
         (check-sat)",
    )
    .unwrap()
}

#[test]
#[timeout(300000)]
fn acquired_slice_trace_restores_early_marker_query_and_roundtrips_aggregate_artifact() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(MEMORY));
    let deadline = Instant::now() + Duration::from_secs(240);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let aggregate = scalar();
    let rows = aggregate
        .query_obligations(remaining(deadline), &token)
        .unwrap();
    assert_eq!(rows.len(), 1);
    let row = &rows[0];
    let QuantifiedChcResult::Unsafe(base) = row.problem().solve(
        remaining(deadline).min(Duration::from_secs(60)),
        Some(MEMORY),
        &token,
    ) else {
        panic!("slice must have a native checked counterexample");
    };
    let trace = base
        .concrete_trace(row.problem(), remaining(deadline), &token)
        .unwrap();
    let values_ptr = trace.bindings().as_ptr();
    let count = trace.bindings().len();
    let lifted = trace
        .lift_to_aggregate(row, &aggregate, remaining(deadline), &token)
        .unwrap();
    assert_eq!(lifted.source_smtlib(), aggregate.source_smtlib());
    assert_eq!(lifted.clause_indices(), &[1, 1, 2, 0]);
    assert_eq!(
        lifted.premise_steps(),
        &[vec![], vec![], vec![0, 1], vec![2]]
    );
    assert_eq!(lifted.bindings().len(), count);
    assert_eq!(lifted.bindings().as_ptr(), values_ptr);
    assert!(lifted.recheck(&aggregate, remaining(deadline), &token));
    assert!(!lifted.recheck(row.problem(), remaining(deadline), &token));
    let bytes = lifted
        .export_artifact(&aggregate, remaining(deadline), &token)
        .unwrap();
    let imported = aggregate
        .validate_trace_artifact(&bytes, remaining(deadline), Some(MEMORY), &token)
        .unwrap();
    assert_eq!(imported.trace().clause_indices(), lifted.clause_indices());
    assert_eq!(
        imported.trace().replay_obligation(),
        lifted.replay_obligation()
    );
    assert!(row
        .problem()
        .validate_trace_artifact(&bytes, remaining(deadline), Some(MEMORY), &token,)
        .is_err());
}

#[test]
#[timeout(180000)]
fn coherent_but_unsatisfying_local_pins_refuse_without_reacquisition_and_return_original() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(MEMORY));
    let deadline = Instant::now() + Duration::from_secs(120);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let aggregate = scalar();
    let rows = aggregate
        .query_obligations(remaining(deadline), &token)
        .unwrap();
    let row = &rows[0];
    // The early synthetic query is slice index 0; its two fact occurrences
    // precede it in the derivation, not in source order.
    let mut trace = fixtures::unchecked_with_models(
        row.problem(),
        vec![1, 1, 0],
        vec![vec![], vec![], vec![0, 1]],
        [1, 1, 0, 1].map(|v| SmtValue::BitVec(v, 2)).into(),
        Vec::new(),
        &token,
    );
    assert!(authenticate_slice(&trace, row.problem(), &control(&token)).is_some());
    assert!(prepare(&trace, row.id(), &aggregate, &control(&token)).is_some());
    let original_pins = trace.replay_obligation().to_owned();
    let original_ptr = trace.bindings().as_ptr();
    let error = trace
        .lift_to_aggregate(row, &aggregate, remaining(deadline), &token)
        .unwrap_err();
    assert_eq!(error.trace().replay_obligation(), original_pins);
    assert_eq!(error.trace().source_smtlib(), row.problem().source_smtlib());
    assert_eq!(error.trace().bindings().as_ptr(), original_ptr);
    trace = error.into_trace();
    trace.bindings[0].value = SmtValue::BitVec(0, 2);
    fixtures::repin(row.problem(), &mut trace, &token);
    let lifted = trace
        .lift_to_aggregate(row, &aggregate, remaining(deadline), &token)
        .unwrap();
    assert_eq!(lifted.bindings().as_ptr(), original_ptr);
    assert!(lifted.recheck(&aggregate, remaining(deadline), &token));
}

fn model(value: u8) -> Vec<ScalarFunctionModel> {
    let sort = ay_core::Sort::bitvec(2);
    let args = [sort.clone()];
    ScalarFunctionModel::decode_smtlib(
        &format!("(model (define-fun f ((x (_ BitVec 2))) (_ BitVec 2) (_ bv{value} 2)))"),
        &[("f", args.as_slice(), &sort)],
    )
    .unwrap()
}

#[test]
#[timeout(180000)]
fn complete_function_is_moved_and_original_universal_premise_replayed() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(MEMORY));
    let deadline = Instant::now() + Duration::from_secs(120);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let aggregate = QuantifiedChcProblem::parse_smtlib(
        "(set-logic HORN)
         (declare-fun f ((_ BitVec 2)) (_ BitVec 2))
         (declare-fun P () Bool)
         (assert (=> (forall ((i (_ BitVec 2))) (= (f i) (_ bv0 2))) P))
         (assert (=> P false)) (check-sat)",
    )
    .unwrap();
    let rows = aggregate
        .query_obligations(remaining(deadline), &token)
        .unwrap();
    let row = &rows[0];
    for value in [1, 0] {
        let trace = fixtures::unchecked_with_models(
            row.problem(),
            vec![0],
            vec![vec![]],
            Vec::new(),
            model(value),
            &token,
        );
        let functions_ptr = trace.function_models().as_ptr();
        let definition_ptr = trace.function_models()[0].definition_smtlib().as_ptr();
        assert!(prepare(&trace, row.id(), &aggregate, &control(&token)).is_some());
        let result = trace.lift_to_aggregate(row, &aggregate, remaining(deadline), &token);
        if value == 1 {
            let original = result.unwrap_err().into_trace();
            assert_eq!(original.function_models().as_ptr(), functions_ptr);
            assert_eq!(original.clause_indices(), &[0]);
        } else {
            let lifted = result.unwrap();
            assert_eq!(lifted.function_models().as_ptr(), functions_ptr);
            assert_eq!(
                lifted.function_models()[0].definition_smtlib().as_ptr(),
                definition_ptr
            );
            assert_eq!(lifted.clause_indices(), &[0, 1]);
            assert_eq!(lifted.premise_steps(), &[vec![], vec![0]]);
            assert_eq!(lifted.replay_obligation().matches("(forall ((").count(), 1);
            assert!(lifted.recheck(&aggregate, remaining(deadline), &token));
        }
    }
}
