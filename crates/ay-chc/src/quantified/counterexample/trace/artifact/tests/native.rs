// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! These are native qualification tests, not passes from prepared fixtures.

use super::*;
use crate::quantified::QuantifiedChcResult;
use ntest::timeout;

const MEMORY: usize = 128 * 1024 * 1024;

fn remaining(deadline: Instant) -> Duration {
    deadline.saturating_duration_since(Instant::now())
}

#[test]
#[timeout(300000)]
fn native_acquired_trace_exports_and_imports_exact_same_complete_assignment() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(MEMORY));
    let deadline = Instant::now() + Duration::from_secs(240);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let (source, _) = fixtures::scalar(&token);
    let QuantifiedChcResult::Unsafe(base) = source.solve(
        remaining(deadline).min(Duration::from_secs(60)),
        Some(MEMORY),
        &token,
    ) else {
        panic!("source must have a native checked counterexample");
    };
    let trace = base
        .concrete_trace(&source, remaining(deadline), &token)
        .unwrap();
    let bytes = trace
        .export_artifact(&source, remaining(deadline), &token)
        .unwrap();
    let imported = source
        .validate_trace_artifact(&bytes, remaining(deadline), Some(MEMORY), &token)
        .unwrap();
    assert_eq!(
        imported.artifact_sha256(),
        transport::digest(&bytes, &control(&token)).unwrap()
    );
    assert_eq!(imported.trace().clause_indices(), trace.clause_indices());
    assert_eq!(imported.trace().premise_steps(), trace.premise_steps());
    assert_eq!(
        imported.trace().replay_obligation(),
        trace.replay_obligation()
    );
    let view = imported
        .trace()
        .view_for(&source, remaining(deadline), &token)
        .unwrap();
    assert_eq!(view.steps().count(), 3);
    assert_eq!(view.steps().map(|s| s.bindings().len()).sum::<usize>(), 4);
    assert_eq!(
        imported
            .into_trace()
            .export_artifact(&source, remaining(deadline), &token)
            .unwrap(),
        bytes
    );
}

#[test]
#[timeout(180000)]
fn recomputed_digest_cannot_admit_unsatisfying_saved_values_or_choose_another_model() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(MEMORY));
    let deadline = Instant::now() + Duration::from_secs(120);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let (source, mut trace) = fixtures::scalar(&token);
    let original = trace
        .export_artifact(&source, remaining(deadline), &token)
        .unwrap();
    trace.bindings[0].value = SmtValue::BitVec(1, 2);
    fixtures::repin(&source, &mut trace, &token);
    let wire = fixtures::wire(&source, &trace, &token);
    let bytes = transport::encode(&wire, &control(&token)).unwrap();
    assert!(rebuild::prepare(&source, &wire, &control(&token)).is_some());
    assert!(source
        .validate_trace_artifact(&bytes, remaining(deadline), Some(MEMORY), &token)
        .is_err());
    assert!(trace
        .export_artifact(&source, remaining(deadline), &token)
        .is_err());
    assert!(source
        .validate_trace_artifact(&original, remaining(deadline), Some(MEMORY), &token)
        .is_ok());
}

#[test]
#[timeout(180000)]
fn changed_total_function_with_recomputed_digest_must_replay_original_forall() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(MEMORY));
    let deadline = Instant::now() + Duration::from_secs(120);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let source = QuantifiedChcProblem::parse_smtlib(
        "(set-logic HORN)
         (declare-fun f ((_ BitVec 2)) (_ BitVec 2))
         (declare-fun P () Bool)
         (assert (=> (forall ((i (_ BitVec 2))) (= (f i) (_ bv0 2))) P))
         (assert (=> P false)) (check-sat)",
    )
    .unwrap();
    let sort = ay_core::Sort::bitvec(2);
    let args = [sort.clone()];
    let expected = [("f", args.as_slice(), &sort)];
    let models = ScalarFunctionModel::decode_smtlib(
        "(model (define-fun f ((x (_ BitVec 2))) (_ BitVec 2) (_ bv0 2)))",
        &expected,
    )
    .unwrap();
    let mut trace = fixtures::unchecked_with_models(
        &source,
        vec![0, 1],
        vec![vec![], vec![0]],
        Vec::new(),
        models,
        &token,
    );
    let original = trace
        .export_artifact(&source, remaining(deadline), &token)
        .unwrap();
    assert!(source
        .validate_trace_artifact(&original, remaining(deadline), Some(MEMORY), &token)
        .is_ok());
    trace.functions = ScalarFunctionModel::decode_smtlib(
        "(model (define-fun f ((x (_ BitVec 2))) (_ BitVec 2) (_ bv1 2)))",
        &expected,
    )
    .unwrap();
    fixtures::repin(&source, &mut trace, &token);
    let wire = fixtures::wire(&source, &trace, &token);
    assert!(rebuild::prepare(&source, &wire, &control(&token)).is_some());
    let changed = transport::encode(&wire, &control(&token)).unwrap();
    assert!(source
        .validate_trace_artifact(&changed, remaining(deadline), Some(MEMORY), &token)
        .is_err());
}
