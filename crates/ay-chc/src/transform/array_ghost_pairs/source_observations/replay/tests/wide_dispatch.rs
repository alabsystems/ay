// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
#[ntest::timeout(90_000)]
fn a_wide_uf_free_source_cannot_be_discharged_by_a_false_finite_hint() {
    const MEMORY: usize = 128 * 1024 * 1024;
    let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(MEMORY));
    let deadline = Instant::now() + Duration::from_secs(60);
    let _deadline = crate::smt::ScopedSmtDeadline::install_until(deadline);
    let source = QuantifiedChcProblem::parse_smtlib(
        "(set-logic HORN)
         (declare-rel P ((Array (_ BitVec 136) (_ BitVec 8))))
         (declare-rel error ())
         (declare-var table (Array (_ BitVec 136) (_ BitVec 8)))
         (rule (=> (= table ((as const (Array (_ BitVec 136) (_ BitVec 8))) (_ bv0 8))) (P table)))
         (rule (=> (P table) error)) (query error)",
    )
    .unwrap();
    assert!(source.function_declarations().is_empty());
    let token = CancellationToken::new();
    let live = SourceControl::new(deadline, &token);
    let layout = super::super::super::Layout::analyze(&source, &live).unwrap();
    let mut interpretations = InvariantModel::new();
    for predicate in source.source_problem().predicates() {
        interpretations.set(
            predicate.id,
            PredicateInterpretation::new(
                layout.canonical(predicate.id).unwrap().to_vec(),
                ChcExpr::Bool(false),
            ),
        );
    }
    let model = ObservationModel {
        layout,
        model: interpretations,
    };
    validate(&source, &model, &live).unwrap();
    let mut prepared = prepare(&source, &model, 0, &live).unwrap();
    assert!(prepared.full_source_only);
    let verdict = crate::smt::executor_adapter::smtlib_first_verdict_via_executor_with_limit(
        &prepared.obligation.smtlib,
        crate::smt::executor_adapter::ReplayLimit::Cancellable {
            deadline,
            cancellation: &live.replay_cancellation,
        },
        Some(MEMORY),
    );
    assert_eq!(verdict.as_deref(), Some("sat"));
    prepared.finite_query = ChcExpr::Bool(false); // White-box fault injection only.
    assert!(!discharge(prepared, 1, &live));
    assert!(live.poll().is_some());
    assert!(Instant::now() < deadline);
}
