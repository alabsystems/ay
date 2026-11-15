// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn source_with_function() -> QuantifiedChcProblem {
    let source = source("fill");
    QuantifiedChcProblem::parse_smtlib(&source.source_smtlib().replace(
        "(set-logic HORN)",
        "(set-logic HORN)\n(declare-fun unused (Bool) (_ BitVec 136))",
    ))
    .unwrap()
}

#[test]
fn preparation_borrows_the_complete_source_including_unused_function_declarations() {
    let source = source_with_function();
    let token = CancellationToken::new();
    let model = model(&source, &control(&token));
    validate(&source, &model, &control(&token)).unwrap();
    for index in 0..source.source_problem().clauses().len() {
        let prepared = prepare(&source, &model, index, &control(&token)).unwrap();
        assert!(std::ptr::eq(prepared.source, &source));
        assert_eq!(prepared.source.function_declarations().len(), 1);
        assert_eq!(
            prepared
                .obligation
                .smtlib
                .matches("(declare-fun unused ")
                .count(),
            1
        );
        assert!(prepared
            .obligation
            .smtlib
            .contains("(declare-fun unused (Bool) (_ BitVec 136))"));
        assert!(!prepared.obligation.smtlib.contains("(define-fun unused "));
    }
}

#[test]
#[ntest::timeout(90_000)]
fn a_contradictory_finite_hint_cannot_bypass_full_original_uf_discharge() {
    const MEMORY: usize = 128 * 1024 * 1024;
    let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(MEMORY));
    let deadline = Instant::now() + Duration::from_secs(60);
    let _deadline = crate::smt::ScopedSmtDeadline::install_until(deadline);
    let source = source_with_function();
    let token = CancellationToken::new();
    let live = SourceControl::new(deadline, &token);
    let mut model = model(&source, &live);
    let id = PredicateId::new(0);
    let mut interpretation = model.model.get(&id).unwrap().clone();
    // False is a well-typed but invalid candidate for a reachable source fact.
    // Its complete initiation counter-obligation is satisfiable: choose every
    // cell and fill false. The unused function has no constraints at all.
    interpretation.formula = ChcExpr::Bool(false);
    model.model.set(id, interpretation);
    validate(&source, &model, &live).unwrap();
    let mut prepared = prepare(&source, &model, 0, &live).unwrap();
    let script = prepared.obligation.smtlib.clone();
    let verdict = crate::smt::executor_adapter::smtlib_first_verdict_via_executor_with_limit(
        &script,
        crate::smt::executor_adapter::ReplayLimit::Cancellable {
            deadline,
            cancellation: &live.replay_cancellation,
        },
        Some(MEMORY),
    );
    assert_eq!(verdict.as_deref(), Some("sat"));
    // White-box fault injection only: production preparation never supplies
    // this inconsistent finite hint. The UF route must not grant it authority.
    prepared.finite_query = ChcExpr::Bool(false);
    assert!(!discharge(prepared, 1, &live));
    assert!(live.poll().is_some());
    assert!(Instant::now() < deadline);
}
