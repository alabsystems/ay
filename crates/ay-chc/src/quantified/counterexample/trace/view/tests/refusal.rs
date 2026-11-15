// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn complete_source_including_unused_declarations_and_binder_order_is_required() {
    let source = source(Change::None);
    let token = CancellationToken::new();
    let trace = unchecked_trace(&source, &token);
    for change in [
        Change::UnusedRecord,
        Change::UnusedPredicate,
        Change::Premise,
        Change::BinderOrder,
    ] {
        let different = fixtures::source(change);
        assert_ne!(source.source_smtlib(), different.source_smtlib());
        assert!(trace
            .view_for(&different, Duration::from_secs(30), &token)
            .is_none());
    }
    assert!(trace
        .view_for(&source, Duration::from_secs(30), &token)
        .is_some());
}

#[test]
fn private_forged_membership_topology_and_pin_mutations_cannot_join() {
    let source = source(Change::None);
    let token = CancellationToken::new();
    let check = |trace: &QuantifiedChcTrace| {
        trace
            .view_for(&source, Duration::from_secs(30), &token)
            .is_none()
    };
    let mut trace = unchecked_trace(&source, &token);
    trace.bindings.pop();
    assert!(check(&trace));
    let mut trace = unchecked_trace(&source, &token);
    trace.bindings.swap(0, 3);
    assert!(check(&trace));
    let mut trace = unchecked_trace(&source, &token);
    trace.bindings[0].variable.name.push_str("_foreign");
    assert!(check(&trace));
    let mut trace = unchecked_trace(&source, &token);
    trace.bindings[0].value = SmtValue::Bool(false);
    assert!(check(&trace));
    let mut trace = unchecked_trace(&source, &token);
    trace.bindings[2].value = SmtValue::BitVec(0, 3);
    assert!(check(&trace));
    let mut trace = unchecked_trace(&source, &token);
    trace.base.premise_steps[2].swap(0, 1);
    assert!(check(&trace));
    let mut trace = unchecked_trace(&source, &token);
    trace.base.clause_indices[0] = usize::MAX;
    assert!(check(&trace));
    let mut trace = unchecked_trace(&source, &token);
    trace.pinned_obligation.push_str("; changed");
    assert!(check(&trace));
}

#[test]
fn controls_refuse_without_renewing_any_evidence_and_allow_fresh_retry() {
    let source = source(Change::None);
    let token = CancellationToken::new();
    let trace = unchecked_trace(&source, &token);
    assert!(trace.view_for(&source, Duration::ZERO, &token).is_none());
    assert!(trace.view_for(&source, Duration::MAX, &token).is_none());
    {
        let _deadline = ScopedSmtDeadline::install_until(Instant::now());
        assert!(trace
            .view_for(&source, Duration::from_secs(30), &token)
            .is_none());
    }
    let stopped = control(&token);
    token.cancel();
    assert!(authenticate(&trace, &source, &stopped).is_none());
    assert!(trace
        .view_for(&source, Duration::from_secs(30), &token)
        .is_none());
    token.reset();
    assert!(authenticate(&trace, &source, &stopped).is_none());
    assert!(trace
        .view_for(&source, Duration::from_secs(30), &token)
        .is_some());
    let exhausted = control(&token);
    exhausted.bytes(64 * 1024 * 1024).unwrap();
    assert!(authenticate(&trace, &source, &exhausted).is_none());
    assert!(authenticate(&trace, &source, &exhausted).is_none());
    assert!(authenticate(&trace, &source, &control(&token)).is_some());
    assert!(!token.is_cancelled());
}

#[test]
fn zero_term_allowance_cannot_be_widened_by_a_no_solver_join() {
    let source = source(Change::None);
    let token = CancellationToken::new();
    let mut trace = unchecked_trace(&source, &token);
    {
        let _memory = SmtContext::scoped_thread_term_memory_budget(Some(0));
        assert!(trace
            .view_for(&source, Duration::from_secs(30), &token)
            .is_none());
    }
    trace.base.memory_budget = Some(0);
    assert!(trace
        .view_for(&source, Duration::from_secs(30), &token)
        .is_none());
    trace.base.memory_budget = Some(128 * 1024 * 1024);
    assert!(trace
        .view_for(&source, Duration::from_secs(30), &token)
        .is_some());
}
