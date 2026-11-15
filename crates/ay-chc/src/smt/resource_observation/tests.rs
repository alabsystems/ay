// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn actual_memory_refusal_survives_context_reset_and_restricted_subsetup() {
    let observation = ScopedResourceObservation::install();
    {
        let _cap = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(1));
        let mut context = crate::smt::SmtContext::new();
        assert!(context.exact_term_memory_exceeded());
        context.reset();
    }
    assert_eq!(observation.first(), Some(ResourceRefusal::Memory));
    note_memory_refusal(false);
    observation.note(ResourceRefusal::Timeout);
    assert_eq!(observation.first(), Some(ResourceRefusal::Memory));
}

#[test]
fn nested_same_owner_refusal_is_shared_and_scope_restoration_is_sticky() {
    let outer = ScopedResourceObservation::install();
    {
        let inner = ScopedResourceObservation::install();
        note_memory_refusal(true);
        assert_eq!(inner.first(), Some(ResourceRefusal::Memory));
        assert_eq!(outer.first(), Some(ResourceRefusal::Memory));
    }
    note_memory_refusal(true);
    assert_eq!(outer.first(), Some(ResourceRefusal::Memory));
}

#[test]
fn unwind_restores_observation_and_fresh_attempt_has_no_old_refusal() {
    let outer = ScopedResourceObservation::install();
    let stopped = std::panic::catch_unwind(|| {
        let inner = ScopedResourceObservation::install();
        inner.note(ResourceRefusal::Cancelled);
        panic!("test-only observation unwind");
    });
    assert!(stopped.is_err());
    assert_eq!(outer.first(), Some(ResourceRefusal::Cancelled));
    note_memory_refusal(true);
    assert_eq!(outer.first(), Some(ResourceRefusal::Cancelled));
    drop(outer);
    let fresh = ScopedResourceObservation::install();
    assert_eq!(fresh.first(), None);
}

#[test]
fn executor_memory_reason_is_observed_but_bare_unknown_is_not_attributed() {
    let observation = ScopedResourceObservation::install();
    let caller = crate::CancellationToken::new();
    let _lane = crate::smt::deadline::ScopedLaneCancellation::install(caller.clone(), None);
    for reason in [
        None,
        Some(ay_dpll::UnknownReason::Incomplete),
        Some(ay_dpll::UnknownReason::Timeout),
        Some(ay_dpll::UnknownReason::Interrupted),
    ] {
        note_executor_refusal(reason);
        assert_eq!(observation.first(), None);
    }
    caller.cancel();
    note_executor_refusal(Some(ay_dpll::UnknownReason::Interrupted));
    caller.reset();
    assert_eq!(observation.first(), Some(ResourceRefusal::Cancelled));
    drop(observation);
    let memory = ScopedResourceObservation::install();
    note_executor_refusal(Some(ay_dpll::UnknownReason::MemoryLimit));
    assert_eq!(memory.first(), Some(ResourceRefusal::Memory));
}
