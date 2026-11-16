// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn none_cannot_erase_caller_term_cap_after_caller_scope_drop_and_worker_move() {
    let original = guard();
    let config = configured().with_memory_budget(None);
    let scope = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(0));
    let owner = ExternalInvariantValidationOwner::capture(&original, &config);
    assert_eq!(owner.memory_budget(), Some(0));
    drop(scope);
    let result = std::thread::spawn(move || owner.with_resources(|| Ok(17)))
        .join()
        .unwrap()
        .unwrap();
    assert_eq!(result, Err(Kind::Memory));
}

#[test]
fn explicit_zero_refuses_before_phase_even_with_fresh_worker_defaults() {
    let original = guard();
    let owner = ExternalInvariantValidationOwner::capture(
        &original,
        &configured().with_memory_budget(Some(0)),
    );
    let worker = owner.clone();
    let calls = Arc::new(AtomicUsize::new(0));
    let count = Arc::clone(&calls);
    let result = std::thread::spawn(move || {
        worker.with_resources(|| {
            count.fetch_add(1, Ordering::Relaxed);
            Ok(17)
        })
    })
    .join()
    .unwrap()
    .unwrap();
    assert_eq!(result, Err(Kind::Memory));
    assert_eq!(calls.load(Ordering::Relaxed), 0);
    assert_eq!(owner.check(), Some(Kind::Memory));
}

#[test]
fn original_group_shed_survives_scope_drop_replacement_and_cancel_reset() {
    let cancel = Arc::new(AtomicBool::new(false));
    let group = ay_sys::MemoryGroup::new(usize::MAX, usize::MAX, Arc::clone(&cancel));
    let weak = Arc::downgrade(&group);
    let scope = ay_sys::enter_memory_group(Arc::clone(&group));
    let original = guard();
    let owner = ExternalInvariantValidationOwner::capture(&original, &configured());
    assert!(group.shed());
    drop(scope);
    drop(group);
    cancel.store(false, Ordering::Relaxed);
    assert!(weak.upgrade().is_none());
    let worker = owner.clone();
    assert_eq!(
        std::thread::spawn(move || {
            let _healthy = ay_sys::enter_memory_group(ay_sys::MemoryGroup::new(
                usize::MAX,
                usize::MAX,
                Arc::new(AtomicBool::new(false)),
            ));
            worker.with_resources(|| Ok(17))
        })
        .join()
        .unwrap()
        .unwrap(),
        Err(Kind::Memory)
    );
    assert_eq!(owner.check(), Some(Kind::Memory));
}

#[test]
fn already_observed_tls_memory_is_copied_before_drop_not_reset_on_worker() {
    let observation = ScopedResourceObservation::install();
    observation.note(ResourceRefusal::Memory);
    let original = guard();
    let owner = ExternalInvariantValidationOwner::capture(&original, &configured());
    drop(observation);
    assert_eq!(
        std::thread::spawn(move || owner.check()).join().unwrap(),
        Some(Kind::Memory)
    );
}

#[test]
fn phase_resource_refusal_survives_internal_error_without_reclassifying_the_error() {
    let original = guard();
    let owner = ExternalInvariantValidationOwner::capture(&original, &configured());
    let result: ChcResult<Result<(), Kind>> = owner.with_resources(|| {
        crate::smt::resource_observation::note_memory_refusal(true);
        Err(ChcError::Internal("exact original error".into()))
    });
    assert!(
        matches!(result, Err(ChcError::Internal(ref reason)) if reason == "exact original error")
    );
    assert_eq!(owner.check(), Some(Kind::Memory));
}
#[test]
fn shorter_caller_ambient_wall_is_retained_after_scope_drop_on_worker() {
    let original = guard();
    let scope = crate::smt::ScopedSmtDeadline::install_until(
        Instant::now()
            .checked_sub(Duration::from_secs(1))
            .expect("fixture instant supports a one-second offset"),
    );
    let owner = ExternalInvariantValidationOwner::capture(&original, &configured());
    drop(scope);
    assert_eq!(
        std::thread::spawn(move || owner.with_resources(|| Ok(17)))
            .join()
            .unwrap()
            .unwrap(),
        Err(Kind::Timeout)
    );
}

#[test]
fn tighter_worker_cap_is_never_overwritten_and_refusal_survives_worker_cleanup() {
    let original = guard();
    let owner = ExternalInvariantValidationOwner::capture(&original, &configured());
    let worker = owner.clone();
    assert_eq!(
        std::thread::spawn(move || {
            let scope = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(0));
            let answer = worker.with_resources(|| Ok(17));
            assert_eq!(
                crate::smt::SmtContext::current_thread_term_memory_budget(),
                Some(0)
            );
            drop(scope);
            answer
        })
        .join()
        .unwrap()
        .unwrap(),
        Err(Kind::Memory)
    );
    assert_eq!(owner.check(), Some(Kind::Memory));
}

#[test]
fn worker_group_refusal_is_folded_before_dropped_scope_and_healthy_replacement() {
    let original = guard();
    let owner = ExternalInvariantValidationOwner::capture(&original, &configured());
    let worker = owner.clone();
    let result = std::thread::spawn(move || {
        let cancel = Arc::new(AtomicBool::new(false));
        let group = ay_sys::MemoryGroup::new(usize::MAX, usize::MAX, Arc::clone(&cancel));
        let scope = ay_sys::enter_memory_group(Arc::clone(&group));
        let answer = worker.with_resources(|| {
            assert!(group.shed());
            drop(scope);
            drop(group);
            cancel.store(false, Ordering::Relaxed);
            let _replacement = ay_sys::enter_memory_group(ay_sys::MemoryGroup::new(
                usize::MAX,
                usize::MAX,
                Arc::new(AtomicBool::new(false)),
            ));
            Ok(17)
        });
        answer
    })
    .join()
    .unwrap()
    .unwrap();
    assert_eq!(result, Err(Kind::Memory));
    assert_eq!(owner.check(), Some(Kind::Memory));
}
