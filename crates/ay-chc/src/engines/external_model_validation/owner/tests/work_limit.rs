// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn guard_work_exhaustion_has_a_distinct_non_verdict_kind() {
    assert_eq!(from_guard(Exhausted::Rlimit), Kind::WorkLimit);
    for other in [
        Kind::Valid,
        Kind::Refuted,
        Kind::Rejected,
        Kind::Timeout,
        Kind::Cancelled,
        Kind::Memory,
        Kind::Inconclusive,
    ] {
        assert_ne!(from_guard(Exhausted::Rlimit), other);
    }
}

#[test]
fn exhausted_capture_skips_phase_and_full_original_model_validation() {
    let mut original = guard();
    original.set_rlimit(Some(0));
    let owner = ExternalInvariantValidationOwner::capture(&original, &configured());
    let ticks = original.ticks();
    let calls = AtomicUsize::new(0);
    assert_eq!(
        owner
            .with_resources(|| {
                calls.fetch_add(1, Ordering::Relaxed);
                Ok(Kind::Valid)
            })
            .unwrap(),
        Err(Kind::WorkLimit)
    );
    let (problem, model) = fixture();
    assert_eq!(
        validate_external_invariant_model_with_owner(&problem, &model, &configured(), &owner)
            .unwrap(),
        Kind::WorkLimit
    );
    assert_eq!(calls.load(Ordering::Relaxed), 0);
    assert_eq!(original.ticks(), ticks);
}

#[test]
fn completed_phase_value_is_withheld_after_actual_shared_work_exhaustion() {
    let mut original = guard();
    original.set_rlimit(Some(1_000));
    let owner = ExternalInvariantValidationOwner::capture(&original, &configured());
    let entered = AtomicUsize::new(0);
    let result = owner
        .with_resources(|| {
            entered.fetch_add(1, Ordering::Relaxed);
            assert_eq!(original.tick(1_000), Err(Exhausted::Rlimit));
            Ok(Kind::Valid)
        })
        .unwrap();
    assert_eq!(entered.load(Ordering::Relaxed), 1);
    assert_eq!(result, Err(Kind::WorkLimit));
    assert_eq!(owner.check(), Some(Kind::WorkLimit));
    let ticks = original.ticks();
    assert_eq!(
        owner.with_resources(|| Ok(Kind::Refuted)).unwrap(),
        Err(Kind::WorkLimit)
    );
    assert_eq!(original.ticks(), ticks);
}

#[test]
fn worker_clone_preserves_exhaustion_without_starting_a_new_allowance() {
    let mut original = guard();
    original.set_rlimit(Some(3));
    let owner = ExternalInvariantValidationOwner::capture(&original, &configured());
    let worker = owner.clone();
    assert_eq!(
        std::thread::spawn(move || {
            assert_eq!(worker.check(), None);
            assert_eq!(worker.check(), Some(Kind::WorkLimit));
            worker.with_resources(|| Ok(17)).unwrap()
        })
        .join()
        .unwrap(),
        Err(Kind::WorkLimit)
    );
    assert_eq!(original.ticks(), 3);
    assert_eq!(owner.check(), Some(Kind::WorkLimit));
    assert_eq!(original.ticks(), 3);
}

#[test]
fn first_work_refusal_survives_later_cancel_and_caller_view_changes() {
    let caller = CancellationToken::new();
    let mut original = guard();
    original.set_rlimit(Some(0));
    let owner = ExternalInvariantValidationOwner::capture(
        &original,
        &configured().with_cancellation_token(Some(caller.clone())),
    );
    assert_eq!(owner.check(), Some(Kind::WorkLimit));
    caller.cancel();
    original.set_rlimit(None);
    assert_eq!(owner.check(), Some(Kind::WorkLimit));
    caller.reset();
    assert_eq!(owner.clone().check(), Some(Kind::WorkLimit));
    // A genuinely separate original invocation has its own healthy owner.
    let fresh = ExternalInvariantValidationOwner::capture(&guard(), &configured());
    assert_eq!(fresh.check(), None);
}

#[test]
fn an_earlier_cancellation_or_opaque_stop_is_not_relabelled_as_work() {
    let caller = CancellationToken::new();
    caller.cancel();
    let mut original = guard();
    original.set_rlimit(Some(0));
    let cancelled = ExternalInvariantValidationOwner::capture(
        &original,
        &configured().with_cancellation_token(Some(caller.clone())),
    );
    assert_eq!(cancelled.check(), Some(Kind::Cancelled));
    caller.reset();
    assert_eq!(cancelled.check(), Some(Kind::Cancelled));

    let scope = ay_core::resource::enter_check_stop(Arc::new(|| true));
    let mut other = guard();
    other.set_rlimit(Some(1_000));
    let opaque = ExternalInvariantValidationOwner::capture(&other, &configured());
    assert_eq!(opaque.check(), Some(Kind::Inconclusive));
    drop(scope);
    assert_eq!(other.tick(1_000), Err(Exhausted::Rlimit));
    assert_eq!(opaque.check(), Some(Kind::Inconclusive));
}

#[test]
fn a_genuine_phase_error_remains_an_error_even_after_work_exhaustion() {
    let mut original = guard();
    original.set_rlimit(Some(1_000));
    let owner = ExternalInvariantValidationOwner::capture(&original, &configured());
    let result = owner.with_resources(|| -> ChcResult<()> {
        assert_eq!(original.tick(1_000), Err(Exhausted::Rlimit));
        Err(ChcError::Internal("work-limit error control".to_owned()))
    });
    assert!(
        matches!(result, Err(ChcError::Internal(message)) if message == "work-limit error control")
    );
    assert_eq!(owner.check(), Some(Kind::WorkLimit));
}
