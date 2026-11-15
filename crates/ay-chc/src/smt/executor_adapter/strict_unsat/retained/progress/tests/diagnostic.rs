// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn healthy_debits_preserve_both_callback_polls_and_the_original_grant() {
    let calls = Cell::new(0usize);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    let mut owner =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    assert_eq!(calls.get(), 2);
    let original = owner.deadline();
    let before = (owner.work, owner.bytes);
    assert!(owner.charge(3, 5));
    assert_eq!(calls.get(), 4);
    assert_eq!((owner.work, owner.bytes), (before.0 + 3, before.1 + 5));
    assert_eq!(owner.deadline(), original);
    assert_eq!(owner.first_refusal, None);
    assert!(owner.check().is_ok());
    assert_eq!(calls.get(), 6);
}

#[test]
fn work_and_byte_ceiling_causes_precede_callback_and_never_reset() {
    for expected in [Refusal::WorkCeiling, Refusal::ByteCeiling] {
        let calls = Cell::new(0usize);
        let mut callback = || {
            calls.set(calls.get() + 1);
            true
        };
        let mut owner =
            RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
        if expected == Refusal::WorkCeiling {
            owner.max_work = owner.work;
        } else {
            owner.max_bytes = owner.bytes;
        }
        let before = (owner.work, owner.bytes, calls.get());
        assert!(!owner.charge(1, 1));
        assert_eq!(owner.first_refusal, Some(expected));
        assert_eq!((owner.work, owner.bytes, calls.get()), before);
        owner.max_work = usize::MAX;
        owner.max_bytes = usize::MAX;
        assert_eq!(owner.check(), Err(expected.message().to_string()));
        assert_eq!(calls.get(), before.2);
    }
}

#[test]
fn work_and_byte_overflow_causes_precede_callback_and_never_reset() {
    for expected in [Refusal::WorkOverflow, Refusal::ByteOverflow] {
        let calls = Cell::new(0usize);
        let mut callback = || {
            calls.set(calls.get() + 1);
            true
        };
        let mut owner =
            RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
        if expected == Refusal::WorkOverflow {
            owner.work = usize::MAX;
        } else {
            owner.bytes = usize::MAX;
        }
        let before = (owner.work, owner.bytes, calls.get());
        assert!(!owner.charge(1, 1));
        assert_eq!(owner.first_refusal, Some(expected));
        assert_eq!((owner.work, owner.bytes, calls.get()), before);
        owner.work = 0;
        owner.bytes = 0;
        assert_eq!(owner.check(), Err(expected.message().to_string()));
        assert_eq!(calls.get(), before.2);
    }
}

#[test]
fn simultaneous_overflow_and_ceiling_refusals_keep_the_original_work_precedence() {
    let mut callback = || true;
    let mut owner =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    owner.work = usize::MAX;
    owner.bytes = usize::MAX;
    assert!(!owner.charge(1, 1));
    assert_eq!(owner.first_refusal, Some(Refusal::WorkOverflow));

    let mut callback = || true;
    let mut owner =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    owner.max_work = owner.work;
    owner.max_bytes = owner.bytes;
    assert!(!owner.charge(1, 1));
    assert_eq!(owner.first_refusal, Some(Refusal::WorkCeiling));
}

#[test]
fn inherited_cancel_has_its_exact_cause_and_parent_reset_cannot_revive_it() {
    let parent = crate::CancellationToken::new();
    let cancellation = ReplayCancellation::new(&parent.child());
    let calls = Cell::new(0usize);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    let mut owner = RetainedReplayProgress::new(
        ReplayLimit::Cancellable {
            deadline: deadline(),
            cancellation: &cancellation,
        },
        &mut callback,
    )
    .unwrap();
    let before = calls.get();
    parent.cancel();
    assert_eq!(
        owner.check(),
        Err(Refusal::InheritedCancellation.message().to_string())
    );
    parent.reset();
    assert!(owner.check().is_err());
    assert_eq!(owner.first_refusal, Some(Refusal::InheritedCancellation));
    assert_eq!(calls.get(), before);
}

#[test]
fn original_limit_expiry_and_retained_legacy_wall_have_the_same_precise_cause() {
    let mut callback = || true;
    assert_eq!(
        RetainedReplayProgress::new(ReplayLimit::Until(Instant::now()), &mut callback).err(),
        Some(Refusal::OriginalDeadline.message().to_string())
    );
    let calls = Cell::new(0usize);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    let mut owner = RetainedReplayProgress::new(ReplayLimit::Legacy, &mut callback).unwrap();
    let before = calls.get();
    owner.deadline = Instant::now(); // Exercise the actual existing wall gate.
    assert_eq!(
        owner.check(),
        Err(Refusal::OriginalDeadline.message().to_string())
    );
    assert_eq!(calls.get(), before);
}

#[test]
fn captured_zero_memory_cause_does_not_become_callback_or_work_exhaustion() {
    let calls = Cell::new(0usize);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    let mut owner =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    let before = calls.get();
    owner.memory = ReplayMemory::capture(Some(0));
    assert_eq!(
        owner.check(),
        Err(Refusal::ZeroTermMemory.message().to_string())
    );
    assert_eq!(calls.get(), before);
}

struct ForcedMemory;
impl Drop for ForcedMemory {
    fn drop(&mut self) {
        ay_sys::force_process_memory_exceeded_for_testing(false);
    }
}

#[test]
fn actual_thread_local_process_memory_refusal_is_reported_without_global_reset() {
    let mut callback = || true;
    let mut owner =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    let _forced = ForcedMemory;
    ay_sys::force_process_memory_exceeded_for_testing(true);
    assert_eq!(
        owner.check(),
        Err(Refusal::TermOrProcessMemory.message().to_string())
    );
    assert_eq!(owner.first_refusal, Some(Refusal::TermOrProcessMemory));
}

#[test]
fn callback_false_at_either_existing_poll_is_exact_and_sticky() {
    for offset in [1, 2] {
        let calls = Cell::new(0usize);
        let stop = Cell::new(usize::MAX);
        let mut callback = || {
            calls.set(calls.get() + 1);
            calls.get() != stop.get()
        };
        let mut owner =
            RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
        let before = calls.get();
        stop.set(before + offset);
        assert!(!owner.charge(3, 5));
        assert_eq!(calls.get(), before + offset);
        assert_eq!(owner.first_refusal, Some(Refusal::CallbackReturnedFalse));
        stop.set(usize::MAX);
        assert_eq!(
            owner.check(),
            Err(Refusal::CallbackReturnedFalse.message().to_string())
        );
        assert_eq!(calls.get(), before + offset);
    }
}

#[test]
fn caught_callback_unwind_reports_only_nonreturn_at_either_existing_poll() {
    for offset in [1, 2] {
        let calls = Cell::new(0usize);
        let panic_at = Cell::new(usize::MAX);
        let mut callback = || {
            calls.set(calls.get() + 1);
            assert_ne!(calls.get(), panic_at.get(), "intentional callback unwind");
            true
        };
        let mut owner =
            RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
        let before = calls.get();
        panic_at.set(before + offset);
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| owner.charge(3, 5))).is_err()
        );
        assert_eq!(owner.first_refusal, Some(Refusal::CallbackDidNotReturn));
        panic_at.set(usize::MAX);
        assert_eq!(
            owner.check(),
            Err(Refusal::CallbackDidNotReturn.message().to_string())
        );
        assert_eq!(calls.get(), before + offset);
    }
}

#[test]
fn explicit_source_error_retains_its_returned_detail_and_never_becomes_resource_cause() {
    let parent = crate::CancellationToken::new();
    let cancellation = ReplayCancellation::new(&parent.child());
    let mut callback = || true;
    let mut owner = RetainedReplayProgress::new(
        ReplayLimit::Cancellable {
            deadline: deadline(),
            cancellation: &cancellation,
        },
        &mut callback,
    )
    .unwrap();
    let detail = String::from("specific original source inventory mismatch");
    assert_eq!(owner.refuse(&detail), detail);
    parent.cancel();
    assert_eq!(
        owner.check(),
        Err(Refusal::ExplicitSourceOrProof.message().to_string())
    );
    assert_eq!(owner.first_refusal, Some(Refusal::ExplicitSourceOrProof));
}

#[test]
fn later_operation_context_cannot_overwrite_the_first_resource_refusal() {
    let mut callback = || true;
    let mut owner =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    owner.max_bytes = owner.bytes;
    assert!(!owner.charge(0, 1));
    assert_eq!(
        owner.refuse("later transport context"),
        "later transport context"
    );
    assert_eq!(
        owner.check(),
        Err(Refusal::ByteCeiling.message().to_string())
    );
    assert_eq!(owner.first_refusal, Some(Refusal::ByteCeiling));
}
