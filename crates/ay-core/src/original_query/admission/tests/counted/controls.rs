// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::resource::{enter_check_stop, ChildSpec, Exhausted, Guard, NodeLabel};

#[test]
fn original_callback_survives_scope_removal_and_one_shot_reset() {
    let armed = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&armed);
    let scope = enter_check_stop(Arc::new(move || observed.swap(false, Ordering::SeqCst)));
    let owner = counted(10, 10);
    drop(scope);
    let _replacement = enter_check_stop(Arc::new(|| false));
    armed.store(true, Ordering::SeqCst);
    let expected = CountedAdmissionError::Original(OriginalAdmissionError::ObserverStopped);
    assert_eq!(owner.admit(1, 1), Err(expected));
    assert!(!armed.load(Ordering::SeqCst));
    assert_eq!(owner.clone().check(), Err(expected));
}

#[test]
fn identical_explicit_and_ambient_callback_is_polled_once_per_admission() {
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let callback: CheckStop = Arc::new(move || {
        observed.fetch_add(1, Ordering::SeqCst);
        false
    });
    let _scope = enter_check_stop(Arc::clone(&callback));
    let owner = CountedAdmission::new(FiniteAdmissionGrant::new(2, 2), None, callback).unwrap();
    assert_eq!(calls.load(Ordering::SeqCst), 0);
    owner.admit(2, 2).unwrap();
    assert_eq!(calls.load(Ordering::SeqCst), 1);
}

#[test]
fn explicit_observer_refusal_prevents_later_ambient_callback_and_debit() {
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let _ambient = enter_check_stop(Arc::new(move || {
        observed.fetch_add(1, Ordering::SeqCst);
        false
    }));
    let slot = Arc::new(std::sync::Mutex::new(None::<CountedAdmission>));
    let observed = Arc::clone(&slot);
    let owner = CountedAdmission::new(
        FiniteAdmissionGrant::new(3, 4),
        None,
        Arc::new(move || {
            let owner = observed.lock().unwrap().as_ref().unwrap().clone();
            owner.refuse(CountedAdmissionError::StorageExhausted);
            false
        }),
    )
    .unwrap();
    *slot.lock().unwrap() = Some(owner.clone());
    assert_eq!(
        owner.admit(1, 1),
        Err(CountedAdmissionError::StorageExhausted)
    );
    assert_eq!(calls.load(Ordering::SeqCst), 0);
    assert_eq!(owner.usage().unwrap().work_admitted, 0);
    slot.lock().unwrap().take();
}

#[test]
fn same_guard_is_debited_once_and_original_survives_an_unrelated_replacement() {
    let original = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(10)));
    let scope = original.enter();
    let owner = counted(20, 20);
    owner.admit(3, 1).unwrap();
    assert_eq!(original.ticks(), 3);
    drop(scope);
    let replacement = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(20)));
    let replacement_scope = replacement.enter();
    owner.admit(6, 1).unwrap();
    assert_eq!(original.ticks(), 9);
    assert_eq!(replacement.ticks(), 6);
    assert_eq!(
        owner.admit(1, 1),
        Err(CountedAdmissionError::Guard(Exhausted::Rlimit))
    );
    drop(replacement_scope);
    assert_eq!(
        owner.clone().check(),
        Err(CountedAdmissionError::Guard(Exhausted::Rlimit))
    );
    assert_eq!(owner.usage().unwrap().work_admitted, 9);
}

#[test]
fn original_memory_refusal_survives_group_replacement_and_cancel_reset() {
    let cancelled = Arc::new(AtomicBool::new(false));
    let group = ay_sys::MemoryGroup::new(1024, usize::MAX, Arc::clone(&cancelled));
    let scope = ay_sys::enter_memory_group(group);
    let owner = counted(20, 20);
    ay_sys::charge_current_for_testing(2048);
    drop(scope);
    cancelled.store(false, Ordering::SeqCst);
    let replacement =
        ay_sys::MemoryGroup::new(usize::MAX, usize::MAX, Arc::new(AtomicBool::new(false)));
    let _replacement = ay_sys::enter_memory_group(replacement);
    assert_eq!(owner.admit(1, 1), Err(CountedAdmissionError::Memory));
    assert_eq!(owner.clone().check(), Err(CountedAdmissionError::Memory));
    assert_eq!(owner.usage().unwrap().work_admitted, 0);
}

#[test]
fn scratch_cleanup_memory_trip_vetoes_success_under_the_same_owner() {
    struct Scratch;
    impl Drop for Scratch {
        fn drop(&mut self) {
            ay_sys::charge_current_for_testing(2048);
        }
    }
    let group = ay_sys::MemoryGroup::new(1024, usize::MAX, Arc::new(AtomicBool::new(false)));
    let scope = ay_sys::enter_memory_group(group);
    let owner = counted(20, 20);
    assert_eq!(
        owner.with_work(|work| {
            work.admit(3, 4)?;
            let _scratch = Scratch;
            Ok(17)
        }),
        Err(CountedAdmissionError::Memory)
    );
    drop(scope);
    let usage = owner.usage().unwrap();
    assert_eq!((usage.work_admitted, usage.storage_admitted), (3, 4));
    assert_eq!(owner.clone().check(), Err(CountedAdmissionError::Memory));
}

#[test]
fn counted_callback_and_operation_panics_are_terminal_across_clones() {
    let owner = CountedAdmission::new(
        FiniteAdmissionGrant::new(3, 4),
        None,
        Arc::new(|| panic!("counted observer")),
    )
    .unwrap();
    let expected = CountedAdmissionError::Original(OriginalAdmissionError::ObserverPanicked);
    assert_eq!(owner.check(), Err(expected));
    assert_eq!(owner.clone().admit(1, 1), Err(expected));
    let owner = counted(3, 4);
    let expected = CountedAdmissionError::Original(OriginalAdmissionError::OperationPanicked);
    assert_eq!(
        owner.with_work::<()>(|work| {
            work.admit(2, 3)?;
            panic!("counted operation");
        }),
        Err(expected)
    );
    assert_eq!(owner.clone().check(), Err(expected));
    assert_eq!(owner.usage().unwrap().work_admitted, 2);
}
