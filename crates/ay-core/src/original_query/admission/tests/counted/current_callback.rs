// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::resource::{enter_check_stop, CheckStop, CheckStopScope};
use std::sync::Mutex;

#[test]
fn later_current_one_shot_stop_is_retained_and_terminal() {
    let owner = counted(10, 10);
    let armed = Arc::new(AtomicBool::new(true));
    let observed = Arc::clone(&armed);
    let scope = enter_check_stop(Arc::new(move || observed.swap(false, Ordering::SeqCst)));
    let expected = CountedAdmissionError::Original(OriginalAdmissionError::ObserverStopped);
    assert_eq!(owner.admit(1, 1), Err(expected));
    assert!(!armed.load(Ordering::SeqCst));
    drop(scope);
    assert_eq!(owner.clone().check(), Err(expected));
    assert_eq!(owner.usage().unwrap().work_admitted, 0);
}

fn removing_scope_owner() -> (CountedAdmission, Arc<Mutex<Option<CheckStopScope>>>) {
    let slot = Arc::new(Mutex::new(None::<CheckStopScope>));
    let observed = Arc::clone(&slot);
    let owner = CountedAdmission::new(
        FiniteAdmissionGrant::new(10, 10),
        None,
        Arc::new(move || {
            drop(observed.lock().unwrap().take());
            false
        }),
    )
    .unwrap();
    (owner, slot)
}

#[test]
fn original_observer_cannot_remove_a_later_current_callback_before_poll() {
    let (owner, scope) = removing_scope_owner();
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    *scope.lock().unwrap() = Some(enter_check_stop(Arc::new(move || {
        observed.fetch_add(1, Ordering::SeqCst);
        true
    })));
    let expected = CountedAdmissionError::Original(OriginalAdmissionError::ObserverStopped);
    assert_eq!(owner.admit(1, 1), Err(expected));
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert!(scope.lock().unwrap().is_none());
    assert_eq!(owner.check(), Err(expected));
}

#[test]
fn retained_ambient_refusal_prevents_later_current_callback_and_debit() {
    let slot = Arc::new(Mutex::new(None::<CountedAdmission>));
    let observed = Arc::clone(&slot);
    let ambient = enter_check_stop(Arc::new(move || {
        observed
            .lock()
            .unwrap()
            .as_ref()
            .unwrap()
            .refuse(CountedAdmissionError::StorageExhausted);
        false
    }));
    let owner = counted(10, 10);
    *slot.lock().unwrap() = Some(owner.clone());
    drop(ambient);
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let _current = enter_check_stop(Arc::new(move || {
        observed.fetch_add(1, Ordering::SeqCst);
        false
    }));
    assert_eq!(
        owner.admit(1, 1),
        Err(CountedAdmissionError::StorageExhausted)
    );
    assert_eq!(calls.load(Ordering::SeqCst), 0);
    assert_eq!(owner.usage().unwrap().work_admitted, 0);
    slot.lock().unwrap().take();
}

#[test]
fn current_identity_is_deduplicated_against_both_retained_callbacks() {
    for explicit_matches in [false, true] {
        let calls = Arc::new(AtomicUsize::new(0));
        let observed = Arc::clone(&calls);
        let callback: CheckStop = Arc::new(move || {
            observed.fetch_add(1, Ordering::SeqCst);
            false
        });
        let original = enter_check_stop(Arc::clone(&callback));
        let observer = if explicit_matches {
            Arc::clone(&callback)
        } else {
            Arc::new(|| false)
        };
        let owner = CountedAdmission::new(FiniteAdmissionGrant::new(2, 2), None, observer).unwrap();
        drop(original);
        let _current = enter_check_stop(callback);
        owner.admit(1, 1).unwrap();
        assert_eq!(calls.load(Ordering::SeqCst), 1);
        assert_eq!(owner.usage().unwrap().work_admitted, 1);
    }
}

#[test]
fn last_current_callback_cleanup_can_refuse_without_deadlocking_bookkeeping() {
    struct Cleanup(CountedAdmission);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            self.0.refuse(CountedAdmissionError::StorageExhausted);
        }
    }
    let (owner, scope) = removing_scope_owner();
    let cleanup = Cleanup(owner.clone());
    *scope.lock().unwrap() = Some(enter_check_stop(Arc::new(move || {
        let _keep_until_last_arc = &cleanup;
        false
    })));
    assert_eq!(
        owner.admit(1, 1),
        Err(CountedAdmissionError::StorageExhausted)
    );
    assert_eq!(owner.usage().unwrap().work_admitted, 0);
    assert_eq!(
        owner.clone().check(),
        Err(CountedAdmissionError::StorageExhausted)
    );
}

#[test]
fn first_observed_callback_stop_precedes_a_different_cleanup_refusal() {
    struct Cleanup(CountedAdmission);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            self.0.refuse(CountedAdmissionError::StorageExhausted);
        }
    }
    let (owner, scope) = removing_scope_owner();
    let cleanup = Cleanup(owner.clone());
    *scope.lock().unwrap() = Some(enter_check_stop(Arc::new(move || {
        let _keep_until_last_arc = &cleanup;
        true
    })));
    let expected = CountedAdmissionError::Original(OriginalAdmissionError::ObserverStopped);
    assert_eq!(owner.admit(1, 1), Err(expected));
    assert_eq!(owner.clone().check(), Err(expected));
    assert_eq!(owner.usage().unwrap().work_admitted, 0);
}

#[test]
fn last_current_callback_cleanup_memory_trip_prevents_admission() {
    struct Cleanup;
    impl Drop for Cleanup {
        fn drop(&mut self) {
            ay_sys::charge_current_for_testing(2048);
        }
    }
    let (owner, scope) = removing_scope_owner();
    let group = ay_sys::MemoryGroup::new(1024, usize::MAX, Arc::new(AtomicBool::new(false)));
    let _memory = ay_sys::enter_memory_group(group);
    let cleanup = Cleanup;
    *scope.lock().unwrap() = Some(enter_check_stop(Arc::new(move || {
        let _keep_until_last_arc = &cleanup;
        false
    })));
    assert_eq!(owner.admit(1, 1), Err(CountedAdmissionError::Memory));
    assert_eq!(owner.usage().unwrap().work_admitted, 0);
    assert_eq!(owner.clone().check(), Err(CountedAdmissionError::Memory));
}

#[test]
fn later_current_callback_panic_is_sticky_without_debit() {
    let owner = counted(10, 10);
    let scope = enter_check_stop(Arc::new(|| panic!("later caller callback")));
    let expected = CountedAdmissionError::Original(OriginalAdmissionError::ObserverPanicked);
    assert_eq!(owner.admit(1, 1), Err(expected));
    drop(scope);
    assert_eq!(owner.clone().check(), Err(expected));
    assert_eq!(owner.usage().unwrap().work_admitted, 0);
}
