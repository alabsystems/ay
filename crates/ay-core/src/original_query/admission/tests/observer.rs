// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::original_query::StopReason;

#[test]
fn observed_original_raw_stop_stays_terminal_after_flag_reset() {
    let (owner, raw) = stopped_flag(10, 10);
    owner.check().expect("original open");
    raw.store(true, Ordering::SeqCst);
    assert_eq!(owner.check(), Err(OriginalAdmissionError::ObserverStopped));
    raw.store(false, Ordering::SeqCst);
    assert_eq!(
        owner.clone().check(),
        Err(OriginalAdmissionError::ObserverStopped)
    );
    assert!(owner.with_work(|_| Ok(())).is_err());
    // Only an explicit different invocation gets a different grant/latch.
    healthy(10, 10)
        .with_work(|work| work.admit(10, 10))
        .expect("new owner");
}

#[test]
fn expired_original_end_is_immutable_and_terminal_across_clones() {
    let deadline = Instant::now();
    let called = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&called);
    let owner = OriginalAdmission::new(
        FiniteAdmissionGrant::new(10, 10),
        deadline,
        Arc::new(move || {
            observed.fetch_add(1, Ordering::SeqCst);
            false
        }),
    );
    let expected = OriginalAdmissionError::Query(QueryError::Interrupted(StopReason::Deadline));
    assert_eq!(owner.deadline(), deadline);
    assert_eq!(owner.clone().with_work(|_| Ok(())), Err(expected));
    assert_eq!(owner.check(), Err(expected));
    assert_eq!(called.load(Ordering::SeqCst), 0);
    assert_eq!(balances(&owner), (10, 10));
}

#[test]
fn observer_panic_is_terminal_without_poisoning_or_retrying_callback() {
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let owner = OriginalAdmission::new(
        FiniteAdmissionGrant::new(10, 10),
        end(),
        Arc::new(move || {
            observed.fetch_add(1, Ordering::SeqCst);
            panic!("test observer panic")
        }),
    );
    assert_eq!(owner.check(), Err(OriginalAdmissionError::ObserverPanicked));
    assert_eq!(
        owner.clone().check(),
        Err(OriginalAdmissionError::ObserverPanicked)
    );
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_eq!(balances(&owner), (10, 10));
}

#[test]
fn observer_unwind_cleanup_cannot_renew_a_clone_or_hide_the_panic_cause() {
    struct Cleanup(OriginalAdmission, Arc<AtomicBool>);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            assert_eq!(
                self.0.check(),
                Err(OriginalAdmissionError::ObserverPanicked)
            );
            self.1.store(true, Ordering::SeqCst);
        }
    }
    let slot = Arc::new(std::sync::Mutex::new(None::<OriginalAdmission>));
    let observed = Arc::clone(&slot);
    let cleaned = Arc::new(AtomicBool::new(false));
    let observed_cleaned = Arc::clone(&cleaned);
    let owner = OriginalAdmission::new(
        FiniteAdmissionGrant::new(10, 10),
        end(),
        Arc::new(move || {
            let owner = observed.lock().expect("test slot").as_ref().cloned();
            let _cleanup = Cleanup(owner.expect("test owner"), Arc::clone(&observed_cleaned));
            panic!("test observer unwind");
        }),
    );
    *slot.lock().expect("test slot") = Some(owner.clone());
    assert_eq!(owner.check(), Err(OriginalAdmissionError::ObserverPanicked));
    assert!(cleaned.load(Ordering::SeqCst));
    assert!(owner.clone().check().is_err());
    slot.lock().expect("test slot").take();
}

#[test]
fn caught_operation_unwind_folds_into_shared_terminal_state() {
    let owner = healthy(10, 10);
    assert_eq!(
        owner.with_work::<()>(|work| {
            work.admit(2, 3)?;
            panic!("test operation unwind")
        }),
        Err(OriginalAdmissionError::OperationPanicked)
    );
    assert_eq!(balances(&owner), (8, 7));
    assert_eq!(
        owner.clone().check(),
        Err(OriginalAdmissionError::OperationPanicked)
    );
}

#[test]
fn operation_unwind_cleanup_cannot_admit_through_a_live_clone() {
    struct Cleanup(OriginalAdmission, Arc<AtomicBool>);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            assert_eq!(
                self.0.check(),
                Err(OriginalAdmissionError::OperationPanicked)
            );
            self.1.store(true, Ordering::SeqCst);
        }
    }
    let owner = healthy(10, 10);
    let cleaned = Arc::new(AtomicBool::new(false));
    let result = owner.with_work::<()>(|work| {
        work.admit(2, 3)?;
        let _cleanup = Cleanup(owner.clone(), Arc::clone(&cleaned));
        panic!("test operation cleanup unwind");
    });
    assert_eq!(result, Err(OriginalAdmissionError::OperationPanicked));
    assert!(cleaned.load(Ordering::SeqCst));
    assert_eq!(balances(&owner), (8, 7));
    assert!(owner.clone().check().is_err());
}

#[test]
fn private_refusal_notifier_panic_cannot_renew_the_scoped_owner() {
    let owner = healthy(10, 10);
    let result = owner.with_work::<()>(|_| {
        let mut sink = |work, bytes| {
            owner
                .inner
                .admit(work, bytes)
                .map_err(OriginalAdmissionError::adapter_error)
        };
        let mut notifier = |_| panic!("test private notifier panic");
        let mut injected = WorkBudget::with_owner_admission(10, &mut sink, &mut notifier);
        injected.refuse_exhaustion();
        Ok(())
    });
    assert_eq!(result, Err(OriginalAdmissionError::OperationPanicked));
    assert_eq!(
        owner.clone().check(),
        Err(OriginalAdmissionError::OperationPanicked)
    );
    assert_eq!(balances(&owner), (10, 10));
}

#[test]
fn observer_recursion_refuses_without_holding_a_deadlock_prone_lock() {
    let slot = Arc::new(std::sync::Mutex::new(None::<OriginalAdmission>));
    let observed = Arc::clone(&slot);
    let owner = OriginalAdmission::new(
        FiniteAdmissionGrant::new(10, 10),
        end(),
        Arc::new(move || {
            let nested = observed.lock().expect("test slot").as_ref().cloned();
            assert_eq!(
                nested.expect("test original owner").check(),
                Err(OriginalAdmissionError::Reentrant)
            );
            false
        }),
    );
    *slot.lock().expect("test slot") = Some(owner.clone());
    assert_eq!(owner.check(), Err(OriginalAdmissionError::Reentrant));
    assert_eq!(
        owner.clone().check(),
        Err(OriginalAdmissionError::Reentrant)
    );
    // Break the deliberate test observer/slot cycle after the assertion.
    slot.lock().expect("test slot").take();
}

#[test]
fn poisoned_bookkeeping_refuses_every_clone_without_running_observer() {
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let owner = OriginalAdmission::new(
        FiniteAdmissionGrant::new(10, 10),
        end(),
        Arc::new(move || {
            observed.fetch_add(1, Ordering::SeqCst);
            false
        }),
    );
    assert!(std::panic::catch_unwind(AssertUnwindSafe(|| owner.inner.test_poison())).is_err());
    assert_eq!(owner.check(), Err(OriginalAdmissionError::Poisoned));
    assert_eq!(owner.clone().check(), Err(OriginalAdmissionError::Poisoned));
    assert_eq!(calls.load(Ordering::SeqCst), 0);
}

#[test]
fn scratch_drop_stop_vetoes_success_before_scoped_return() {
    struct Scratch(Arc<AtomicBool>);
    impl Drop for Scratch {
        fn drop(&mut self) {
            self.0.store(true, Ordering::SeqCst);
        }
    }
    let (owner, raw) = stopped_flag(10, 10);
    let result = owner.with_work(|work| {
        work.admit(2, 3)?;
        let _scratch = Scratch(Arc::clone(&raw));
        Ok(17usize)
    });
    assert_eq!(result, Err(OriginalAdmissionError::ObserverStopped));
    raw.store(false, Ordering::SeqCst);
    assert_eq!(
        owner.clone().check(),
        Err(OriginalAdmissionError::ObserverStopped)
    );
    assert_eq!(balances(&owner), (8, 7));
}

#[test]
fn original_observer_handle_remains_live_across_healthy_phases() {
    let (owner, raw) = stopped_flag(10, 10);
    let original_end = owner.deadline();
    owner
        .with_work(|work| work.admit(2, 3))
        .expect("first phase");
    assert_eq!(owner.clone().deadline(), original_end);
    raw.store(true, Ordering::SeqCst);
    assert_eq!(
        owner.clone().with_work(|work| work.admit(1, 1)),
        Err(OriginalAdmissionError::ObserverStopped)
    );
    assert_eq!(balances(&owner), (8, 7));
}
