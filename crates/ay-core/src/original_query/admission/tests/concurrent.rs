// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::sync::{mpsc, Barrier, Condvar, Mutex};

#[test]
fn concurrent_original_debits_serialize_without_false_reentry() {
    let (entered_tx, entered_rx) = mpsc::channel();
    let release = Arc::new((Mutex::new(false), Condvar::new()));
    let active = Arc::new(AtomicUsize::new(0));
    let peak = Arc::new(AtomicUsize::new(0));
    let calls = Arc::new(AtomicUsize::new(0));
    let observer_release = Arc::clone(&release);
    let observer_active = Arc::clone(&active);
    let observer_peak = Arc::clone(&peak);
    let observer_calls = Arc::clone(&calls);
    let deadline = end();
    let owner = OriginalAdmission::new(
        FiniteAdmissionGrant::new(6, 10),
        deadline,
        Arc::new(move || {
            let now = observer_active.fetch_add(1, Ordering::SeqCst) + 1;
            observer_peak.fetch_max(now, Ordering::SeqCst);
            if observer_calls.fetch_add(1, Ordering::SeqCst) == 0 {
                entered_tx.send(()).expect("test entered");
                let (lock, changed) = &*observer_release;
                let mut released = lock.lock().expect("test release");
                while !*released && Instant::now() < deadline {
                    let remaining = deadline.saturating_duration_since(Instant::now());
                    released = changed
                        .wait_timeout(released, remaining)
                        .expect("test release")
                        .0;
                }
            }
            observer_active.fetch_sub(1, Ordering::SeqCst);
            false
        }),
    );
    let first_owner = owner.clone();
    let first = std::thread::spawn(move || first_owner.inner.admit(3, 5));
    entered_rx
        .recv_timeout(Duration::from_secs(2))
        .expect("first observer");

    let start = Arc::new(Barrier::new(2));
    let second_start = Arc::clone(&start);
    let second_owner = owner.clone();
    let second = std::thread::spawn(move || {
        second_start.wait();
        second_owner.inner.admit(3, 5)
    });
    start.wait();
    assert!(
        wait_for_registered_waiter(&owner),
        "second admission reached the wait branch"
    );
    {
        let (lock, changed) = &*release;
        *lock.lock().expect("test release") = true;
        changed.notify_all();
    }
    assert_eq!(first.join().expect("first thread"), Ok(()));
    assert_eq!(second.join().expect("second thread"), Ok(()));
    assert_eq!(calls.load(Ordering::SeqCst), 2);
    assert_eq!(peak.load(Ordering::SeqCst), 1);
    assert_eq!(active.load(Ordering::SeqCst), 0);
    assert_eq!(balances(&owner), (0, 0));
    assert_eq!(owner.inner.test_waiters(), 0);
    owner
        .check()
        .expect("zero-debit terminal fence remains healthy");
}

#[test]
fn concurrent_scoped_adapters_share_one_work_and_copy_balance() {
    let owner = healthy(120, 200);
    let start = Arc::new(Barrier::new(3));
    let mut threads = Vec::new();
    for _ in 0..2 {
        let clone = owner.clone();
        let start = Arc::clone(&start);
        threads.push(std::thread::spawn(move || {
            start.wait();
            clone.with_work(|work| {
                for _ in 0..10 {
                    work.admit(6, 10)?;
                }
                Ok(())
            })
        }));
    }
    start.wait();
    for thread in threads {
        assert_eq!(thread.join().expect("test adapter thread"), Ok(()));
    }
    assert_eq!(balances(&owner), (0, 0));
    assert_eq!(
        owner.with_work(|work| work.admit(1, 1)),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
}

#[test]
fn first_refusal_in_one_thread_is_terminal_for_another_clone() {
    let owner = healthy(1, 1);
    let clone = owner.clone();
    assert_eq!(
        std::thread::spawn(move || clone.with_work(|work| work.admit(2, 1)))
            .join()
            .expect("test refused thread"),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert_eq!(balances(&owner), (1, 1));
    assert!(owner.clone().with_work(|_| Ok(())).is_err());
}

fn wait_for_registered_waiter(owner: &OriginalAdmission) -> bool {
    while Instant::now() < owner.deadline() {
        // Registration is set under this same mutex BEFORE wait_timeout.
        // Acquiring the mutex and seeing it proves the waiter released the
        // guard to Condvar; a mere start barrier cannot establish that fact.
        if owner.inner.test_waiters() > 0 {
            return true;
        }
        std::thread::yield_now();
    }
    false
}

fn wait_until_original_end(deadline: Instant) {
    while Instant::now() < deadline {
        let remaining = deadline.saturating_duration_since(Instant::now());
        std::thread::sleep(remaining.min(Duration::from_millis(1)));
    }
}

#[test]
fn healthy_observer_crossing_original_end_refuses_before_any_debit() {
    let deadline = Instant::now() + Duration::from_secs(2);
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let operated = Arc::new(AtomicBool::new(false));
    let owner = OriginalAdmission::new(
        FiniteAdmissionGrant::new(6, 10),
        deadline,
        Arc::new(move || {
            observed.fetch_add(1, Ordering::SeqCst);
            wait_until_original_end(deadline);
            false
        }),
    );
    let expected = OriginalAdmissionError::Query(QueryError::Interrupted(
        crate::original_query::StopReason::Deadline,
    ));
    let result = owner.with_work(|work| {
        operated.store(true, Ordering::SeqCst);
        work.admit(3, 5)
    });
    assert_eq!(result, Err(expected));
    assert!(!operated.load(Ordering::SeqCst));
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_eq!(balances(&owner), (6, 10));
    assert_eq!(owner.deadline(), deadline);
    assert_eq!(owner.clone().check(), Err(expected));
    assert_eq!(calls.load(Ordering::SeqCst), 1);
}

#[test]
fn registered_waiter_crossing_original_end_never_calls_observer_or_debits() {
    let deadline = Instant::now() + Duration::from_secs(2);
    let (entered_tx, entered_rx) = mpsc::channel();
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let owner = OriginalAdmission::new(
        FiniteAdmissionGrant::new(6, 10),
        deadline,
        Arc::new(move || {
            observed.fetch_add(1, Ordering::SeqCst);
            entered_tx.send(()).expect("first observer entered");
            wait_until_original_end(deadline);
            false
        }),
    );
    let first_owner = owner.clone();
    let first = std::thread::spawn(move || first_owner.inner.admit(3, 5));
    entered_rx
        .recv_timeout(deadline.saturating_duration_since(Instant::now()))
        .expect("first observer before original end");
    let second_owner = owner.clone();
    let second = std::thread::spawn(move || second_owner.inner.admit(3, 5));
    assert!(
        wait_for_registered_waiter(&owner),
        "actual Condvar registration"
    );
    let first_result = first.join().expect("first observer joined");
    let second_result = second.join().expect("waiter joined");
    let expected = OriginalAdmissionError::Query(QueryError::Interrupted(
        crate::original_query::StopReason::Deadline,
    ));
    assert_eq!(first_result, Err(expected));
    assert_eq!(second_result, Err(expected));
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_eq!(balances(&owner), (6, 10));
    assert_eq!(owner.inner.test_waiters(), 0);
    assert_eq!(owner.deadline(), deadline);
    assert_eq!(
        owner.clone().with_work(|work| work.admit(3, 5)),
        Err(expected)
    );
    assert_eq!(calls.load(Ordering::SeqCst), 1);
}
