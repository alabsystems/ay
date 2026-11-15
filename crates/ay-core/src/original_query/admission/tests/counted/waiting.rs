// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::resource::{ChildSpec, DeadlineSource, Exhausted, Guard, NodeLabel};
use std::sync::{mpsc, Mutex};
use std::thread::JoinHandle;

struct HeldObserver {
    owner: CountedAdmission,
    release: mpsc::Sender<()>,
    first: JoinHandle<Result<(), CountedAdmissionError>>,
    calls: Arc<AtomicUsize>,
}

fn hold_observer() -> HeldObserver {
    let (entered, arrival) = mpsc::channel();
    let (release, released) = mpsc::channel();
    let released = Mutex::new(released);
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let owner = CountedAdmission::new(
        FiniteAdmissionGrant::new(10, 10),
        None,
        Arc::new(move || {
            if observed.fetch_add(1, Ordering::SeqCst) == 0 {
                entered.send(()).unwrap();
                // Diagnostic containment for a broken test, NOT an owner end.
                released
                    .lock()
                    .unwrap()
                    .recv_timeout(Duration::from_secs(10))
                    .unwrap();
            }
            false
        }),
    )
    .unwrap();
    assert_eq!(owner.deadline(), None);
    let clone = owner.clone();
    let first = std::thread::spawn(move || clone.admit(1, 1));
    arrival.recv_timeout(Duration::from_secs(2)).unwrap();
    HeldObserver {
        owner,
        release,
        first,
        calls,
    }
}

fn caller(
    owner: CountedAdmission,
    end: Instant,
) -> (
    JoinHandle<()>,
    mpsc::Receiver<Result<(), CountedAdmissionError>>,
) {
    let (result, received) = mpsc::channel();
    let worker = std::thread::spawn(move || {
        let guard = Guard::root_child(
            ChildSpec::new(NodeLabel::Check).with_deadline(DeadlineSource::Fixed(end)),
        );
        let _scope = guard.enter();
        result.send(owner.admit(1, 1)).unwrap();
    });
    (worker, received)
}

fn finish(
    held: HeldObserver,
    worker: JoinHandle<()>,
    observed: Result<Result<(), CountedAdmissionError>, mpsc::RecvTimeoutError>,
) {
    // Release and join even if the deadline regression failed: no stranded
    // thread is needed to demonstrate that an indefinite wait was incorrect.
    held.release.send(()).unwrap();
    let first = held.first.join().unwrap();
    worker.join().unwrap();
    let expected = CountedAdmissionError::Guard(Exhausted::Deadline);
    assert_eq!(observed, Ok(Err(expected)));
    assert_eq!(first, Err(expected));
    assert_eq!(held.calls.load(Ordering::SeqCst), 1);
    assert_eq!(held.owner.test_waiters(), 0);
    assert_eq!(held.owner.usage().unwrap().work_admitted, 0);
    assert_eq!(held.owner.usage().unwrap().storage_admitted, 0);
    assert_eq!(held.owner.check(), Err(expected));
}

#[test]
fn expired_later_caller_refuses_while_another_observer_is_still_held() {
    let held = hold_observer();
    let (worker, received) = caller(held.owner.clone(), Instant::now());
    let observed = received.recv_timeout(Duration::from_secs(2));
    finish(held, worker, observed);
}

#[test]
fn registered_waiter_obeys_its_real_caller_end_without_a_new_owner_clock() {
    let held = hold_observer();
    let end = Instant::now() + Duration::from_secs(2);
    let (worker, received) = caller(held.owner.clone(), end);
    let mut registered = false;
    while Instant::now() < end {
        if held.owner.test_waiters() > 0 {
            registered = true;
            break;
        }
        std::thread::yield_now();
    }
    let observed = received.recv_timeout(Duration::from_secs(4));
    finish(held, worker, observed);
    assert!(
        registered,
        "the later caller actually released the mutex to Condvar"
    );
}
