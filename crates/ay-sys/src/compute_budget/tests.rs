// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::sync::mpsc;

fn bank(width: usize) -> Arc<Bank> {
    Bank::new(NonZeroUsize::new(width).expect("positive test width"))
}

#[test]
fn nested_scopes_keep_one_unit_even_when_dropped_out_of_order() {
    let bank = bank(1);
    let outer = ComputeScope::enter_on(&bank).expect("base");
    let inner = ComputeScope::enter_on(&bank).expect("nested never waits");
    assert!(inner.try_extra().expect("probe").is_none());
    drop(outer);
    assert!(bank.acquire(Acquisition::Try).expect("probe").is_none());
    drop(inner);
    assert_eq!(bank.state.lock().expect("state").active, 0);
}

#[test]
fn independent_pools_share_the_same_actual_units() {
    let bank = bank(3);
    let first = ComputeScope::enter_on(&bank).expect("first caller");
    let extra = first.try_extra().expect("probe").expect("second unit");
    let other_bank = Arc::clone(&bank);
    std::thread::spawn(move || {
        let second = ComputeScope::enter_on(&other_bank).expect("independent caller");
        assert!(second.try_extra().expect("probe").is_none());
        assert_eq!(other_bank.state.lock().expect("state").active, 3);
    })
    .join()
    .expect("second pool");
    drop(extra);
    drop(first);
    assert_eq!(bank.state.lock().expect("state").active, 0);
}

#[test]
fn detached_worker_keeps_its_unit_until_real_exit() {
    let bank = bank(2);
    let scope = ComputeScope::enter_on(&bank).expect("caller");
    let extra = scope.try_extra().expect("probe").expect("worker");
    let (started_tx, started_rx) = mpsc::channel();
    let (finish_tx, finish_rx) = mpsc::channel();
    let (exited_tx, exited_rx) = mpsc::channel();
    let handle = std::thread::spawn(move || {
        extra
            .run(|| {
                started_tx.send(()).expect("started");
                finish_rx.recv().expect("finish");
            })
            .expect("worker scope");
        exited_tx.send(()).expect("exit");
    });
    started_rx.recv().expect("running");
    drop(handle);
    assert!(scope.try_extra().expect("probe").is_none());
    finish_tx.send(()).expect("release");
    exited_rx.recv().expect("actual exit");
    assert!(scope.try_extra().expect("probe").is_some());
}

#[test]
fn worker_unwind_returns_its_unit_and_nested_work_never_waits() {
    let bank = bank(2);
    let scope = ComputeScope::enter_on(&bank).expect("caller");
    let extra = scope.try_extra().expect("probe").expect("worker");
    let worker_bank = Arc::clone(&bank);
    assert!(std::thread::spawn(move || {
        extra.run(|| {
            let nested = ComputeScope::enter_on(&worker_bank).expect("nested");
            assert!(nested.try_extra().expect("probe").is_none());
            panic!("injected worker unwind");
        })
    })
    .join()
    .is_err());
    assert_eq!(bank.state.lock().expect("state").active, 1);
    assert!(scope.try_extra().expect("probe").is_some());
}

#[test]
fn a_lower_ceiling_waits_for_held_work_instead_of_revoking_it() {
    let bank = bank(3);
    let scope = ComputeScope::enter_on(&bank).expect("caller");
    let first = scope.try_extra().expect("probe").expect("first");
    let second = scope.try_extra().expect("probe").expect("second");
    bank.state.lock().expect("state").ceiling = 1;
    assert_eq!(bank.state.lock().expect("state").active, 3);
    assert!(scope.try_extra().expect("probe").is_none());
    drop(first);
    drop(second);
    assert!(scope.try_extra().expect("probe").is_none());
    drop(scope);
    assert_eq!(bank.state.lock().expect("state").active, 0);
}

#[test]
fn independent_try_entry_declines_without_starting_work() {
    let bank = bank(1);
    let scope = ComputeScope::enter_on(&bank).expect("caller");
    let other = Arc::clone(&bank);
    std::thread::spawn(move || {
        assert!(ComputeScope::enter_on_mode(&other, Acquisition::Try)
            .expect("try entry")
            .is_none());
        assert_eq!(other.state.lock().expect("state").active, 1);
    })
    .join()
    .expect("other caller");
    drop(scope);
    assert_eq!(bank.state.lock().expect("state").active, 0);
}

#[test]
fn queued_bases_get_fifo_priority_over_new_extras() {
    let bank = bank(1);
    let original = bank
        .acquire(Acquisition::Wait)
        .expect("base")
        .expect("unit");
    let (entered_tx, entered_rx) = mpsc::channel();
    let mut releases = Vec::new();
    let mut handles = Vec::new();
    for index in 0..2 {
        let worker_bank = Arc::clone(&bank);
        let entered = entered_tx.clone();
        let (release_tx, release_rx) = mpsc::channel();
        releases.push(release_tx);
        handles.push(std::thread::spawn(move || {
            let unit = worker_bank
                .acquire(Acquisition::Wait)
                .expect("queued base")
                .expect("unit");
            entered.send(index).expect("entered");
            release_rx.recv().expect("release");
            drop(unit);
        }));
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
        while bank.state.lock().expect("state").waiting.len() != index + 1 {
            assert!(std::time::Instant::now() < deadline, "base did not queue");
            std::thread::yield_now();
        }
    }
    drop(original);
    // Whether the waiter has run or not, its queued claim prevents a new
    // extra from taking the released unit.
    assert!(bank
        .acquire(Acquisition::Try)
        .expect("extra probe")
        .is_none());
    assert_eq!(entered_rx.recv().expect("first base"), 0);
    releases[0].send(()).expect("release first");
    assert_eq!(entered_rx.recv().expect("second base"), 1);
    releases[1].send(()).expect("release second");
    for handle in handles {
        handle.join().expect("base exited");
    }
    assert_eq!(bank.state.lock().expect("state").active, 0);
    assert!(bank.state.lock().expect("state").waiting.is_empty());
}

#[test]
fn original_caller_cancellation_and_unwind_remove_only_their_pending_ticket() {
    let bank = bank(1);
    let original = bank
        .acquire(Acquisition::Wait)
        .expect("base")
        .expect("unit");
    let other = Arc::clone(&bank);
    std::thread::spawn(move || {
        let mut polls = 0;
        let scope = ComputeScope::enter_on_progress(
            &other,
            Acquisition::Wait,
            Some(&mut || {
                polls += 1;
                polls >= 2
            }),
        )
        .expect("cancelled admission");
        assert!(scope.is_none());
        assert_eq!(polls, 2);
    })
    .join()
    .expect("cancelled caller");
    assert_eq!(bank.state.lock().expect("state").active, 1);
    assert!(bank.state.lock().expect("state").waiting.is_empty());
    let other = Arc::clone(&bank);
    assert!(std::thread::spawn(move || {
        let mut polls = 0;
        let _scope = ComputeScope::enter_on_progress(
            &other,
            Acquisition::Wait,
            Some(&mut || {
                polls += 1;
                assert!(polls < 2, "injected original caller unwind");
                false
            }),
        );
    })
    .join()
    .is_err());
    assert_eq!(bank.state.lock().expect("state").active, 1);
    assert!(bank.state.lock().expect("state").waiting.is_empty());
    drop(original);
    assert_eq!(bank.state.lock().expect("state").active, 0);
}

#[test]
fn suspended_nested_caller_releases_exactly_one_unit_and_restores_before_cleanup() {
    let bank = bank(1);
    let outer = ComputeScope::enter_on(&bank).expect("original caller");
    let inner = ComputeScope::enter_on(&bank).expect("nested caller");
    let worker_bank = Arc::clone(&bank);
    let (ran, ran_rx) = mpsc::channel();
    let worker = std::thread::spawn(move || {
        let _scope = ComputeScope::enter_on(&worker_bank).expect("actual competing unit");
        assert_eq!(worker_bank.state.lock().expect("state").active, 1);
        ran.send(()).expect("ran");
    });
    with_suspended_current(|| {
        assert!(ComputeScope::enter_on(&bank).is_err());
        let mut polled = false;
        assert!(ComputeScope::enter_until(|| {
            polled = true;
            false
        })
        .is_err());
        assert!(!polled, "suspended reentry must not invoke caller code");
        assert!(try_extra().is_err());
        assert!(with_suspended_current(|| ()).is_err());
        ran_rx.recv().expect("Q1 competing caller progresses");
        worker.join().expect("real exit before restoration");
    })
    .expect("restore");
    ENTERED.with(|entered| {
        let entered = entered.borrow();
        let (_, depth, unit) = entered.as_ref().expect("same TLS owner");
        assert_eq!(*depth, 2);
        assert!(unit.as_ref().expect("same original unit").active);
    });
    assert_eq!(bank.state.lock().expect("state").active, 1);
    drop(inner);
    assert!(outer
        .try_extra()
        .expect("original unit still retained")
        .is_none());
    drop(outer);
    assert_eq!(bank.state.lock().expect("state").active, 0);
}

#[test]
fn suspended_wait_panic_restores_before_outer_capture_cleanup() {
    struct Cleanup(Arc<Bank>, Arc<std::sync::atomic::AtomicBool>);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            let active = self.0.state.lock().expect("state").active;
            self.1.store(
                active == 1 && try_extra().expect("restored current scope").is_none(),
                std::sync::atomic::Ordering::Release,
            );
        }
    }
    let bank = bank(1);
    let scope = ComputeScope::enter_on(&bank).expect("original caller");
    let cleaned = Arc::new(std::sync::atomic::AtomicBool::new(false));
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _cleanup = Cleanup(Arc::clone(&bank), Arc::clone(&cleaned));
        let _ = with_suspended_current(|| panic!("passive wait panic"));
    }))
    .is_err());
    assert!(cleaned.load(std::sync::atomic::Ordering::Acquire));
    assert_eq!(bank.state.lock().expect("state").active, 1);
    drop(scope);
    assert_eq!(bank.state.lock().expect("state").active, 0);
}

#[test]
fn suspended_original_deadline_is_not_restarted() {
    let bank = bank(1);
    let scope = ComputeScope::enter_on(&bank).expect("original caller");
    let deadline = std::time::Instant::now() + std::time::Duration::from_millis(10);
    let (_held, receive) = mpsc::channel::<()>();
    let result = with_suspended_current(|| {
        receive.recv_timeout(deadline.saturating_duration_since(std::time::Instant::now()))
    })
    .expect("restore after original timeout");
    assert!(matches!(result, Err(mpsc::RecvTimeoutError::Timeout)));
    assert!(std::time::Instant::now() >= deadline);
    assert!(scope.try_extra().expect("original unit restored").is_none());
}
