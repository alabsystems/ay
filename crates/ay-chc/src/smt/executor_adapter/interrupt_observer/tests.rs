// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::CancellationToken;

struct DropSignal(Arc<AtomicBool>);

impl Drop for DropSignal {
    fn drop(&mut self) {
        self.0.store(true, Ordering::SeqCst);
    }
}

fn wait_for(flag: &AtomicBool) -> bool {
    let until = ay_core::time::Instant::now() + Duration::from_secs(5);
    while !flag.load(Ordering::SeqCst) && ay_core::time::Instant::now() < until {
        std::thread::yield_now();
    }
    flag.load(Ordering::SeqCst)
}

fn tracked_observer(
    cancellation: &ReplayCancellation,
    dropped: Arc<AtomicBool>,
) -> InterruptObserver {
    InterruptObserver::with_spawner(cancellation, |worker| {
        std::thread::Builder::new().spawn(move || {
            let _owner = DropSignal(dropped);
            worker.run_with(Worker::observe);
        })
    })
    .unwrap()
}

#[test]
fn precancelled_attempt_never_spawns_and_never_clears_the_caller() {
    let token = CancellationToken::new();
    token.cancel();
    let cancellation = ReplayCancellation::new(&token);
    let mut spawned = false;
    let mut observer = InterruptObserver::with_spawner(&cancellation, |_| {
        spawned = true;
        Err(std::io::Error::other("must not spawn"))
    })
    .unwrap();
    assert!(!spawned);
    assert!(observer.interrupt().load(Ordering::Relaxed));
    assert!(!observer.finish());
    assert!(token.is_cancelled());
}

#[test]
fn inherited_cancel_reaches_live_flag_and_reset_cannot_resume_the_attempt() {
    let parent = CancellationToken::new();
    let child = parent.child();
    let cancellation = ReplayCancellation::new(&child);
    let mut observer = InterruptObserver::new(&cancellation).unwrap();
    let interrupt = observer.interrupt();
    assert!(!interrupt.load(Ordering::Relaxed));
    parent.cancel();
    let observed = wait_for(&interrupt);
    parent.reset();
    // Even an observation timeout unwinds through a joined observer, so a
    // scheduling failure cannot leak the test worker.
    assert!(
        observed,
        "observer did not sample the inherited cancellation"
    );
    assert!(!child.is_cancelled());
    assert!(!observer.finish());
    // Join synchronizes the worker's sticky observation before inspecting it
    // separately; the interrupt flag itself is deliberately only a stop signal.
    assert!(cancellation.is_cancelled());
    assert!(interrupt.load(Ordering::Relaxed));
}

#[test]
fn live_completion_joins_owned_worker_and_is_idempotent() {
    let token = CancellationToken::new();
    let cancellation = ReplayCancellation::new(&token);
    let dropped = Arc::new(AtomicBool::new(false));
    let mut observer = tracked_observer(&cancellation, Arc::clone(&dropped));
    assert!(observer.finish());
    assert!(dropped.load(Ordering::SeqCst));
    assert!(observer.worker.is_none());
    assert!(observer.finish());
    assert!(!token.is_cancelled());
    assert!(!cancellation.is_cancelled());
}

#[test]
fn caller_unwind_joins_worker_and_preserves_original_payload() {
    let token = CancellationToken::new();
    let cancellation = ReplayCancellation::new(&token);
    let dropped = Arc::new(AtomicBool::new(false));
    let identity = Arc::new(());
    let payload = Arc::clone(&identity);
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        let _observer = tracked_observer(&cancellation, Arc::clone(&dropped));
        std::panic::panic_any(payload);
    }));
    let caught = outcome.expect_err("caller operation must still unwind");
    assert!(Arc::ptr_eq(
        caught.downcast_ref::<Arc<()>>().unwrap(),
        &identity
    ));
    assert!(dropped.load(Ordering::SeqCst));
    assert!(!token.is_cancelled());
}

#[test]
fn spawn_failure_is_typed_and_does_not_poison_caller_tokens() {
    let token = CancellationToken::new();
    let cancellation = ReplayCancellation::new(&token);
    let result = InterruptObserver::with_spawner(&cancellation, |_worker| {
        Err(std::io::Error::other("injected spawn refusal"))
    });
    let Err(ObserverStartError::Spawn(error)) = result else {
        panic!("failed observer creation must not become an absent control");
    };
    assert_eq!(error.to_string(), "injected spawn refusal");
    assert!(!token.is_cancelled());
    assert!(!cancellation.is_cancelled());
}

#[test]
fn worker_panic_latches_interrupt_before_the_owner_joins() {
    let token = CancellationToken::new();
    let cancellation = ReplayCancellation::new(&token);
    let mut observer = InterruptObserver::with_spawner(&cancellation, |worker| {
        std::thread::Builder::new()
            .spawn(move || worker.run_with(|_| panic!("injected observer panic")))
    })
    .unwrap();
    assert!(wait_for(&observer.interrupt()));
    assert!(
        observer.worker.is_some(),
        "panic must latch before join is called"
    );
    assert!(!observer.finish());
    assert!(!token.is_cancelled());
}

#[test]
fn poisoned_stop_mutex_is_recovered_for_shutdown_without_joining_under_lock() {
    let token = CancellationToken::new();
    let cancellation = ReplayCancellation::new(&token);
    let mut observer = InterruptObserver::with_spawner(&cancellation, |worker| {
        std::thread::Builder::new().spawn(move || {
            worker.run_with(|worker| {
                let _held = worker.state.stopped.lock().unwrap();
                panic!("poison the observer stop mutex");
            });
        })
    })
    .unwrap();
    assert!(wait_for(&observer.interrupt()));
    assert!(!observer.finish());
    assert!(observer.worker.is_none());
    assert!(observer.state.stopped.is_poisoned());
    assert!(!token.is_cancelled());
}

#[test]
fn final_sample_observes_cancellation_after_the_worker_joined() {
    let token = CancellationToken::new();
    let cancellation = ReplayCancellation::new(&token);
    let mut observer = InterruptObserver::new(&cancellation).unwrap();
    observer.stop_and_join();
    assert!(!observer.interrupt().load(Ordering::Relaxed));
    token.cancel();
    assert!(!observer.finish());
    token.reset();
    assert!(!observer.finish());
}

#[test]
fn worker_payload_destructor_panic_cannot_replace_a_caller_unwind() {
    struct BadPayload;
    impl Drop for BadPayload {
        fn drop(&mut self) {
            panic!("secondary worker-payload destructor panic");
        }
    }
    let token = CancellationToken::new();
    let cancellation = ReplayCancellation::new(&token);
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        let observer = InterruptObserver::with_spawner(&cancellation, |worker| {
            std::thread::Builder::new()
                .spawn(move || worker.run_with(|_| std::panic::panic_any(BadPayload)))
        })
        .unwrap();
        assert!(wait_for(&observer.interrupt()));
        std::panic::panic_any(417_u32);
    }));
    let payload = outcome.expect_err("original caller panic must survive observer cleanup");
    assert_eq!(payload.downcast_ref::<u32>(), Some(&417));
    assert!(!token.is_cancelled());
}
