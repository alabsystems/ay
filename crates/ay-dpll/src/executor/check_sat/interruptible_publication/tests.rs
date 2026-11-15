// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use std::sync::atomic::AtomicUsize;
use std::time::Duration;

mod boundaries;

struct DropSignal(Arc<AtomicBool>);

impl DropSignal {
    fn touch(&self) {}
}

impl Drop for DropSignal {
    fn drop(&mut self) {
        self.0.store(true, Ordering::SeqCst);
    }
}

/// Also terminates the old detached worker if a regression assertion fails.
struct ReleaseOnDrop(Arc<AtomicBool>);

impl Drop for ReleaseOnDrop {
    fn drop(&mut self) {
        self.0.store(true, Ordering::SeqCst);
    }
}

fn wait_for(flag: &AtomicBool) -> bool {
    let until = Instant::now() + Duration::from_secs(2);
    while !flag.load(Ordering::SeqCst) && Instant::now() < until {
        std::thread::yield_now();
    }
    flag.load(Ordering::SeqCst)
}

fn install_distinct_controls(executor: &mut Executor) -> (Arc<AtomicBool>, Instant, Instant) {
    let parent = Arc::new(AtomicBool::new(false));
    let search = Instant::now() + Duration::from_secs(60);
    let certification = search + Duration::from_secs(60);
    executor.set_interrupt(Arc::clone(&parent));
    executor.solve_deadline.set(Some(search));
    executor.certification_deadline.set(Some(certification));
    (parent, search, certification)
}

fn assert_controls(executor: &Executor, saved: &(Arc<AtomicBool>, Instant, Instant)) {
    assert!(Arc::ptr_eq(
        executor
            .solve_interrupt
            .as_ref()
            .expect("original interrupt"),
        &saved.0,
    ));
    assert!(!saved.0.load(Ordering::Relaxed));
    assert_eq!(executor.solve_deadline.get(), Some(saved.1));
    assert_eq!(executor.certification_deadline.get(), Some(saved.2));
}

fn assert_revoked(executor: &Executor) {
    assert!(executor.last_result.is_none());
    assert!(executor.last_model.is_none());
    assert!(!executor.last_model_validated);
    assert!(executor.last_sat_certificate.is_none());
    assert!(executor.last_unsat_certificate.is_none());
    assert!(executor.last_proof.is_none());
    assert!(executor.last_assumptions.is_none());
    assert!(executor.last_assumption_core.is_none());
}

fn seed_partial_evidence(executor: &mut Executor) {
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(crate::executor::model::Model::empty());
    executor.last_model_validated = true;
    executor.last_proof = Some(ay_core::Proof::new());
    executor.last_assumptions = Some(Vec::new());
    executor.last_assumption_core = Some(Vec::new());
}

#[test]
#[cfg(not(target_arch = "wasm32"))]
fn operation_unwind_joins_owner_restores_both_walls_and_revokes_evidence() {
    let mut executor = Executor::new();
    let saved = install_distinct_controls(&mut executor);
    let released = Arc::new(AtomicBool::new(false));
    let release = ReleaseOnDrop(Arc::clone(&released));
    let dropped = Arc::new(AtomicBool::new(false));
    let owner = DropSignal(Arc::clone(&dropped));
    let identity = Arc::new(());
    let payload = Arc::clone(&identity);
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        executor.with_interruptible_publication_controls(
            move || {
                owner.touch();
                released.load(Ordering::SeqCst)
            },
            |active| {
                seed_partial_evidence(active);
                // Restoration must not merely retain the operation's last wall.
                active.set_deadline(None);
                std::panic::panic_any(payload)
            },
        )
    }));
    let joined_before_escape = dropped.load(Ordering::SeqCst);
    // Release even an old detached worker before asserting the regression.
    drop(release);
    assert!(wait_for(&dropped), "the test worker must not leak");
    assert!(
        joined_before_escape,
        "callback owner survived the caller unwind"
    );
    let caught = outcome.expect_err("original operation must unwind");
    assert!(Arc::ptr_eq(
        caught
            .downcast_ref::<Arc<()>>()
            .expect("unchanged payload type"),
        &identity,
    ));
    assert_controls(&executor, &saved);
    assert_revoked(&executor);
}

#[test]
#[cfg(not(target_arch = "wasm32"))]
fn background_callback_panic_interrupts_while_operation_is_active() {
    let mut executor = Executor::new();
    let saved = install_distinct_controls(&mut executor);
    let calls = Arc::new(AtomicUsize::new(0));
    let samples = Arc::clone(&calls);
    let dropped = Arc::new(AtomicBool::new(false));
    let owner = DropSignal(Arc::clone(&dropped));
    let mut observed_in_operation = false;
    let result = executor.with_interruptible_publication_controls(
        move || {
            owner.touch();
            if samples.fetch_add(1, Ordering::SeqCst) > 0 {
                panic!("background callback panic");
            }
            false
        },
        |active| {
            // This bounded wait exits even against the old implementation,
            // which only noticed the panic after the operation returned.
            observed_in_operation =
                wait_for(active.solve_interrupt.as_ref().expect("local interrupt"));
            Ok(SolveResult::Sat)
        },
    );
    assert!(
        observed_in_operation,
        "worker panic did not interrupt active work"
    );
    assert_eq!(result.expect("fail-closed result"), SolveResult::Unknown);
    assert_eq!(calls.load(Ordering::SeqCst), 2);
    assert!(dropped.load(Ordering::SeqCst));
    assert_eq!(
        executor.unknown_reason(),
        Some(crate::UnknownReason::Interrupted)
    );
    assert!(executor.last_sat_certificate.is_none());
    assert!(executor.last_unsat_certificate.is_none());
    assert_controls(&executor, &saved);
}

#[test]
fn callback_owner_destructor_panic_is_inside_publication_transaction() {
    struct PanickingOwner;
    impl PanickingOwner {
        fn touch(&self) {}
    }
    impl Drop for PanickingOwner {
        fn drop(&mut self) {
            std::panic::panic_any(491_u32);
        }
    }
    let mut executor = Executor::new();
    let saved = install_distinct_controls(&mut executor);
    let owner = PanickingOwner;
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        executor.with_interruptible_publication_controls(
            move || {
                owner.touch();
                true // Deterministic no-worker path, including on wasm.
            },
            |active| {
                seed_partial_evidence(active);
                Ok(SolveResult::Sat)
            },
        )
    }));
    let payload = outcome.expect_err("callback owner destruction must unwind");
    assert_eq!(payload.downcast_ref::<u32>(), Some(&491));
    assert_controls(&executor, &saved);
    assert_revoked(&executor);
}

#[test]
fn secondary_cleanup_payload_cannot_replace_the_original_unwind() {
    struct Secondary(Arc<AtomicBool>);
    impl Drop for Secondary {
        fn drop(&mut self) {
            self.0.store(true, Ordering::SeqCst);
            panic!("dropping secondary payload must not replace original panic");
        }
    }
    struct PanickingOwner(Arc<AtomicBool>);
    impl PanickingOwner {
        fn touch(&self) {}
    }
    impl Drop for PanickingOwner {
        fn drop(&mut self) {
            std::panic::panic_any(Secondary(Arc::clone(&self.0)));
        }
    }
    let mut executor = Executor::new();
    let saved = install_distinct_controls(&mut executor);
    let secondary_dropped = Arc::new(AtomicBool::new(false));
    let owner = PanickingOwner(Arc::clone(&secondary_dropped));
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        executor.with_interruptible_publication_controls(
            move || {
                owner.touch();
                true
            },
            |active| {
                seed_partial_evidence(active);
                std::panic::panic_any(733_u32)
            },
        )
    }));
    let payload = outcome.expect_err("original operation panic");
    assert_eq!(payload.downcast_ref::<u32>(), Some(&733));
    assert!(!secondary_dropped.load(Ordering::SeqCst));
    assert_controls(&executor, &saved);
    assert_revoked(&executor);
}
