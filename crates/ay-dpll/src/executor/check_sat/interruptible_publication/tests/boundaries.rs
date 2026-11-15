// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn normal_and_error_returns_restore_independent_deadlines() {
    for reject in [false, true] {
        let mut executor = Executor::new();
        let saved = install_distinct_controls(&mut executor);
        let result = executor.with_interruptible_publication_controls(
            || false,
            |active| {
                assert_eq!(active.solve_deadline.get(), Some(saved.1));
                assert_eq!(active.certification_deadline.get(), Some(saved.2));
                active.set_deadline(None);
                if reject {
                    Err(crate::ExecutorError::ArtifactExport(
                        "original error".into(),
                    ))
                } else {
                    Ok(SolveResult::Sat)
                }
            },
        );
        if reject {
            assert!(matches!(result,
                Err(crate::ExecutorError::ArtifactExport(message)) if message == "original error"));
        } else {
            assert_eq!(result.expect("normal completion"), SolveResult::Sat);
        }
        assert_controls(&executor, &saved);
    }
}

#[test]
fn initial_callback_panic_changes_no_controls_or_evidence() {
    let mut executor = Executor::new();
    let saved = install_distinct_controls(&mut executor);
    seed_partial_evidence(&mut executor);
    let calls = Arc::new(AtomicUsize::new(0));
    let samples = Arc::clone(&calls);
    let mut operation_called = false;
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        executor.with_interruptible_publication_controls(
            move || {
                samples.fetch_add(1, Ordering::SeqCst);
                std::panic::panic_any(211_u32)
            },
            |_| {
                operation_called = true;
                Ok(SolveResult::Sat)
            },
        )
    }));
    let payload = outcome.expect_err("initial callback panic");
    assert_eq!(payload.downcast_ref::<u32>(), Some(&211));
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert!(!operation_called);
    assert_controls(&executor, &saved);
    assert_eq!(executor.last_result, Some(SolveResult::Sat));
    assert!(executor.last_model.is_some());
}

#[test]
fn already_stopped_parent_uses_no_worker_and_remains_isolated() {
    let mut executor = Executor::new();
    let saved = install_distinct_controls(&mut executor);
    saved.0.store(true, Ordering::Relaxed);
    let calls = Arc::new(AtomicUsize::new(0));
    let samples = Arc::clone(&calls);
    let caller = std::thread::current().id();
    let result = executor.with_interruptible_publication_controls(
        move || {
            assert_eq!(std::thread::current().id(), caller);
            samples.fetch_add(1, Ordering::SeqCst);
            false
        },
        |active| {
            let local = active.solve_interrupt.as_ref().expect("local flag");
            assert!(!Arc::ptr_eq(local, &saved.0));
            assert!(local.load(Ordering::Relaxed));
            Ok(SolveResult::Sat)
        },
    );
    assert_eq!(result.expect("stopped publication"), SolveResult::Unknown);
    // Initial parent short-circuit skips callback; final sample remains.
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert!(saved.0.load(Ordering::Relaxed));
    assert!(Arc::ptr_eq(
        executor.solve_interrupt.as_ref().unwrap(),
        &saved.0
    ));
    assert_eq!(executor.solve_deadline.get(), Some(saved.1));
    assert_eq!(executor.certification_deadline.get(), Some(saved.2));
}

#[test]
fn no_worker_operation_unwind_revokes_a_real_preceding_sat_capability() {
    let mut executor = Executor::new();
    // The empty formula has a concrete SAT admission without running search.
    // Pin a real private certificate, not just a manually set validation bit.
    assert_eq!(
        executor.emit_sat_verdict(SolveResult::Sat, &[]).unwrap(),
        SolveResult::Sat,
    );
    assert!(executor.last_sat_certificate.is_some());
    let saved = install_distinct_controls(&mut executor);
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        executor.with_interruptible_publication_controls(
            || true, // No worker exists even against the old implementation.
            |_| std::panic::panic_any(819_u32),
        )
    }));
    let payload = outcome.expect_err("operation panic on the no-worker path");
    assert_eq!(payload.downcast_ref::<u32>(), Some(&819));
    assert_controls(&executor, &saved);
    assert_revoked(&executor);
}
