// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Solver-free tests of the same captured owner used by BMC workers/fallbacks.
//! Only thread-local state changes; process-global limits remain untouched.

use super::*;
use std::cell::Cell;
use std::panic::{catch_unwind, AssertUnwindSafe};

const MIB: usize = 1024 * 1024;

#[test]
fn explicit_adaptive_and_caller_limits_intersect_without_defaulting_or_dividing() {
    for (explicit, adaptive, inherited, expected) in [
        (None, None, None, None),
        (Some(64 * MIB), None, None, Some(64 * MIB)),
        (None, Some(32 * MIB), None, Some(32 * MIB)),
        (Some(64 * MIB), Some(32 * MIB), None, Some(32 * MIB)),
        (
            Some(64 * MIB),
            Some(32 * MIB),
            Some(16 * MIB),
            Some(16 * MIB),
        ),
        (Some(8 * MIB), Some(32 * MIB), Some(16 * MIB), Some(8 * MIB)),
        (None, None, Some(16 * MIB), Some(16 * MIB)),
        (Some(usize::MAX), None, None, Some(usize::MAX)),
    ] {
        let _scope = SmtContext::scoped_thread_term_memory_budget(inherited);
        let captured = Budget::capture(explicit, adaptive);
        assert_eq!(captured.bytes, expected);
        let result = captured.run(|| SmtContext::new().term_memory_budget);
        assert_eq!(result, Some(expected));
        assert_eq!(SmtContext::current_thread_term_memory_budget(), inherited);
    }
}

#[test]
fn every_zero_source_refuses_before_the_production_operation_runs() {
    for (explicit, adaptive, inherited) in [
        (Some(0), None, None),
        (Some(64 * MIB), Some(0), None),
        (Some(64 * MIB), Some(32 * MIB), Some(0)),
    ] {
        let _scope = SmtContext::scoped_thread_term_memory_budget(inherited);
        let calls = Cell::new(0);
        let captured = Budget::capture(explicit, adaptive);
        assert!(!captured.open());
        assert_eq!(captured.run(|| calls.set(calls.get() + 1)), None);
        assert_eq!(
            calls.get(),
            0,
            "no clone/preprocessing operation was entered"
        );
        assert_eq!(SmtContext::current_thread_term_memory_budget(), inherited);
    }
    let _live = SmtContext::scoped_thread_term_memory_budget(Some(64 * MIB));
    assert_eq!(Budget::capture(None, None).run(|| 7), Some(7));
}

#[test]
fn real_worker_inherits_captured_owner_and_restores_its_own_tighter_scope() {
    let _caller = SmtContext::scoped_thread_term_memory_budget(Some(64 * MIB));
    let captured = Budget::capture(Some(96 * MIB), Some(80 * MIB));
    let caller_thread = std::thread::current().id();
    std::thread::scope(|scope| {
        scope
            .spawn(move || {
                assert_ne!(std::thread::current().id(), caller_thread);
                assert_eq!(SmtContext::current_thread_term_memory_budget(), None);
                assert_eq!(
                    captured.run(|| SmtContext::new().term_memory_budget),
                    Some(Some(64 * MIB))
                );
                assert_eq!(SmtContext::current_thread_term_memory_budget(), None);
                {
                    let _worker = SmtContext::scoped_thread_term_memory_budget(Some(32 * MIB));
                    assert_eq!(
                        captured.run(|| SmtContext::new().term_memory_budget),
                        Some(Some(32 * MIB))
                    );
                    assert_eq!(
                        SmtContext::current_thread_term_memory_budget(),
                        Some(32 * MIB)
                    );
                    let _zero = SmtContext::scoped_thread_term_memory_budget(Some(0));
                    assert!(captured
                        .run(|| panic!("a worker-local zero cap must win"))
                        .is_none());
                }
                assert_eq!(SmtContext::current_thread_term_memory_budget(), None);
            })
            .join()
            .unwrap();
    });
    assert_eq!(
        SmtContext::current_thread_term_memory_budget(),
        Some(64 * MIB)
    );
    // The same owner also wraps the calling-thread spawn-failure path.
    assert_eq!(
        captured.run(|| SmtContext::new().term_memory_budget),
        Some(Some(64 * MIB))
    );
}

#[test]
fn nested_scope_and_panicking_operation_restore_the_exact_previous_owner() {
    let _caller = SmtContext::scoped_thread_term_memory_budget(Some(64 * MIB));
    let captured = Budget::capture(Some(32 * MIB), None);
    let outcome: Result<Option<()>, _> = catch_unwind(AssertUnwindSafe(|| {
        captured.run(|| {
            assert_eq!(SmtContext::new().term_memory_budget, Some(32 * MIB));
            {
                let tighter = Budget::capture(Some(16 * MIB), None);
                let _nested = tighter.install();
                assert_eq!(SmtContext::new().term_memory_budget, Some(16 * MIB));
            }
            assert_eq!(SmtContext::new().term_memory_budget, Some(32 * MIB));
            panic!("expected operation failure");
        })
    }));
    assert!(outcome.is_err());
    assert_eq!(
        SmtContext::current_thread_term_memory_budget(),
        Some(64 * MIB)
    );
    assert_eq!(captured.run(|| 9), Some(9));
    assert_eq!(
        SmtContext::current_thread_term_memory_budget(),
        Some(64 * MIB)
    );
}

#[test]
fn persistent_executor_keeps_tighter_caps_and_refuses_actual_existing_storage() {
    let _caller = SmtContext::scoped_thread_term_memory_budget(Some(64 * MIB));
    let captured = Budget::capture(Some(32 * MIB), None);
    let mut executor = ay_dpll::Executor::new();
    assert!(captured.constrain(&mut executor));
    assert_eq!(executor.term_memory_limit(), Some(32 * MIB));
    executor.set_term_memory_limit(Some(16 * MIB));
    assert!(captured.constrain(&mut executor));
    assert_eq!(executor.term_memory_limit(), Some(16 * MIB));
    assert!(executor.terms().true_memory_bytes() > 1);
    executor.set_term_memory_limit(Some(1));
    assert!(!captured.constrain(&mut executor));
    assert!(!captured.executor_open(&executor));
    assert_eq!(executor.term_memory_limit(), Some(1));
    let mut fresh = ay_dpll::Executor::new();
    assert!(captured.constrain(&mut fresh));
    assert!(captured.executor_open(&fresh));
    {
        let _worker = SmtContext::scoped_thread_term_memory_budget(Some(8 * MIB));
        let mut worker = ay_dpll::Executor::new();
        assert!(captured.constrain(&mut worker));
        assert_eq!(worker.term_memory_limit(), Some(8 * MIB));
        let _zero = SmtContext::scoped_thread_term_memory_budget(Some(0));
        assert!(!captured.constrain(&mut worker));
        assert_eq!(worker.term_memory_limit(), Some(0));
    }
    let zero = Budget::capture(Some(0), None);
    assert!(!zero.constrain(&mut fresh));
    assert_eq!(fresh.term_memory_limit(), Some(0));
}
