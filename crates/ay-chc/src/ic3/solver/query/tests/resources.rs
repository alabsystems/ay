// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::sync::atomic::AtomicUsize;

#[test]
fn original_resource_stop_reaches_init_and_transition_before_evidence() {
    for init in [true, false] {
        let open = Arc::new(AtomicBool::new(true));
        let poll = open.clone();
        let mut solver =
            safe_solver().with_resource_poll(Arc::new(move || poll.load(Ordering::Relaxed)));
        open.store(false, Ordering::Relaxed);
        let result = if init {
            solver.init_query(&[])
        } else {
            solver.transition_query(&[])
        };
        assert!(result.is_err());
        assert!(solver.query_stopped.get());
        open.store(true, Ordering::Relaxed);
        assert!(solver.init_query(&[]).is_err());
        assert!(solver.transition_query(&[]).is_err());
        assert!(matches!(solver.solve(), Ic3Result::Unknown));
        assert!(solver.frames.is_empty());
    }
}

#[test]
fn original_poll_can_refuse_inside_native_sat_without_atomic_interrupt() {
    let calls = Arc::new(AtomicUsize::new(0));
    let poll = calls.clone();
    let mut solver = safe_solver().with_resource_poll(Arc::new(move || {
        poll.fetch_add(1, Ordering::Relaxed) + 1 < 2
    }));
    assert!(solver.init_query(&[]).is_err());
    assert_eq!(calls.load(Ordering::Relaxed), 3);
    assert!(solver.query_stopped.get());
    assert!(matches!(solver.solve(), Ic3Result::Unknown));
}

#[test]
fn original_cleanup_refusal_discards_genuine_safe_and_model_results() {
    let open = Arc::new(AtomicBool::new(true));
    let poll = open.clone();
    let mut solver =
        safe_solver().with_resource_poll(Arc::new(move || poll.load(Ordering::Relaxed)));
    let query = solver.init_query(&[]);
    assert!(matches!(query, Ok(AssumeResult::Sat(_))));
    open.store(false, Ordering::Relaxed);
    assert!(solver.after_query_cleanup(query).is_err());
    open.store(true, Ordering::Relaxed);
    assert!(matches!(solver.solve(), Ic3Result::Unknown));
    let poll = open.clone();
    let mut fresh =
        safe_solver().with_resource_poll(Arc::new(move || poll.load(Ordering::Relaxed)));
    let safe = fresh.solve();
    assert!(matches!(safe, Ic3Result::Safe { .. }));
    open.store(false, Ordering::Relaxed);
    assert!(matches!(fresh.admit_result(safe), Ic3Result::Unknown));
    open.store(true, Ordering::Relaxed);
    assert!(matches!(fresh.solve(), Ic3Result::Unknown));
}
