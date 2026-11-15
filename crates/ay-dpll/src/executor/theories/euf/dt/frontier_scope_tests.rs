// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::sync::Arc;

#[test]
fn frontier_scope_restores_both_predecessors_for_every_result_and_early_error() {
    for saved in [false, true] {
        for verdict in [SolveResult::Sat, SolveResult::unsat(), SolveResult::Unknown] {
            let mut exec = Executor::new();
            exec.dt_frontier_tester_diet_armed = saved;
            let expected = verdict.clone();
            let result = exec.with_dt_frontier_tester_diet(|inner| {
                assert!(inner.dt_frontier_tester_diet_armed);
                Ok::<_, ()>(verdict)
            });
            assert_eq!(result, Ok(expected));
            assert_eq!(exec.dt_frontier_tester_diet_armed, saved);
        }
        let mut exec = Executor::new();
        exec.dt_frontier_tester_diet_armed = saved;
        let marker = Arc::new(());
        let outcome: std::result::Result<SolveResult, Arc<()>> =
            exec.with_dt_frontier_tester_diet(|inner| {
                assert!(inner.dt_frontier_tester_diet_armed);
                // The exact early-? shape that used to bypass restoration.
                let lazy: std::result::Result<Option<SolveResult>, Arc<()>> = Err(marker.clone());
                let _ = lazy?;
                panic!("the early error must propagate");
            });
        assert!(Arc::ptr_eq(outcome.as_ref().unwrap_err(), &marker));
        assert_eq!(exec.dt_frontier_tester_diet_armed, saved);
    }
}

#[test]
fn nested_frontier_scopes_restore_each_saved_level_and_preserve_other_state() {
    for saved in [false, true] {
        let mut exec = Executor::new();
        exec.dt_frontier_tester_diet_armed = saved;
        exec.dt_lazy_auflia_eager_arm = false;
        exec.with_dt_frontier_tester_diet(|outer| {
            assert!(outer.dt_frontier_tester_diet_armed);
            let result = outer.with_dt_frontier_tester_diet(|inner| {
                assert!(inner.dt_frontier_tester_diet_armed);
                inner.dt_lazy_auflia_eager_arm = true;
                Err::<(), _>("inner error")
            });
            assert_eq!(result, Err("inner error"));
            assert!(outer.dt_frontier_tester_diet_armed);
        });
        assert_eq!(exec.dt_frontier_tester_diet_armed, saved);
        assert!(
            exec.dt_lazy_auflia_eager_arm,
            "the scope owns only its frontier flag"
        );
    }
}

#[test]
fn frontier_scope_restores_on_unwind_and_resumes_the_identical_panic_payload() {
    for saved in [false, true] {
        let mut exec = Executor::new();
        exec.dt_frontier_tester_diet_armed = saved;
        let marker = Arc::new(());
        let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            exec.with_dt_frontier_tester_diet(|inner| {
                assert!(inner.dt_frontier_tester_diet_armed);
                std::panic::panic_any(marker.clone());
            });
        }))
        .expect_err("the scope must resume the original unwind");
        assert!(Arc::ptr_eq(
            panic.downcast_ref::<Arc<()>>().unwrap(),
            &marker
        ));
        assert_eq!(exec.dt_frontier_tester_diet_armed, saved);
    }
}
