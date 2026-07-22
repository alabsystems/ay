// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration test: default QF_LRA path exports `dpll.eager.*` counters (#6597).
//!
//! The standalone QF_LRA path routes through `solve_lra_standalone_incremental()`
//! with `eager_extension: true` (crates/ay-dpll/src/executor/theories/lra.rs:151).
//! This test verifies that the eager extension counters are present in the
//! exported statistics without any env-gated measurement harness.

use ay_dpll::Executor;
use ay_frontend::parse;

fn int_stat(exec: &Executor, name: &str) -> u64 {
    exec.statistics().get_int(name).unwrap_or(0)
}

fn run_script(input: &str) -> (Executor, Vec<String>) {
    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: LRA script should execute");
    (exec, outputs)
}

/// Default QF_LRA standalone path must export `dpll.eager.*` counters.
///
/// This catches regressions where the eager extension is accidentally disabled
/// or the stats export macro is removed from the `@eager_persistent` arm.
#[test]
fn test_default_qf_lra_exports_eager_stats_6597() {
    // Small QF_LRA problem with a disequality to trigger at least one split
    // iteration and exercise the eager extension's propagate() callback.
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (>= x 0.0))
        (assert (<= x 1.0))
        (assert (>= y 0.0))
        (assert (<= y 1.0))
        (assert (not (= x y)))
        (check-sat)
    "#;

    let (exec, outputs) = run_script(input);
    assert_eq!(outputs, vec!["sat"]);

    // The eager extension must have been called at least once. propagate_calls
    // counts how many times the SAT solver invoked the extension's propagate()
    // callback during BCP.
    let propagate_calls = int_stat(&exec, "dpll.eager.propagate_calls");
    assert!(
        propagate_calls > 0,
        "expected dpll.eager.propagate_calls > 0 on default QF_LRA path; got {propagate_calls}. \
         The eager extension may have been disabled or the stats export removed."
    );

    // At least one level-0 check should occur (the initial theory check before
    // any decisions are made).
    let level0_checks = int_stat(&exec, "dpll.eager.level0_checks");
    assert!(
        level0_checks > 0,
        "expected dpll.eager.level0_checks > 0 on default QF_LRA path; got {level0_checks}."
    );

    // Verify all eager stat keys are present (non-None). Values can be 0 for
    // some counters depending on the problem, but the keys must exist.
    let eager_stat_keys = [
        "dpll.eager.propagate_calls",
        "dpll.eager.state_unchanged_skips",
        "dpll.eager.bound_refinement_handoffs",
        "dpll.eager.batch_defers",
        "dpll.eager.level0_batch_guard_hits",
        "dpll.eager.level0_checks",
    ];

    for key in &eager_stat_keys {
        assert!(
            exec.statistics().get_int(key).is_some(),
            "missing eager stat key {key:?} in statistics export; \
             keys present: {:?}",
            exec.statistics()
                .extra
                .keys()
                .filter(|k| k.starts_with("dpll.eager"))
                .collect::<Vec<_>>()
        );
    }

    // Sanity: the split-loop round_trips counter should also be present since
    // the eager persistent arm exports both eager and split-loop stats.
    assert!(
        exec.statistics().get_int("dpll.round_trips").is_some(),
        "dpll.round_trips should be present alongside eager stats"
    );
}

/// QF_LRA UNSAT problem should also export eager stats.
///
/// Tests that the UNSAT exit path in the `@eager_persistent` arm correctly
/// exports accumulated eager stats before returning.
#[test]
fn test_default_qf_lra_unsat_exports_eager_stats_6597() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (>= x 1.0))
        (assert (<= x 0.0))
        (check-sat)
    "#;

    let (exec, outputs) = run_script(input);
    assert_eq!(outputs, vec!["unsat"]);

    // Even on a trivially UNSAT problem, the eager extension should have been
    // invoked at least once to discover the conflict.
    let propagate_calls = int_stat(&exec, "dpll.eager.propagate_calls");
    assert!(
        propagate_calls > 0,
        "expected dpll.eager.propagate_calls > 0 on UNSAT QF_LRA; got {propagate_calls}"
    );
}
