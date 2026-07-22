// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_dpll::{Executor, StatValue};
use ay_frontend::parse;
use ntest::timeout;
fn assert_statistics_has_all(exec: &Executor, keys: &[&str]) {
    for key in keys {
        assert!(
            exec.statistics().extra.contains_key(*key) || exec.statistics().get_int(key).is_some(),
            "expected statistic key {key:?} in {:?}",
            exec.statistics().extra
        );
    }
}

fn float_stat(exec: &Executor, name: &str) -> f64 {
    match exec.statistics().extra.get(name) {
        Some(StatValue::Float(value)) => *value,
        Some(StatValue::Int(value)) => *value as f64,
        _ => 0.0,
    }
}

fn int_stat(exec: &Executor, name: &str) -> u64 {
    exec.statistics().get_int(name).unwrap_or(0)
}

fn run_script(input: &str) -> (Executor, Vec<String>) {
    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: split-loop script should execute");
    (exec, outputs)
}

#[test]
#[timeout(10_000)]
fn test_split_loop_timing_accumulates_on_rebuilds_6503() {
    let input = "\
        (set-logic QF_LIA)\
        (declare-const x Int)\
        (assert (>= x 1))\
        (declare-const y Int)\
        (assert (>= y 1))\
        (assert (not (= x y)))\
        (assert (= x 1))\
        (check-sat)\
        (get-info :all-statistics)";
    let (exec, outputs) = run_script(input);

    assert!(
        outputs.iter().any(|output| output == "sat"),
        "split-loop regression should remain SAT"
    );
    assert_statistics_has_all(
        &exec,
        &[
            "time.dpll.sat_solve",
            "time.dpll.theory_check",
            "time.dpll.theory_sync",
            "time.split_loop.model_extract",
            "time.split_loop.store_model",
            "time.split_loop.total",
            "dpll.rebuilds",
            "dpll.round_trips",
        ],
    );

    let rebuilds = int_stat(&exec, "dpll.rebuilds");
    let round_trips = int_stat(&exec, "dpll.round_trips");
    let sat_solve = float_stat(&exec, "time.dpll.sat_solve");
    let total = float_stat(&exec, "time.split_loop.total");

    assert!(
        round_trips >= 1,
        "expected split-loop case to run at least one round trip, got rebuilds={rebuilds}, round_trips={round_trips}, total={total:.6}"
    );
    assert!(
        sat_solve > 0.0,
        "expected accumulated SAT solve timing, got {sat_solve}"
    );
    assert!(total > 0.0, "expected non-zero split-loop total timing");
}
