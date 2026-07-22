// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_dpll::{Executor, StatValue};
use ay_frontend::parse;

const SPLIT_LOOP_STATS_KEYS: [&str; 8] = [
    ":time.dpll.sat-solve",
    ":time.dpll.theory-check",
    ":time.dpll.theory-sync",
    ":time.split-loop.model-extract",
    ":time.split-loop.store-model",
    ":time.split-loop.total",
    ":dpll.rebuilds",
    ":dpll.round-trips",
];

struct SplitLoopCase {
    name: &'static str,
    expected_result: &'static str,
    input: &'static str,
}

struct SplitLoopStats {
    rebuilds: u64,
    sat_solve: f64,
    theory_check: f64,
    theory_sync: f64,
    replay_splits: f64,
    dpll_create: f64,
    pre_solve: f64,
    handle_step: f64,
    post_split: f64,
    model_extract: f64,
    store_model: f64,
    total: f64,
}

const LRA_SPLIT_LOOP_CASES: [SplitLoopCase; 3] = [
    SplitLoopCase {
        name: "pure_lra_disequality_sat",
        expected_result: "sat",
        input: r#"
            (set-logic QF_LRA)
            (declare-const x Real)
            (declare-const y Real)
            (assert (not (= x y)))
            (assert (>= x 0.0))
            (assert (<= x 1.0))
            (assert (>= y 0.0))
            (assert (<= y 1.0))
            (check-sat)
            (get-info :all-statistics)
        "#,
    },
    SplitLoopCase {
        name: "tight_multivar_disequality_unsat",
        expected_result: "unsat",
        input: r#"
            (set-logic QF_LRA)
            (declare-const x Real)
            (declare-const y Real)
            (declare-const z Real)
            (assert (= x 1.0))
            (assert (= y 0.0))
            (assert (= z 1.0))
            (assert (not (= (+ x y) z)))
            (check-sat)
            (get-info :all-statistics)
        "#,
    },
    SplitLoopCase {
        name: "buffered_single_and_multi_disequalities_sat",
        expected_result: "sat",
        input: r#"
            (set-logic QF_LRA)
            (declare-const a Real)
            (declare-const b Real)
            (assert (>= a 3.0))
            (assert (<= a 10.0))
            (assert (>= b 3.0))
            (assert (<= b 10.0))
            (assert (not (= a 3.0)))
            (assert (not (= a 4.0)))
            (assert (not (= a 5.0)))
            (assert (not (= a b)))
            (check-sat)
            (get-info :all-statistics)
        "#,
    },
];

fn assert_stats_contains_all(stats: &str, keys: &[&str]) {
    for key in keys {
        assert!(stats.contains(key), "expected {key} in stats: {stats}");
    }
}

fn float_stat(exec: &Executor, name: &str) -> f64 {
    match exec.statistics().extra.get(name) {
        Some(StatValue::Float(value)) => *value,
        Some(StatValue::Int(value)) => *value as f64,
        _ => 0.0,
    }
}

fn run_script(input: &str) -> (Executor, Vec<String>) {
    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: split-loop script should execute");
    (exec, outputs)
}

fn split_loop_stats(exec: &Executor) -> SplitLoopStats {
    SplitLoopStats {
        rebuilds: exec
            .statistics()
            .get_int("dpll.rebuilds")
            .expect("split-loop benchmark should export rebuild count"),
        sat_solve: float_stat(exec, "time.dpll.sat_solve"),
        theory_check: float_stat(exec, "time.dpll.theory_check"),
        theory_sync: float_stat(exec, "time.dpll.theory_sync"),
        replay_splits: float_stat(exec, "time.split_loop.replay_splits"),
        dpll_create: float_stat(exec, "time.split_loop.dpll_create"),
        pre_solve: float_stat(exec, "time.split_loop.pre_solve"),
        handle_step: float_stat(exec, "time.split_loop.handle_step_result"),
        post_split: float_stat(exec, "time.split_loop.post_split"),
        model_extract: float_stat(exec, "time.split_loop.model_extract"),
        store_model: float_stat(exec, "time.split_loop.store_model"),
        total: float_stat(exec, "time.split_loop.total"),
    }
}

fn accounted_split_loop_time(stats: &SplitLoopStats) -> f64 {
    stats.sat_solve
        + stats.theory_check
        + stats.theory_sync
        + stats.replay_splits
        + stats.dpll_create
        + stats.pre_solve
        + stats.handle_step
        + stats.post_split
        + stats.model_extract
        + stats.store_model
}

fn observe_split_loop_case(case: &SplitLoopCase) -> (String, f64) {
    let (exec, outputs) = run_script(case.input);

    assert_eq!(
        outputs.len(),
        2,
        "{}: expected result + statistics",
        case.name
    );
    assert_eq!(
        outputs[0], case.expected_result,
        "{}: unexpected satisfiability",
        case.name
    );
    assert_stats_contains_all(&outputs[1], &SPLIT_LOOP_STATS_KEYS);

    let stats = split_loop_stats(&exec);
    let accounted = accounted_split_loop_time(&stats);
    (
        format!(
            "{}: rebuilds={}, sat_solve={:.6}, total={:.6}, accounted={:.6}, replay={:.6}, \
             create={:.6}, pre_solve={:.6}",
            case.name,
            stats.rebuilds,
            stats.sat_solve,
            stats.total,
            accounted,
            stats.replay_splits,
            stats.dpll_create,
            stats.pre_solve
        ),
        // Return total instead of replay_splits: the incremental pipeline
        // (default for LRA) never replays splits (that's for the non-incremental
        // path). total > 0.0 proves the timing export is wired.
        stats.total,
    )
}

#[test]
fn test_lra_split_loop_exports_accumulated_timing_stats_6503() {
    let mut observations = Vec::new();
    let mut best_total = 0.0_f64;

    for case in &LRA_SPLIT_LOOP_CASES {
        let (observation, total) = observe_split_loop_case(case);
        observations.push(observation);
        best_total = best_total.max(total);
    }

    assert!(
        best_total > 0.0,
        "expected at least one split-loop case to record total timing; observations: {}",
        observations.join(" | ")
    );
}

#[test]
fn test_measure_split_loop_benchmark_6503() {
    if std::env::var_os("AY_MEASURE_SPLIT_LOOP_6503").is_none() {
        return;
    }

    let path = std::env::var("AY_MEASURE_SPLIT_LOOP_PATH")
        .unwrap_or_else(|_| "benchmarks/smtcomp/QF_LRA/sc-6.induction3.cvc.smt2".to_string());
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(path);
    let input = std::fs::read_to_string(&path).expect("benchmark should be readable");
    let (exec, outputs) = run_script(&input);
    let result = outputs
        .first()
        .cloned()
        .expect("benchmark should produce a satisfiability result");
    let stats = split_loop_stats(&exec);
    let accounted = accounted_split_loop_time(&stats);
    let unaccounted = if stats.total > accounted {
        stats.total - accounted
    } else {
        0.0
    };

    println!(
        "{path}\tresult={result}\trebuilds={rebuilds}",
        path = path.display(),
        rebuilds = stats.rebuilds,
    );
    println!(
        "  total={:.6}  accounted={accounted:.6}  unaccounted={unaccounted:.6}",
        stats.total
    );
    println!(
        "  sat_solve={:.6}  theory_check={:.6}  theory_sync={:.6}",
        stats.sat_solve, stats.theory_check, stats.theory_sync
    );
    println!(
        "  dpll_create={:.6}  pre_solve={:.6}  replay={:.6}",
        stats.dpll_create, stats.pre_solve, stats.replay_splits
    );
    println!(
        "  handle_step={:.6}  post_split={:.6}  model_extract={:.6}  store_model={:.6}",
        stats.handle_step, stats.post_split, stats.model_extract, stats.store_model
    );

    // The incremental pipeline (default for LRA) has 0 rebuilds and 0 replay.
    // Only assert properties true for both incremental and non-incremental paths.
    assert!(
        stats.sat_solve > 0.0,
        "expected accumulated SAT timing on measured benchmark, got {}",
        stats.sat_solve
    );
    assert!(
        stats.total > 0.0,
        "expected total split-loop timing, got {}",
        stats.total
    );
}
