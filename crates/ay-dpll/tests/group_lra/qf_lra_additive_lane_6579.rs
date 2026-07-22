// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Additive-lane trace harness for #6579.
//!
//! Verifies that compound wakeup counters (`lra_simplex_sat`,
//! `lra_compound_use_vars`, `lra_compound_wake_dirty_hits`,
//! `lra_compound_wake_candidates`, `lra_compound_queued`) are exported
//! through the executor statistics interface regardless of solve outcome
//! (sat, unsat, unknown).
//!
//! The env-gated `test_measure_additive_lane_6579` runs real benchmarks
//! (sc-6, sc-21) and prints the trace surface for routing decisions.
//!
//! Part of #6579.

use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use ay_dpll::{Executor, StatValue};
use ay_frontend::parse;

/// Compound-lane counter names exported by the LRA solver (#6579).
const COMPOUND_STAT_KEYS: [&str; 4] = [
    "lra_compound_use_vars",
    "lra_compound_wake_dirty_hits",
    "lra_compound_wake_candidates",
    "lra_compound_queued",
];

fn run_script(input: &str) -> (Executor, Vec<String>) {
    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: script should execute");
    (exec, outputs)
}

fn int_stat(exec: &Executor, name: &str) -> u64 {
    exec.statistics().get_int(name).unwrap_or(0)
}

fn float_stat(exec: &Executor, name: &str) -> f64 {
    match exec.statistics().extra.get(name) {
        Some(StatValue::Float(value)) => *value,
        Some(StatValue::Int(value)) => *value as f64,
        _ => 0.0,
    }
}

fn benchmark_input(rel_path: &str) -> String {
    let repo_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let path = repo_root.join(rel_path);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("failed to read {rel_path}: {e}"))
}

fn classify_sc6_boundary(exec: &Executor, result: &str) -> &'static str {
    if result == "timeout" {
        return "timeout-before-diagnosis";
    }
    let round_trips = int_stat(exec, "dpll.round_trips");
    let simplex_sat = int_stat(exec, "lra_simplex_sat");
    let compound_use_vars = int_stat(exec, "lra_compound_use_vars");
    let wake_dirty_hits = int_stat(exec, "lra_compound_wake_dirty_hits");
    let wake_candidates = int_stat(exec, "lra_compound_wake_candidates");
    let compound_queued = int_stat(exec, "lra_compound_queued");

    if round_trips == 0 {
        "split-loop-inactive"
    } else if simplex_sat == 0 {
        "pre-simplex-boundary"
    } else if compound_use_vars == 0 {
        "compound-registration-gap"
    } else if wake_dirty_hits == 0 {
        "dirty-wake-gap"
    } else if wake_candidates == 0 {
        "wake-candidate-gap"
    } else if compound_queued == 0 {
        "pre-queue-live-boundary"
    } else if result == "sat" {
        "sat"
    } else {
        "post-queue-boundary"
    }
}

/// Verify that compound stats keys exist in executor after a QF_LRA solve.
/// Accepts any result (sat/unsat/unknown) — the point is stats visibility.
#[test]
fn test_compound_stats_exported_on_sat_6579() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (>= x 0.0))
        (assert (<= x 10.0))
        (assert (>= y 0.0))
        (assert (<= y 10.0))
        (assert (= (+ x y) 5.0))
        (check-sat)
    "#;
    let (exec, outputs) = run_script(input);
    assert_eq!(outputs.len(), 1, "expected one output from check-sat");
    assert_eq!(outputs[0], "sat", "simple additive formula should be sat");

    // All compound stat keys should be present (possibly zero).
    for key in &COMPOUND_STAT_KEYS {
        assert!(
            exec.statistics().get_int(key).is_some(),
            "missing compound stat key {key} after sat result"
        );
    }
}

#[test]
fn test_compound_stats_exported_on_unsat_6579() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (>= x 3.0))
        (assert (>= y 3.0))
        (assert (= (+ x y) 5.0))
        (check-sat)
    "#;
    let (exec, outputs) = run_script(input);
    assert_eq!(outputs[0], "unsat");

    // Stats should still be exported even on unsat when the additive path is active.
    for key in &COMPOUND_STAT_KEYS {
        assert!(
            exec.statistics().get_int(key).is_some(),
            "missing compound stat key {key} after unsat result"
        );
    }
}

/// Run a benchmark with an interrupt timeout, returning the executor and result string.
///
/// The done flag lets the watchdog exit early when the solve completes,
/// avoiding a full timeout wait on benchmarks that solve quickly.
fn solve_with_timeout_secs(input: &str, timeout_secs: u64) -> (Executor, &'static str) {
    use std::sync::atomic::Ordering;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let interrupt = Arc::new(AtomicBool::new(false));
    let done = Arc::new(AtomicBool::new(false));
    exec.set_interrupt(interrupt.clone());
    let done_clone = done.clone();
    let handle = std::thread::spawn(move || {
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(timeout_secs);
        while std::time::Instant::now() < deadline {
            if done_clone.load(Ordering::Relaxed) {
                return;
            }
            std::thread::sleep(std::time::Duration::from_millis(50));
        }
        interrupt.store(true, Ordering::SeqCst);
    });

    let mut result: &str = "error";
    for cmd in &commands {
        match exec.execute(cmd) {
            Ok(Some(ref output)) => match output.as_str() {
                "sat" => result = "sat",
                "unsat" => result = "unsat",
                "unknown" => result = "unknown",
                _ => {}
            },
            Ok(None) => {}
            Err(_) => break,
        }
    }
    done.store(true, Ordering::Relaxed);
    let _ = handle.join();
    (exec, result)
}

fn solve_with_timeout(input: &str) -> (Executor, &'static str) {
    solve_with_timeout_secs(input, 10)
}

fn print_benchmark_stats(exec: &Executor, label: &str, rel_path: &str, result: &str) {
    println!("--- {label} ---");
    println!("  path:       {rel_path}");
    println!("  result:     {result}");
    println!(
        "  simplex_sat:              {}",
        int_stat(exec, "lra_simplex_sat")
    );
    println!(
        "  round_trips:              {}",
        int_stat(exec, "dpll.round_trips")
    );
    println!(
        "  compound_use_vars:        {}",
        int_stat(exec, "lra_compound_use_vars")
    );
    println!(
        "  compound_wake_dirty_hits: {}",
        int_stat(exec, "lra_compound_wake_dirty_hits")
    );
    println!(
        "  compound_wake_candidates: {}",
        int_stat(exec, "lra_compound_wake_candidates")
    );
    println!(
        "  compound_queued:          {}",
        int_stat(exec, "lra_compound_queued")
    );
    println!(
        "  theory_reconstruct:       {:.6}",
        float_stat(exec, "time.split_loop.theory_reconstruct")
    );
    println!(
        "  sat_solve:                {:.6}",
        float_stat(exec, "time.dpll.sat_solve")
    );
    println!(
        "  theory_conflicts:         {}",
        int_stat(exec, "dpll.theory_conflicts")
    );
    println!(
        "  theory_propagations:      {}",
        int_stat(exec, "dpll.theory_propagations")
    );
    println!(
        "  eager_propagate_calls:    {}",
        int_stat(exec, "dpll.eager.propagate_calls")
    );
    println!(
        "  eager_level0_checks:      {}",
        int_stat(exec, "dpll.eager.level0_checks")
    );
    println!(
        "  split_loop_total:         {:.6}",
        float_stat(exec, "time.split_loop.total")
    );
    if rel_path.ends_with("sc-6.induction3.cvc.smt2") {
        println!(
            "  boundary:                 {}",
            classify_sc6_boundary(exec, result)
        );
    }
    println!();
}

#[test]
fn test_sc6_persistent_boundary_6579() {
    let input = benchmark_input("benchmarks/smtcomp/QF_LRA/sc-6.induction3.cvc.smt2");
    let (exec, result) = solve_with_timeout_secs(&input, 30);
    let round_trips = int_stat(&exec, "dpll.round_trips");
    let simplex_sat = int_stat(&exec, "lra_simplex_sat");
    let compound_use_vars = int_stat(&exec, "lra_compound_use_vars");
    let wake_dirty_hits = int_stat(&exec, "lra_compound_wake_dirty_hits");
    let wake_candidates = int_stat(&exec, "lra_compound_wake_candidates");
    let compound_queued = int_stat(&exec, "lra_compound_queued");
    let boundary = classify_sc6_boundary(&exec, result);

    eprintln!(
        "[#6579 trace] sc-6 executor: result={result}, round_trips={round_trips}, \
         simplex_sat={simplex_sat}, compound_use_vars={compound_use_vars}, \
         wake_dirty_hits={wake_dirty_hits}, wake_candidates={wake_candidates}, \
         compound_queued={compound_queued}, boundary={boundary}"
    );

    assert_eq!(
        result, "sat",
        "sc-6 should stay sat on the persistent eager path"
    );

    assert!(
        round_trips > 0,
        "sc-6 should exercise the incremental split loop (dpll.round_trips={round_trips})"
    );
    assert!(
        simplex_sat > 0,
        "sc-6 should reach simplex sat at least once (lra_simplex_sat={simplex_sat})"
    );
    assert!(
        compound_use_vars > 0,
        "sc-6 should register compound vars (lra_compound_use_vars={compound_use_vars})"
    );

    assert!(
        wake_dirty_hits > 0,
        "sc-6 should observe dirty wake hits (lra_compound_wake_dirty_hits={wake_dirty_hits})"
    );
    assert!(
        wake_candidates > 0,
        "sc-6 should enumerate wake candidates (lra_compound_wake_candidates={wake_candidates})"
    );
}

/// #7966: Regression test for persistent final-check stale model-equality suppression.
///
/// This formula uses arrays with integer indices that trigger NeedModelEquality
/// requests during theory combination. The persistent eager path should suppress
/// already-encoded model equalities without consuming the round budget.
///
/// The key invariant: the solver must converge (sat) without degrading to Unknown
/// from model-equality round exhaustion.
#[test]
fn test_persistent_stale_model_equality_suppression_7966() {
    // QF_AUFLIA formula: two stores to the same array with potentially equal indices.
    // The arrays theory will emit NeedModelEquality(i, j) to decide whether
    // (select (store (store a i 1) j 2) i) equals 1 or 2.
    // After the first encoding, repeated final-check calls should not re-consume
    // the model-equality round budget.
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (assert (= (select (store (store a i 1) j 2) i) 1))
        (assert (not (= i j)))
        (check-sat)
    "#;
    let (exec, outputs) = run_script(input);
    assert_eq!(outputs.len(), 1, "expected one check-sat output");
    assert_eq!(
        outputs[0], "sat",
        "#7966: persistent path should converge to sat without round exhaustion"
    );

    // Also verify with equal indices (should be unsat: select returns 2, not 1).
    let input_unsat = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (assert (= (select (store (store a i 1) j 2) i) 1))
        (assert (= i j))
        (check-sat)
    "#;
    let (_exec_u, outputs_u) = run_script(input_unsat);
    assert_eq!(outputs_u.len(), 1, "expected one check-sat output");
    assert_eq!(
        outputs_u[0], "unsat",
        "#7966: when i=j, store overwrites and select(... i) = 2 != 1"
    );

    // Verify the solver did not burn excessive round trips for the sat case.
    let round_trips = int_stat(&exec, "dpll.round_trips");
    assert!(
        round_trips <= 10,
        "#7966: persistent model-equality suppression should keep round trips low (got {round_trips})"
    );
}

/// Env-gated benchmark trace for additive lane diagnosis.
///
/// Run with:
///   AY_MEASURE_ADDITIVE_6579=1 cargo test -p ay-dpll --release \
///     --test qf_lra_additive_lane_6579 test_measure_additive_lane_6579 -- --nocapture
#[test]
fn test_measure_additive_lane_6579() {
    if std::env::var_os("AY_MEASURE_ADDITIVE_6579").is_none() {
        return;
    }

    let benchmarks = [
        (
            "sc-6 (green control)",
            "benchmarks/smtcomp/QF_LRA/sc-6.induction3.cvc.smt2",
        ),
        (
            "sc-21 (red target)",
            "benchmarks/smtcomp/QF_LRA/sc-21.induction2.cvc.smt2",
        ),
    ];
    let repo_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");

    for (label, rel_path) in &benchmarks {
        let path = repo_root.join(rel_path);
        if !path.exists() {
            println!("SKIP {label}: {rel_path} not found");
            continue;
        }
        let input = std::fs::read_to_string(&path).expect("benchmark should be readable");
        let (exec, result) = solve_with_timeout(&input);
        print_benchmark_stats(&exec, label, rel_path, result);
    }
}
