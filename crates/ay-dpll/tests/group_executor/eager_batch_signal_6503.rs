// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_dpll::{Executor, StatValue};
use ay_frontend::parse;

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

fn run_script(input: &str) -> (Executor, Vec<String>) {
    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: LRA script should execute");
    (exec, outputs)
}

#[test]
fn test_lra_statistics_export_eager_batch_counters_6503() {
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

    // QF_LRA uses the incremental split-loop pipeline (#6579), which emits
    // dpll.round_trips and lra_* counters instead of dpll.eager.* counters.
    // The dormant TheoryExtension packet for #6586 is not enabled here.
    for key in ["dpll.round_trips", "lra_checks", "lra_simplex_sat"] {
        assert!(
            exec.statistics().get_int(key).is_some(),
            "expected incremental pipeline counter {key:?} in {:?}",
            exec.statistics().extra
        );
    }

    assert!(
        int_stat(&exec, "dpll.round_trips") > 0,
        "expected round trips on QF_LRA incremental path"
    );
    assert!(
        int_stat(&exec, "lra_checks") > 0,
        "expected at least one LRA check on QF_LRA incremental path"
    );
}

#[test]
fn test_measure_simple_startup_level0_batch_signal_6503() {
    if std::env::var_os("AY_MEASURE_EAGER_BATCH_SIGNAL_6503").is_none() {
        return;
    }

    let rel_path = std::env::var("AY_MEASURE_EAGER_BATCH_SIGNAL_PATH").unwrap_or_else(|_| {
        "benchmarks/smtcomp/QF_LRA/simple_startup_5nodes.abstract.base.smt2".to_string()
    });
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(&rel_path);
    let input = std::fs::read_to_string(&path).expect("benchmark should be readable");
    let start = std::time::Instant::now();
    let (exec, outputs) = run_script(&input);
    let wall = start.elapsed().as_secs_f64();
    let result = outputs
        .iter()
        .find_map(|output| match output.as_str() {
            "sat" | "unsat" | "unknown" => Some(output.as_str()),
            _ => None,
        })
        .unwrap_or("<no-result>");

    println!(
        "{}\tresult={result}\twall_s={wall:.3}\trebuilds={}\tpropagate_calls={}\tlevel0_checks={}\tlevel0_guard_hits={}\tbatch_defers={}\tstate_unchanged_skips={}\tsat_solve_s={:.6}\tsplit_total_s={:.6}",
        path.display(),
        int_stat(&exec, "dpll.rebuilds"),
        int_stat(&exec, "dpll.eager.propagate_calls"),
        int_stat(&exec, "dpll.eager.level0_checks"),
        int_stat(&exec, "dpll.eager.level0_batch_guard_hits"),
        int_stat(&exec, "dpll.eager.batch_defers"),
        int_stat(&exec, "dpll.eager.state_unchanged_skips"),
        float_stat(&exec, "time.dpll.sat_solve"),
        float_stat(&exec, "time.split_loop.total"),
    );

    assert!(
        exec.statistics()
            .get_int("dpll.eager.level0_batch_guard_hits")
            .is_some(),
        "measurement run should export eager batch signal counters"
    );
}
