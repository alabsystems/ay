// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_dpll::Executor;
use ay_dpll::StatValue;
use ay_frontend::parse;

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

fn int_stat(exec: &Executor, name: &str) -> u64 {
    exec.statistics().get_int(name).unwrap_or(0)
}

fn emit_measurement_row(path: &str) {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(path);
    let input = std::fs::read_to_string(&path).expect("benchmark should be readable");
    let commands = parse(&input).expect("benchmark should parse");
    let mut exec = Executor::new();
    let start = std::time::Instant::now();
    let outputs = exec
        .execute_all(&commands)
        .expect("benchmark should execute");
    let result = outputs
        .iter()
        .find_map(|output| match output.as_str() {
            "sat" | "unsat" | "unknown" => Some(output.as_str()),
            _ => None,
        })
        .unwrap_or("<no-result>");
    let wall = start.elapsed().as_secs_f64();

    println!(
        "{}\t{result}\t{wall:.3}\t{:.3}\t{:.3}\t{:.3}\t{:.3}\t{:.3}\t{:.3}\t{:.3}\t{:.3}\t{}\t{:.3}\t{:.3}\t{:.3}",
        path.display(),
        float_stat(&exec, "time.construct.preprocess"),
        float_stat(&exec, "time.construct.tseitin"),
        float_stat(&exec, "time.construct.from_tseitin"),
        float_stat(&exec, "time.construct.clause_load"),
        float_stat(&exec, "time.construct.theory_atom_scan"),
        float_stat(&exec, "time.construct.freeze_internalize"),
        float_stat(&exec, "time.construct.extension_register_atoms"),
        float_stat(&exec, "time.construct.extension_bound_axioms"),
        int_stat(&exec, "dpll.rebuilds"),
        float_stat(&exec, "time.dpll.sat_solve"),
        float_stat(&exec, "time.dpll.theory_check"),
        float_stat(&exec, "time.dpll.theory_sync"),
    );
}

#[test]
fn test_lra_all_statistics_include_construction_counters_6364() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (> x 0.0))
        (assert (< y 10.0))
        (assert (= (+ x y) 7.0))
        (check-sat)
        (get-info :all-statistics)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: LRA script should execute");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");

    let stats = &outputs[1];
    // QF_LRA defaults to the incremental split-loop pipeline, which emits
    // timing stats and round-trip counters. The full DpllT construction
    // sub-phase timings (from_tseitin, clause_load, etc.) are still specific
    // to the non-incremental path.
    assert_stats_contains_all(
        stats,
        &[
            ":time.dpll.sat-solve",
            ":time.dpll.theory-check",
            ":time.dpll.theory-sync",
            ":time.construct.preprocess",
        ],
    );
}

#[test]
fn test_emit_construction_measurements_6364() {
    if std::env::var_os("AY_MEASURE_CONSTRUCTION").is_none() {
        return;
    }

    let paths: Vec<String> = std::env::var("AY_MEASURE_PATHS")
        .map(|value| value.split(':').map(str::to_owned).collect())
        .unwrap_or_else(|_| {
            vec![
                "benchmarks/smtcomp/QF_LRA/simple_startup_5nodes.abstract.base.smt2".to_string(),
                "benchmarks/smtcomp/QF_LRA/simple_startup_10nodes.bug.induct.smt2".to_string(),
                "benchmarks/smtcomp/QF_LRA/sc-6.induction3.cvc.smt2".to_string(),
                "benchmarks/smtcomp/QF_LRA/sc-21.induction2.cvc.smt2".to_string(),
            ]
        });

    println!(
        "file\tresult\twall_s\tpreprocess_s\ttseitin_s\tfrom_tseitin_s\tclause_load_s\ttheory_atom_scan_s\tfreeze_internalize_s\text_register_atoms_s\text_bound_axioms_s\trebuilds\tsat_solve_s\ttheory_check_s\ttheory_sync_s"
    );

    for path in paths {
        emit_measurement_row(&path);
    }
}
