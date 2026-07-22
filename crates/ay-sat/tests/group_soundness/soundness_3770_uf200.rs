// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

use ay_sat::{parse_dimacs, SatResult};
use ntest::timeout;

/// Solve a known-SAT CNF and verify the result.
///
/// Returns `Err(name)` on wrong-UNSAT, panics on Unknown or invalid model.
fn solve_known_sat(cnf: &str, label: &str) -> Result<(), String> {
    let formula = parse_dimacs(cnf).expect("parse");
    let original_clauses = formula.clauses.clone();
    let mut solver = formula.into_solver();
    let result = solver.solve().into_inner();
    match &result {
        SatResult::Sat(model) => {
            super::common::assert_model_satisfies(&original_clauses, model, label);
            Ok(())
        }
        SatResult::Unsat(_) => Err(label.to_owned()),
        SatResult::Unknown => panic!("Unknown on known-SAT {label}"),
        _ => unreachable!(),
    }
}

/// Regression test (#3770): default preprocessing must not return UNSAT on
/// known-SAT uf200 instances.
#[test]
#[timeout(300_000)]
fn uf200_known_sat_default_config_regression() {
    let sat_benchmarks = &[
        "reference/creusat/tests/satlib/UF200.860.100/uf200-036.cnf",
        "reference/creusat/tests/satlib/UF200.860.100/uf200-043.cnf",
    ];
    for relative_path in sat_benchmarks {
        let path = super::common::workspace_root().join(relative_path);
        let Some(cnf) = super::common::load_optional_benchmark(&path) else {
            return;
        };
        let name = relative_path.rsplit('/').next().unwrap();
        if let Err(label) = solve_known_sat(&cnf, &format!("default-uf200/{name}")) {
            panic!("WRONG-UNSAT: default config returned UNSAT on known-SAT {label}");
        }
    }
}

/// Soundness gate (#3815): all 100 uf200-860 instances must return SAT with
/// valid models. This exercises block-UIP shrink + minimize_keep on random
/// 3-SAT at the satisfiability threshold. Any wrong-UNSAT is a soundness bug.
#[test]
#[timeout(600_000)]
fn uf200_all_100_shrink_soundness_gate() {
    let dir = super::common::workspace_root().join("reference/creusat/tests/satlib/UF200.860.100");
    if !dir.exists() {
        assert!(
            std::env::var_os("CI").is_none(),
            "UF200.860.100 directory missing in CI: {}",
            dir.display()
        );
        eprintln!("SKIP: UF200.860.100 directory not found, skipping all-100 test");
        return;
    }

    // Gate: verify shrink is enabled by default (#3815). If a future change
    // disables shrink, this fires instead of silently losing coverage.
    assert!(
        ay_sat::Solver::new(1).inprocessing_feature_profile().shrink,
        "BUG: shrink disabled — this gate requires shrink_enabled=true",
    );

    let mut entries: Vec<_> = std::fs::read_dir(&dir)
        .expect("read UF200 dir")
        .filter_map(Result::ok)
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "cnf"))
        .collect();
    entries.sort_by_key(std::fs::DirEntry::file_name);
    assert_eq!(
        entries.len(),
        100,
        "Expected 100 uf200 benchmarks, found {}",
        entries.len()
    );

    let mut wrong_unsats = Vec::new();
    for entry in &entries {
        let path = entry.path();
        let name = path.file_name().unwrap().to_string_lossy();
        let cnf = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {name}: {e}"));
        if let Err(label) = solve_known_sat(&cnf, &format!("uf200-all/{name}")) {
            wrong_unsats.push(label);
        }
    }

    assert!(
        wrong_unsats.is_empty(),
        "WRONG-UNSAT on {}/{} uf200 instances: {:?}",
        wrong_unsats.len(),
        entries.len(),
        wrong_unsats,
    );
}
