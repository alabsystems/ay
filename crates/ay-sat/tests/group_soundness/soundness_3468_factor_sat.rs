// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

use ay_sat::{parse_dimacs, Literal, SatResult};
use ntest::timeout;

fn run_isolated_factor_sat_case(path: &str, label: &str) {
    if !std::path::Path::new(path).exists() {
        eprintln!("{label}: benchmark missing, skipping: {path}");
        return;
    }
    let content = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("{label}: failed to read {path}: {e}"));
    let formula =
        parse_dimacs(&content).unwrap_or_else(|e| panic!("{label}: failed to parse {path}: {e}"));
    let original_clauses: Vec<Vec<Literal>> = formula.clauses.clone();

    let mut solver = formula.into_solver();
    super::common::disable_all_inprocessing(&mut solver);
    solver.set_factor_enabled(true);

    let result = solver.solve().into_inner();
    let factor_stats = solver.factor_stats();
    assert!(factor_stats.rounds > 0, "{label}: factorization never ran");

    match result {
        SatResult::Sat(model) => {
            super::common::assert_model_satisfies(&original_clauses, &model, label);
        }
        SatResult::Unsat(_) => {
            eprintln!(
                "{label}: factor stats before UNSAT: rounds={}, factored_count={}, extension_vars={}",
                factor_stats.rounds, factor_stats.factored_count, factor_stats.extension_vars
            );
            panic!("{label}: known-SAT benchmark returned UNSAT")
        }
        SatResult::Unknown => {
            panic!("{label}: benchmark returned Unknown")
        }
        _ => unreachable!(),
    }
}

/// Regression test for #3468:
/// factorization in isolation must preserve SAT + model validity on stric-bmc-ibm-10.
#[test]
#[timeout(180_000)]
fn factor_isolated_sat_stric_bmc_ibm_10() {
    run_isolated_factor_sat_case(
        concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../reference/creusat/tests/cnf-hard/stric-bmc-ibm-10.cnf"
        ),
        "factor_isolated_sat_stric_bmc_ibm_10",
    );
}

/// Regression test for #3468:
/// stric-bmc-ibm-12 must remain SAT in isolated-factor mode.
#[test]
#[timeout(600_000)]
fn factor_isolated_sat_stric_bmc_ibm_12() {
    run_isolated_factor_sat_case(
        concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../reference/creusat/tests/cnf-hard/stric-bmc-ibm-12.cnf"
        ),
        "factor_isolated_sat_stric_bmc_ibm_12",
    );
}
