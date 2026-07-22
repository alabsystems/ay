// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

use ay_sat::{parse_dimacs, SatResult};
use ntest::timeout;

fn assert_known_sat(path: &str, label: &str) {
    let cnf = match super::common::load_optional_repo_benchmark(path) {
        Some(c) => c,
        None => return,
    };
    let formula = parse_dimacs(&cnf).expect("parse");
    let original_clauses = formula.clauses.clone();

    let mut solver = formula.into_solver();
    match solver.solve().into_inner() {
        SatResult::Sat(model) => {
            super::common::assert_model_satisfies(&original_clauses, &model, label);
        }
        SatResult::Unsat(_) => {
            panic!("WRONG-UNSAT (#3913): default preprocessing returned UNSAT on known-SAT {path}");
        }
        SatResult::Unknown => {
            panic!("Unknown (#3913): expected SAT on {path}");
        }
        _ => unreachable!(),
    }
}

/// Regression test for #3913 on uf200 random 3-SAT.
#[test]
#[timeout(180_000)]
fn uf200_known_sat_preprocessing_regression_3913() {
    assert_known_sat(
        "reference/creusat/tests/satlib/UF200.860.100/uf200-01.cnf",
        "regression_3913/uf200-01",
    );
}

/// Regression test for #3913 on uf250 random 3-SAT.
#[test]
#[timeout(180_000)]
fn uf250_known_sat_preprocessing_regression_3913() {
    assert_known_sat(
        "reference/creusat/tests/satlib/UF250.1065.100/uf250-02.cnf",
        "regression_3913/uf250-02",
    );
}
