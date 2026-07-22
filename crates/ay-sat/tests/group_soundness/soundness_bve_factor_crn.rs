// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

use ay_sat::{parse_dimacs, SatResult};
use ntest::timeout;

/// Regression test: crn_11_99_u (1287 vars, 2332 clauses) is known UNSAT
/// (verified by CaDiCaL 3.0.0 in 0.41s with 53K conflicts).
///
/// #8397: The root cause was BVE pruning root-level-false literals from
/// resolvents, which broke the conditional autarky property during multi-
/// variable reconstruction cascades. The fix keeps root-false literals in
/// resolvents, making reconstruction sound.
///
/// Related: #5543 (BVE-only UNKNOWN on manol-pipe-c9), #3864 (reconstruction
/// rollback gap).
#[test]
#[timeout(60_000)]
fn crn_11_99_u_default_preprocessing_must_be_unsat() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/crn_11_99_u.cnf");
    let content = std::fs::read_to_string(&path).unwrap_or_else(|error| {
        panic!(
            "required tracked BVE fixture {} is unavailable: {error}",
            path.display()
        )
    });
    let formula = parse_dimacs(&content).expect("parse crn_11_99_u.cnf");
    let mut solver = formula.into_solver();
    let result = solver.solve().into_inner();
    match result {
        SatResult::Unsat(_) => {} // correct
        SatResult::Sat(_) => panic!("crn_11_99_u: known UNSAT returned SAT (soundness bug)"),
        SatResult::Unknown => panic!(
            "crn_11_99_u: known UNSAT returned Unknown — BVE+factor preprocessing \
             interaction bug (model verification caught invalid SAT assignment)"
        ),
        _ => unreachable!(),
    }
}

/// Workaround confirmation: disabling BVE allows the solver to find UNSAT.
#[test]
#[timeout(60_000)]
fn crn_11_99_u_no_bve_is_unsat() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/crn_11_99_u.cnf");
    let content = std::fs::read_to_string(&path).unwrap_or_else(|error| {
        panic!(
            "required tracked BVE fixture {} is unavailable: {error}",
            path.display()
        )
    });
    let formula = parse_dimacs(&content).expect("parse");
    let mut solver = formula.into_solver();
    solver.set_bve_enabled(false);
    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "crn_11_99_u with BVE disabled must be UNSAT, got {result:?}"
    );
}

/// With factoring disabled, the solver may return UNSAT or Unknown depending
/// on the BVE elimination choices. The key correctness assertion is that it
/// NEVER returns SAT (since the formula is known UNSAT).
///
/// Prior to #8397 fix, disabling factoring was a workaround for the BVE
/// reconstruction soundness bug. Now that root-false literals are kept in
/// resolvents, the default path reliably gives UNSAT. The no-factor path
/// may return Unknown (search incomplete) because BVE's longer resolvents
/// change elimination economics, and without factoring the solver may not
/// have enough simplification to find UNSAT within its search budget.
#[test]
#[timeout(60_000)]
fn crn_11_99_u_no_factor_must_not_return_sat() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/crn_11_99_u.cnf");
    let content = std::fs::read_to_string(&path).unwrap_or_else(|error| {
        panic!(
            "required tracked BVE fixture {} is unavailable: {error}",
            path.display()
        )
    });
    let formula = parse_dimacs(&content).expect("parse");
    let mut solver = formula.into_solver();
    solver.set_factor_enabled(false);
    let result = solver.solve().into_inner();
    assert!(
        !matches!(result, SatResult::Sat(_)),
        "crn_11_99_u with factoring disabled must not return SAT (known UNSAT), got {result:?}"
    );
}
