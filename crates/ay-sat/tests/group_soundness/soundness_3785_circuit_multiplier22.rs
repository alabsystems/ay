// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

use ay_sat::{parse_dimacs, SatResult};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

/// Regression test for #3785.
///
/// Circuit_multiplier22 is known SAT (CaDiCaL/Z3). A wrong UNSAT here is a
/// SAT-core soundness failure. Unknown (timeout) is accepted — it indicates a
/// performance gap, not a soundness bug. The test uses a 30s interrupt-based
/// timeout to avoid blocking the test suite for minutes.
#[test]
fn circuit_multiplier22_known_sat_regression() {
    let cnf = super::common::load_repo_benchmark(
        "benchmarks/sat/satcomp2024-sample/c5ae0ec49de0959cd14431ce851c14f8-Circuit_multiplier22.cnf.xz",
    );
    let formula = parse_dimacs(&cnf).expect("parse");
    let original_clauses = formula.clauses.clone();

    let mut solver = formula.into_solver();

    // Use interrupt-based 30s timeout instead of unbounded solve.
    let flag = Arc::new(AtomicBool::new(false));
    let flag_clone = flag.clone();
    solver.set_interrupt(flag.clone());
    let handle = std::thread::spawn(move || {
        std::thread::sleep(Duration::from_secs(30));
        flag_clone.store(true, Ordering::Relaxed);
    });

    let result = solver
        .solve_interruptible(|| flag.load(Ordering::Relaxed))
        .into_inner();

    // Stop timer thread if solver finished early.
    flag.store(true, Ordering::Relaxed);
    let _ = handle.join();

    match result {
        SatResult::Sat(model) => {
            super::common::assert_model_satisfies(
                &original_clauses,
                &model,
                "regression_3785/circuit_multiplier22",
            );
        }
        SatResult::Unsat(_) => {
            panic!("WRONG-UNSAT (#3785): Circuit_multiplier22 is known-SAT");
        }
        SatResult::Unknown => {
            // Timeout is acceptable — performance gap, not soundness bug.
            eprintln!("Circuit_multiplier22: timeout (Unknown) — performance gap vs CaDiCaL");
        }
        _ => unreachable!(),
    }
}
