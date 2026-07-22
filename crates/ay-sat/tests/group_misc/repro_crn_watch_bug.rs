// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for crn_11_99_u watch list corruption bug (#7991).
//!
//! Root cause: `reattach_jit_watches()` created duplicate and stale watch
//! entries when called after JIT invalidation with budget_exhausted. The
//! fix (commit 99b50f392) adds a Phase 2 that strips existing watch entries
//! for JIT-eligible clauses before reattaching fresh entries.
//!
//! The default-config test is the primary regression gate. A ChrBT-disabled
//! variant was omitted because it hits a separate conflict analysis bug
//! ("trail exhausted in conflict analysis"), unrelated to watch corruption.

#![allow(clippy::panic)]

use ay_sat::{parse_dimacs, SatResult};
use ntest::timeout;

fn load_crn() -> Option<ay_sat::DimacsFormula> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/crn_11_99_u.cnf");
    if !path.exists() {
        eprintln!(
            "crn_11_99_u: benchmark missing at {}, skipping",
            path.display()
        );
        return None;
    }
    let content = std::fs::read_to_string(&path).expect("read crn_11_99_u.cnf");
    Some(parse_dimacs(&content).expect("parse crn_11_99_u.cnf"))
}

/// Test with ChrBT trail reuse disabled but ChrBT enabled.
/// Must not return SAT (formula is known UNSAT). May return Unknown
/// if the solver cannot find UNSAT within its search budget with this
/// configuration.
#[test]
#[timeout(60_000)]
fn crn_no_chrono_reuse_must_not_return_sat() {
    let Some(formula) = load_crn() else { return };
    let mut solver = formula.into_solver();
    solver.set_chrono_reuse_trail(false);
    let result = solver.solve().into_inner();
    match result {
        SatResult::Unsat(_) | SatResult::Unknown => {}
        SatResult::Sat(_) => {
            panic!("crn_11_99_u (no chrono reuse): known UNSAT returned SAT (soundness bug)")
        }
        _ => unreachable!(),
    }
}

/// Test with ALL inprocessing disabled — if this passes, the bug is in inprocessing.
#[test]
#[timeout(60_000)]
fn crn_no_inprocessing_must_be_unsat() {
    let Some(formula) = load_crn() else { return };
    let mut solver = formula.into_solver();
    solver.disable_all_inprocessing();
    let result = solver.solve().into_inner();
    match result {
        SatResult::Unsat(_) => {}
        other => panic!("crn_11_99_u (no inprocessing): expected UNSAT, got {other:?}"),
    }
}

/// Default configuration: reproduces the crash.
#[test]
#[timeout(60_000)]
fn crn_default_must_be_unsat() {
    let Some(formula) = load_crn() else { return };
    let mut solver = formula.into_solver();
    let result = solver.solve().into_inner();
    match result {
        SatResult::Unsat(_) => {}
        other => panic!("crn_11_99_u (default): expected UNSAT, got {other:?}"),
    }
}
