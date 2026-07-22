// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Soundness regressions for QF_ALIA spurious array models.
//!
//! The array theory could produce a candidate model whose reconstructed
//! store/select interpretation, evaluated independently over the concrete
//! arithmetic index values, REFUTES an original assertion (store-congruence
//! over arithmetic indices). Model validation previously DELEGATED such a
//! concrete `Bool(false)` array assertion back to the array theory that
//! produced the model — a circular trust bypass that let an UNSAT formula be
//! reported SAT.
//!
//! The fix makes a CONCRETE false evaluation of an array assertion a hard
//! refutation of the candidate model: it fails closed (Incomplete -> Unknown)
//! instead of delegating. These benchmarks are declared UNSAT and z3 confirms
//! UNSAT, so the only sound AY outcomes are `unsat` or `unknown`. Reporting
//! `sat` is a wrong answer and MUST NOT regress.

mod common;

use common::SolverOutcome;
use ntest::timeout;

fn assert_not_spuriously_sat(rel_path: &str) {
    let path = common::workspace_path(rel_path);
    if !path.is_file() {
        eprintln!(
            "skipping optional QF_ALIA soundness benchmark not present in this checkout: {}",
            path.display()
        );
        return;
    }

    let outcome = common::run_executor_file_with_timeout(&path, 30)
        .unwrap_or_else(|err| panic!("solver error on {rel_path}: {err}"));
    assert_ne!(
        outcome,
        SolverOutcome::Sat,
        "{rel_path} is declared/z3 UNSAT; AY must not report SAT (spurious array \
         model). Sound outcomes are unsat or unknown (fail-closed)."
    );
}

#[test]
#[timeout(60_000)]
fn read2_not_spuriously_sat() {
    assert_not_spuriously_sat("benchmarks/smtcomp/QF_ALIA/cvc/read2.smt2");
}

#[test]
#[timeout(60_000)]
fn ios_store_congruence_not_spuriously_sat() {
    assert_not_spuriously_sat(
        "benchmarks/smtcomp/QF_ALIA/ios/ios_t1_ios_bia_np_sf_ai_00002_001.cvc.smt2",
    );
}
