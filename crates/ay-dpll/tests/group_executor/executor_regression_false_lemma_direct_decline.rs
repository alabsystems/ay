// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression: a FALSE lemma the wire-gap repair offers the printer is
//! declined by the complete bit-blast's direct solve, not by its sweep.
//!
//! `regression_false_lemma_direct_decline.smt2` is UNSAT by a preprocessor
//! fold. With proofs observable, the repair asks whether the first assertion
//! alone prints as a refutation: a false lemma over a 64-bit divider and
//! multiplier. The direct lane found its model and declined, the case split
//! and the sweep then spent their envelopes, and the monolithic search last
//! said "satisfiable" again; at every ask. Measured 2026-10-08 on the CLI:
//! `unknown (timeout)` at the query's 60 s before the fix, `unsat` in 1.2 s
//! after it (`sat_sweep::Direct::Satisfiable`).

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

#[test]
#[timeout(300_000)]
fn a_false_lemma_costs_the_wire_gap_repair_one_direct_solve() {
    let mut path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("../../tests/bv/regression_false_lemma_direct_decline.smt2");
    let input = std::fs::read_to_string(path).expect("read the regression query");

    let commands = parse(&input).expect("parse");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all");

    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "the verdict must not wait out the query's timeout: {outputs:?}"
    );
}
