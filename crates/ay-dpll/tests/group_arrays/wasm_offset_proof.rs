// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact external-codegen Wasm memory offset queries, including its canonical ordering.

use ay_dpll::Executor;
use ay_frontend::parse;

fn run(query: &str, expected: &str) {
    let body = query.trim_end().strip_suffix("(exit)").unwrap();
    let script = format!(
        "(set-option :produce-proofs true)\n\
         (set-option :check-proofs-strict true)\n{body}"
    );
    let mut executor = Executor::new();
    let commands = parse(&script).expect("compiler query must parse");
    let output = executor.execute_all(&commands).expect("query must run");
    assert_eq!(
        output.last().map(String::as_str),
        Some(expected),
        "strict compiler query refused: {:?}",
        executor.unknown_reason()
    );
    if expected == "unsat" {
        let command = parse("(get-proof)").unwrap();
        let proof = executor.execute_all(&command).unwrap().pop().unwrap();
        assert!(proof.contains("(assume ") && proof.contains("(cl)"));
        for rule in [":rule hole", ":rule trust"] {
            assert!(!proof.contains(rule), "compiler proof contains {rule}");
        }
    }
}

#[test]
fn wasm_offset_i64_canonical_order_publishes_a_strict_proof() {
    run(
        include_str!("wasm_offset_proof/offset-i64.lane.smt2"),
        "unsat",
    );
}

#[test]
fn wasm_offset_i64_source_order_keeps_a_strict_proof() {
    run(
        include_str!("wasm_offset_proof/offset-i64.raw.smt2"),
        "unsat",
    );
}

#[test]
fn wasm_wrong_offset_i64_keeps_a_counterexample() {
    run(
        include_str!("wasm_offset_proof/wrong-offset-i64.lane.smt2"),
        "sat",
    );
}
