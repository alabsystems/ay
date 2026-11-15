// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact array-free queries emitted by ExternalCodegen's shared memory-read owner.
//! No array axioms, finite-memory interpretation or new solver premise.

use super::super::Executor;

const POSITIVE: &str = include_str!("fixtures/array_read_ite_positive.smt2");
const WRONG_VALUE: &str = include_str!("fixtures/array_read_ite_wrong_value.smt2");

fn solve(text: &str) -> (Executor, Vec<String>) {
    let commands = ay_frontend::parse(&format!(
        "(set-option :produce-proofs true)\n(set-option :check-proofs-strict true)\n{text}"
    ))
    .expect("the exact compiler-emitted query parses");
    let mut executor = Executor::new();
    let results = executor.execute_all(&commands).expect("query executes");
    (executor, results)
}

#[test]
fn compiler_array_read_ite_has_a_complete_authored_proof() {
    let (executor, results) = solve(POSITIVE);
    assert_eq!(
        results,
        ["unsat", "exit"],
        "strict publication must close the actual query"
    );
    let proof = executor
        .last_proof
        .as_ref()
        .expect("UNSAT retains its derivation");
    let quality = executor
        .check_proof_strict_with_datatypes(proof)
        .expect("the unchanged strict checker judges the entire derivation");
    assert!(quality.is_complete());
    let mut bytes = Vec::new();
    executor
        .try_export_last_proof_alethe_for_problem_scope_to(&mut bytes)
        .expect("the exact authored scope remains exportable")
        .expect("export succeeds");
    println!(
        "ARRAY_READ_ITE_CERT={}",
        serde_json::json!({
            "type": "alethe_certificate", "version": "1.0",
            "problem": POSITIVE,
            "proof": String::from_utf8(bytes).expect("Alethe is UTF-8"),
        })
    );
}

#[test]
fn compiler_array_read_ite_wrong_stored_value_remains_sat() {
    let (_, results) = solve(WRONG_VALUE);
    assert_eq!(results, ["sat", "exit"]);
}

#[test]
fn compiler_array_read_ite_missing_guard_remains_sat() {
    let unguarded = POSITIVE.replace("(and (= p q) (not", "(and true (not");
    let (_, results) = solve(&unguarded);
    assert_eq!(results, ["sat", "exit"]);
}

#[test]
fn compiler_array_read_ite_literal_spellings_keep_complete_export() {
    for constant in ["#b01", "(_ bv01 2)"] {
        let text = POSITIVE.replace("(_ bv1 2)", constant);
        let (executor, results) = solve(&text);
        assert_eq!(results, ["unsat", "exit"], "{constant}");
        let proof = executor.last_proof.as_ref().expect("proof");
        assert!(executor
            .check_proof_strict_with_datatypes(proof)
            .expect("strict checker")
            .is_complete());
        let mut bytes = Vec::new();
        executor
            .try_export_last_proof_alethe_for_problem_scope_to(&mut bytes)
            .expect("authored scope")
            .expect("export");
    }
}
