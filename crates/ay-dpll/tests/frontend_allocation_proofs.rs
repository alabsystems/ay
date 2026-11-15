// Copyright 2026 Andrew Yates | Apache-2.0

//! Bounded allocation VCs transcribed from the frontend's typed debug AST.
//! These exercise the original guards, saturated multiplication, and byte
//! limits. They qualify the solver/proof path, not compiler proof transport.

use ay_dpll::Executor;
use ay_frontend::parse;

fn check(script: &str, expected: &str) {
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    let commands = parse(script).expect("well-typed allocation formula");
    assert_eq!(executor.execute_all(&commands).unwrap(), [expected]);
    if expected == "sat" {
        return;
    }
    let proof = executor.last_proof().expect("retained refutation");
    let checked = ay_proof::check_proof_strict(proof, executor.terms())
        .expect("original allocation clause must pass strict checking");
    assert_eq!(checked.trust_count, 0);
    let proof = executor
        .execute_all(&parse("(get-proof)").unwrap())
        .unwrap();
    let proof = proof.last().expect("Alethe output");
    assert!(!proof.starts_with("(error"), "{proof}");
    assert!(!proof.contains(":rule hole"), "{proof}");
    assert!(!proof.contains(":rule trust"), "{proof}");
    println!(
        "FRONTEND_ALLOCATION_CERTIFICATE={}",
        serde_json::json!({
            "type":"alethe_certificate", "version":"1.0", "problem":script, "proof":proof
        })
    );
}

macro_rules! case {
    ($name:ident, $file:literal, $expected:literal) => {
        #[test]
        fn $name() {
            check(
                include_str!(concat!("fixtures/frontend_allocation/", $file, ".smt2")),
                $expected,
            );
        }
    };
}

case!(
    bounded_u32_resize_has_complete_proof,
    "allocation-0",
    "unsat"
);
case!(
    bounded_i64_resize_has_complete_proof,
    "allocation-1",
    "unsat"
);
case!(
    bounded_bool_resize_has_complete_proof,
    "allocation-2",
    "unsat"
);
case!(
    large_u32_bound_has_counterexample,
    "allocation-0-large-bound",
    "sat"
);
case!(
    large_i64_bound_has_counterexample,
    "allocation-1-large-bound",
    "sat"
);
case!(
    large_bool_bound_has_counterexample,
    "allocation-2-large-bound",
    "sat"
);
