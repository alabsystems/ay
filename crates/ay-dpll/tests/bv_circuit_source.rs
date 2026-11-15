// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_dpll::Executor;
use ay_frontend::parse;

fn publish(name: &str, input: &str) {
    let query = input.replace("(get-proof)", "").replace("(exit)", "");
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    let outputs = executor
        .execute_all(&parse(&format!("{query}(get-proof)\n")).unwrap())
        .unwrap();
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{outputs:?}"
    );
    let proof = outputs.get(1).expect("published proof");
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "{proof}"
    );
    let path = std::env::temp_dir().join(format!(
        "ay-circuit-public-{name}-{}.json",
        std::process::id()
    ));
    std::fs::write(&path, serde_json::to_vec(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":input,"proof":proof})).unwrap()).unwrap();
    println!("independent replay certificate: {}", path.display());
}

#[test]
fn coroutine_original_closed_array_publishes() {
    publish(
        "coroutine",
        include_str!(
            "../../ay-proof/src/alethe_printer/bv_packed/fixtures/coroutine_disjoint.smt2"
        ),
    );
}

#[test]
fn coroutine_original_index_publishes() {
    publish(
        "index-0-0",
        include_str!("../../ay-proof/src/alethe_printer/bv_packed/fixtures/coro-index-0-0.smt2"),
    );
}

#[test]
fn missing_disjointness_has_a_counterexample() {
    let input =
        include_str!("../../ay-proof/src/alethe_printer/bv_packed/fixtures/coro-index-0-0.smt2")
            .replace("(get-proof)", "")
            .replace(
                "(bvuge (bvadd (_ bv24 64) frame) (bvadd (_ bv8 64) vbase))",
                "true",
            );
    let outputs = Executor::new()
        .execute_all(&parse(&input).unwrap())
        .unwrap();
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "{outputs:?}"
    );
}

#[test]
fn original_checked_overflow_formulas_publish_complete_certificates() {
    for (name, input) in [
        (
            "sadd-64",
            include_str!(
                "../../ay-proof/src/alethe_printer/bv_packed/fixtures/checked-sadd-64.smt2"
            ),
        ),
        (
            "ssub-64",
            include_str!(
                "../../ay-proof/src/alethe_printer/bv_packed/fixtures/checked-ssub-64.smt2"
            ),
        ),
        (
            "uadd-64",
            include_str!(
                "../../ay-proof/src/alethe_printer/bv_packed/fixtures/checked-uadd-64.smt2"
            ),
        ),
        (
            "usub-64",
            include_str!(
                "../../ay-proof/src/alethe_printer/bv_packed/fixtures/checked-usub-64.smt2"
            ),
        ),
    ] {
        publish(name, input);
    }
}

#[test]
fn original_packed_shift_and_multiply_formulas_publish_complete_certificates() {
    for (name, input) in [
        (
            "psllq",
            include_str!("../../ay-proof/src/alethe_printer/bv_packed/fixtures/packed-psllq.smt2"),
        ),
        (
            "psrlq",
            include_str!("../../ay-proof/src/alethe_printer/bv_packed/fixtures/packed-psrlq.smt2"),
        ),
        (
            "pmuludq",
            include_str!(
                "../../ay-proof/src/alethe_printer/bv_packed/fixtures/packed-pmuludq.smt2"
            ),
        ),
    ] {
        publish(name, input);
    }
}

#[test]
fn changed_original_packed_shift_amount_has_a_counterexample() {
    let input =
        include_str!("../../ay-proof/src/alethe_printer/bv_packed/fixtures/packed-psllq.smt2");
    let original = "((_ zero_extend 58) count)";
    let last = input.rfind(original).unwrap();
    let mut changed = input.to_string();
    changed.replace_range(
        last..last + original.len(),
        "(bvadd ((_ zero_extend 58) count) (_ bv1 64))",
    );
    let outputs = Executor::new()
        .execute_all(&parse(&changed).unwrap())
        .unwrap();
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "{outputs:?}"
    );
}

#[test]
fn original_checked_multiply_overflow_publishes_complete_certificates() {
    for (name, input) in [
        (
            "smul-64",
            include_str!(
                "../../ay-proof/src/alethe_printer/bv_packed/fixtures/checked-smul-64.smt2"
            ),
        ),
        (
            "umul-64",
            include_str!(
                "../../ay-proof/src/alethe_printer/bv_packed/fixtures/checked-umul-64.smt2"
            ),
        ),
    ] {
        publish(name, input);
    }
}
