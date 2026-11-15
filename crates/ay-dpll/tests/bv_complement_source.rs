// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_dpll::Executor;
use ay_frontend::parse;

fn publish_original(name: &str, input: &str) {
    let query = input.trim_end().strip_suffix("(exit)").unwrap();
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
    assert!(proof.contains(":rule poly_simp_rel"), "{proof}");
    assert!(!proof.contains(":rule hole") && !proof.contains(":rule trust"));
    let path = std::env::temp_dir().join(format!(
        "ay-complement-public-{name}-{}.json",
        std::process::id()
    ));
    std::fs::write(&path, serde_json::to_vec(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":input,"proof":proof})).unwrap()).unwrap();
    println!("independent replay certificate: {}", path.display());
}

#[test]
fn original_branch_relocation_has_a_checked_source_proof() {
    publish_original("call", include_str!("fixtures/complement_call.smt2"));
}

#[test]
fn original_page_relocation_has_a_checked_source_proof() {
    publish_original("page", include_str!("fixtures/complement_page.smt2"));
}

#[test]
fn changed_complement_adjustment_has_a_counterexample() {
    let original = include_str!("fixtures/complement_call.smt2");
    let input = original.replace("(_ bv1 64)", "(_ bv2 64)");
    assert_ne!(input, original);
    let outputs = Executor::new()
        .execute_all(&parse(&input).unwrap())
        .unwrap();
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "{outputs:?}"
    );
}
