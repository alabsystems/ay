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
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "{proof}"
    );
    let path = std::env::temp_dir().join(format!(
        "ay-masked-original-{name}-{}.json",
        std::process::id()
    ));
    std::fs::write(&path, serde_json::to_vec(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":input,"proof":proof})).unwrap()).unwrap();
    println!("independent replay certificate: {}", path.display());
}

#[test]
fn original_page_split_has_a_checked_source_proof() {
    publish_original("page", include_str!("fixtures/masked_page.smt2"));
}

#[test]
fn original_thunk_reconstruction_has_a_checked_source_proof() {
    publish_original("thunk", include_str!("fixtures/masked_thunk.smt2"));
}

#[test]
fn original_high_tls_bits_have_a_checked_source_proof() {
    publish_original("high-tls", include_str!("fixtures/masked_high_tls.smt2"));
}

#[test]
fn original_split_tls_bits_have_a_checked_source_proof() {
    publish_original("split-tls", include_str!("fixtures/masked_split_tls.smt2"));
}

#[test]
fn missing_low_bit_has_a_counterexample() {
    let input = include_str!("fixtures/masked_page.smt2").replace("(_ bv4095 64)", "(_ bv4094 64)");
    assert_ne!(input, include_str!("fixtures/masked_page.smt2"));
    let outputs = Executor::new()
        .execute_all(&parse(&input).unwrap())
        .unwrap();
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "{outputs:?}"
    );
}
