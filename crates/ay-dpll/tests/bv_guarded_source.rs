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
    assert!(proof.contains(":rule and_pos"), "{proof}");
    assert!(!proof.contains(":rule hole") && !proof.contains(":rule trust"));
    let path = std::env::temp_dir().join(format!(
        "ay-guarded-public-{name}-{}.json",
        std::process::id()
    ));
    std::fs::write(&path, serde_json::to_vec(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":input,"proof":proof})).unwrap()).unwrap();
    println!("independent replay certificate: {}", path.display());
}

#[test]
fn original_tls_range_has_a_checked_source_proof() {
    publish_original("range", include_str!("fixtures/guarded_range_tls.smt2"));
}

#[test]
fn original_tls_alignment_has_a_checked_source_proof() {
    publish_original("mask", include_str!("fixtures/guarded_mask_tls.smt2"));
}

#[test]
fn weakened_tls_guards_have_counterexamples() {
    for (original, before, after) in [
        (
            include_str!("fixtures/guarded_range_tls.smt2"),
            "(_ bv16777216 64)",
            "(_ bv33554432 64)",
        ),
        (
            include_str!("fixtures/guarded_mask_tls.smt2"),
            "(_ bv7 64)",
            "(_ bv3 64)",
        ),
    ] {
        let input = original.replace(before, after);
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
}
