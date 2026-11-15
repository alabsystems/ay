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
    assert!(proof.contains(":rule pbblast_bv"), "{proof}");
    assert!(!proof.contains(":rule hole") && !proof.contains(":rule trust"));
    // Two lanes certify this root: the named interval partition
    // (pbblast/la_generic/poly_simp, 2.27 MB, carcara 0.1 s) and, since
    // 73810d00d lowered bvuge/bvule, a 20,481-gate complete blast (`@ay_cbb_`
    // gates, 10.4 MB, carcara 105-130 s). The smaller document is published.
    assert!(
        !proof.contains("@ay_cbb_") && proof.contains(":rule poly_simp"),
        "the complete blast displaced the partition lane ({} bytes)",
        proof.len()
    );
    assert!(proof.len() < 4 << 20, "{} bytes", proof.len());
    let path = std::env::temp_dir().join(format!(
        "ay-partition-public-{name}-{}.json",
        std::process::id()
    ));
    std::fs::write(&path, serde_json::to_vec(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":input,"proof":proof})).unwrap()).unwrap();
    println!("independent replay certificate: {}", path.display());
}

#[test]
fn original_exception_coverage_publishes_a_checked_source_proof() {
    publish_original("coverage", include_str!("fixtures/partition_coverage.smt2"));
}

#[test]
fn wrapped_exception_interval_has_a_counterexample() {
    let original = include_str!("fixtures/partition_coverage.smt2");
    let input = original.replace(
        "(bvuge (bvadd region_len region_start) region_start)",
        "true",
    );
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
