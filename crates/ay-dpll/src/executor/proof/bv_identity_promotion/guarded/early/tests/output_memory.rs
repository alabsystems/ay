// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const OUTPUT_MEMORY: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../ay-proof/src/alethe_printer/bv_packed/circuit/memory_fixtures/output-memory.smt2"
));

#[test]
fn output_memory_original_early_stages_require_checked_refutation() {
    let mut executor = loaded(OUTPUT_MEMORY);
    executor.set_memory_limit(Some(8 * 1024 * 1024 * 1024));
    arm(&mut executor);
    let start = Instant::now();
    let authored = executor
        .authenticated_plain_query_assertions_after_named_core_redirect()
        .expect("authenticated original query");
    assert_eq!(authored.len(), 1);
    let assertion = source::expand(&executor.ctx, &executor.ctx.assertions_parsed()[0])
        .expect("bounded original source expansion");
    println!("OUTPUT_MEMORY_STAGE expanded elapsed={:?}", start.elapsed());
    assert_eq!(bounded_source(&assertion), Some(true));
    assert!(large_source(&assertion));
    assert_eq!(
        executor.ctx.elaborate_surface_subterm(&assertion),
        Some(authored[0])
    );
    println!(
        "OUTPUT_MEMORY_STAGE elaborated elapsed={:?}",
        start.elapsed()
    );
    let root = executor
        .raw_intern_ground_bv_surface(&assertion)
        .expect("bounded faithful raw interning");
    let negative = executor.ctx.terms.mk_not_raw(root);
    println!("OUTPUT_MEMORY_STAGE interned elapsed={:?}", start.elapsed());
    assert!(executor.guarded_terms_print_faithfully(&[root, negative]));
    println!(
        "OUTPUT_MEMORY_STAGE roundtrip elapsed={:?}",
        start.elapsed()
    );
    let mut candidate = Proof::new();
    let premise = candidate.add_assume(root, None);
    let lemma =
        candidate.add_theory_lemma_with_kind("bv", vec![negative], TheoryLemmaKind::BvBitBlast);
    candidate.add_resolution(Vec::new(), root, premise, lemma);
    let checked = executor.check_proof_strict_derivation_with_datatypes(&candidate);
    println!(
        "OUTPUT_MEMORY_STAGE checked={checked:?} elapsed={:?}",
        start.elapsed()
    );
    assert!(
        checked.is_ok(),
        "original conditional memory theorem needs a checked refutation"
    );
}

#[test]
fn output_memory_public_api_requires_complete_original_certificate() {
    let mut executor = loaded(OUTPUT_MEMORY);
    executor.set_memory_limit(Some(8 * 1024 * 1024 * 1024));
    let outputs = executor
        .execute_all(
            &ay_frontend::parse("(set-option :produce-proofs true)(check-sat)(get-proof)").unwrap(),
        )
        .unwrap();
    println!("OUTPUT_MEMORY_PUBLIC verdict={:?}", outputs.first());
    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));
    let proof = executor.last_proof().expect("public proof retained");
    executor.check_proof_strict_with_datatypes(proof).unwrap();
    let text = outputs.last().unwrap();
    assert!(
        !text.starts_with("(error")
            && !text.contains(":rule hole")
            && !text.contains(":rule trust")
    );
    let path = std::env::temp_dir().join(format!("ay-output-memory-{}.json", std::process::id()));
    std::fs::write(
        &path,
        serde_json::to_vec(&serde_json::json!({
            "type":"alethe_certificate", "version":"1.0", "problem":OUTPUT_MEMORY, "proof":text
        }))
        .unwrap(),
    )
    .unwrap();
    println!("independent replay certificate: {}", path.display());
}
