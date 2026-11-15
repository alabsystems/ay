// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

// Exact original E1 queries and controls from the ordinary CG observation
// driver. Keep every source/target definition and guard, including the SAT
// missing-source-product relation; source reconstruction grants no verdict.
const SOURCES: [&str; 5] = [
    include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/external_codegen_e1_aggregate_lane0.smt2"
    )),
    include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/external_codegen_e1_aggregate_lane1.smt2"
    )),
    include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/external_codegen_e1_aggregate_outside.smt2"
    )),
    include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/external_codegen_e1_aggregate_premises.smt2"
    )),
    include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/external_codegen_e1_aggregate_missing_relation.smt2"
    )),
];

#[test]
fn compact_e1_memory_sources_reach_existing_checked_producer() {
    for (index, source) in SOURCES.iter().enumerate() {
        let mut executor = loaded(source);
        let assertion = &executor.ctx.assertions_parsed()[0];
        assert_eq!(bounded_source(assertion), Some(true), "source {index}");
        assert!(!large_source(assertion), "source {index}");
        let expected = executor.ctx.assertions[0];
        assert!(
            executor.early_ground_memory_root(expected).is_some(),
            "source {index}"
        );
    }
}

fn check_original_source_proof(index: usize) {
    let source = SOURCES[index];
    let mut executor = loaded(source);
    executor.set_memory_limit(Some(8 * 1024 * 1024 * 1024));
    let outputs = executor
        .execute_all(
            &ay_frontend::parse("(set-option :produce-proofs true)(check-sat)(get-proof)").unwrap(),
        )
        .unwrap();
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "source {index}: {:?}",
        executor.unknown_reason()
    );
    let proof = executor.last_proof().expect("strict source proof retained");
    executor.check_proof_strict_with_datatypes(proof).unwrap();
    assert!(executor
        .last_proof_with_authenticated_alethe_surface()
        .is_some());
    let text = outputs.last().unwrap();
    assert!(!text.starts_with("(error"), "source {index}: {text}");
    assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
}

#[test]
fn compact_e1_lane0_publishes_a_strict_original_source_proof() {
    check_original_source_proof(0);
}
#[test]
fn compact_e1_lane1_publishes_a_strict_original_source_proof() {
    check_original_source_proof(1);
}
#[test]
fn compact_e1_outside_publishes_a_strict_original_source_proof() {
    check_original_source_proof(2);
}

#[test]
fn compact_e1_definitions_and_missing_source_relation_stay_satisfiable() {
    for (index, source) in SOURCES[3..].iter().enumerate() {
        let mut executor = loaded(source);
        let outputs = executor
            .execute_all(
                &ay_frontend::parse("(set-option :produce-proofs true)(check-sat)").unwrap(),
            )
            .unwrap();
        assert_eq!(outputs, ["sat"], "control {index}");
        assert!(executor.last_proof().is_none());
    }
}

#[test]
fn compact_e1_source_still_needs_the_exact_public_query_epoch() {
    let mut executor = loaded(SOURCES[0]);
    declined_without_authority(&mut executor);
    arm(&mut executor);
    executor.ctx.assertions[0] = executor.ctx.terms.true_term();
    declined_without_authority(&mut executor);
}
