// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

// Exact CG12c5 CoreToLir FinalMemory obligation from original TY ordinal3.
// SHA256 0794544284e2841a8047c43d857cc20eb4d4235c06b32337c5fe4d4860c5e478.
const ORIGINAL: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/external_codegen_scalar_action_final_memory.smt2"
));

#[test]
fn original_scalar_final_memory_requires_a_complete_checked_refutation() {
    let mut executor = loaded(ORIGINAL);
    let assertion = &executor.ctx.assertions_parsed()[0];
    assert!(
        large_source(assertion),
        "the early hint covers the late scan cliff"
    );
    assert!(crate::executor::proof_trust_surgery_provenance::surface_source_is_bounded(assertion));
    let outputs = executor
        .execute_all(
            &ay_frontend::parse("(set-option :produce-proofs true)(check-sat)(get-proof)").unwrap(),
        )
        .unwrap();
    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));
    let proof = executor
        .last_proof()
        .expect("original-source proof retained");
    executor.check_proof_strict_with_datatypes(proof).unwrap();
    let text = outputs.last().unwrap();
    assert!(!text.starts_with("(error"));
    assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
}

#[test]
fn original_scalar_source_without_the_exact_query_epoch_cannot_mint_authority() {
    let mut executor = loaded(ORIGINAL);
    declined_without_authority(&mut executor);
    arm(&mut executor);
    executor.ctx.assertions[0] = executor.ctx.terms.true_term();
    declined_without_authority(&mut executor);
}

#[test]
fn negating_the_original_scalar_counterexample_does_not_mint_a_refutation() {
    let mut executor = loaded(ORIGINAL);
    let assertion = executor.ctx.assertions_parsed()[0].clone();
    executor
        .execute_all(&ay_frontend::parse("(reset-assertions)").unwrap())
        .unwrap();
    executor
        .execute_all(&[Command::Assert(FrontendTerm::App(
            "not".into(),
            vec![assertion],
        ))])
        .unwrap();
    arm(&mut executor);
    declined_without_authority(&mut executor);
    let outputs = executor
        .execute_all(&ay_frontend::parse("(check-sat)").unwrap())
        .unwrap();
    assert_eq!(outputs, ["sat"]);
}
