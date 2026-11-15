// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use sha2::{Digest, Sha256};

const ORIGINAL: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/external_codegen_actual_e1_local_exit0.smt2"
));

#[test]
fn actual_e1_local_source_reconstruction_retains_checked_original_root() {
    assert_eq!(ORIGINAL.len(), 14_185);
    assert_eq!(
        format!("{:x}", Sha256::digest(ORIGINAL.as_bytes())),
        "3c6a76f8bf286e8eceef4121805712025808865cb9268847277435f0fb9c4ca5"
    );
    let mut executor = loaded(ORIGINAL);
    let assertion = executor.ctx.assertions_parsed()[0].clone();
    assert_eq!(bounded_source(&assertion), Some(true));
    assert!(!large_source(&assertion));
    let expected = executor.ctx.assertions[0];
    let (root, kind, used_definition) = executor.early_ground_memory_root(expected).unwrap();
    assert_eq!(kind, EarlyGroundKind::CompactMemory);
    assert!(!used_definition);
    assert_eq!(
        executor.raw_intern_ground_bv_surface(&assertion),
        Some(root)
    );
    let negative = executor.ctx.terms.mk_not_raw(root);
    assert!(executor.early_ground_memory_terms_print_faithfully(&[root, negative]));
    let candidate = executor
        .early_ground_closure_memory_candidate(root)
        .expect("actual source needs a bounded existing-rule derivation");
    assert!(candidate
        .steps
        .iter()
        .all(|step| !matches!(step, ay_core::ProofStep::Assume(term) if *term != root)));
    assert!(executor
        .check_proof_strict_derivation_with_datatypes(&candidate)
        .unwrap()
        .is_complete());
    assert!(
        executor.last_proof.is_none() && executor.last_proof_raw_original_assertions.is_empty()
    );
}

#[test]
fn actual_e1_local_public_entry_exports_complete_original_proof() {
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    executor.set_timeout(Some(Duration::from_secs(30)));
    executor.set_memory_limit(Some(8 * 1024 * 1024 * 1024));
    for command in ay_frontend::parse(ORIGINAL).unwrap() {
        if !matches!(command, Command::CheckSat | Command::Exit) {
            executor.execute_authored(&command).unwrap();
        }
    }
    assert_eq!(
        executor
            .execute_authored(&Command::CheckSat)
            .unwrap()
            .as_deref(),
        Some("unsat"),
        "{:?}",
        executor.unknown_reason()
    );
    let proof = executor.last_proof().unwrap();
    ay_proof::validate_reachable_assumes_in_problem_scope(
        proof,
        &executor.proof_export_scope_assertions(),
    )
    .unwrap();
    assert!(executor
        .check_proof_strict_with_datatypes(proof)
        .unwrap()
        .is_complete());
    assert!(executor
        .last_proof_with_authenticated_alethe_surface()
        .is_some());
    let text = executor
        .execute_authored(&Command::GetProof)
        .unwrap()
        .unwrap();
    assert!(
        !text.starts_with("(error")
            && !text.contains(":rule hole")
            && !text.contains(":rule trust")
    );
    println!("ACTUAL_E1_LOCAL public proof bytes={}", text.len());
}
