// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_frontend::parse;
use std::sync::{atomic::AtomicBool, Arc};

const ORIGINAL: &str = include_str!("memory-roundtrip-low-extract.smt2");

fn fixture(problem: &str) -> Executor {
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    for command in parse(problem).expect("original compiler query") {
        match command {
            Command::Assert(surface) => {
                let raw = executor
                    .raw_intern_ground_bv_surface(&surface)
                    .expect("bounded source rebuild");
                executor.ctx.add_assertion_with_parsed(raw, surface);
            }
            Command::CheckSat | Command::Exit => (),
            other => {
                executor.execute(&other).expect("source declaration");
            }
        }
    }
    executor
}

fn candidate(executor: &mut Executor) -> Option<Proof> {
    let parsed = executor.ctx.assertions_parsed().to_vec();
    let scope = executor.proof_export_scope_assertions();
    let mut selected = Vec::new();
    for surface in &parsed {
        let root = executor
            .raw_intern_surface(surface)
            .expect("generic bounded raw rebuild");
        assert!(
            scope.contains(&root),
            "raw root keeps authored assumption authority"
        );
        assert!(executor.rebuilt_root_prints_as_authored_up_to_literals(root, surface));
        selected.push((root, surface));
    }
    executor.authored_bv_bitblast_candidate(&selected, &scope, false)
}

fn captured_saved_pair_certificate(executor: &Executor, proof: &Proof, name: &str) {
    let scope = executor
        .proof_export_scope_assertions_for(proof)
        .expect("original source scope");
    let (document, report) = ay_proof::capture_alethe_dialect_report(|| {
        executor
            .in_alethe_dialect(|| executor.get_proof_alethe_with_authored_surfaces(proof, &scope))
    });
    let overrides = executor.proof_export_term_overrides();
    let surface = executor
        .problem_and_proof_surface(proof, overrides.as_ref())
        .with_dialect_report(&report);
    let path =
        std::env::temp_dir().join(format!("ay-saved-pair-{name}-{}.json", std::process::id()));
    let certificate = serde_json::json!({
        "type": "alethe_certificate",
        "version": "1.0",
        "problem": include_str!("saved-pair-captured-ty-80.smt2"),
        "proof": document,
        "carcara_surface": surface.to_string(),
        "alethe_dialect": executor.alethe_dialect().name(),
        "clean_only_notes": report.clean_only_notes(),
    });
    std::fs::write(
        &path,
        serde_json::to_vec(&certificate).expect("certificate JSON"),
    )
    .expect("write independent replay certificate");
    println!(
        "saved-pair independent replay certificate: {}",
        path.display()
    );
}

#[test]
fn raw_authored_memory_candidate_preserves_the_unfolded_surface() {
    let mut executor = fixture(ORIGINAL);
    let proof = candidate(&mut executor)
        .expect("the exact raw memory theorem must pass native semantic replay");
    assert!(
        executor.wire_repair_candidate_prints_clean(&proof),
        "a natively proved raw theorem must retain a complete printed proof"
    );
    assert!(Executor::proof_derives_empty_clause(&proof));
    assert!(executor
        .check_proof_strict_with_datatypes(&proof)
        .unwrap()
        .is_complete());
}

#[test]
fn changed_memory_value_has_no_refutation_candidate() {
    let wrong = ORIGINAL.replacen(
        "(not (= recon_v (concat",
        "(not (= (bvnot recon_v) (concat",
        1,
    );
    assert_ne!(wrong, ORIGINAL);
    let mut executor = fixture(&wrong);
    assert!(
        candidate(&mut executor).is_none(),
        "the changed claim is satisfiable"
    );
}

#[test]
fn interrupted_memory_repair_cannot_return_a_candidate() {
    let mut executor = fixture(ORIGINAL);
    executor.set_interrupt(Arc::new(AtomicBool::new(true)));
    assert!(candidate(&mut executor).is_none());
}

#[test]
fn captured_saved_pair_preserves_arbitrary_memory_and_prints_a_complete_proof() {
    // Original ExternalCodegen query: arbitrary entry/resume byte arrays, both saved
    // words and SP premises. This conditional pair theorem does not prove
    // the intervening caller/body or grant machine publication authority.
    let original = include_str!("saved-pair-captured-ty-80.smt2");
    let mut executor = fixture(original);
    let proof = candidate(&mut executor)
        .expect("the unchanged saved-pair theorem needs a checked source-bound proof");
    assert!(Executor::proof_derives_empty_clause(&proof));
    assert!(executor
        .check_proof_strict_with_datatypes(&proof)
        .expect("strict whole-proof replay")
        .is_complete());
    captured_saved_pair_certificate(&executor, &proof, "candidate");
    assert!(executor.wire_repair_candidate_prints_clean(&proof));
}

#[test]
fn captured_saved_pair_offset_normalized_candidate_has_complete_replay() {
    let original = include_str!("saved-pair-captured-ty-80.smt2");
    let mut executor = fixture(original);
    let surface = executor.ctx.assertions_parsed()[0].clone();
    let root = executor
        .raw_intern_surface(&surface)
        .expect("original raw root");
    let scope = executor.proof_export_scope_assertions();
    assert!(
        scope.contains(&root),
        "original assumption must remain in scope"
    );
    assert!(
        executor.rebuilt_root_prints_as_authored_up_to_literals(root, &surface),
        "raw root must print as the exact authored claim"
    );
    let mut seen = ay_core::kani_compat::DetHashSet::default();
    let mut pending = vec![root];
    while let Some(term) = pending.pop() {
        if seen.insert(term) {
            pending.extend(executor.ctx.terms.children(term));
        }
    }
    println!("saved-pair raw DAG nodes={}", seen.len());
    let mut derivation = Proof::new();
    let assume = derivation.add_assume(root, None);
    let (normalized, _) = ay_proof::derive_bv_offset_normalization(
        &mut executor.ctx.terms,
        &mut derivation,
        root,
        assume,
    )
    .expect("normalization must derive its cuts within the existing envelope");
    assert_ne!(
        normalized, root,
        "normalization must actually change the source root"
    );
    let authentication = ay_proof::authenticate_bool_bv_unsat_query(
        &executor.ctx.terms,
        &[normalized],
        Some(std::time::Instant::now() + std::time::Duration::from_secs(30)),
    );
    println!("saved-pair normalized source authentication={authentication:?}");
    let negated = executor.ctx.terms.mk_not_raw(normalized);
    assert!(
        executor.recognize_bv_bitblast_until_stopped(&[negated]),
        "the normalized original claim must pass the existing native recognizer"
    );
    let proof = executor
        .authored_bv_bitblast_candidate_in_form(
            &[(root, &surface)],
            &scope,
            false,
            WordForm::OffsetNormalized,
        )
        .expect("checked offset normalization must retain the exact authored memory claim");
    assert!(Executor::proof_derives_empty_clause(&proof));
    assert!(executor
        .check_proof_strict_with_datatypes(&proof)
        .expect("strict whole-proof replay")
        .is_complete());
    captured_saved_pair_certificate(&executor, &proof, "offset-normalized");
    assert!(executor.wire_repair_candidate_prints_clean(&proof));
}

#[test]
fn original_e1_exit0_rebuilds_exact_raw_source_under_existing_limits() {
    use crate::executor::Executor;
    use sha2::{Digest, Sha256};
    const QUERY: &str = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/executor/proof_original_e1_exit0.smt2"
    ));
    assert_eq!(QUERY.len(), 1_073_945);
    assert_eq!(
        format!("{:x}", Sha256::digest(QUERY.as_bytes())),
        "79fbfab7d17542fea628e919f8cb9310c88c1a1988be2edf434e15ba1f693773"
    );
    let mut executor = Executor::new();
    for command in parse(QUERY).expect("unchanged original E1 query") {
        if !matches!(command, Command::CheckSat | Command::Exit) {
            executor
                .execute(&command)
                .expect("actual original declarations and assertion");
        }
    }
    assert_eq!(executor.ctx.assertions_parsed().len(), 1);
    let source = executor.ctx.assertions_parsed()[0].clone();
    let canonical = executor.ctx.assertions[0];
    let raw = executor
        .raw_intern_shared_ground_memory_surface(&source)
        .expect("actual shared typed/raw reconstruction must fit unchanged limits");
    assert_eq!(executor.ctx.terms.sort(raw), &Sort::Bool);
    assert_eq!(
        executor.ctx.elaborate_surface_subterm(&source),
        Some(canonical)
    );
    assert!(
        executor.rebuilt_root_prints_as_authored_up_to_literals(raw, &source),
        "shared reconstruction retains the actual original source spelling"
    );
    assert!(
        executor.last_proof_raw_original_assertions.is_empty(),
        "source reconstruction alone does not grant Assume authority"
    );
    assert!(executor.last_proof().is_none());
}
