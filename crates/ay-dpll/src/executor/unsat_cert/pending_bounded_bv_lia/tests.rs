// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_frontend::parse;

/// Spelled `ubv_to_int`, which AY elaborates to the same term as `bv2nat`:
/// pinned Carcara defines only the SMT-LIB 2.7 name, and strict proofs
/// withhold an UNSAT whose problem it cannot parse.
const PINNED_U16: &str = r#"
    (set-option :produce-proofs true)
    (set-option :check-proofs-strict true)
    (set-logic QF_UFBVLIA)
    (declare-const result (_ BitVec 16))
    (declare-const x (_ BitVec 16))
    (assert (= x #x9c40))
    (assert (= x result))
    (assert (<= (* (ubv_to_int x) 2) 65535))
"#;

fn provisional_native_refutation() -> (Executor, SolveResult) {
    let commands = parse(PINNED_U16).expect("valid pinned u16 query");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("install pinned u16 query");
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    let proposed = executor
        .solve_authored_plain_hard_query(&[])
        .expect("bounded source solve");
    assert!(proposed.is_unsat());
    assert!(executor.pending_bounded_bv_lia_unsat.is_some());
    (executor, proposed)
}

fn certified_native_refutation() -> Executor {
    let (mut executor, proposed) = provisional_native_refutation();
    let published = executor.certify_unsat_for_publication(proposed, &[]);
    assert!(published.is_unsat());
    let certificate = executor
        .last_unsat_certificate
        .as_ref()
        .expect("strict-native certificate");
    assert!(certificate.strict_proof_verified());
    assert!(!certificate.independently_verified());
    assert!(matches!(
        &certificate.0,
        UnsatCertificateKind::StrictNativeBvLiaBundle(_)
    ));
    let proof = executor.last_proof.as_ref().expect("canonical proof");
    assert!(executor
        .strict_native_bv_lia_bundle_for_proof(proof)
        .is_some());
    executor
}

#[test]
fn pending_route_allows_append_only_growth_then_seals_final_snapshot() {
    let (mut executor, proposed) = provisional_native_refutation();
    let _ = executor
        .ctx
        .terms
        .mk_var("post_source_append", CoreSort::Bool);
    assert!(executor
        .pending_bounded_bv_lia_unsat
        .as_ref()
        .is_some_and(|pending| executor.pending_bounded_bv_lia_unsat_matches_bound_epoch(pending)));

    let published = executor.certify_unsat_for_publication(proposed, &[]);
    assert!(published.is_unsat());
    let proof = executor.last_proof.as_ref().expect("canonical proof");
    let bundle = executor
        .strict_native_bv_lia_bundle_for_proof(proof)
        .expect("final-snapshot bundle");
    assert!(re_check_bundle_strict(bundle)
        .expect("offline replay")
        .quality
        .is_complete());
}

#[test]
fn sealed_bundle_and_certificate_reject_later_term_growth() {
    let mut executor = certified_native_refutation();
    let proof = executor.last_proof.clone().expect("canonical proof");
    let _ = executor
        .ctx
        .terms
        .mk_var("post_bundle_append", CoreSort::Bool);

    assert!(executor
        .strict_native_bv_lia_bundle_for_proof(&proof)
        .is_none());
    assert!(executor.take_unsat_certificate().is_none());
}

#[test]
fn sealed_bundle_and_certificate_reject_proof_shape_mutation() {
    let mut executor = certified_native_refutation();
    executor
        .last_proof
        .as_mut()
        .expect("canonical proof")
        .steps
        .pop();
    let mutated = executor.last_proof.clone().expect("mutated proof");

    assert!(executor
        .strict_native_bv_lia_bundle_for_proof(&mutated)
        .is_none());
    assert!(executor.take_unsat_certificate().is_none());
}

#[test]
fn consumed_certificate_bundle_rejects_solver_assumption_mutation() {
    let mut executor = certified_native_refutation();
    let proof = executor.last_proof.clone().expect("canonical proof");
    assert!(executor.take_unsat_certificate().is_some());
    assert!(executor
        .strict_native_bv_lia_bundle_for_proof(&proof)
        .is_some());

    let existing_assertion = executor
        .unsat_query_epoch
        .as_ref()
        .and_then(|epoch| epoch.assertions.first())
        .copied()
        .expect("authored assertion");
    executor.last_assumptions = Some(vec![existing_assertion]);

    assert!(executor
        .strict_native_bv_lia_bundle_for_proof(&proof)
        .is_none());
}
