// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The full external-codegen canonical PBLENDVB query, with raw concat/extract terms.
//! No source simplification or stronger resource allowance is used here.

use ay_proof::{authenticate_bool_bv_unsat_query, BoolBvUnsatAuthenticationError};

#[path = "fixtures/packed_mask.rs"]
mod packed_mask;
use packed_mask::{query, Mutation};

#[test]
fn full_canonical_mask_is_authenticated_at_the_existing_limits() {
    let (terms, root) = query(Mutation::None);
    assert!(terms.len() < 300, "retain the shared source DAG");
    authenticate_bool_bv_unsat_query(&terms, &[root], None).expect("full raw PBLENDVB query");
}

#[test]
fn canonical_mask_all_bits_agree_and_wrong_data_or_choice_is_refused() {
    // Every bit of a canonical 00/ff mask agrees with its sign bit.
    let (terms, root) = query(Mutation::WrongMaskBit);
    authenticate_bool_bv_unsat_query(&terms, &[root], None).expect("canonical byte bit 6 agrees");
    for mutation in [Mutation::ReversedChoice, Mutation::WrongSourceByte] {
        let (terms, root) = query(mutation);
        assert!(
            matches!(
                authenticate_bool_bv_unsat_query(&terms, &[root], None),
                Err(BoolBvUnsatAuthenticationError::Satisfiable)
            ),
            "a corrupted selected byte must remain a counterexample"
        );
    }
}

#[test]
fn packed_mask_strict_replay_fits_the_existing_envelope_and_reserves_private_work() {
    use ay_core::{TermData, TheoryLemmaKind};
    use ay_proof::{
        check_proof_strict_with_context_and_progress, Proof, ProofCheckError,
        MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA, MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA,
    };
    let (terms, root) = query(Mutation::None);
    let TermData::Not(equality) = terms.get(root) else {
        panic!("negated equality")
    };
    let mut proof = Proof::new();
    let assumption = proof.add_assume(root, None);
    let lemma =
        proof.add_theory_lemma_with_kind("BV", vec![*equality], TheoryLemmaKind::BvBitBlast);
    proof.add_resolution(vec![], *equality, assumption, lemma);

    let mut private_reservations = 0;
    let (mut work, mut bytes) = (0usize, 0usize);
    let quality = check_proof_strict_with_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        Some(&[root]),
        &mut |w, b| {
            if w == MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA as usize
                && b == MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA
            {
                private_reservations += 1;
            }
            work = work.checked_add(w).expect("work overflow");
            bytes = bytes.checked_add(b).expect("byte overflow");
            work <= 350_000_000 && bytes <= 1_342_177_280
        },
    )
    .expect("exact authored query fits the unchanged strict envelope");
    assert_eq!(private_reservations, 1);
    assert_eq!(quality.trust_count, 0);
    assert_eq!(quality.hole_count, 0);

    // Even a warm semantic cache cannot avoid the caller's private replay
    // reservation. Rejecting it must stop the check before proof acceptance.
    let error = check_proof_strict_with_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        Some(&[root]),
        &mut |w, b| {
            !(w == MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA as usize
                && b == MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA)
        },
    )
    .expect_err("private budget rejection must remain binding");
    assert_eq!(error, ProofCheckError::ResourceLimit);
}
