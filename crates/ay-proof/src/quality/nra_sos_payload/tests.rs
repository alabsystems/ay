// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use num_bigint::BigInt;

fn certificate(variable: TermId) -> NraSosCertificate {
    let zero = NraSosRational {
        numerator: BigInt::from(0u8),
        denominator: BigInt::from(1u8),
    };
    NraSosCertificate {
        basis: vec![vec![], vec![variable]],
        gram: vec![vec![zero.clone(); 2]; 2],
        terms: vec![],
        rhs: zero,
    }
}

fn fixture() -> (TermStore, Vec<TermId>, NraSosCertificate) {
    let mut terms = TermStore::new();
    let variable = terms.mk_var("meter_sos_x", Sort::Real);
    let clause = vec![terms.true_term()];
    (terms, clause, certificate(variable))
}

fn measured(
    terms: &TermStore,
    clause: &Vec<TermId>,
    certificate: &NraSosCertificate,
) -> (usize, usize, Vec<TermId>) {
    let mut pending = Vec::new();
    let mut work = 0;
    let mut bytes = 0;
    meter(
        terms,
        ProofId(0),
        clause,
        certificate,
        &mut pending,
        &mut |w, b| {
            work += w;
            bytes += b;
            true
        },
    )
    .expect("shape-valid payload");
    (work, bytes, pending)
}

#[test]
fn nra_sos_authentication_charges_rational_limbs_and_all_roots() {
    let (terms, clause, small) = fixture();
    let (small_work, small_bytes, roots) = measured(&terms, &clause, &small);
    assert_eq!(roots, vec![clause[0], small.basis[1][0]]);
    let mut wide = small;
    wide.gram[0][0].numerator = BigInt::from(1u8) << (NraSosRational::MAX_BITS as usize - 1);
    wide.rhs.denominator = BigInt::from(1u8) << (NraSosRational::MAX_BITS as usize - 1);
    let (wide_work, wide_bytes, _) = measured(&terms, &clause, &wide);
    assert!(wide_work > small_work);
    assert!(wide_bytes >= small_bytes + 254);
}

#[test]
fn nra_sos_authentication_can_cancel_before_root_allocation() {
    let (terms, clause, certificate) = fixture();
    let mut pending = Vec::new();
    assert!(matches!(
        meter(
            &terms,
            ProofId(0),
            &clause,
            &certificate,
            &mut pending,
            &mut |_, _| false
        ),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert!(pending.is_empty());
}

#[test]
fn nra_sos_authentication_caps_payload_before_cloning_roots() {
    let (terms, clause, mut oversized) = fixture();
    oversized.gram[0] = vec![oversized.rhs.clone(); NraSosCertificate::MAX_BASIS + 1];
    let mut pending = Vec::new();
    assert!(matches!(
        meter(
            &terms,
            ProofId(0),
            &clause,
            &oversized,
            &mut pending,
            &mut |_, _| true
        ),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert!(pending.is_empty());
}

#[test]
fn nra_sos_public_authentication_rejects_forged_root_without_panicking() {
    let (terms, clause, mut certificate) = fixture();
    certificate.basis[1][0] = TermId(u32::MAX);
    let proof = Proof::from_steps(vec![ProofStep::NraSos {
        clause,
        certificate,
    }]);
    let result =
        crate::authenticate_premise_clauses_strict_with_context(&proof, &terms, None, None, &[]);
    assert!(matches!(
        result,
        Err(ProofCheckError::InvalidTheoryLemma { .. })
    ));
}

#[test]
fn nra_sos_semantic_charge_uses_dynamic_checker_meter() {
    let step = ProofStep::NraSos {
        clause: vec![TermId(3)],
        certificate: certificate(TermId(8)),
    };
    let payload = PayloadStats {
        work: usize::MAX,
        unfolded_work: usize::MAX,
        bytes: usize::MAX,
        fp_assignments: 0,
        order_assignments: 0,
    };
    assert_eq!(super::super::step_clause_len(&step), 1);
    assert_eq!(
        super::super::strict_semantic_charge(&step, payload, SemanticChargeClass::General)
            .expect("actual checker work is separately debited"),
        (0, 0)
    );
}
