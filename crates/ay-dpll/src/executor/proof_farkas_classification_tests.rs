// Copyright 2026 Andrew Yates | Apache-2.0

//! Existing certificates must keep their clause, coefficients and LIA payload.

use ay_core::kani_compat::DetHashMap;
use ay_core::{
    FarkasAnnotation, LiaAnnotation, Proof, ProofStep, Sort, TermId, TermStore, TheoryLemmaKind,
};

use super::reconstruct_missing_farkas_coefficients;

fn fixture() -> (TermStore, Proof, TermId, TermId) {
    let mut terms = TermStore::new();
    let n = terms.mk_var("allocation_n", Sort::Int);
    let four = terms.mk_int(4.into());
    let limit = terms.mk_int(268435456.into());
    // Preserve the operand order: mk_mul canonicalizes to the override below.
    let scaled = terms.mk_app(ay_core::Symbol::named("*"), [four, n], Sort::Int);
    let first = terms.mk_ge(scaled, limit);
    let second = terms.mk_ge(n, limit);
    let clause = vec![first, terms.mk_not_raw(second)];
    let mut proof = Proof::new();
    proof.add_step(ProofStep::TheoryLemma {
        theory: "LIA".to_owned(),
        clause,
        farkas: Some(FarkasAnnotation::from_ints(&[1, 4])),
        kind: TheoryLemmaKind::LiaGeneric,
        lia: None,
    });
    (terms, proof, scaled, second)
}

#[test]
fn retained_linear_certificate_gets_exact_surface_replay() {
    let (mut terms, mut proof, scaled, second) = fixture();
    let original = proof.clone();
    let mut surface = DetHashMap::default();
    surface.insert(scaled, "(* allocation_n 4)".to_owned());
    let wire_rule = |terms: &TermStore, proof: &Proof, surface: &DetHashMap<TermId, String>| {
        let ProofStep::TheoryLemma {
            clause,
            farkas,
            kind,
            ..
        } = &proof.steps[0]
        else {
            panic!("theory lemma");
        };
        ay_proof::promoted_wire_rule(terms, kind, clause, farkas.as_ref(), Some(surface)).to_owned()
    };
    assert_eq!(wire_rule(&terms, &proof, &surface), "hole");
    reconstruct_missing_farkas_coefficients(&mut terms, &mut proof, &[], &[], &|| false);
    assert_eq!(wire_rule(&terms, &proof, &surface), "la_generic");
    let ProofStep::TheoryLemma { kind, .. } = &mut proof.steps[0] else {
        panic!("theory lemma");
    };
    assert_eq!(*kind, TheoryLemmaKind::LraFarkas);
    *kind = TheoryLemmaKind::LiaGeneric;
    assert_eq!(
        proof, original,
        "classification is the only changed proof content"
    );

    reconstruct_missing_farkas_coefficients(&mut terms, &mut proof, &[], &[], &|| false);
    surface.insert(second, "(>= allocation_n 1)".to_owned());
    assert_eq!(
        wire_rule(&terms, &proof, &surface),
        "hole",
        "n=1 refutes the changed clause"
    );
}

#[test]
fn retained_invalid_coefficients_are_not_reclassified() {
    let (mut terms, mut proof, _, _) = fixture();
    let ProofStep::TheoryLemma { farkas, .. } = &mut proof.steps[0] else {
        panic!("theory lemma");
    };
    *farkas = Some(FarkasAnnotation::from_ints(&[1, 1]));
    let original = proof.clone();
    reconstruct_missing_farkas_coefficients(&mut terms, &mut proof, &[], &[], &|| false);
    assert_eq!(proof, original);
    assert!(ay_proof::check_proof_strict(&proof, &terms).is_err());
}

#[test]
fn retained_integer_payload_is_not_reclassified() {
    let (mut terms, mut proof, _, _) = fixture();
    let ProofStep::TheoryLemma { lia, .. } = &mut proof.steps[0] else {
        panic!("theory lemma");
    };
    *lia = Some(LiaAnnotation::BoundsGap);
    let original = proof.clone();
    reconstruct_missing_farkas_coefficients(&mut terms, &mut proof, &[], &[], &|| false);
    assert_eq!(proof, original);
}

#[test]
fn cancellation_preserves_retained_classification() {
    let (mut terms, mut proof, _, _) = fixture();
    let original = proof.clone();
    reconstruct_missing_farkas_coefficients(&mut terms, &mut proof, &[], &[], &|| true);
    assert_eq!(proof, original);
}
