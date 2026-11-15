// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Portable native SOS adapter tests; no producer solver is invoked.

use ay_core::{NraSosCertificate, NraSosOrigin, NraSosRational, NraSosTerm};
use num_bigint::BigInt;

use super::*;

mod descendants;

fn rational(value: i64) -> NraSosRational {
    NraSosRational {
        numerator: BigInt::from(value),
        denominator: BigInt::from(1u8),
    }
}

struct Fixture {
    terms: TermStore,
    proof: Proof,
    assumptions: Vec<TermId>,
    variable: TermId,
    foreign: TermId,
}

impl Fixture {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let x = terms.mk_var("sos_x", Sort::Real);
        let foreign = terms.mk_var("sos_foreign", Sort::Real);
        let one = terms.mk_rational(num_rational::BigRational::from_integer(BigInt::from(1u8)));
        let zero = terms.mk_rational(num_rational::BigRational::from_integer(BigInt::from(0u8)));
        let lower = terms.mk_ge(x, one);
        let upper = terms.mk_le(x, zero);
        let not_lower = terms.mk_not(lower);
        let not_upper = terms.mk_not(upper);
        let certificate = NraSosCertificate {
            basis: vec![vec![], vec![x]],
            gram: vec![vec![rational(0); 2]; 2],
            terms: vec![
                NraSosTerm {
                    origin: NraSosOrigin::ClauseLiteral { position: 0 },
                    multiplier: rational(1),
                },
                NraSosTerm {
                    origin: NraSosOrigin::ClauseLiteral { position: 1 },
                    multiplier: rational(1),
                },
            ],
            rhs: rational(-1),
        };
        let mut proof = Proof::new();
        let lemma = proof.add_step(ProofStep::NraSos {
            clause: vec![not_lower, not_upper],
            certificate,
        });
        let lower_assume = proof.add_assume(lower, None);
        let upper_assume = proof.add_assume(upper, None);
        let tail = proof.add_resolution(vec![not_upper], lower, lemma, lower_assume);
        proof.add_resolution(vec![], upper, tail, upper_assume);
        Self {
            terms,
            proof,
            assumptions: vec![lower, upper],
            variable: x,
            foreign,
        }
    }

    fn bundle(&self) -> SerializableProofBundle {
        SerializableProofBundle::from_proof(&self.proof, &self.terms, self.assumptions.clone())
    }
}

fn payload(bundle: &mut SerializableProofBundle) -> &mut NraSosCertificate {
    let ProofStep::NraSos { certificate, .. } = &mut bundle.steps[0] else {
        panic!("SOS fixture")
    };
    certificate
}

#[test]
fn nra_sos_bundle_roundtrip_rechecks_and_retains_native_quality() {
    let fixture = Fixture::new();
    let encoded = serde_json::to_vec(&fixture.bundle()).expect("serialize exact raw DTO");
    let bundle: SerializableProofBundle =
        serde_json::from_slice(&encoded).expect("decode bounded DTO");
    let checked =
        re_check_bundle_strict(&bundle).expect("source-bound native theorem and authored closure");
    assert_eq!(checked.quality.theory_lemma_count, 1);
    assert_eq!(checked.quality.trust_count, 0);
    assert_eq!(checked.quality.hole_count, 0);
    assert_eq!(checked.assume_terms, fixture.assumptions);
}

#[test]
fn nra_sos_metered_bundle_copy_retains_fresh_independent_replay() {
    let fixture = Fixture::new();
    let mut charged_bytes = 0;
    let bundle = SerializableProofBundle::from_proof_with_progress(
        &fixture.proof,
        &fixture.terms,
        &fixture.assumptions,
        &mut |_, bytes| {
            charged_bytes += bytes;
            true
        },
    )
    .expect("caller-metered native SOS copy");
    assert!(charged_bytes > 0);
    assert_eq!(bundle.steps, fixture.proof.steps);
    let checked = re_check_bundle_strict(&bundle).expect("fresh source-bound native SOS replay");
    assert_eq!(checked.quality.theory_lemma_count, 1);
    assert_eq!(checked.assume_terms, fixture.assumptions);
}

#[test]
fn nra_sos_bundle_preflight_rejects_missing_basis_root_before_reconstruction() {
    let fixture = Fixture::new();
    let mut bundle = fixture.bundle();
    payload(&mut bundle).basis[1][0] = TermId(u32::MAX);
    assert!(matches!(
        preflight_bundle(&bundle),
        Err(ProofCheckError::MalformedProofBundle { .. })
    ));
}

#[test]
fn nra_sos_bundle_preflight_rejects_mistyped_roots_and_source_slots() {
    let fixture = Fixture::new();
    let mut bundle = fixture.bundle();
    payload(&mut bundle).basis[1][0] = fixture.assumptions[0];
    assert!(preflight_bundle(&bundle).is_err());
    let mut bundle = fixture.bundle();
    let ProofStep::NraSos { clause, .. } = &mut bundle.steps[0] else {
        panic!("SOS fixture")
    };
    clause[0] = fixture.variable;
    assert!(preflight_bundle(&bundle).is_err());
    let mut bundle = fixture.bundle();
    payload(&mut bundle).terms[0].origin = NraSosOrigin::Product { left: 0, right: 2 };
    assert!(preflight_bundle(&bundle).is_err());
}

#[test]
fn nra_sos_bundle_preflight_caps_payload_and_rejects_bad_denominators() {
    let fixture = Fixture::new();
    let mut bundle = fixture.bundle();
    payload(&mut bundle).basis = vec![vec![]; NraSosCertificate::MAX_BASIS + 1];
    assert!(matches!(
        preflight_bundle(&bundle),
        Err(ProofCheckError::ResourceLimit)
    ));
    let mut bundle = fixture.bundle();
    payload(&mut bundle).rhs.numerator = BigInt::from(1u8) << NraSosRational::MAX_BITS as usize;
    assert!(matches!(
        preflight_bundle(&bundle),
        Err(ProofCheckError::ResourceLimit)
    ));
    let mut bundle = fixture.bundle();
    payload(&mut bundle).rhs.denominator = BigInt::from(0u8);
    assert!(matches!(
        preflight_bundle(&bundle),
        Err(ProofCheckError::MalformedProofBundle { .. })
    ));
}

#[test]
fn nra_sos_native_reader_rejects_payload_and_source_root_mutations() {
    let fixture = Fixture::new();
    let mut bundle = fixture.bundle();
    payload(&mut bundle).terms[0].multiplier = rational(2);
    assert!(re_check_bundle_strict(&bundle).is_err());
    let mut bundle = fixture.bundle();
    payload(&mut bundle).basis[1][0] = fixture.foreign;
    assert!(re_check_bundle_strict(&bundle).is_err());
    let mut bundle = fixture.bundle();
    let ProofStep::NraSos { clause, .. } = &mut bundle.steps[0] else {
        panic!("SOS fixture")
    };
    clause[0] = fixture.assumptions[0]; // Reverse only the source literal polarity.
    assert!(re_check_bundle_strict(&bundle).is_err());
}

#[test]
fn nra_sos_alethe_is_a_checked_lowering_not_an_invented_rule() {
    let fixture = Fixture::new();
    let printer = AlethePrinter::new(&fixture.terms);
    printer
        .prepare_proof(&fixture.proof)
        .expect("bounded native payload prepares");
    let text = printer
        .format_step(&fixture.proof.steps[0], ProofId(0))
        .expect("checked lowering renders");
    assert!(text.contains("ay-nra-sos:"));
    // The linear certificate is one pinned `la_generic` plus the resolution
    // binding the step's own clause; never a fabricated SOS rule.
    assert!(text.contains(":rule la_generic"));
    assert!(!text.contains(":rule hole"));
    assert!(!text.contains(":rule trust"));
    assert!(!text.contains(":rule nra_sos"));
    let document =
        crate::try_export_alethe(&fixture.proof, &fixture.terms).expect("native SOS document");
    assert!(!document.contains(":rule hole"), "{document}");
}

#[test]
fn nra_sos_printer_rejects_bad_payload_before_clause_copy() {
    let fixture = Fixture::new();
    let mut proof = fixture.proof.clone();
    let ProofStep::NraSos { certificate, .. } = &mut proof.steps[0] else {
        panic!("SOS fixture")
    };
    certificate.basis[1][0] = TermId(u32::MAX);
    let printer = AlethePrinter::new(&fixture.terms);
    assert!(printer.prepare_proof(&proof).is_err());
    assert!(printer.format_step(&proof.steps[0], ProofId(0)).is_err());
    assert!(!crate::carcara_proof_surface_is_supported(
        &proof,
        &fixture.terms,
        None
    ));
}

#[test]
fn nra_sos_variable_collectors_include_embedded_basis_roots() {
    let fixture = Fixture::new();
    let mut proof = fixture.proof.clone();
    let ProofStep::NraSos { certificate, .. } = &mut proof.steps[0] else {
        panic!("SOS fixture")
    };
    // This is deliberately semantically invalid: root collectors must still
    // see payload-only roots, not silently omit the altered declaration.
    certificate.basis[1][0] = fixture.foreign;
    let vars = crate::variables::collect_proof_variables(&proof, &fixture.terms)
        .expect("typed distinct symbols");
    assert!(vars.iter().any(|(name, _)| name == "sos_foreign"));
    let auxiliary = crate::variables::collect_auxiliary_proof_declarations(
        &proof,
        &fixture.terms,
        &fixture.assumptions,
    )
    .expect("auxiliary root collection");
    assert!(auxiliary.iter().any(|(name, _)| name == "sos_foreign"));
}

#[test]
fn nra_sos_native_leaf_does_not_hide_foreign_assumptions() {
    let fixture = Fixture::new();
    let native = crate::terminal_trust_report_with_provenance(&fixture.proof, |term| {
        fixture.assumptions.contains(&term)
    });
    assert!(native.is_trust_free());
    let foreign = crate::terminal_trust_report_with_provenance(&fixture.proof, |term| {
        term == fixture.assumptions[0]
    });
    assert_eq!(foreign.foreign_assume_on_path, 1);
    assert!(crate::validate_reachable_assumes_in_problem_scope(
        &fixture.proof,
        &fixture.assumptions[..1]
    )
    .is_err());
    assert!(crate::validate_reachable_assumes_in_problem_scope(
        &fixture.proof,
        &fixture.assumptions
    )
    .is_ok());
}
