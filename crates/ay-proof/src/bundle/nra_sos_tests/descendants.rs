// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Direct live APIs must refuse dangling descendants before indexing them.

use super::*;

fn assert_live_apis_refuse(fixture: &Fixture, entries: Vec<(TermData, Sort)>) {
    let terms = TermStore::from_entries(entries, None, None, fixture.terms.var_counter());
    let authenticated = crate::authenticate_premise_clauses_strict_with_context(
        &fixture.proof,
        &terms,
        None,
        None,
        &fixture.assumptions,
    );
    assert!(matches!(
        authenticated,
        Err(ProofCheckError::MalformedProofBundle { .. })
    ));
    assert!(matches!(
        crate::check_proof_strict(&fixture.proof, &terms),
        Err(ProofCheckError::MalformedProofBundle { .. })
    ));
    assert!(!crate::carcara_proof_surface_is_supported(
        &fixture.proof,
        &terms,
        None
    ));
    assert!(crate::try_export_alethe(&fixture.proof, &terms).is_err());
}

#[test]
fn nra_sos_live_apis_reject_dangling_negation_descendants() {
    let fixture = Fixture::new();
    let ProofStep::NraSos { clause, .. } = &fixture.proof.steps[0] else {
        panic!("SOS fixture")
    };
    for missing in [TermId(fixture.terms.len() as u32), TermId(u32::MAX)] {
        let mut entries = fixture.terms.entries_snapshot();
        entries[clause[0].index()].0 = TermData::Not(missing);
        assert_live_apis_refuse(&fixture, entries);
    }
}

#[test]
fn nra_sos_live_apis_reject_dangling_arithmetic_descendants() {
    let fixture = Fixture::new();
    for missing in [TermId(fixture.terms.len() as u32), TermId(u32::MAX)] {
        let mut entries = fixture.terms.entries_snapshot();
        let TermData::App(_, arguments) = &mut entries[fixture.assumptions[0].index()].0 else {
            panic!("comparison fixture")
        };
        arguments[0] = missing;
        assert_live_apis_refuse(&fixture, entries);
    }
}

#[test]
fn nra_sos_live_apis_preserve_valid_descendant_control() {
    let fixture = Fixture::new();
    crate::authenticate_premise_clauses_strict_with_context(
        &fixture.proof,
        &fixture.terms,
        None,
        None,
        &fixture.assumptions,
    )
    .expect("source-bound theorem and problem-authorized resolution remain accepted");
    crate::check_proof_strict(&fixture.proof, &fixture.terms)
        .expect("complete native proof remains accepted");
    assert!(crate::carcara_proof_surface_is_supported(
        &fixture.proof,
        &fixture.terms,
        None
    ));
    let document = crate::try_export_alethe(&fixture.proof, &fixture.terms)
        .expect("checked native lowering remains renderable");
    assert!(document.contains(":rule la_generic"), "{document}");
    assert!(!document.contains(":rule hole"), "{document}");
}
