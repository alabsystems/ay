// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

mod boundaries;
mod progress;

fn fixture() -> SerializableProofBundle {
    let mut terms = TermStore::new();
    let proposition = terms.mk_var("preflight_p", Sort::Bool);
    let negative = terms.mk_not_raw(proposition);
    let mut proof = Proof::new();
    let positive_step = proof.add_assume(proposition, None);
    let negative_step = proof.add_assume(negative, None);
    proof.add_resolution(vec![], proposition, positive_step, negative_step);
    SerializableProofBundle::from_proof(&proof, &terms, vec![proposition, negative])
}

fn with_context() -> SerializableProofBundle {
    let mut bundle = fixture();
    bundle.datatype_declarations = vec![("D".into(), vec!["DZero".into(), "DWrap".into()])];
    bundle.constructor_selectors = vec![
        ("DZero".into(), vec![]),
        ("DWrap".into(), vec!["d_value".into()]),
    ];
    let carrier = Sort::Uninterpreted("D".into());
    bundle.datatype_member_signatures = [
        ("DZero", vec![], carrier.clone()),
        ("DWrap", vec![Sort::Int], carrier.clone()),
        ("is-DZero", vec![carrier.clone()], Sort::Bool),
        ("is-DWrap", vec![carrier.clone()], Sort::Bool),
        ("d_value", vec![carrier], Sort::Int),
    ]
    .into_iter()
    .map(
        |(identity, argument_sorts, result_sort)| DatatypeMemberSignature {
            identity: identity.into(),
            argument_sorts,
            result_sort,
            nullary_term: None,
        },
    )
    .collect();
    bundle
}

fn compare(
    bundle: &SerializableProofBundle,
) -> Result<HashMap<String, &'static str>, ProofCheckError> {
    let old = preflight_bundle_legacy(bundle);
    let new = preflight_bundle_with_progress(bundle, &mut |_, _| true);
    assert_eq!(old.is_ok(), new.is_ok(), "old={old:?}, new={new:?}");
    if let (Ok(old), Ok(new)) = (&old, &new) {
        assert_eq!(old, new);
    }
    new
}

fn assert_malformed<T>(result: Result<T, ProofCheckError>, expected: &str) {
    assert!(
        matches!(result, Err(ProofCheckError::MalformedProofBundle { ref reason }) if reason.contains(expected))
    );
}

fn assert_resource<T>(result: Result<T, ProofCheckError>) {
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
}

#[test]
fn valid_plain_and_declaration_bundles_return_the_same_namespace_as_legacy() {
    assert!(compare(&fixture()).expect("plain control").is_empty());
    let symbols = compare(&with_context()).expect("declaration control");
    assert_eq!(symbols.len(), 5);
    for (name, role) in [
        ("DZero", "a constructor"),
        ("DWrap", "a constructor"),
        ("is-DZero", "a derived tester"),
        ("is-DWrap", "a derived tester"),
        ("d_value", "a selector"),
    ] {
        assert_eq!(symbols.get(name).copied(), Some(role));
    }
}

#[test]
fn schema_identity_nullary_authority_and_variable_counter_remain_separate() {
    let mut bundle = fixture();
    bundle.schema = "not-the-replay-schema".repeat(4_096);
    bundle.var_counter = u32::MAX;
    bundle
        .datatype_member_signatures
        .push(DatatypeMemberSignature {
            identity: "not-declared".into(),
            argument_sorts: vec![],
            result_sort: Sort::Bool,
            nullary_term: Some(TermId::SENTINEL),
        });
    // The replay/context layers reject unsupported schema or signature
    // authority. Neither the old nor new structural preflight grants it.
    compare(&bundle).expect("preflight is not schema or typed-context authentication");
}

#[test]
fn malformed_declarations_constructor_uses_and_proof_edges_match_legacy() {
    let mut duplicate = with_context();
    duplicate.constructor_selectors[1].1.push("DZero".into());
    assert_malformed(compare(&duplicate), "ambiguous");

    let mut constructor = with_context();
    constructor
        .term_entries
        .push((TermData::Var("DZero".into(), 500), Sort::Int));
    assert_malformed(compare(&constructor), "outside datatype");

    let mut proof = with_context();
    let ProofStep::Resolution { clause1, .. } = &mut proof.steps[2] else {
        panic!("fixture resolution");
    };
    *clause1 = ProofId(u32::MAX);
    assert_malformed(compare(&proof), "missing proof step");
}

#[test]
fn non_prior_term_edges_and_duplicate_complete_entries_still_fail_first() {
    let mut edge = fixture();
    edge.term_entries
        .push((TermData::Not(TermId::SENTINEL), Sort::Bool));
    edge.true_term = None;
    assert_malformed(compare(&edge), "non-prior term");
    let mut duplicate = fixture();
    duplicate
        .term_entries
        .push(duplicate.term_entries[0].clone());
    assert_malformed(
        compare(&duplicate),
        "duplicates an earlier canonical term entry",
    );
}
