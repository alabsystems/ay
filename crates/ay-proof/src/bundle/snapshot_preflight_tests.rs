// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Snapshot shapes must be checked before recursive canonical-entry hashing.

use super::*;
use ay_core::{ArraySort, BitVecSort, DatatypeConstructor, DatatypeField, DatatypeSort};

fn base_entries() -> Vec<(TermData, Sort)> {
    vec![
        (TermData::Const(Constant::Bool(true)), Sort::Bool),
        (TermData::Const(Constant::Bool(false)), Sort::Bool),
    ]
}

fn overdeep_sort() -> Sort {
    // Only one level beyond the reader's bound: enough to exercise refusal,
    // without constructing a pathological fixture whose Drop could overflow.
    let mut sort = Sort::Bool;
    for _ in 0..=MAX_BUNDLE_SORT_DEPTH {
        sort = Sort::Seq(Box::new(sort));
    }
    sort
}

fn assert_snapshot_rejected(entries: Vec<(TermData, Sort)>, fragment: &str) {
    let error = validate_term_snapshot(&entries).expect_err("invalid snapshot shape");
    assert!(
        matches!(&error, ProofCheckError::MalformedProofBundle { .. }),
        "expected a structural preflight error, got {error}"
    );
    assert!(error.to_string().contains(fragment), "{error}");
    let bundle = SerializableProofBundle {
        schema: PROOF_BUNDLE_SCHEMA.to_string(),
        steps: Vec::new(),
        term_entries: entries,
        true_term: Some(TermId(0)),
        false_term: Some(TermId(1)),
        var_counter: 0,
        obligation_assertions: Vec::new(),
        datatype_declarations: Vec::new(),
        constructor_selectors: Vec::new(),
        datatype_member_signatures: Vec::new(),
        declared_function_identities: Vec::new(),
    };
    let error = re_check_bundle_strict(&bundle).expect_err("public reader must preflight first");
    assert!(
        matches!(&error, ProofCheckError::MalformedProofBundle { .. }),
        "snapshot must fail before proof reconstruction/checking: {error}"
    );
    assert!(error.to_string().contains(fragment), "{error}");
}

#[test]
fn overdeep_recorded_sort_is_rejected_by_snapshot_preflight() {
    let mut entries = base_entries();
    entries.push((TermData::Var("deep".to_string(), 0), overdeep_sort()));
    assert_snapshot_rejected(entries, "maximum sort nesting depth");
}

#[test]
fn overdeep_forall_binder_sort_is_rejected_by_snapshot_preflight() {
    let mut entries = base_entries();
    entries.push((
        TermData::Forall(
            vec![
                ("shallow".to_string(), Sort::Int),
                ("deep".to_string(), overdeep_sort()),
            ],
            TermId(0),
            Vec::new(),
        ),
        Sort::Bool,
    ));
    assert_snapshot_rejected(entries, "maximum sort nesting depth");
}

#[test]
fn overdeep_exists_binder_sort_is_rejected_by_snapshot_preflight() {
    let mut entries = base_entries();
    entries.push((
        TermData::Exists(
            vec![("deep".to_string(), overdeep_sort())],
            TermId(0),
            Vec::new(),
        ),
        Sort::Bool,
    ));
    assert_snapshot_rejected(entries, "maximum sort nesting depth");
}

fn malformed_nested_datatype() -> Sort {
    Sort::Datatype(DatatypeSort::new(
        "D",
        vec![DatatypeConstructor::new(
            "C",
            vec![DatatypeField::new(
                "field",
                Sort::Array(Box::new(ArraySort::new(
                    Sort::Int,
                    Sort::Seq(Box::new(Sort::BitVec(BitVecSort::new(0)))),
                ))),
            )],
        )],
    ))
}

#[test]
fn malformed_nested_datatype_field_is_rejected_in_recorded_and_binder_sorts() {
    let mut entries = base_entries();
    entries.push((
        TermData::Var("d".to_string(), 0),
        malformed_nested_datatype(),
    ));
    assert_snapshot_rejected(entries, "invalid bit-vector width 0");
    let mut entries = base_entries();
    entries.push((
        TermData::Forall(
            vec![("d".to_string(), malformed_nested_datatype())],
            TermId(0),
            Vec::new(),
        ),
        Sort::Bool,
    ));
    assert_snapshot_rejected(entries, "invalid bit-vector width 0");
}

#[test]
fn duplicate_valid_entries_remain_rejected_after_shape_validation() {
    let mut entries = base_entries();
    entries.push((TermData::Var("x".to_string(), 7), Sort::Int));
    assert!(validate_term_snapshot(&entries).is_ok());
    entries.push((TermData::Var("x".to_string(), 7), Sort::Int));
    assert_snapshot_rejected(entries, "duplicates an earlier canonical term entry");
}

#[test]
fn duplicate_valid_quantifiers_remain_rejected() {
    let mut entries = base_entries();
    let binder_sort = Sort::Seq(Box::new(Sort::Int));
    let quantified = TermData::Forall(vec![("x".to_string(), binder_sort)], TermId(0), Vec::new());
    entries.push((quantified.clone(), Sort::Bool));
    assert!(validate_term_snapshot(&entries).is_ok());
    entries.push((quantified, Sort::Bool));
    assert_snapshot_rejected(entries, "duplicates an earlier canonical term entry");
}

#[test]
fn recorded_and_quantified_sort_at_depth_limit_remains_admitted() {
    let mut sort = Sort::Bool;
    for _ in 0..MAX_BUNDLE_SORT_DEPTH {
        sort = Sort::Seq(Box::new(sort));
    }
    let mut entries = base_entries();
    entries.push((TermData::Var("at_limit".to_string(), 0), sort.clone()));
    entries.push((
        TermData::Exists(vec![("bound".to_string(), sort)], TermId(0), Vec::new()),
        Sort::Bool,
    ));
    assert!(validate_term_snapshot(&entries).is_ok());
}

#[test]
fn overdeep_anchor_sort_is_rejected_before_proof_reconstruction() {
    let bundle = SerializableProofBundle {
        schema: PROOF_BUNDLE_SCHEMA.into(),
        steps: vec![ProofStep::Anchor {
            end_step: ProofId(0),
            variables: vec![("deep_anchor".into(), overdeep_sort())],
        }],
        term_entries: base_entries(),
        true_term: Some(TermId(0)),
        false_term: Some(TermId(1)),
        var_counter: 0,
        obligation_assertions: vec![],
        datatype_declarations: vec![],
        constructor_selectors: vec![],
        datatype_member_signatures: vec![],
        declared_function_identities: vec![],
    };
    let error = re_check_bundle_strict(&bundle).expect_err("refuse before steps.clone()");
    assert!(matches!(
        &error,
        ProofCheckError::MalformedProofBundle { .. }
    ));
    assert!(error.to_string().contains("maximum sort nesting depth"));
}

#[test]
fn anchor_sort_preflight_retains_the_inclusive_depth_boundary() {
    let mut sort = Sort::Bool;
    for _ in 0..MAX_BUNDLE_SORT_DEPTH {
        sort = Sort::Seq(Box::new(sort));
    }
    let steps = vec![ProofStep::Anchor {
        end_step: ProofId(0),
        variables: vec![("at_limit".into(), sort)],
    }];
    assert!(validate_proof_snapshot(&steps, &base_entries()).is_ok());
    // Structural admission does not authenticate an anchor-only refutation.
    let terms = TermStore::from_entries(base_entries(), Some(TermId(0)), Some(TermId(1)), 0);
    assert!(crate::check_proof_strict(&Proof::from_steps(steps), &terms).is_err());
}

#[test]
fn malformed_nested_anchor_sort_is_rejected_by_proof_preflight() {
    let steps = vec![ProofStep::Anchor {
        end_step: ProofId(0),
        variables: vec![("bad_anchor".into(), malformed_nested_datatype())],
    }];
    let error = validate_proof_snapshot(&steps, &base_entries()).expect_err("invalid field sort");
    assert!(matches!(
        &error,
        ProofCheckError::MalformedProofBundle { .. }
    ));
    assert!(error.to_string().contains("invalid bit-vector width 0"));
}
