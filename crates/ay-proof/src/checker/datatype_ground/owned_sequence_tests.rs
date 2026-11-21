// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{Sort, Symbol};

fn registries() -> (Vec<(String, Vec<String>)>, Vec<(String, Vec<String>)>) {
    (
        vec![("OwnedR".into(), vec!["owned_r".into()])],
        vec![("owned_r".into(), vec!["children".into()])],
    )
}
fn carrier() -> Sort {
    Sort::Uninterpreted("OwnedR".into())
}

#[test]
fn owned_sequence_checker_admits_physical_edges_before_copy_and_observes_preparation_stop() {
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", carrier());
    let repeated = terms.mk_app(Symbol::named("wide"), vec![r; 100_000], Sort::Bool);
    let (datatypes, selectors) = registries();
    let mut charged_edges = false;
    let result = validate_datatype_ground_conflict_with_progress(
        &terms,
        ProofId(0),
        &[repeated],
        &datatypes,
        &selectors,
        &mut |work, _| {
            charged_edges |= work == 100_000;
            work < 100_000
        },
    );
    assert!(
        charged_edges,
        "physical repeated edges must be admitted before their scan/copy"
    );
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));

    let mut polls = 0;
    let result = validate_datatype_ground_conflict_with_progress(
        &terms,
        ProofId(0),
        &[repeated],
        &datatypes,
        &selectors,
        &mut |_, _| {
            polls += 1;
            false
        },
    );
    assert_eq!(
        polls, 1,
        "an initial stop must precede all preparation copies"
    );
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
}

#[test]
fn owned_sequence_checker_stop_during_closure_cannot_publish_a_conflict() {
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", carrier());
    let unit = terms.mk_app(Symbol::named("seq.unit"), [r], Sort::seq(carrier()));
    let parent = terms.mk_app(Symbol::named("owned_r"), [unit], carrier());
    let eq = terms.mk_eq(r, parent);
    let denied = terms.mk_not(eq);
    let (datatypes, selectors) = registries();
    let mut round_admitted = false;
    let mut stopped_in_round = false;
    let result = validate_datatype_ground_conflict_with_progress(
        &terms,
        ProofId(0),
        &[denied],
        &datatypes,
        &selectors,
        &mut |work, _| {
            if round_admitted {
                stopped_in_round = true;
                return false;
            }
            round_admitted = work > 1000;
            true
        },
    );
    assert!(round_admitted && stopped_in_round);
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
}

#[test]
fn owned_sequence_native_checker_unit_cycle_and_forged_source_refusal() {
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", carrier());
    let other = terms.mk_var("other", carrier());
    let unit = terms.mk_app(Symbol::named("seq.unit"), [r], Sort::seq(carrier()));
    let parent = terms.mk_app(Symbol::named("owned_r"), [unit], carrier());
    let eq = terms.mk_eq(r, parent);
    let denied = terms.mk_not(eq);
    let forged = terms.mk_eq(other, parent);
    let forged = terms.mk_not(forged);
    let (datatypes, selectors) = registries();
    assert!(recognize_datatype_ground_conflict(
        &terms,
        &[denied],
        &datatypes,
        &selectors
    ));
    assert!(!recognize_datatype_ground_conflict(
        &terms,
        &[forged],
        &datatypes,
        &selectors
    ));
    assert!(!recognize_datatype_ground_conflict(
        &terms,
        &[denied],
        &[],
        &[]
    ));
}

#[test]
fn owned_sequence_native_checker_nth_clause_requires_exact_in_bounds_premises() {
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", carrier());
    let sequence = terms.mk_var("children", Sort::seq(carrier()));
    let other = terms.mk_var("other_children", Sort::seq(carrier()));
    let index = terms.mk_var("index", Sort::Int);
    let zero = terms.mk_int(0.into());
    let parent = terms.mk_app(Symbol::named("owned_r"), [sequence], carrier());
    let nth = terms.mk_app(Symbol::named("seq.nth"), [sequence, index], carrier());
    let eq_parent = terms.mk_eq(r, parent);
    let eq_nth = terms.mk_eq(r, nth);
    let len = terms.mk_app(Symbol::named("seq.len"), [sequence], Sort::Int);
    let other_len = terms.mk_app(Symbol::named("seq.len"), [other], Sort::Int);
    let lower = terms.mk_app(Symbol::named("<="), [zero, index], Sort::Bool);
    let upper = terms.mk_app(Symbol::named("<"), [index, len], Sort::Bool);
    let wrong_upper = terms.mk_app(Symbol::named("<"), [index, other_len], Sort::Bool);
    let a = terms.mk_not(eq_parent);
    let b = terms.mk_not(eq_nth);
    let lo = terms.mk_not(lower);
    let hi = terms.mk_not(upper);
    let wrong = terms.mk_not(wrong_upper);
    let (datatypes, selectors) = registries();
    assert!(recognize_datatype_ground_conflict(
        &terms,
        &[a, b, lo, hi],
        &datatypes,
        &selectors
    ));
    for clause in [
        vec![a, b, hi],
        vec![a, b, lo],
        vec![a, b, lo, wrong],
        vec![a, b, lo, upper],
    ] {
        assert!(
            !recognize_datatype_ground_conflict(&terms, &clause, &datatypes, &selectors),
            "missing, other-sequence or OOB guard cannot prove containment"
        );
    }
    let mut refused = |_, _| false;
    assert_eq!(
        validate_datatype_ground_conflict_with_progress(
            &terms,
            ProofId(0),
            &[a, b, lo, hi],
            &datatypes,
            &selectors,
            &mut refused
        ),
        Err(ProofCheckError::ResourceLimit)
    );
}

#[test]
fn owned_sequence_native_checker_finite_tree_and_concat_identity_are_not_cycles() {
    let mut terms = TermStore::new();
    let s = terms.mk_var("s", Sort::seq(carrier()));
    let empty = terms.mk_app(Symbol::named("seq.empty"), [], Sort::seq(carrier()));
    let concat = terms.mk_app(Symbol::named("seq.++"), [s, empty], Sort::seq(carrier()));
    let parent = terms.mk_app(Symbol::named("owned_r"), [s], carrier());
    let r = terms.mk_var("r", carrier());
    let r_parent = terms.mk_eq(r, parent);
    let self_concat = terms.mk_eq(s, concat);
    let a = terms.mk_not(r_parent);
    let b = terms.mk_not(self_concat);
    let (datatypes, selectors) = registries();
    assert!(!recognize_datatype_ground_conflict(
        &terms,
        &[a, b],
        &datatypes,
        &selectors
    ));
}

#[test]
fn owned_sequence_native_strict_complete_proof_binds_actual_typed_declarations_and_source() {
    use crate::{check_proof_strict_with_typed_context, DatatypeMemberSignature};
    use ay_core::{Proof, TheoryLemmaKind};
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", carrier());
    let other = terms.mk_var("other", carrier());
    let sequence = terms.mk_app(Symbol::named("seq.unit"), [r], Sort::seq(carrier()));
    let parent = terms.mk_app(Symbol::named("owned_r"), [sequence], carrier());
    let equality = terms.mk_eq(r, parent);
    let denied = terms.mk_not(equality);
    let wrong = terms.mk_eq(other, parent);
    let mut proof = Proof::new();
    let lemma = proof.add_theory_lemma_with_kind(
        "DT+Seq",
        vec![denied],
        TheoryLemmaKind::DatatypeGroundConflict,
    );
    let assumption = proof.add_assume(equality, None);
    proof.add_resolution(vec![], equality, lemma, assumption);
    let (datatypes, selectors) = registries();
    let signatures = vec![
        DatatypeMemberSignature {
            identity: "owned_r".into(),
            argument_sorts: vec![Sort::seq(carrier())],
            result_sort: carrier(),
            nullary_term: None,
        },
        DatatypeMemberSignature {
            identity: "children".into(),
            argument_sorts: vec![carrier()],
            result_sort: Sort::seq(carrier()),
            nullary_term: None,
        },
        DatatypeMemberSignature {
            identity: "is-owned_r".into(),
            argument_sorts: vec![carrier()],
            result_sort: Sort::Bool,
            nullary_term: None,
        },
    ];
    let quality = check_proof_strict_with_typed_context(
        &proof,
        &terms,
        Some(&datatypes),
        Some(&selectors),
        &signatures,
        Some(&[equality]),
    )
    .expect("independently checked complete native proof");
    assert!(quality.is_complete());
    assert_eq!(quality.trust_count, 0);
    assert_eq!(quality.hole_count, 0);
    assert!(
        check_proof_strict_with_typed_context(
            &proof,
            &terms,
            Some(&datatypes),
            Some(&selectors),
            &signatures,
            Some(&[wrong])
        )
        .is_err(),
        "serialized/changed premises cannot authorize the actual Assume"
    );
    let mut wrong_signatures = signatures;
    wrong_signatures[0].argument_sorts[0] = Sort::seq(Sort::Int);
    assert!(
        check_proof_strict_with_typed_context(
            &proof,
            &terms,
            Some(&datatypes),
            Some(&selectors),
            &wrong_signatures,
            Some(&[equality])
        )
        .is_err(),
        "wrong constructor field metadata grants no native proof authority"
    );
}

#[test]
fn owned_sequence_native_strict_nth_proof_retains_every_guard_source() {
    use crate::{check_proof_strict_with_typed_context, DatatypeMemberSignature};
    use ay_core::{Proof, TheoryLemmaKind};
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", carrier());
    let children = terms.mk_var("nth_children_value", Sort::seq(carrier()));
    let index = terms.mk_var("index", Sort::Int);
    let zero = terms.mk_int(0.into());
    let parent = terms.mk_app(Symbol::named("owned_r"), [children], carrier());
    let nth = terms.mk_app(Symbol::named("seq.nth"), [children, index], carrier());
    let parent_eq = terms.mk_eq(r, parent);
    let nth_eq = terms.mk_eq(r, nth);
    let len = terms.mk_app(Symbol::named("seq.len"), [children], Sort::Int);
    let lower = terms.mk_app(Symbol::named("<="), [zero, index], Sort::Bool);
    let upper = terms.mk_app(Symbol::named("<"), [index, len], Sort::Bool);
    let roots = [parent_eq, nth_eq, lower, upper];
    let literals: Vec<_> = roots.iter().map(|&root| terms.mk_not(root)).collect();
    let mut proof = Proof::new();
    let mut previous = proof.add_theory_lemma_with_kind(
        "DT+Seq",
        literals.clone(),
        TheoryLemmaKind::DatatypeGroundConflict,
    );
    for (index, &root) in roots.iter().enumerate() {
        let assumption = proof.add_assume(root, None);
        previous = proof.add_resolution(literals[index + 1..].to_vec(), root, previous, assumption);
    }
    let (datatypes, selectors) = registries();
    let signatures = [
        DatatypeMemberSignature {
            identity: "owned_r".into(),
            argument_sorts: vec![Sort::seq(carrier())],
            result_sort: carrier(),
            nullary_term: None,
        },
        DatatypeMemberSignature {
            identity: "children".into(),
            argument_sorts: vec![carrier()],
            result_sort: Sort::seq(carrier()),
            nullary_term: None,
        },
        DatatypeMemberSignature {
            identity: "is-owned_r".into(),
            argument_sorts: vec![carrier()],
            result_sort: Sort::Bool,
            nullary_term: None,
        },
    ];
    let check = |scope: &[TermId]| {
        check_proof_strict_with_typed_context(
            &proof,
            &terms,
            Some(&datatypes),
            Some(&selectors),
            &signatures,
            Some(scope),
        )
    };
    let quality = check(&roots).expect("typed strict native nth-cycle proof");
    assert!(quality.is_complete());
    assert_eq!(quality.trust_count, 0);
    assert_eq!(quality.hole_count, 0);
    assert!(
        check(&roots[..3]).is_err(),
        "missing actual guard scope cannot authorize Assume"
    );
    let opposite = terms.mk_not(upper);
    assert!(
        check_proof_strict_with_typed_context(
            &proof,
            &terms,
            Some(&datatypes),
            Some(&selectors),
            &signatures,
            Some(&[parent_eq, nth_eq, lower, opposite])
        )
        .is_err(),
        "opposite upper guard is a different original source"
    );
}
