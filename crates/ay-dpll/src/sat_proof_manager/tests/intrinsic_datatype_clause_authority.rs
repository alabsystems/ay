// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::TheoryLemmaKind;

fn datatype_registries() -> crate::theory_inference::DatatypeRegistryData {
    (
        vec![(
            "Tower".to_owned(),
            vec!["stack".to_owned(), "empty".to_owned()],
        )],
        vec![
            (
                "stack".to_owned(),
                vec!["top".to_owned(), "rest".to_owned()],
            ),
            ("empty".to_owned(), Vec::new()),
        ],
    )
}

#[test]
fn exact_fragment_checks_registered_datatype_authority_unit() {
    let mut terms = TermStore::new();
    let tower = Sort::Uninterpreted("Tower".to_owned());
    let value = terms.mk_var("cycle_value", tower.clone());
    let head = terms.mk_var("cycle_head", Sort::Int);
    let empty = terms.mk_fresh_named_var("empty", tower.clone());
    let stack = terms.mk_app(Symbol::named("stack"), [head, value], tower.clone());
    let cycle = terms.mk_eq(value, stack);
    let registries = datatype_registries();
    let (datatype_decls, constructor_selectors) = &registries;
    let not_cycle = terms.mk_not_raw(cycle);
    assert!(ay_proof::recognize_datatype_ground_conflict(
        &terms,
        &[not_cycle],
        datatype_decls,
        constructor_selectors,
    ));

    let var_to_term = HashMap::from_iter([(0, cycle)]);
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::negative(Variable::new(0))], true);

    let without_registry = SatProofManager::new(&var_to_term, &mut terms)
        .build_exact_original_proof_fragment(&trace, &[])
        .expect_err("a datatype clause without its registry must remain unauthenticated");
    assert!(matches!(
        without_registry,
        ExactOriginalProofError::UnauthenticatedOriginalClause { clause_id: 1, .. }
    ));

    let mut manager = SatProofManager::new(&var_to_term, &mut terms);
    manager.set_dt_registry_data(Some(&registries));
    let fragment = manager
        .build_exact_original_proof_fragment(&trace, &[])
        .expect("the registered structural cycle has intrinsic datatype authority");
    let proof_id = fragment.bindings[&1].proof_id;
    assert!(matches!(
        fragment.proof.get_step(proof_id),
        Some(ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::DatatypeAcyclicDirect,
            clause,
            ..
        }) if clause == &vec![not_cycle]
    ));

    let mut proof = fragment.proof;
    let assume_cycle = proof.add_assume(cycle, None);
    proof.add_resolution(Vec::new(), cycle, proof_id, assume_cycle);
    let signatures = [
        ay_proof::DatatypeMemberSignature {
            identity: "stack".to_owned(),
            argument_sorts: vec![Sort::Int, tower.clone()],
            result_sort: tower.clone(),
            nullary_term: None,
        },
        ay_proof::DatatypeMemberSignature {
            identity: "is-stack".to_owned(),
            argument_sorts: vec![tower.clone()],
            result_sort: Sort::Bool,
            nullary_term: None,
        },
        ay_proof::DatatypeMemberSignature {
            identity: "top".to_owned(),
            argument_sorts: vec![tower.clone()],
            result_sort: Sort::Int,
            nullary_term: None,
        },
        ay_proof::DatatypeMemberSignature {
            identity: "rest".to_owned(),
            argument_sorts: vec![tower.clone()],
            result_sort: tower.clone(),
            nullary_term: None,
        },
        ay_proof::DatatypeMemberSignature {
            identity: "empty".to_owned(),
            argument_sorts: Vec::new(),
            result_sort: tower.clone(),
            nullary_term: Some(empty),
        },
        ay_proof::DatatypeMemberSignature {
            identity: "is-empty".to_owned(),
            argument_sorts: vec![tower],
            result_sort: Sort::Bool,
            nullary_term: None,
        },
    ];
    let assertions = [cycle];
    let quality = ay_proof::check_proof_strict_with_typed_context(
        &proof,
        &terms,
        Some(datatype_decls),
        Some(constructor_selectors),
        &signatures,
        Some(&assertions),
    )
    .expect("the registered datatype lemma must pass strict checking");
    assert_eq!(quality.trust_count, 0);
}
