// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use ay_core::AletheRule;

fn append_contradiction(terms: &mut TermStore, proof: &mut Proof, duplicate: bool) -> Vec<TermId> {
    let positive = terms.mk_var("cancel-contradiction", Sort::Bool);
    let negative = terms.mk_not(positive);
    let first = proof.add_assume(positive, None);
    if duplicate {
        proof.add_assume(positive, None);
    }
    let second = proof.add_assume(negative, None);
    if duplicate {
        proof.add_assume(positive, None);
    }
    proof.add_resolution(vec![], positive, first, second);
    vec![positive, negative]
}

pub(super) fn contradiction(duplicate: bool) -> SerializableProofBundle {
    let mut terms = TermStore::new();
    let mut proof = Proof::new();
    let assumptions = append_contradiction(&mut terms, &mut proof, duplicate);
    SerializableProofBundle::from_proof(&proof, &terms, assumptions)
}

pub(super) fn skolem() -> SerializableProofBundle {
    let mut terms = TermStore::new();
    let bound = terms.mk_var("cancel-bound", Sort::Int);
    let witness = terms.mk_var("cancel-witness", Sort::Int);
    terms.mark_skolem_symbol("cancel-witness");
    let body = terms.mk_app(Symbol::named("cancel-predicate"), [bound], Sort::Bool);
    let source = terms.mk_forall(vec![("cancel-bound".to_owned(), Sort::Int)], body);
    let instance = terms.mk_app(Symbol::named("cancel-predicate"), [witness], Sort::Bool);
    let choice = terms.mk_app(Symbol::named("="), [source, instance], Sort::Bool);
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Skolem, vec![choice], vec![], vec![witness]);
    let assumptions = append_contradiction(&mut terms, &mut proof, false);
    SerializableProofBundle::from_proof(&proof, &terms, assumptions)
}

pub(super) fn datatype() -> SerializableProofBundle {
    let mut terms = TermStore::new();
    let carrier = Sort::Uninterpreted("CancelColor".to_owned());
    let red = terms.mk_fresh_named_var("cancel-red", carrier.clone());
    let green = terms.mk_fresh_named_var("cancel-green", carrier.clone());
    let equality = terms.mk_app(Symbol::named("="), [red, green], Sort::Bool);
    let disequality = terms.mk_not_raw(equality);
    let mut proof = Proof::new();
    let distinct = proof.add_theory_lemma_with_kind(
        "DT",
        vec![disequality],
        TheoryLemmaKind::DatatypeDistinct,
    );
    let assumption = proof.add_assume(equality, None);
    proof.add_resolution(vec![], equality, distinct, assumption);
    let mut signatures = Vec::new();
    for (name, term) in [("cancel-red", red), ("cancel-green", green)] {
        signatures.push(DatatypeMemberSignature {
            identity: name.to_owned(),
            argument_sorts: vec![],
            result_sort: carrier.clone(),
            nullary_term: Some(term),
        });
        signatures.push(DatatypeMemberSignature {
            identity: format!("is-{name}"),
            argument_sorts: vec![carrier.clone()],
            result_sort: Sort::Bool,
            nullary_term: None,
        });
    }
    SerializableProofBundle::from_proof_with_typed_context(
        &proof,
        &terms,
        vec![equality],
        vec![(
            "CancelColor".to_owned(),
            vec!["cancel-red".to_owned(), "cancel-green".to_owned()],
        )],
        vec![
            ("cancel-red".to_owned(), vec![]),
            ("cancel-green".to_owned(), vec![]),
        ],
        signatures,
    )
}
