// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Public fragment/context controls; fragment authority is not an UNSAT verdict.

use ay_core::{AletheRule, ProofId, Symbol};
use ay_proof::{
    authenticate_premise_clauses_strict_with_typed_context_and_progress,
    check_proof_strict_with_typed_context_and_progress, DatatypeMemberSignature,
};

use super::*;

fn quantified_fragment(rule: AletheRule) -> (TermStore, Proof, TermId) {
    let mut terms = TermStore::new();
    let bound = terms.mk_var("consumer_bound", Sort::Int);
    let witness = terms.mk_var("consumer_witness", Sort::Int);
    terms.mark_skolem_symbol("consumer_witness");
    let body = terms.mk_app(Symbol::named("consumer_p"), [bound], Sort::Bool);
    let quantified = terms.mk_forall(vec![("consumer_bound".into(), Sort::Int)], body);
    let instance = terms.mk_app(Symbol::named("consumer_p"), [witness], Sort::Bool);
    let literal = if rule == AletheRule::Skolem {
        terms.mk_app(Symbol::named("="), [quantified, instance], Sort::Bool)
    } else {
        let negative = terms.mk_not_raw(quantified);
        terms.mk_app(Symbol::named("or"), [negative, instance], Sort::Bool)
    };
    let mut proof = Proof::new();
    proof.add_rule_step(rule, vec![literal], vec![], vec![witness]);
    (terms, proof, literal)
}

#[test]
fn public_quantifier_fragments_authenticate_exact_clauses_and_obey_cancellation() {
    for rule in [AletheRule::ForallInst, AletheRule::Skolem] {
        let (terms, proof, literal) = quantified_fragment(rule);
        let mut calls = 0;
        let authenticated = authenticate_premise_clauses_strict_with_typed_context_and_progress(
            &proof,
            &terms,
            None,
            None,
            &[],
            &[],
            &mut |_, _| {
                calls += 1;
                true
            },
        )
        .unwrap();
        assert_eq!(authenticated.step_count(), 1);
        assert_eq!(authenticated.clause(ProofId(0)), Some([literal].as_slice()));
        for stop in [1, calls / 2, calls] {
            let mut seen = 0;
            let result = authenticate_premise_clauses_strict_with_typed_context_and_progress(
                &proof,
                &terms,
                None,
                None,
                &[],
                &[],
                &mut |_, _| {
                    seen += 1;
                    seen != stop
                },
            );
            assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
            assert_eq!(seen, stop);
        }
    }
}

#[test]
fn public_live_skolem_fragment_cannot_borrow_a_missing_producer_registry() {
    let (terms, proof, _) = quantified_fragment(AletheRule::Skolem);
    let ids = terms.boolean_constant_ids();
    let raw = TermStore::from_entries(terms.entries_snapshot(), ids.0, ids.1, terms.var_counter());
    assert!(matches!(
        authenticate_premise_clauses_strict_with_typed_context_and_progress(
            &proof,
            &raw,
            None,
            None,
            &[],
            &[],
            &mut |_, _| true,
        ),
        Err(ProofCheckError::InvalidBooleanRule { .. })
    ));
}

#[test]
fn public_typed_context_authenticates_unused_members_and_rejects_wrong_signatures() {
    let mut terms = TermStore::new();
    let carrier = Sort::Uninterpreted("ConsumerUnit".into());
    let constructor = terms.mk_var("consumer_unit", carrier.clone());
    let declarations = vec![("ConsumerUnit".into(), vec!["consumer_unit".into()])];
    let selectors = vec![("consumer_unit".into(), vec![])];
    let signatures = vec![
        DatatypeMemberSignature {
            identity: "consumer_unit".into(),
            argument_sorts: vec![],
            result_sort: carrier.clone(),
            nullary_term: Some(constructor),
        },
        DatatypeMemberSignature {
            identity: "is-consumer_unit".into(),
            argument_sorts: vec![carrier.clone()],
            result_sort: Sort::Bool,
            nullary_term: None,
        },
    ];
    let positive = terms.mk_var("consumer_bool", Sort::Bool);
    let negative = terms.mk_not(positive);
    let mut proof = Proof::new();
    let first = proof.add_assume(positive, None);
    let second = proof.add_assume(negative, None);
    proof.add_resolution(vec![], positive, first, second);
    let assertions = [positive, negative];
    let check = |store: &TermStore| {
        check_proof_strict_with_typed_context_and_progress(
            &proof,
            store,
            Some(&declarations),
            Some(&selectors),
            &signatures,
            Some(&assertions),
            &mut |_, _| true,
        )
    };
    assert_eq!(check(&terms).unwrap().resolution_count, 1);
    terms.mk_app(Symbol::named("consumer_unit"), [positive], carrier);
    assert!(matches!(
        check(&terms),
        Err(ProofCheckError::InvalidDatatypeSignatureContext { .. })
    ));
}
