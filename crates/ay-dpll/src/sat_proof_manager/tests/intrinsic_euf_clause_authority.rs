// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::TheoryLemmaKind;

fn build_fragment_for_clause(
    terms: &mut TermStore,
    atoms: &[TermId],
    clause: Vec<Literal>,
) -> Result<ExactOriginalProofFragment, ExactOriginalProofError> {
    let var_to_term: HashMap<_, _> = atoms
        .iter()
        .copied()
        .enumerate()
        .map(|(index, term)| {
            (
                u32::try_from(index).expect("small test variable index"),
                term,
            )
        })
        .collect();
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, clause, true);
    SatProofManager::new(&var_to_term, terms).build_exact_original_proof_fragment(&trace, &[])
}

fn positive(variable: u32) -> Literal {
    Literal::positive(Variable::new(variable))
}

fn negative(variable: u32) -> Literal {
    Literal::negative(Variable::new(variable))
}

#[test]
fn exact_fragment_reorders_and_checks_direct_euf_transitivity() {
    let mut terms = TermStore::new();
    let sort = Sort::Uninterpreted("direct_euf_transitivity".to_owned());
    let a = terms.mk_var("direct_euf_a", sort.clone());
    let b = terms.mk_var("direct_euf_b", sort.clone());
    let c = terms.mk_var("direct_euf_c", sort);
    let eq_ac = terms.mk_eq(a, c);
    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);

    // Match the SAT trace regression: positive conclusion first, followed by
    // the negated premises. The strict EUF validator requires conclusion-last.
    let fragment = build_fragment_for_clause(
        &mut terms,
        &[eq_ac, eq_ab, eq_bc],
        vec![positive(0), negative(1), negative(2)],
    )
    .expect("a permuted direct transitivity clause has intrinsic authority");
    let binding = fragment
        .bindings
        .get(&1)
        .expect("binding for original ID 1");
    let proof_id = binding.proof_id;
    let not_ab = terms.mk_not_raw(eq_ab);
    let not_bc = terms.mk_not_raw(eq_bc);
    assert!(matches!(
        fragment.proof.get_step(proof_id),
        Some(ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::EufTransitive,
            clause,
            ..
        }) if clause == &vec![not_ab, not_bc, eq_ac]
    ));

    let mut proof = fragment.proof;
    let assume_ab = proof.add_assume(eq_ab, None);
    let after_ab = proof.add_resolution(vec![not_bc, eq_ac], eq_ab, proof_id, assume_ab);
    let assume_bc = proof.add_assume(eq_bc, None);
    let after_bc = proof.add_resolution(vec![eq_ac], eq_bc, after_ab, assume_bc);
    let not_ac = terms.mk_not_raw(eq_ac);
    let assume_not_ac = proof.add_assume(not_ac, None);
    proof.add_resolution(Vec::new(), eq_ac, after_bc, assume_not_ac);
    let quality = ay_proof::check_proof_strict(&proof, &terms)
        .expect("the reordered direct transitivity lemma must pass strict checking");
    assert_eq!(quality.trust_count, 0);
}

#[test]
fn exact_fragment_reorders_and_checks_direct_euf_congruence() {
    let mut terms = TermStore::new();
    let sort = Sort::Uninterpreted("direct_euf_congruence".to_owned());
    let a = terms.mk_var("direct_cong_a", sort.clone());
    let b = terms.mk_var("direct_cong_b", sort.clone());
    let f_a = terms.mk_app(Symbol::named("direct_cong_f"), [a], sort.clone());
    let f_b = terms.mk_app(Symbol::named("direct_cong_f"), [b], sort);
    let eq_f = terms.mk_eq(f_a, f_b);
    let eq_ab = terms.mk_eq(a, b);

    let fragment =
        build_fragment_for_clause(&mut terms, &[eq_f, eq_ab], vec![positive(0), negative(1)])
            .expect("a permuted direct congruence clause has intrinsic authority");
    let binding = fragment
        .bindings
        .get(&1)
        .expect("binding for original ID 1");
    let proof_id = binding.proof_id;
    let not_ab = terms.mk_not_raw(eq_ab);
    assert!(matches!(
        fragment.proof.get_step(proof_id),
        Some(ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::EufCongruent,
            clause,
            ..
        }) if clause == &vec![not_ab, eq_f]
    ));

    let mut proof = fragment.proof;
    let assume_ab = proof.add_assume(eq_ab, None);
    let positive_f = proof.add_resolution(vec![eq_f], eq_ab, proof_id, assume_ab);
    let not_f = terms.mk_not_raw(eq_f);
    let assume_not_f = proof.add_assume(not_f, None);
    proof.add_resolution(Vec::new(), eq_f, positive_f, assume_not_f);
    let quality = ay_proof::check_proof_strict(&proof, &terms)
        .expect("the reordered direct congruence lemma must pass strict checking");
    assert_eq!(quality.trust_count, 0);
}

#[test]
fn exact_fragment_rejects_disconnected_direct_euf_chain() {
    let mut terms = TermStore::new();
    let sort = Sort::Uninterpreted("direct_euf_disconnected".to_owned());
    let a = terms.mk_var("direct_bad_a", sort.clone());
    let b = terms.mk_var("direct_bad_b", sort.clone());
    let c = terms.mk_var("direct_bad_c", sort.clone());
    let d = terms.mk_var("direct_bad_d", sort);
    let eq_ac = terms.mk_eq(a, c);
    let eq_ab = terms.mk_eq(a, b);
    let eq_cd = terms.mk_eq(c, d);
    let not_ab = terms.mk_not_raw(eq_ab);
    let not_cd = terms.mk_not_raw(eq_cd);

    assert!(!ay_proof::recognize_euf_transitive(
        &terms,
        &[not_ab, not_cd, eq_ac]
    ));
    assert_eq!(
        build_fragment_for_clause(
            &mut terms,
            &[eq_ac, eq_ab, eq_cd],
            vec![positive(0), negative(1), negative(2)],
        )
        .expect_err("a disconnected equality graph must remain unauthenticated"),
        ExactOriginalProofError::UnauthenticatedOriginalClause {
            clause_id: 1,
            clause: vec![eq_ac, not_ab, not_cd],
        }
    );
}
