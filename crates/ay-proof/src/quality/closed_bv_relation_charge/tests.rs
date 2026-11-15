// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::*;

fn literal(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
    let eq = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    terms.mk_not_raw(eq)
}

fn step(literal: TermId) -> ProofStep {
    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("bool", vec![literal], TheoryLemmaKind::BoolTautology);
    proof.steps.pop().unwrap()
}

fn constants() -> (TermStore, TermId, TermId) {
    let mut terms = TermStore::new();
    let one = terms.mk_bitvec(1.into(), 64);
    let two = terms.mk_bitvec(2.into(), 64);
    (terms, one, two)
}

#[test]
fn closed_relation_price_retains_work_and_does_not_decide_truth() {
    let (mut terms, one, two) = constants();
    let different = step(literal(&mut terms, one, two));
    let equal = step(literal(&mut terms, one, one));
    for candidate in [&different, &equal] {
        assert!(super::matches(candidate, &terms));
        assert!(matches!(
            select_semantic_charge_class(candidate, &terms),
            SemanticChargeClass::ClosedBvConstantRelation
        ));
        let payload = PayloadStats {
            work: 61,
            bytes: 1313,
            unfolded_work: 4,
            ..PayloadStats::default()
        };
        let previous = semantic_validator_charge(
            candidate,
            payload,
            SemanticChargeClass::BoundedAssignmentEval,
        )
        .unwrap();
        let current = semantic_validator_charge(
            candidate,
            payload,
            SemanticChargeClass::ClosedBvConstantRelation,
        )
        .unwrap();
        assert_eq!(current.0, previous.0);
        assert!(current.1 < previous.1);
    }
}

#[test]
fn near_misses_keep_the_previous_price() {
    let (mut terms, one, two) = constants();
    let relation = literal(&mut terms, one, two);
    let TermData::Not(eq) = terms.get(relation) else {
        unreachable!()
    };
    let positive = *eq;
    let nested = terms.mk_not_raw(relation);
    let variable = terms.mk_var("x", Sort::bitvec(64));
    let symbolic = literal(&mut terms, variable, two);
    let narrow = terms.mk_bitvec(2.into(), 32);
    let mismatch = literal(&mut terms, one, narrow);
    let wide1 = terms.mk_bitvec(1.into(), 65);
    let wide2 = terms.mk_bitvec(2.into(), 65);
    let wide = literal(&mut terms, wide1, wide2);
    for value in [positive, nested, symbolic, mismatch, wide] {
        assert!(!super::matches(&step(value), &terms));
    }
    let mut wrong_kind = step(relation);
    let ProofStep::TheoryLemma { kind, .. } = &mut wrong_kind else {
        unreachable!()
    };
    *kind = TheoryLemmaKind::Generic;
    assert!(!super::matches(&wrong_kind, &terms));
    for (value, width, sort) in [
        ((-1).into(), 64, Sort::bitvec(64)),
        (256.into(), 8, Sort::bitvec(8)),
        (0.into(), 0, Sort::bitvec(0)),
        (1.into(), 65, Sort::bitvec(65)),
        (1.into(), 64, Sort::Bool),
    ] {
        assert!(!super::canonical(&value, width, &sort));
    }
}

fn many_ground_relations() -> (TermStore, Proof, TermId) {
    let mut terms = TermStore::new();
    let values: Vec<_> = (0..80).map(|i| terms.mk_bitvec(i.into(), 64)).collect();
    let false_term = terms.mk_bool(false);
    let mut proof = Proof::new();
    let assumed = proof.add_assume(false_term, None);
    for i in 0..values.len() {
        for j in i + 1..values.len() {
            let relation = literal(&mut terms, values[i], values[j]);
            proof.add_theory_lemma_with_kind(
                "bool",
                vec![relation],
                TheoryLemmaKind::BoolTautology,
            );
        }
    }
    let not_false = terms.mk_not_raw(false_term);
    let axiom = proof.add_rule_step(AletheRule::False, vec![not_false], vec![], vec![]);
    proof.add_resolution(vec![], false_term, assumed, axiom);
    (terms, proof, false_term)
}

#[test]
fn all_3160_closed_relations_are_checked_inside_the_unchanged_general_bytes() {
    let (terms, proof, false_term) = many_ground_relations();
    let (mut work, mut bytes) = (0usize, 0usize);
    let quality = check_proof_strict_with_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        Some(&[false_term]),
        &mut |w, b| {
            work = work.checked_add(w).unwrap();
            bytes = bytes.checked_add(b).unwrap();
            work <= 250_000_000 && bytes <= 512 * 1024 * 1024
        },
    )
    .unwrap();
    println!(
        "CLOSED_RELATION_NATIVE steps={} work={work} bytes={bytes}",
        proof.steps.len()
    );
    assert!(quality.is_complete());
}

#[test]
fn a_false_closed_relation_remains_a_strict_semantic_rejection() {
    let (mut terms, mut proof, false_term) = many_ground_relations();
    let value = terms.mk_bitvec(17.into(), 64);
    proof.steps[1] = step(literal(&mut terms, value, value));
    assert!(super::matches(&proof.steps[1], &terms));
    let error = check_proof_strict_with_context(&proof, &terms, None, None, Some(&[false_term]))
        .unwrap_err();
    assert!(matches!(
        error,
        ProofCheckError::InvalidTheoryLemma {
            step: ProofId(1),
            ..
        }
    ));
}
