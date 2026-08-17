// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn exact_original_fragment_rejects_unannotated_generated_clause() {
    use ay_core::{TheoryLemmaKind, TheoryLemmaProof};

    let (mut terms, var_to_term, _negations) = setup_test_terms();
    let p = var_to_term[&0];
    let q = var_to_term[&1];
    let mut content_annotations = HashMap::default();
    content_annotations.insert(
        vec![q],
        TheoryLemmaProof {
            clause: vec![q],
            kind: TheoryLemmaKind::Generic,
            farkas: None,
            lia: None,
        },
    );
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(1))], true);

    let error = {
        let mut manager = SatProofManager::new(&var_to_term, &mut terms);
        manager.set_theory_lemma_proofs(&content_annotations);
        manager
            .build_exact_original_proof_fragment(&trace, &[p])
            .expect_err("content-keyed fallback is not exact identity authority")
    };

    assert_eq!(
        error,
        ExactOriginalProofError::UnauthenticatedOriginalClause {
            clause_id: 1,
            clause: vec![q],
        }
    );
}

/// (P3b, c6) Authored `(or S false false)` fold root with survivor
/// `S = (and p q)`: the conjunct unit `[q]` is admitted through the
/// Assume + or + false-resolution + and_pos chain, and the emitted chain
/// terminates in exactly the unit clause.
#[test]
fn exact_original_fragment_admits_or_fold_survivor_conjunct() {
    let (mut terms, var_to_term, _negations) = setup_test_terms();
    let p = var_to_term[&0];
    let q = var_to_term[&1];
    let survivor = terms.mk_app(Symbol::named("and"), [p, q], Sort::Bool);
    let false_term = terms.false_term();
    let root = terms.mk_app(
        Symbol::named("or"),
        [survivor, false_term, false_term],
        Sort::Bool,
    );
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(1))], true);

    let fragment = SatProofManager::new(&var_to_term, &mut terms)
        .build_exact_original_proof_fragment(&trace, &[root])
        .expect("a fold-survivor conjunct unit has chain authority");
    let binding = fragment.bindings.get(&1).expect("binding for ID 1");
    let Some(ProofStep::Resolution { clause, .. }) = fragment.proof.get_step(binding.proof_id)
    else {
        panic!("expected the chain to terminate in a resolution step");
    };
    assert_eq!(clause, &vec![q]);
    // The chain must Assume exactly the authored or-root, nothing else.
    let assumed: Vec<TermId> = fragment
        .proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Assume(term) => Some(*term),
            _ => None,
        })
        .collect();
    assert_eq!(assumed, vec![root]);
}

/// (P3b, c6 negative) An `or` root with TWO distinct non-false disjuncts is
/// not a fold: NO disjunct — not even the first — may be admitted as a
/// survivor unit (a false sibling does not make the other disjuncts true).
/// The traced unit here is the disjunct a first-non-false shortcut would
/// wrongly elect, so relaxing the single-survivor screen makes this build
/// succeed and the test fail.
#[test]
fn exact_original_fragment_rejects_two_survivor_or_root() {
    let (mut terms, var_to_term, _negations) = setup_test_terms();
    let p = var_to_term[&0];
    let q = var_to_term[&1];
    let false_term = terms.false_term();
    let root = terms.mk_app(Symbol::named("or"), [p, q, false_term], Sort::Bool);
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(0))], true);

    let error = SatProofManager::new(&var_to_term, &mut terms)
        .build_exact_original_proof_fragment(&trace, &[root])
        .expect_err("two non-false disjuncts are not a fold");
    assert_eq!(
        error,
        ExactOriginalProofError::UnauthenticatedOriginalClause {
            clause_id: 1,
            clause: vec![p],
        }
    );
}

/// (P3b, c6 negative) An `or` root whose non-survivor disjunct is merely
/// FALSIFIABLE (not the literal `false` term) is not a fold candidate: the
/// unit must stay unauthenticated even though it is the other disjunct's
/// conjunct.
#[test]
fn exact_original_fragment_rejects_or_root_without_literal_false() {
    let (mut terms, var_to_term, _negations) = setup_test_terms();
    let p = var_to_term[&0];
    let q = var_to_term[&1];
    let not_p = terms.mk_not(p);
    let conjunction = terms.mk_app(Symbol::named("and"), [p, q], Sort::Bool);
    let root = terms.mk_app(Symbol::named("or"), [conjunction, not_p], Sort::Bool);
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(1))], true);

    let error = SatProofManager::new(&var_to_term, &mut terms)
        .build_exact_original_proof_fragment(&trace, &[root])
        .expect_err("a falsifiable disjunct is not the literal false term");
    assert_eq!(
        error,
        ExactOriginalProofError::UnauthenticatedOriginalClause {
            clause_id: 1,
            clause: vec![q],
        }
    );
}

/// (P3b, c6 negative) A unit that is NOT a conjunct of the survivor gains
/// nothing from the fold root.
#[test]
fn exact_original_fragment_rejects_non_conjunct_of_fold_survivor() {
    let (mut terms, var_to_term, _negations) = setup_test_terms();
    let p = var_to_term[&0];
    let q = var_to_term[&1];
    let false_term = terms.false_term();
    let root = terms.mk_app(Symbol::named("or"), [p, false_term], Sort::Bool);
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(1))], true);

    let error = SatProofManager::new(&var_to_term, &mut terms)
        .build_exact_original_proof_fragment(&trace, &[root])
        .expect_err("q is not the survivor or one of its conjuncts");
    assert_eq!(
        error,
        ExactOriginalProofError::UnauthenticatedOriginalClause {
            clause_id: 1,
            clause: vec![q],
        }
    );
}

/// (P3b, c4 fold bridge) A sealed eval-folded-`false` derivation admits the
/// `[false]` unit through the forall_inst chain plus the strict
/// `BvLiaTautology`/`BoolTautology` bridge, and duplicate `[false]` originals
/// share ONE emitted chain (the bridge precharge is per emitted lemma).
#[test]
fn exact_original_fragment_bridges_folded_false_instance_and_memoizes() {
    use num_bigint::BigInt;

    let mut terms = TermStore::new();
    let mut var_to_term: HashMap<u32, TermId> = HashMap::default();
    let width = 8u32;
    let bv_sort = Sort::BitVec(ay_core::BitVecSort::new(width));
    let x = terms.mk_var("ofb_x", bv_sort.clone());
    let square = terms.mk_app(Symbol::named("bvmul"), [x, x], bv_sort.clone());
    let zero = terms.mk_bitvec(BigInt::ZERO, width);
    let body = terms.mk_app(Symbol::named("bvslt"), [square, zero], Sort::Bool);
    let quantifier = terms.mk_forall(vec![("ofb_x".to_string(), bv_sort)], body);
    let mut substitution: HashMap<String, TermId> = HashMap::default();
    substitution.insert("ofb_x".to_string(), zero);
    let instance = crate::ematching::subst_vars_exact_qf(&mut terms, body, &substitution)
        .expect("closed substitution succeeds");
    let false_term = terms.false_term();
    var_to_term.insert(0, quantifier);
    var_to_term.insert(1, false_term);

    let mut derivations: HashMap<TermId, FragmentInstanceDerivation> = HashMap::default();
    derivations.insert(
        false_term,
        FragmentInstanceDerivation {
            quantifier,
            values: vec![zero],
            instance,
        },
    );

    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(0))], true);
    trace.add_clause(2, vec![Literal::positive(Variable::new(1))], true);
    trace.add_clause(3, vec![Literal::positive(Variable::new(1))], true);

    let fragment = {
        let mut manager = SatProofManager::new(&var_to_term, &mut terms);
        manager.set_instance_derivations(&derivations);
        manager
            .build_exact_original_proof_fragment(&trace, &[quantifier])
            .expect("the folded false unit has bridged chain authority")
    };
    let second = fragment.bindings.get(&2).expect("binding for ID 2");
    let third = fragment.bindings.get(&3).expect("binding for ID 3");
    assert_eq!(
        second.proof_id, third.proof_id,
        "duplicate folded-false originals must share one emitted chain"
    );
    let Some(ProofStep::Resolution { clause, .. }) = fragment.proof.get_step(second.proof_id)
    else {
        panic!("expected the bridge to terminate in a resolution step");
    };
    assert_eq!(clause, &vec![false_term]);
    let bv_lemmas = fragment
        .proof
        .steps
        .iter()
        .filter(|step| {
            matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: ay_core::TheoryLemmaKind::BvLiaTautology,
                    ..
                }
            )
        })
        .count();
    assert_eq!(bv_lemmas, 1, "one shared bridge lemma for both originals");
}

/// (P3b, c4 fold bridge negative) A fold-bridged derivation keyed by anything
/// OTHER than the literal `false` term is refused: no strict rule can bridge a
/// closed BV instance to an arbitrary folded unit, so the builder must fail
/// closed rather than emit an unauthenticatable chain. The key here is an
/// ordinary Boolean variable — a forged claim that the false instance folded
/// to a satisfied solver atom.
#[test]
fn exact_original_fragment_rejects_fold_bridge_to_non_false_unit() {
    use num_bigint::BigInt;

    let mut terms = TermStore::new();
    let mut var_to_term: HashMap<u32, TermId> = HashMap::default();
    let width = 8u32;
    let bv_sort = Sort::BitVec(ay_core::BitVecSort::new(width));
    let x = terms.mk_var("ofn_x", bv_sort.clone());
    let square = terms.mk_app(Symbol::named("bvmul"), [x, x], bv_sort.clone());
    let zero = terms.mk_bitvec(BigInt::ZERO, width);
    let body = terms.mk_app(Symbol::named("bvslt"), [square, zero], Sort::Bool);
    let quantifier = terms.mk_forall(vec![("ofn_x".to_string(), bv_sort)], body);
    let mut substitution: HashMap<String, TermId> = HashMap::default();
    substitution.insert("ofn_x".to_string(), zero);
    let instance = crate::ematching::subst_vars_exact_qf(&mut terms, body, &substitution)
        .expect("closed substitution succeeds");
    let forged_unit = terms.mk_var("ofn_forged", Sort::Bool);
    var_to_term.insert(0, quantifier);
    var_to_term.insert(1, forged_unit);

    let mut derivations: HashMap<TermId, FragmentInstanceDerivation> = HashMap::default();
    derivations.insert(
        forged_unit,
        FragmentInstanceDerivation {
            quantifier,
            values: vec![zero],
            instance,
        },
    );

    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(1))], true);

    let error = {
        let mut manager = SatProofManager::new(&var_to_term, &mut terms);
        manager.set_instance_derivations(&derivations);
        manager
            .build_exact_original_proof_fragment(&trace, &[quantifier])
            .expect_err("a fold bridge may only target the literal false unit")
    };
    assert_eq!(
        error,
        ExactOriginalProofError::UnauthenticatedOriginalClause {
            clause_id: 1,
            clause: vec![forged_unit],
        }
    );
}
