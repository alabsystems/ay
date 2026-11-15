// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;

/// `x + x`, `levels` times over: one new DAG node per level, while the tree
/// expansion doubles.
fn doubling_chain(terms: &mut TermStore, x: TermId, levels: usize) -> Vec<TermId> {
    let mut chain = vec![x];
    for _ in 0..levels {
        let last = chain[chain.len() - 1];
        chain.push(terms.mk_app(Symbol::named("bvadd"), [last, last], Sort::bitvec(9)));
    }
    chain
}

/// Only a term the lowering would copy is named: `x + x` is read twice, so
/// it becomes `proof_def_<t1>`; its one parent and the literal stay inline.
#[test]
fn a_shared_term_becomes_one_leaf_and_one_definition() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("definitional-shape", Sort::bitvec(9));
    let chain = doubling_chain(&mut terms, x, 2);
    let zero = terms.mk_bitvec(0.into(), 9);
    let identity = terms.mk_app(Symbol::named("="), [chain[2], zero], Sort::Bool);
    let shared = BvExpr::leaf(&format!("proof_def_{}", chain[1].index()), 9);
    let x_leaf = BvExpr::leaf(&format!("proof_bv_{}", x.index()), 9);

    let mut lowerer = ProofProducingLowerer::new_for_lemma_validation(&terms, deadline());
    lowerer.record_definitions(&[identity]);
    let literal = lowerer.lower_bool(identity).unwrap();
    assert_eq!(
        literal,
        BvExpr::eq(
            BvExpr::add(shared.clone(), shared.clone()),
            BvExpr::const_val(0, 9)
        )
    );
    assert_eq!(
        lowerer.take_negated_definitions(&[literal]),
        vec![BvExpr::not(BvExpr::eq(
            shared,
            BvExpr::add(x_leaf.clone(), x_leaf)
        ))]
    );
}

/// The tree lowering runs out of its construction budget on a 20-level chain
/// (2^20 leaves); its DAG is 22 terms. The definitional retry proves the true
/// identity `2^20 * x = 0` (mod 2^9) and still refuses the false one
/// `2^20 * x = x`.
#[test]
fn a_shared_dag_past_the_tree_cap_is_proved_through_definitions() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("definitional-wide", Sort::bitvec(9));
    let chain = doubling_chain(&mut terms, x, 20);
    let top = chain[20];
    let zero = terms.mk_bitvec(0.into(), 9);
    let identity = terms.mk_app(Symbol::named("="), [top, zero], Sort::Bool);
    let mut ordinary = ProofProducingLowerer::new_for_lemma_validation(&terms, deadline());
    assert!(ordinary.lower_bool(identity).is_err() && ordinary.resource_exhausted);
    assert!(bv_bitblast_requires_proof_producer(&terms, &[identity]));
    validate_bv_bitblast_with_progress(&terms, ProofId(0), &[identity], None, &mut |_, _| true)
        .unwrap();
    assert!(terms.strict_bv_semantics_validated(&[identity]));

    let false_claim = terms.mk_app(Symbol::named("="), [top, x], Sort::Bool);
    assert!(matches!(
        validate_bv_bitblast_with_progress(
            &terms,
            ProofId(1),
            &[false_claim],
            None,
            &mut |_, _| true
        ),
        Err(ProofCheckError::InvalidTheoryLemma { .. })
    ));
    assert!(!terms.strict_bv_semantics_validated(&[false_claim]));
}

/// A concat two extracts read is named, and each extract reads its bits off
/// the name: a named concat has no operands to slice.
#[test]
fn an_extract_of_a_named_concat_reads_the_name() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("definitional-high", Sort::bitvec(8));
    let y = terms.mk_var("definitional-low", Sort::bitvec(8));
    let joined = terms.mk_app(Symbol::named("concat"), [x, y], Sort::bitvec(16));
    let slice = |terms: &mut TermStore, high: u32, low: u32| {
        let sort = Sort::bitvec(high - low + 1);
        terms.mk_app(Symbol::indexed("extract", vec![high, low]), [joined], sort)
    };
    let (first, second) = (slice(&mut terms, 11, 4), slice(&mut terms, 12, 5));
    let equal = terms.mk_app(Symbol::named("="), [first, second], Sort::Bool);
    let named = BvExpr::leaf(&format!("proof_def_{}", joined.index()), 16);

    let mut lowerer = ProofProducingLowerer::new_for_lemma_validation(&terms, deadline());
    lowerer.record_definitions(&[equal]);
    assert_eq!(
        lowerer.lower_bool(equal).unwrap(),
        BvExpr::eq(
            BvExpr::extract(named.clone(), 11, 4),
            BvExpr::extract(named, 12, 5)
        )
    );
}
