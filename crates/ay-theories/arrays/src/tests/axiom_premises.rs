// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array axiom instances keep the literals that justify their equality
//! substitutions and skipped store writes (2026-09-23 hunt D4-a and D4-d).

use super::*;
use ay_core::TheoryLemma;
use num_bigint::BigInt;

/// Every lemma concluding `conclusion` must carry the negation of each
/// antecedent.
fn assert_instances_carry(lemmas: &[TheoryLemma], conclusion: TermId, antecedents: &[TermId]) {
    let instances: Vec<&TheoryLemma> = lemmas
        .iter()
        .filter(|lemma| lemma.clause.contains(&TheoryLit::new(conclusion, true)))
        .collect();
    assert!(
        !instances.is_empty(),
        "no instance concluding {conclusion:?}: {lemmas:?}"
    );
    for lemma in instances {
        for &antecedent in antecedents {
            assert!(
                lemma.clause.contains(&TheoryLit::new(antecedent, false)),
                "instance {:?} omits the antecedent {antecedent:?}",
                lemma.clause
            );
        }
    }
}

/// D4-d: `a = b` and `b = K1` put `a` in the class of `K1` with no direct
/// `(= a K1)` atom. The instance `default(a) = 1` holds only under that path;
/// emitted without it, it was the unit that refuted const_11_0110.
#[test]
fn default_const_instance_through_a_path_is_not_a_unit() {
    let mut store = TermStore::new();
    let a = store.mk_var("a", make_array_sort());
    let b = store.mk_var("b", make_array_sort());
    let one = store.mk_int(BigInt::from(1));
    let k1 = store.mk_const_array(Sort::Int, one);
    let default_a = store.mk_array_default(a);
    let conclusion = store.mk_eq(default_a, one);
    let eq_a_b = store.mk_eq(a, b);
    let eq_b_k1 = store.mk_eq(b, k1);
    assert!(store.find_eq(a, k1).is_none());

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_a_b, true);
    solver.assert_literal(eq_b_k1, true);
    solver.populate_caches();
    solver.pending_default_const.push((default_a, k1));

    let Some(TheoryResult::NeedLemmas(lemmas)) = solver.check_default_const() else {
        panic!("expected the default-const instance as a lemma");
    };
    assert_instances_carry(&lemmas, conclusion, &[eq_a_b, eq_b_k1]);
}

/// D4-a: a read that skips a write at a provably distinct index holds only
/// while that index stays distinct, whether it lands on a deeper write or on
/// the const-array base.
#[test]
fn effective_read_keeps_the_skipped_write_distinctness() {
    let mut store = TermStore::new();
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let one = store.mk_int(BigInt::from(1));
    let two = store.mk_int(BigInt::from(2));
    let three = store.mk_int(BigInt::from(3));
    let base = store.mk_const_array(Sort::Int, one);
    let eq_i_j = store.mk_eq(i, j);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_i_j, false);
    solver.populate_caches();

    let outer = (i, two, Vec::new());
    let (base_value, base_reasons) = solver
        .effective_read_value_at(base, &[outer.clone()], j)
        .expect("a write at a distinct index lets the read reach the base");
    assert_eq!(base_value, one);
    assert_eq!(base_reasons, vec![TheoryLit::new(eq_i_j, false)]);

    let inner = (j, three, Vec::new());
    let (inner_value, inner_reasons) = solver
        .effective_read_value_at(base, &[outer, inner], j)
        .expect("a write at a distinct index lets the read reach the inner write");
    assert_eq!(inner_value, three);
    assert_eq!(inner_reasons, vec![TheoryLit::new(eq_i_j, false)]);
}
