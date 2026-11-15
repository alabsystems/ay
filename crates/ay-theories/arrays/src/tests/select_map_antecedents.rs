// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The select-map and select-as-array axiom instances carry every antecedent
//! (2026-09-23 hunt D4-d, second half).
//!
//! `select(X, i) = f(select(a, i))` holds only where `X = map[f](a)`, and
//! `select(X, i) = f(i)` only where `X = as-array[f]`. When the application
//! `f(..)` in the formula was located through an argument equality (`f(v)`
//! with `v = select(a, i)`, or `f(y)` read at `x` with `x = y`), the lemma
//! kept the array antecedent but dropped that substitution: a clause that
//! still asserts `select(X, i) = f(v)` after `v = select(a, i)` is retracted.
//! (The same hunk makes an instance reached through a PATH of array
//! equalities, with no direct `(= X map[f](a))` atom, carry the explained
//! path instead of nothing; the standalone solver does not pair a select with
//! a function-backed array through a transitive path, so that half has no
//! unit test here.) Each test checks that every emitted instance of the axiom
//! names every antecedent.

use super::*;
use ay_core::{Symbol, TheoryLemma};
use num_bigint::BigInt;

/// Every lemma that concludes `conclusion` (as a positive literal) must also
/// contain the negation of every literal in `antecedents`.
fn assert_instances_carry(lemmas: &[TheoryLemma], conclusion: TermId, antecedents: &[TermId]) {
    let instances: Vec<&TheoryLemma> = lemmas
        .iter()
        .filter(|lemma| {
            lemma
                .clause
                .iter()
                .any(|lit| lit.term == conclusion && lit.value)
        })
        .collect();
    assert!(
        !instances.is_empty(),
        "expected an axiom instance concluding {conclusion:?}, got {lemmas:?}"
    );
    for lemma in instances {
        for &antecedent in antecedents {
            assert!(
                lemma
                    .clause
                    .iter()
                    .any(|lit| lit.term == antecedent && !lit.value),
                "axiom instance {:?} omits the antecedent {antecedent:?}: it would \
                 hold the conclusion even where that literal is false",
                lemma.clause
            );
        }
    }
}

/// Run `check` (then `final_check`) until the solver stops asking for lemmas,
/// collecting every lemma it emits.
fn collect_lemmas(solver: &mut ArraySolver<'_>) -> Vec<TheoryLemma> {
    let mut lemmas = Vec::new();
    for _ in 0..6 {
        match solver.check() {
            TheoryResult::NeedLemmas(batch) => lemmas.extend(batch),
            TheoryResult::Sat
            | TheoryResult::NeedModelEquality(_)
            | TheoryResult::NeedModelEqualities(_) => match solver.final_check() {
                TheoryResult::NeedLemmas(batch) => lemmas.extend(batch),
                // A model-equality request is a case split the search would
                // answer; the axiom instances under test do not depend on it.
                TheoryResult::NeedModelEquality(_) | TheoryResult::NeedModelEqualities(_) => {}
                _ => break,
            },
            other => panic!("expected Sat or NeedLemmas, got {other:?}"),
        }
    }
    lemmas
}

/// `b = map[f](a)` directly, but the application in the formula is `f(v)` with
/// `v = select(a, 0)`: the instance `select(b, 0) = f(v)` needs that
/// substitution as well.
#[test]
fn select_map_instance_through_an_argument_equality_names_it() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();
    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort.clone());
    let v = store.mk_var("v", Sort::Int);
    let zero = store.mk_int(BigInt::from(0));
    let map_f_a = store.mk_array_map("f", vec![a], arr_sort);
    let sel_b_0 = store.mk_select(b, zero);
    let sel_a_0 = store.mk_select(a, zero);
    let f_v = store.mk_app(Symbol::named("f"), vec![v], Sort::Int);
    let conclusion = store.mk_eq(sel_b_0, f_v);
    let eq_b_map = store.mk_eq(b, map_f_a);
    let eq_v_sel = store.mk_eq(v, sel_a_0);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_b_map, true);
    solver.assert_literal(eq_v_sel, true);
    let lemmas = collect_lemmas(&mut solver);
    assert_instances_carry(&lemmas, conclusion, &[eq_b_map, eq_v_sel]);
}

/// `b = as-array[f]` directly, but the application in the formula is `f(y)`
/// with `x = y` while the read is `select(b, x)`: the instance
/// `select(b, x) = f(y)` needs that index substitution as well.
#[test]
fn select_as_array_instance_through_an_argument_equality_names_it() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();
    let b = store.mk_var("b", arr_sort.clone());
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let as_array_f = store.mk_as_array("f", arr_sort);
    let sel_b_x = store.mk_select(b, x);
    let f_y = store.mk_app(Symbol::named("f"), vec![y], Sort::Int);
    let conclusion = store.mk_eq(sel_b_x, f_y);
    let eq_b_aa = store.mk_eq(b, as_array_f);
    let eq_x_y = store.mk_eq(x, y);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_b_aa, true);
    solver.assert_literal(eq_x_y, true);
    let lemmas = collect_lemmas(&mut solver);
    assert_instances_carry(&lemmas, conclusion, &[eq_b_aa, eq_x_y]);
}
