// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_disjunctive_store_target_lemma_keeps_root_faithful_branch_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let rhs = store.mk_var("rhs", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let vi = store.mk_var("vi", Sort::Int);
    let vj = store.mk_var("vj", Sort::Int);

    let select_a_i = store.mk_select(a, i);
    let select_a_j = store.mk_select(a, j);
    let store_i = store.mk_store(a, i, vi);
    let store_j = store.mk_store(a, j, vj);

    let eq_store_i_rhs = store.mk_eq(store_i, rhs);
    let eq_store_j_rhs = store.mk_eq(store_j, rhs);
    let eq_i_j = store.mk_eq(i, j);
    let eq_a_rhs = store.mk_eq(a, rhs);
    let eq_vi_select_a_i = store.mk_eq(vi, select_a_i);
    let eq_vj_select_a_j = store.mk_eq(vj, select_a_j);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_store_i_rhs, true);
    solver.assert_literal(eq_store_j_rhs, true);
    solver.assert_literal(eq_vi_select_a_i, true);
    solver.assert_literal(eq_vj_select_a_j, true);
    solver.assert_literal(eq_i_j, false);
    solver.assert_literal(eq_a_rhs, false);
    solver.populate_caches();

    let Some(TheoryResult::NeedLemmas(lemmas)) = solver.check_disjunctive_store_target_equalities()
    else {
        panic!("expected NeedLemmas from root-faithful disjunctive store-target equalities");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "root-faithful same-target stores should emit one disjunctive lemma"
    );
    assert_eq!(
        lemmas[0].clause,
        vec![
            TheoryLit::new(eq_store_i_rhs, false),
            TheoryLit::new(eq_store_j_rhs, false),
            TheoryLit::new(eq_i_j, true),
            TheoryLit::new(eq_a_rhs, true),
        ],
        "lemma must preserve the root-faithful a = rhs branch instead of forcing only i = j"
    );
}

#[test]
fn test_arrays_check_surfaces_disjunctive_store_target_lemma_inline_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let rhs = store.mk_var("rhs", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let vi = store.mk_var("vi", Sort::Int);
    let vj = store.mk_var("vj", Sort::Int);

    let store_i = store.mk_store(a, i, vi);
    let store_j = store.mk_store(a, j, vj);

    let eq_store_i_rhs = store.mk_eq(store_i, rhs);
    let eq_store_j_rhs = store.mk_eq(store_j, rhs);
    let eq_i_j = store.mk_eq(i, j);
    let eq_a_rhs = store.mk_eq(a, rhs);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_store_i_rhs, true);
    solver.assert_literal(eq_store_j_rhs, true);
    solver.assert_literal(eq_i_j, false);
    solver.assert_literal(eq_a_rhs, false);

    let TheoryResult::NeedLemmas(lemmas) = solver.check() else {
        panic!("expected inline NeedLemmas from disjunctive store-target equalities");
    };

    assert!(
        lemmas.iter().any(|lemma| {
            lemma.clause
                == vec![
                    TheoryLit::new(eq_store_i_rhs, false),
                    TheoryLit::new(eq_store_j_rhs, false),
                    TheoryLit::new(eq_i_j, true),
                    TheoryLit::new(eq_a_rhs, true),
                ]
        }),
        "inline check() must surface the guarded store-target clause; got {lemmas:?}"
    );
}
