// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Completeness the 2026-09-23 hunt's D4-a repair exposed: once the
//! store-chain value conflict carries its index-distinctness reasons, two
//! consequences the old (unconditional, sometimes wrong) clause used to stand
//! in for need their own sound derivation.

use super::*;
use num_bigint::BigInt;

/// storeeq_41_0240 (unsat): store chains over const-arrays with provably
/// distinct defaults are never equal over an infinite index sort, and the
/// conflict needs no premise about the written indices. Before, the only route
/// to it was the store-chain value conflict, which needs a support index
/// provably distinct from every written index; with `i` and `j` undecided it
/// stayed silent and the search could end on an assignment no model satisfies.
#[test]
fn test_store_chains_over_distinct_const_defaults_conflict() {
    let mut store = TermStore::new();
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let w = store.mk_var("w", Sort::Int);
    let zero = store.mk_int(BigInt::from(0));
    let one = store.mk_int(BigInt::from(1));
    let k1 = store.mk_const_array(Sort::Int, one);
    let k0 = store.mk_const_array(Sort::Int, zero);
    let lhs = store.mk_store(k1, i, v);
    let rhs = store.mk_store(k0, j, w);
    let eq = store.mk_eq(lhs, rhs);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq, true);
    solver.populate_caches();

    let Some(TheoryResult::NeedLemmas(lemmas)) = solver.check_const_array_equality_conflict()
    else {
        panic!("store chains over const 1 and const 0 cannot be equal over Int");
    };
    assert_eq!(lemmas.len(), 1);
    assert_eq!(
        lemmas[0].clause,
        vec![TheoryLit::new(eq, false)],
        "the conflict rests on the equality alone, not on i or j"
    );
}

/// Control: over a FINITE index sort finitely many stores can cover every
/// index, so the chains may be equal (`(store K1 p 0) = (store K0 q 1)` holds
/// over Bool whenever `p != q`) and no conflict is drawn.
#[test]
fn test_store_chains_over_distinct_const_defaults_finite_index_no_conflict() {
    let mut store = TermStore::new();
    let p = store.mk_var("p", Sort::Bool);
    let q = store.mk_var("q", Sort::Bool);
    let zero = store.mk_int(BigInt::from(0));
    let one = store.mk_int(BigInt::from(1));
    let k1 = store.mk_const_array(Sort::Bool, one);
    let k0 = store.mk_const_array(Sort::Bool, zero);
    let lhs = store.mk_store(k1, p, zero);
    let rhs = store.mk_store(k0, q, one);
    let eq = store.mk_eq(lhs, rhs);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq, true);
    solver.populate_caches();

    assert!(
        solver.check_const_array_equality_conflict().is_none(),
        "over Bool the two chains are equal when p != q"
    );
}

/// storeeq_41_0261 (sat): a base array the solver observed only through reads
/// takes its else value from a store parent whose default is known.
/// `store(a, 1, 5) = store(K7, 1, 5)` pins every unwritten cell of `a` to 7;
/// extraction used to pass defaults only UP a chain (base to store), so `a`
/// kept `default: None` and the renderer invented one, printing a model that
/// falsifies the asserted equality.
#[test]
fn test_extract_model_base_inherits_default_from_store_parent() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let one = store.mk_int(BigInt::from(1));
    let two = store.mk_int(BigInt::from(2));
    let five = store.mk_int(BigInt::from(5));
    let seven = store.mk_int(BigInt::from(7));
    let k7 = store.mk_const_array(Sort::Int, seven);
    let lhs = store.mk_store(a, one, five);
    let rhs = store.mk_store(k7, one, five);
    let eq = store.mk_eq(lhs, rhs);
    let read = store.mk_select(a, two);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq, true);
    solver.populate_caches();

    let mut term_values = HashMap::default();
    term_values.insert(one, "1".to_string());
    term_values.insert(two, "2".to_string());
    term_values.insert(five, "5".to_string());
    term_values.insert(seven, "7".to_string());
    term_values.insert(read, "7".to_string());

    let model = solver.extract_model(&term_values);
    let interp = model
        .array_values
        .get(&a)
        .expect("the read gives `a` an interpretation");
    assert_eq!(
        interp.default.as_deref(),
        Some("7"),
        "`a` agrees with store(a, 1, 5) = store(K7, 1, 5) off index 1; got {interp:?}"
    );
}

/// storeeq_2609_0415 (sat): `K0 = (store a0 2 0)` makes `a0` read 0 at every
/// index but 2, so `(= (select a0 0) 5)` contradicts it -- with no upward
/// read-over-write term in the store. The fresh verification combiner runs
/// this solver on a conflict's literals alone; without this derivation it
/// called that core satisfiable and the fail-closed gate discarded a sound
/// conflict, ending the whole first AUFLIA pass `unknown`.
#[test]
fn test_const_chain_base_read_at_an_unwritten_index_conflicts() {
    let mut store = TermStore::new();
    let a0 = store.mk_var("a0", make_array_sort());
    let zero = store.mk_int(BigInt::from(0));
    let two = store.mk_int(BigInt::from(2));
    let five = store.mk_int(BigInt::from(5));
    let k0 = store.mk_const_array(Sort::Int, zero);
    let chain = store.mk_store(a0, two, zero);
    let eq = store.mk_eq(k0, chain);
    let read = store.mk_select(a0, zero);
    let read_is_five = store.mk_eq(read, five);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq, true);
    solver.assert_literal(read_is_five, true);
    solver.populate_caches();

    let Some(TheoryResult::NeedLemmas(lemmas)) = solver.check_const_array_store_chain_conflict()
    else {
        panic!("(store a0 2 0) = const 0 forces a0[0] = 0, so a0[0] = 5 is a conflict");
    };
    assert_eq!(lemmas.len(), 1);
    let mut expected = vec![
        TheoryLit::new(eq, false),
        TheoryLit::new(read_is_five, false),
    ];
    expected.sort_by_key(|lit| (lit.term.0, lit.value));
    assert_eq!(
        lemmas[0].clause, expected,
        "the conflict rests on the chain equality and the read's value alone"
    );

    // Control: a read AT the written index is the chain's own write, not the
    // base's, so `a0[2] = 5` is no conflict.
    let mut store = TermStore::new();
    let a0 = store.mk_var("a0", make_array_sort());
    let zero = store.mk_int(BigInt::from(0));
    let two = store.mk_int(BigInt::from(2));
    let five = store.mk_int(BigInt::from(5));
    let k0 = store.mk_const_array(Sort::Int, zero);
    let chain = store.mk_store(a0, two, zero);
    let eq = store.mk_eq(k0, chain);
    let read = store.mk_select(a0, two);
    let read_is_five = store.mk_eq(read, five);
    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq, true);
    solver.assert_literal(read_is_five, true);
    solver.populate_caches();
    assert!(
        solver.check_const_array_store_chain_conflict().is_none(),
        "a0[2] is overwritten by the chain, so it is unconstrained"
    );
}

/// The verifier's variant d4d_013 (sat; main answers at once): the search drew
/// the distinct-defaults conflict on an atom between `store(K0, i, v)` and
/// `store(K1, i, v)` and explained it by the path through `a2`. The fresh solver
/// of the fail-closed conflict verifier holds only the path -- `a2 = store(K0,
/// i, v)`, `a2 = store(K1, i, v)` -- and used to call it satisfiable, which
/// ended the whole AUFLIA pass `unknown`. Chains merged transitively conflict
/// like chains equal by one atom, on the path alone.
#[test]
fn test_store_chains_over_distinct_const_defaults_in_one_class_conflict() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();
    let a2 = store.mk_var("a2", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let zero = store.mk_int(BigInt::from(0));
    let one = store.mk_int(BigInt::from(1));
    let k0 = store.mk_const_array(Sort::Int, zero);
    let k1 = store.mk_const_array(Sort::Int, one);
    let over_k0 = store.mk_store(k0, i, v);
    let over_k1 = store.mk_store(k1, i, v);
    let eq0 = store.mk_eq(a2, over_k0);
    let eq1 = store.mk_eq(a2, over_k1);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq0, true);
    solver.assert_literal(eq1, true);
    solver.populate_caches();

    let Some(TheoryResult::NeedLemmas(lemmas)) = solver.check_const_array_equality_conflict()
    else {
        panic!("a2 cannot equal store chains over const 0 and const 1 over Int");
    };
    assert_eq!(lemmas.len(), 1);
    let mut clause = lemmas[0].clause.clone();
    clause.sort_by_key(|lit| lit.term.0);
    let mut expected = vec![TheoryLit::new(eq0, false), TheoryLit::new(eq1, false)];
    expected.sort_by_key(|lit| lit.term.0);
    assert_eq!(clause, expected, "the conflict rests on the path alone");
}

/// Control: over Bool the two chains can be equal (the stores cover the
/// domain), and chains over const-arrays with the SAME default never conflict.
#[test]
fn test_store_chains_in_one_class_no_conflict_over_bool_or_equal_defaults() {
    let mut store = TermStore::new();
    let bool_arr = Sort::array(Sort::Bool, Sort::Int);
    let a = store.mk_var("a", bool_arr);
    let p = store.mk_var("p", Sort::Bool);
    let q = store.mk_var("q", Sort::Bool);
    let zero = store.mk_int(BigInt::from(0));
    let one = store.mk_int(BigInt::from(1));
    let k0 = store.mk_const_array(Sort::Bool, zero);
    let k1 = store.mk_const_array(Sort::Bool, one);
    let over_k0 = store.mk_store(k0, p, one);
    let over_k1 = store.mk_store(k1, q, zero);
    let eq0 = store.mk_eq(a, over_k0);
    let eq1 = store.mk_eq(a, over_k1);
    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq0, true);
    solver.assert_literal(eq1, true);
    solver.populate_caches();
    assert!(
        solver.check_const_array_equality_conflict().is_none(),
        "over Bool, store(K0, p, 1) = store(K1, q, 0) holds when q = (not p)"
    );

    let mut store = TermStore::new();
    let arr_sort = make_array_sort();
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let two = store.mk_int(BigInt::from(2));
    let k2 = store.mk_const_array(Sort::Int, two);
    let lhs = store.mk_store(k2, i, two);
    let rhs = store.mk_store(k2, j, two);
    let eq_l = store.mk_eq(b, lhs);
    let eq_r = store.mk_eq(b, rhs);
    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_l, true);
    solver.assert_literal(eq_r, true);
    solver.populate_caches();
    assert!(
        solver.check_const_array_equality_conflict().is_none(),
        "both chains are over const 2"
    );
}

/// Fresh storeeq_2809_0025 (sat at once on main and z3 5.1.0): the search's
/// conflict `{b = K1, a0 = b, 7 = (select a0 j), ...}` went to the fail-closed
/// verifier, whose fresh solver also holds two store chains in the class of
/// `a0`. The event-driven const-read queue never paired `(select a0 j)` with
/// `K1` there, `final_check` answered `Sat` (with the three literals alone it
/// finds the conflict), the verifier rejected a valid conflict and the whole
/// AUFLIA pass ended `unknown`. `final_check` now reads every array whose class
/// holds a const-array.
#[test]
fn test_read_of_a_class_holding_a_const_array_conflicts_in_final_check() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();
    let a0 = store.mk_var("a0", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let j = store.mk_var("j", Sort::Int);
    let k = store.mk_var("k", Sort::Int);
    let zero = store.mk_int(BigInt::from(0));
    let one = store.mk_int(BigInt::from(1));
    let two = store.mk_int(BigInt::from(2));
    let seven = store.mk_int(BigInt::from(7));
    let minus_one = store.mk_int(BigInt::from(-1));
    let k1 = store.mk_const_array(Sort::Int, one);
    let st = store.mk_store(a0, zero, seven);
    let sel_st_j = store.mk_select(st, j);
    let sel_a0_j = store.mk_select(a0, j);
    let jm1 = store.mk_add(vec![j, minus_one]);
    let inner = store.mk_store(b, k, sel_st_j);
    let chain = store.mk_store(inner, jm1, one);
    let b_is_k1 = store.mk_eq(b, k1);
    let read_is_7 = store.mk_eq(seven, sel_a0_j);
    let a0_is_b = store.mk_eq(a0, b);
    let lits = [
        b_is_k1,
        read_is_7,
        a0_is_b,
        store.mk_eq(k, two),
        store.mk_eq(k, jm1),
        store.mk_eq(seven, sel_st_j),
        store.mk_eq(sel_st_j, sel_a0_j),
        store.mk_eq(st, chain),
        store.mk_eq(a0, chain),
    ];
    let mut solver = ArraySolver::new(&store);
    for &lit in &lits {
        solver.assert_literal(lit, true);
    }
    let _ = solver.check();
    let TheoryResult::NeedLemmas(lemmas) = solver.final_check() else {
        panic!("a0 = b = (as const 1) cannot read 7 at j");
    };
    let clause: Vec<TheoryLit> = lemmas[0].clause.clone();
    // A conflict among the asserted literals (a read of `a0` valued 7 through
    // `(select a0 j)` or `(select (store a0 0 7) j)`), resting on `a0 = b = K1`.
    assert!(
        clause
            .iter()
            .all(|lit| !lit.value && lits.contains(&lit.term)),
        "every literal is a negated asserted literal: {clause:?}"
    );
    for lit in [b_is_k1, a0_is_b] {
        assert!(
            clause.contains(&TheoryLit::new(lit, false)),
            "the conflict rests on b = K1 and a0 = b: {clause:?}"
        );
    }
}

/// Fresh storeeq_2609_0448 (sat at once on main and z3 5.1.0): `{K0 =
/// store(a1, 5, 0), a1 = store(K0, 2, 1)}` is a conflict (the chain reads 1
/// at 2, `K0` reads 0), but collecting the chain walked from the base `K0`
/// back into `store(a1, 5, 0)` through `K0`'s own class, cycled to the
/// iteration cap and returned no map. A const-array base ends the chain.
#[test]
fn test_chain_through_its_const_base_class_reads_the_written_index() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();
    let a1 = store.mk_var("a1", arr_sort);
    let zero = store.mk_int(BigInt::from(0));
    let one = store.mk_int(BigInt::from(1));
    let two = store.mk_int(BigInt::from(2));
    let five = store.mk_int(BigInt::from(5));
    let k0 = store.mk_const_array(Sort::Int, zero);
    let outer = store.mk_store(a1, five, zero);
    let inner = store.mk_store(k0, two, one);
    let k0_is_outer = store.mk_eq(k0, outer);
    let a1_is_inner = store.mk_eq(a1, inner);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(k0_is_outer, true);
    solver.assert_literal(a1_is_inner, true);
    solver.populate_caches();

    let Some(TheoryResult::NeedLemmas(lemmas)) = solver.check_const_array_store_chain_conflict()
    else {
        panic!("store(store(K0, 2, 1), 5, 0) reads 1 at 2 and cannot equal K0");
    };
    let mut clause = lemmas[0].clause.clone();
    clause.sort_by_key(|lit| lit.term.0);
    let mut expected = vec![
        TheoryLit::new(k0_is_outer, false),
        TheoryLit::new(a1_is_inner, false),
    ];
    expected.sort_by_key(|lit| lit.term.0);
    assert_eq!(clause, expected);
}

/// Fresh storeeq_2809_0597 (sat at once on main): `(= K1 (store (store (store
/// K1 j j) i 2) (+ j 2) 3))` is a conflict by its OUTERMOST write alone (`3 !=
/// 1` at `j + 2`), whatever `i` and `j` are; the complete effective map it
/// used to wait for needs every index relation decided. Control: an outermost
/// value equal to the default is no conflict.
#[test]
fn test_outermost_write_of_a_chain_equal_to_a_const_conflicts() {
    for (outer_value, conflict) in [(3, true), (1, false)] {
        let mut store = TermStore::new();
        let i = store.mk_var("i", Sort::Int);
        let j = store.mk_var("j", Sort::Int);
        let one = store.mk_int(BigInt::from(1));
        let two = store.mk_int(BigInt::from(2));
        let value = store.mk_int(BigInt::from(outer_value));
        let k1 = store.mk_const_array(Sort::Int, one);
        let j2 = store.mk_add(vec![j, two]);
        let s1 = store.mk_store(k1, j, j);
        let s2 = store.mk_store(s1, i, two);
        let s3 = store.mk_store(s2, j2, value);
        let eq = store.mk_eq(k1, s3);

        let mut solver = ArraySolver::new(&store);
        solver.assert_literal(eq, true);
        solver.populate_caches();

        let result = solver.check_const_array_store_chain_conflict();
        if conflict {
            let Some(TheoryResult::NeedLemmas(lemmas)) = result else {
                panic!("the outermost write 3 cannot read K1's 1: {result:?}");
            };
            assert_eq!(lemmas[0].clause, vec![TheoryLit::new(eq, false)]);
        } else {
            assert!(
                result.is_none(),
                "an outermost 1 agrees with K1: {result:?}"
            );
        }
    }
}
