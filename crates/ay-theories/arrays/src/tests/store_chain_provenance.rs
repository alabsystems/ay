// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Store-map provenance beyond the two D4 pins in `store_chain.rs`
//! (`test_partial_walker_keeps_skipped_store_as_shadow`,
//! `test_store_permutation_requires_complete_maps`): a skipped write reached
//! through an asserted alias still shadows, and a complete-map permutation
//! equality carries the shadowing, base and distinctness premises it rests on.

use super::*;
use num_bigint::BigInt;

/// The D4-b shape with the middle of the chain reached through an asserted
/// alias: `alias = store(store(b, j, 1), i, v)` and `lhs = store(alias, 2, j)`.
/// The write at `i` is skipped (its shadowing by the write at 2 is undecided),
/// but it still hides the write at `j` whenever `i = j`.
#[test]
fn partial_walker_keeps_skipped_alias_store_as_shadow() {
    let mut terms = TermStore::new();
    let b = terms.mk_var("b", make_array_sort());
    let alias = terms.mk_var("alias", make_array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let five = terms.mk_int(BigInt::from(5));
    let j_is_five = terms.mk_eq(j, five);
    let inner = terms.mk_store(b, j, one);
    let middle = terms.mk_store(inner, i, v);
    let alias_is_middle = terms.mk_eq(alias, middle);
    let lhs = terms.mk_store(alias, two, j);

    let mut solver = ArraySolver::new(&terms);
    solver.assert_literal(j_is_five, true);
    solver.assert_literal(alias_is_middle, true);
    solver.register_term(lhs);
    solver.populate_caches();
    let chain = solver
        .collect_effective_stores_shared(lhs)
        .expect("aliased store chain");
    assert!(
        chain.2.iter().all(|(idx, _, _)| *idx != j),
        "the write reached through the alias can still shadow j: {:?}",
        chain.2
    );
}

/// `store(store(b, i, 1), j, 2) = store(c, j, 2)` over `b = c` holds only when
/// the outer write hides the inner one, i.e. under `i = j`; the explanation
/// must name that shadowing equality and the base equality.
#[test]
fn complete_permutation_keeps_shadow_and_base_equalities() {
    let mut terms = TermStore::new();
    let b = terms.mk_var("b", make_array_sort());
    let c = terms.mk_var("c", make_array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let equal_bases = terms.mk_eq(b, c);
    let equal_indices = terms.mk_eq(i, j);
    let inner = terms.mk_store(b, i, one);
    let lhs = terms.mk_store(inner, j, two);
    let rhs = terms.mk_store(c, j, two);
    let equal_chains = terms.mk_eq(lhs, rhs);

    let mut solver = ArraySolver::new(&terms);
    solver.register_atom(equal_chains);
    solver.assert_literal(equal_bases, true);
    solver.populate_caches();
    assert!(
        solver
            .complete_store_permutation_reasons(lhs, rhs)
            .is_none(),
        "without i = j the write of 1 may survive"
    );
    solver.assert_literal(equal_indices, true);
    solver.populate_caches();
    let reasons = solver
        .complete_store_permutation_reasons(lhs, rhs)
        .expect("the outer write provably shadows the inner write");
    assert!(
        reasons.contains(&TheoryLit::new(equal_indices, true)),
        "{reasons:?}"
    );
    assert!(
        reasons.contains(&TheoryLit::new(equal_bases, true)),
        "{reasons:?}"
    );
}

/// Two writes commute only at distinct indices: the permutation equality
/// `store(store(b, i, 1), j, 2) = store(store(b, j, 2), i, 1)` must carry
/// `i != j`.
#[test]
fn complete_permutation_keeps_distinctness_for_reordered_writes() {
    let mut terms = TermStore::new();
    let b = terms.mk_var("b", make_array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let equal_indices = terms.mk_eq(i, j);
    let lhs_inner = terms.mk_store(b, i, one);
    let lhs = terms.mk_store(lhs_inner, j, two);
    let rhs_inner = terms.mk_store(b, j, two);
    let rhs = terms.mk_store(rhs_inner, i, one);
    let equal_chains = terms.mk_eq(lhs, rhs);

    let mut solver = ArraySolver::new(&terms);
    solver.register_atom(equal_chains);
    solver.assert_literal(equal_indices, false);
    solver.populate_caches();
    let reasons = solver
        .complete_store_permutation_reasons(lhs, rhs)
        .expect("distinct writes commute over the same base");
    assert!(
        reasons.contains(&TheoryLit::new(equal_indices, false)),
        "{reasons:?}"
    );
}
