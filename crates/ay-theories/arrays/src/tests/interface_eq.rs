// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the Nelson-Oppen interface-equality shared-read distinctness
//! prune (`arrays_distinct_by_shared_read`): arrays provably distinguished by a
//! read at a common index must NOT spawn an interface-equality split, but
//! genuinely-undecided array pairs still must.

use super::*;

/// Two arrays read at a common index with provably-distinct values are forced
/// unequal by extensionality — the interface-equality generator must suppress
/// the (useless) `a = b` split. This is the fix for the O(N²) interface-eq blow
/// up that turned trivially-SAT problems (N independent arrays distinguished
/// only by their reads) into `unknown`.
#[test]
fn test_interface_eq_pruned_when_reads_provably_distinct() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let j = store.mk_var("j", Sort::Int);

    let sel_a = store.mk_select(a, j);
    let sel_b = store.mk_select(b, j);
    let eq_sel = store.mk_eq(sel_a, sel_b);

    let mut solver = ArraySolver::new(&store);
    // select(a, j) != select(b, j): forces a != b, so no split is needed.
    solver.assert_literal(eq_sel, false);
    let _ = solver.check();

    assert!(
        solver.check_interface_equalities().is_none(),
        "arrays distinguished by a provably-distinct shared read must not \
         request an interface-equality split"
    );
}

/// Contrast: with no distinguishing read, the two arrays could still be equal,
/// so the interface-equality split MUST be requested (Nelson-Oppen
/// completeness). This guards against the prune over-suppressing.
#[test]
fn test_interface_eq_requested_when_reads_not_distinct() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let j = store.mk_var("j", Sort::Int);

    // Reads keep both arrays "active" but are NOT asserted distinct.
    let _sel_a = store.mk_select(a, j);
    let _sel_b = store.mk_select(b, j);

    let mut solver = ArraySolver::new(&store);
    let _ = solver.check();

    assert!(
        solver.check_interface_equalities().is_some(),
        "arrays that could still be equal must get their interface-equality \
         split — the prune must not suppress a genuinely-undecided pair"
    );
}

/// The prune must not fire when the shared-index read disequality is only
/// *asserted at distinct indices* (not a common index) — reads at different
/// indices say nothing about array equality.
#[test]
fn test_interface_eq_not_pruned_when_read_indices_differ() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let j = store.mk_var("j", Sort::Int);
    let k = store.mk_var("k", Sort::Int);

    let sel_a = store.mk_select(a, j);
    let sel_b = store.mk_select(b, k);
    let eq_sel = store.mk_eq(sel_a, sel_b);

    let mut solver = ArraySolver::new(&store);
    // select(a, j) != select(b, k) with j, k NOT known-equal: says nothing
    // about a vs b, so the split is still required.
    solver.assert_literal(eq_sel, false);
    let _ = solver.check();

    assert!(
        solver.check_interface_equalities().is_some(),
        "a read disequality at unrelated indices must not prune the split"
    );
}

/// Distinct index terms that are asserted equal denote the same read position.
/// The equality bridge must therefore enable the same sound prune as a
/// syntactically shared index.
#[test]
fn test_interface_eq_pruned_when_read_indices_are_provably_equal() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let j = store.mk_var("j", Sort::Int);
    let k = store.mk_var("k", Sort::Int);

    let sel_a = store.mk_select(a, j);
    let sel_b = store.mk_select(b, k);
    let eq_indices = store.mk_eq(j, k);
    let eq_selects = store.mk_eq(sel_a, sel_b);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_indices, true);
    solver.assert_literal(eq_selects, false);
    let _ = solver.check();

    assert!(
        solver.check_interface_equalities().is_none(),
        "known-equal read indices with distinct values prove the arrays distinct"
    );
}

/// Free-array lazy skip (Z3's shared-vars discipline): a FREE store base — a
/// plain array `Var` observed only as the base of a store, with no direct
/// reads and no equality edges — must never receive an interface-equality
/// split. Nothing can force its equality with another array and any model can
/// keep it distinct, so the split is useless; eagerly generating it is the
/// O(N²) blowup that livelocked N independent `select (store bₖ iₖ vₖ) j`
/// terms past N≈105. Read-carrying arrays must still be split (see
/// `test_interface_eq_requested_when_reads_not_distinct`, which pins the
/// non-free side).
#[test]
fn test_interface_eq_skips_free_store_bases() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let b0 = store.mk_var("b0", arr_sort.clone());
    let b1 = store.mk_var("b1", arr_sort);
    let i0 = store.mk_var("i0", Sort::Int);
    let i1 = store.mk_var("i1", Sort::Int);
    let v0 = store.mk_var("v0", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);
    let j = store.mk_var("j", Sort::Int);

    // b0/b1 are observed ONLY as store bases; the selects read the STORES.
    let s0 = store.mk_store(b0, i0, v0);
    let s1 = store.mk_store(b1, i1, v1);
    let _sel0 = store.mk_select(s0, j);
    let _sel1 = store.mk_select(s1, j);

    let mut solver = ArraySolver::new(&store);
    let _ = solver.check();

    let requests = solver.check_interface_equalities().unwrap_or_default();
    assert!(
        requests
            .iter()
            .all(|r| r.lhs != b0 && r.rhs != b0 && r.lhs != b1 && r.rhs != b1),
        "free store bases (no direct reads, no equality edges) must never be \
         interface-equality split — got {requests:?}"
    );
}
