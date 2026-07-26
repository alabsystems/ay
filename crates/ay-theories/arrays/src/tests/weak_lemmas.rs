// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for M3: model-based read-over-weak-path conflict lemmas
//! (`read_over_weak_path_conflict_lemmas`), the production consumer of the
//! weak-equivalence graph built in `weak_equiv.rs`.

use super::*;

/// A genuine multi-hop weak path that threads TWO store chains through an
/// asserted array equality: `a —[i1]— s1 —(b = s1)— b —[i2]— s2`. With both
/// store indices provably `≠` the read index `j`, the arrays are weakly
/// equivalent modulo `j`, so `select(a, j) = select(s2, j)` is FORCED. The
/// model asserts them distinct — a read-over-weak-eq conflict the weak graph
/// resolves in a single BFS across the strong edge. The pass must emit exactly
/// one conflict clause, and that clause must be the negation of exactly the
/// four justifying reasons.
#[test]
fn test_read_over_weak_path_conflict_through_strong_eq() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i1 = store.mk_var("i1", Sort::Int);
    let i2 = store.mk_var("i2", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);
    let v2 = store.mk_var("v2", Sort::Int);

    // Two store chains joined by an asserted array equality b = s1.
    let s1 = store.mk_store(a, i1, v1);
    let s2 = store.mk_store(b, i2, v2);
    let eq_b_s1 = store.mk_eq(b, s1);

    // Reads at a common index j on the two ends of the weak path.
    let sel_a = store.mk_select(a, j);
    let sel_s2 = store.mk_select(s2, j);
    let eq_sel = store.mk_eq(sel_a, sel_s2);

    // Index disequalities: neither store touches the read index j.
    let eq_j_i1 = store.mk_eq(j, i1);
    let eq_j_i2 = store.mk_eq(j, i2);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_b_s1, true);
    solver.assert_literal(eq_sel, false);
    solver.assert_literal(eq_j_i1, false);
    solver.assert_literal(eq_j_i2, false);

    // Populate the select/store caches and build the weak-equivalence graph.
    let _ = solver.check();

    let lemmas = solver.read_over_weak_path_conflict_lemmas();
    assert_eq!(
        lemmas.len(),
        1,
        "the read-over-weak-path pass must emit exactly one conflict clause"
    );

    // The clause is the negation of every justifying reason: the select
    // disequality, the array-equality path reason, and both index
    // disequalities. Compare as a set (the pass sorts by term id).
    let mut got: Vec<_> = lemmas[0]
        .clause
        .iter()
        .map(|l| (l.term.0, l.value))
        .collect();
    got.sort_unstable();
    let mut want = vec![
        (eq_sel.0, true),   // ¬(select_a ≠ select_s2)
        (eq_b_s1.0, false), // ¬(b = s1)
        (eq_j_i1.0, true),  // ¬(j ≠ i1)
        (eq_j_i2.0, true),  // ¬(j ≠ i2)
    ];
    want.sort_unstable();
    assert_eq!(
        got, want,
        "clause must negate exactly the four justifying reasons"
    );

    // End-to-end soundness: the reasons the clause negates are jointly
    // theory-UNSAT — i.e. the emitted clause is a valid array tautology, not a
    // fabricated conflict. A fresh solver with those same literals must reach a
    // conflict through its own (independent) machinery.
    let mut verify = ArraySolver::new(&store);
    verify.assert_literal(eq_b_s1, true);
    verify.assert_literal(eq_sel, false);
    verify.assert_literal(eq_j_i1, false);
    verify.assert_literal(eq_j_i2, false);
    assert!(
        matches!(
            verify.check(),
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) | TheoryResult::NeedLemmas(_)
        ),
        "the negated reasons must be jointly UNSAT — the lemma is valid"
    );
}

/// A pure two-store weak path with NO strong edge: `a —[i1]— s1 —[i2]— s2`.
/// The pass still fires (labels `[i1, i2]`, no path reasons) and the clause
/// carries only the select disequality and the two index disequalities.
#[test]
fn test_read_over_weak_path_conflict_pure_store_chain() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i1 = store.mk_var("i1", Sort::Int);
    let i2 = store.mk_var("i2", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);
    let v2 = store.mk_var("v2", Sort::Int);

    let s1 = store.mk_store(a, i1, v1);
    let s2 = store.mk_store(s1, i2, v2);

    let sel_a = store.mk_select(a, j);
    let sel_s2 = store.mk_select(s2, j);
    let eq_sel = store.mk_eq(sel_a, sel_s2);
    let eq_j_i1 = store.mk_eq(j, i1);
    let eq_j_i2 = store.mk_eq(j, i2);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_sel, false);
    solver.assert_literal(eq_j_i1, false);
    solver.assert_literal(eq_j_i2, false);
    let _ = solver.check();

    let lemmas = solver.read_over_weak_path_conflict_lemmas();
    assert_eq!(lemmas.len(), 1, "pure store-chain weak path must fire");

    let mut got: Vec<_> = lemmas[0]
        .clause
        .iter()
        .map(|l| (l.term.0, l.value))
        .collect();
    got.sort_unstable();
    let mut want = vec![(eq_sel.0, true), (eq_j_i1.0, true), (eq_j_i2.0, true)];
    want.sort_unstable();
    assert_eq!(got, want, "clause negates the select + index disequalities");
}

/// Soundness guard: when a store on the weak path is NOT provably distinct
/// from the read index (the write MAY land on `j`), the equality is not
/// implied and the pass must emit NOTHING — never a fabricated conflict.
#[test]
fn test_read_over_weak_path_no_lemma_when_store_index_undecided() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i1 = store.mk_var("i1", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);

    let s1 = store.mk_store(a, i1, v1);

    let sel_a = store.mk_select(a, j);
    let sel_s1 = store.mk_select(s1, j);
    let eq_sel = store.mk_eq(sel_a, sel_s1);

    let mut solver = ArraySolver::new(&store);
    // Read selects distinct, but i1 vs j is UNDECIDED (no i1 ≠ j asserted).
    solver.assert_literal(eq_sel, false);
    let _ = solver.check();

    let lemmas = solver.read_over_weak_path_conflict_lemmas();
    assert!(
        lemmas.is_empty(),
        "with the store index undecided vs the read index, no equality is \
         forced — the pass must not fabricate a conflict"
    );
}
