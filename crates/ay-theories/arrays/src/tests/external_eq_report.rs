// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `assert_external_equality_with_reasons` reports whether it changed the
//! solver (#no-index-eq-livelock).
//!
//! The Nelson-Oppen index pass asserts an external equality for every
//! undecided store/select index pair EUF has proved equal, and re-runs the
//! fixpoint when the array solver has something new to consume. The pair
//! stays undecided for the array solver afterwards — the sentinel edge is not
//! an asserted atom and `known_equal` never sees it — so the report is the
//! only thing standing between that pass and a 100-iteration loop that
//! re-asserts the same edge on every snapshot.

use super::*;

#[test]
fn external_equality_reports_new_edge_then_duplicate_then_grown_reasons() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let guard_a = store.mk_var("guard_a", Sort::Bool);
    let guard_b = store.mk_var("guard_b", Sort::Bool);

    let mut solver = ArraySolver::new(&store);
    assert!(
        solver.assert_external_equality_with_reasons(x, y, &[TheoryLit::new(guard_a, true)]),
        "a new sentinel edge is a change"
    );
    assert!(
        !solver.assert_external_equality_with_reasons(y, x, &[TheoryLit::new(guard_a, true)]),
        "the same edge with the same reasons, either orientation, changes nothing"
    );
    assert!(
        !solver.assert_external_equality_with_reasons(x, y, &[]),
        "the same edge with no reasons changes nothing"
    );
    assert!(
        solver.assert_external_equality_with_reasons(x, y, &[TheoryLit::new(guard_b, true)]),
        "a reason the edge did not carry yet is a change"
    );
    assert!(
        !solver.assert_external_equality_with_reasons(
            x,
            y,
            &[TheoryLit::new(guard_a, true), TheoryLit::new(guard_b, true)],
        ),
        "the union of reasons already stored changes nothing"
    );
    assert_eq!(
        solver.external_eqs.len(),
        1,
        "one sentinel edge record for the pair throughout"
    );
}

#[test]
fn unreasoned_external_equality_reports_only_the_first_insertion() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let mut solver = ArraySolver::new(&store);
    assert!(solver.assert_external_equality(x, y));
    assert!(!solver.assert_external_equality(x, y));
    assert!(!solver.assert_external_equality(y, x));
}

/// The premise the index pass used to rely on, pinned as it actually is: an
/// external equality between two store indices does NOT settle the pair for
/// `undecided_index_pairs`, whose store-chain walk asks the atom-keyed
/// `known_equal`. A consumer that wants the pair settled must obtain the
/// asserted atom (the SAT-level model-equality split).
#[test]
fn external_index_equality_does_not_settle_the_undecided_pair() {
    let mut store = TermStore::new();
    let t = store.mk_var("t", make_array_sort());
    let s = store.mk_var("s", make_array_sort());
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let chain = store.mk_store(t, i, v);
    let eq_s = store.mk_eq(s, chain);
    let read = store.mk_select(s, j);
    let seven = store.mk_int(BigInt::from(7));
    let read_atom = store.mk_eq(read, seven);
    let guard = store.mk_var("guard", Sort::Bool);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_s, true);
    solver.assert_literal(read_atom, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    let before = solver.undecided_index_pairs();
    assert!(
        before
            .iter()
            .any(|p| ArraySolver::ordered_pair(p.idx1, p.idx2) == ArraySolver::ordered_pair(i, j)),
        "the store index and the read index are an undecided pair: {before:?}"
    );

    assert!(solver.assert_external_equality_with_reasons(i, j, &[TheoryLit::new(guard, true)]));
    let after = solver.undecided_index_pairs();
    assert!(
        after
            .iter()
            .any(|p| ArraySolver::ordered_pair(p.idx1, p.idx2) == ArraySolver::ordered_pair(i, j)),
        "the sentinel edge does not settle the pair for the store-chain walk: {after:?}"
    );
    assert!(
        !solver.assert_external_equality_with_reasons(i, j, &[TheoryLit::new(guard, true)]),
        "and asserting it again is not progress"
    );
}
