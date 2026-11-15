// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `propagate_equalities` must be a function of the theory state modulo the
//! already-sent set: a second scan of an UNCHANGED state returns nothing.
//!
//! The Nelson-Oppen loop declares a fixpoint when the drain returns nothing
//! and the always-on Sat-time postcondition (`assert_fixpoint_convergence`,
//! #4714/#4998) re-runs the same drain and asserts it still returns nothing.
//! Between the two, only the `prop_eq_snapshot` short-circuit stood: with
//! the cache invalidated (which `import_sent_equality_replays` does on every
//! combiner `check()`) the #8785 "one representative select equality per
//! (array pair, index class)" bound elected a NEW representative on every
//! re-scan, because an already-sent pair was skipped before it consumed the
//! class slot. That was the `BUG: AX fixpoint violation — sub-theory has 25
//! undrained equalities` process abort on QF_AUFLIA
//! `swap_invalid_t1_pp_sf_ai_00010_002` (main c4cad0aa11, 2026-09-21).
//!
//! Each test here drives one of the three class-bounded rules through the
//! exact sequence: first scan, spurious snapshot invalidation, second scan.

use super::*;

/// Invalidate the `prop_eq_snapshot` short-circuit the way the combiner's
/// per-`check()` replay import does, without adding anything to the sent set.
fn invalidate_snapshot(solver: &mut ArraySolver<'_>) {
    solver.import_sent_equality_replays(&HashSet::default());
    assert!(
        solver.prop_eq_snapshot.is_none(),
        "the replay import must reset the propagation snapshot for this test to mean anything"
    );
}

fn select_pairs(result: &EqualityPropagationResult) -> Vec<(TermId, TermId)> {
    result
        .equalities
        .iter()
        .map(|eq| ArraySolver::ordered_pair(eq.lhs, eq.rhs))
        .collect()
}

/// Same-array read congruence: four reads of one array whose indices form a
/// single asserted equality class. The first scan elects exactly one
/// representative select equality for the class; a re-scan of the unchanged
/// state must elect none.
#[test]
fn same_array_read_congruence_rescan_of_unchanged_state_is_empty() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();
    let a = store.mk_var("a", arr_sort);
    let idx: Vec<TermId> = ["i", "j", "k", "l"]
        .iter()
        .map(|name| store.mk_var(*name, Sort::Int))
        .collect();
    let selects: Vec<TermId> = idx.iter().map(|&i| store.mk_select(a, i)).collect();
    // The reads must be visible to the solver as select terms; registering
    // them through a (false) equality atom keeps them out of the index class.
    let sink = store.mk_var("sink", Sort::Int);
    let sink_atoms: Vec<TermId> = selects.iter().map(|&s| store.mk_eq(s, sink)).collect();
    let idx_eqs = [
        store.mk_eq(idx[0], idx[1]),
        store.mk_eq(idx[1], idx[2]),
        store.mk_eq(idx[2], idx[3]),
    ];

    let mut solver = ArraySolver::new(&store);
    for &atom in &sink_atoms {
        solver.register_atom(atom);
    }
    for &eq in &idx_eqs {
        solver.assert_literal(eq, true);
    }

    let first = solver.propagate_equalities();
    let first_pairs = select_pairs(&first);
    assert_eq!(
        first_pairs.len(),
        1,
        "the #8785 bound elects exactly one representative per (array, index class): {first:?}"
    );
    let (lhs, rhs) = first_pairs[0];
    assert!(
        selects.contains(&lhs) && selects.contains(&rhs),
        "the representative is a select pair over `a`: {first:?}"
    );
    assert_eq!(
        first.equalities[0].reason.len(),
        1,
        "adjacent reads are justified by one index-equality literal: {first:?}"
    );

    invalidate_snapshot(&mut solver);
    let second = solver.propagate_equalities();
    assert!(
        second.equalities.is_empty(),
        "a re-scan of an unchanged state elected a NEW representative — the drain is not \
         idempotent and the Sat-time convergence re-drain will abort: {second:?}"
    );

    // And the result is stable under any number of spurious invalidations.
    for _ in 0..3 {
        invalidate_snapshot(&mut solver);
        assert!(solver.propagate_equalities().equalities.is_empty());
    }
}

/// Array congruence across an asserted array equality `a = b`: reads of `a`
/// and `b` over one index class. Same contract as above.
#[test]
fn array_congruence_rescan_of_unchanged_state_is_empty() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();
    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let idx: Vec<TermId> = ["i", "j", "k"]
        .iter()
        .map(|name| store.mk_var(*name, Sort::Int))
        .collect();
    let sel_a: Vec<TermId> = idx.iter().map(|&i| store.mk_select(a, i)).collect();
    let sel_b: Vec<TermId> = idx.iter().map(|&i| store.mk_select(b, i)).collect();
    let sink = store.mk_var("sink", Sort::Int);
    let sink_atoms: Vec<TermId> = sel_a
        .iter()
        .chain(sel_b.iter())
        .map(|&s| store.mk_eq(s, sink))
        .collect();
    let eq_ab = store.mk_eq(a, b);
    let idx_eqs = [store.mk_eq(idx[0], idx[1]), store.mk_eq(idx[1], idx[2])];

    let mut solver = ArraySolver::new(&store);
    for &atom in &sink_atoms {
        solver.register_atom(atom);
    }
    solver.assert_literal(eq_ab, true);
    for &eq in &idx_eqs {
        solver.assert_literal(eq, true);
    }

    let first = solver.propagate_equalities();
    assert!(
        !first.equalities.is_empty(),
        "the asserted array equality with an index class must propagate at least one read pair"
    );
    let mut sent = HashSet::default();
    for pair in select_pairs(&first) {
        assert!(sent.insert(pair), "no pair is emitted twice in one scan");
    }

    invalidate_snapshot(&mut solver);
    let second = solver.propagate_equalities();
    assert!(
        second.equalities.is_empty(),
        "array-congruence re-scan of an unchanged state must be empty: {second:?}"
    );
}

/// Transitive array equalities through the equality graph (`a = b`, `b = c`)
/// with one index class. Same contract as above.
#[test]
fn transitive_array_rescan_of_unchanged_state_is_empty() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();
    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort.clone());
    let c = store.mk_var("c", arr_sort);
    let idx: Vec<TermId> = ["i", "j", "k"]
        .iter()
        .map(|name| store.mk_var(*name, Sort::Int))
        .collect();
    let mut selects = Vec::new();
    for &arr in &[a, b, c] {
        for &i in &idx {
            selects.push(store.mk_select(arr, i));
        }
    }
    let sink = store.mk_var("sink", Sort::Int);
    let sink_atoms: Vec<TermId> = selects.iter().map(|&s| store.mk_eq(s, sink)).collect();
    let arr_eqs = [store.mk_eq(a, b), store.mk_eq(b, c)];
    let idx_eqs = [store.mk_eq(idx[0], idx[1]), store.mk_eq(idx[1], idx[2])];

    let mut solver = ArraySolver::new(&store);
    for &atom in &sink_atoms {
        solver.register_atom(atom);
    }
    for &eq in arr_eqs.iter().chain(idx_eqs.iter()) {
        solver.assert_literal(eq, true);
    }

    let first = solver.propagate_equalities();
    assert!(!first.equalities.is_empty());
    let mut sent = HashSet::default();
    for pair in select_pairs(&first) {
        assert!(sent.insert(pair), "no pair is emitted twice in one scan");
    }

    invalidate_snapshot(&mut solver);
    let second = solver.propagate_equalities();
    assert!(
        second.equalities.is_empty(),
        "transitive-array re-scan of an unchanged state must be empty: {second:?}"
    );
}

/// The other half of the contract: a scan after a REAL change still emits.
/// A second array joining the equality class after the first scan yields
/// new representative pairs, so idempotence is not silence.
#[test]
fn rescan_after_a_real_change_still_propagates() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();
    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let sel_a_i = store.mk_select(a, i);
    let sel_a_j = store.mk_select(a, j);
    let sel_b_i = store.mk_select(b, i);
    let sink = store.mk_var("sink", Sort::Int);
    let sink_atoms = [
        store.mk_eq(sel_a_i, sink),
        store.mk_eq(sel_a_j, sink),
        store.mk_eq(sel_b_i, sink),
    ];
    let eq_ij = store.mk_eq(i, j);
    let eq_ab = store.mk_eq(a, b);

    let mut solver = ArraySolver::new(&store);
    for &atom in &sink_atoms {
        solver.register_atom(atom);
    }
    solver.assert_literal(eq_ij, true);
    let first = select_pairs(&solver.propagate_equalities());
    assert_eq!(
        first,
        vec![ArraySolver::ordered_pair(sel_a_i, sel_a_j)],
        "the same-array read pair is the only propagation before `a = b`"
    );

    invalidate_snapshot(&mut solver);
    assert!(solver.propagate_equalities().equalities.is_empty());

    solver.assert_literal(eq_ab, true);
    let after = select_pairs(&solver.propagate_equalities());
    assert!(
        after.contains(&ArraySolver::ordered_pair(sel_a_i, sel_b_i))
            || after.contains(&ArraySolver::ordered_pair(sel_a_j, sel_b_i)),
        "asserting `a = b` is a real change and must propagate a read of `b`: {after:?}"
    );
}
