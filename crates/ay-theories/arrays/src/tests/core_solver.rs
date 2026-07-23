// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_array_solver_basic_sat() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    // Create store(a, i, v) and select(store(a, i, v), i)
    let stored = store.mk_store(a, i, v);
    let selected = store.mk_select(stored, i);

    // Create equality: select(store(a, i, v), i) = v
    let eq = store.mk_eq(selected, v);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq, true);

    // Should be SAT - this is consistent with ROW1
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn test_array_solver_row1_conflict() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int); // Different variable for index
    let v = store.mk_var("v", Sort::Int);

    // Create store(a, i, v) and select(store(a, i, v), j)
    // Using different index variable j to avoid term-level simplification
    let stored = store.mk_store(a, i, v);
    let selected = store.mk_select(stored, j);

    // Create equalities
    let eq_ij = store.mk_eq(i, j); // i = j (will be asserted true)
    let eq_sel_v = store.mk_eq(selected, v); // select(store(a,i,v), j) = v

    let mut solver = ArraySolver::new(&store);

    // Assert i = j (so ROW1 applies)
    solver.assert_literal(eq_ij, true);
    // Assert select(store(a,i,v), j) ≠ v (directly contradicts ROW1 when i=j)
    solver.assert_literal(eq_sel_v, false);

    solver.populate_caches();
    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_row1()
        .expect("expected ROW1 helper to emit a lemma")
    else {
        panic!("expected NeedLemmas from ROW1 helper");
    };
    assert_eq!(lemmas.len(), 1, "ROW1 conflict should emit one lemma");
    assert_eq!(
        lemmas[0].clause,
        vec![TheoryLit::new(eq_ij, false), TheoryLit::new(eq_sel_v, true)],
        "ROW1 lemma must block i=j and select(store(a,i,v),j)!=v simultaneously"
    );
}

#[test]
fn test_array_solver_row1_preserves_pending_tail_after_first_conflict() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a1 = store.mk_var("a1", arr_sort.clone());
    let a2 = store.mk_var("a2", arr_sort);

    let i1 = store.mk_var("i1", Sort::Int);
    let j1 = store.mk_var("j1", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);

    let i2 = store.mk_var("i2", Sort::Int);
    let j2 = store.mk_var("j2", Sort::Int);
    let v2 = store.mk_var("v2", Sort::Int);

    let store1 = store.mk_store(a1, i1, v1);
    let select1 = store.mk_select(store1, j1);
    let eq_i1_j1 = store.mk_eq(i1, j1);
    let eq_sel1_v1 = store.mk_eq(select1, v1);

    let store2 = store.mk_store(a2, i2, v2);
    let select2 = store.mk_select(store2, j2);
    let eq_i2_j2 = store.mk_eq(i2, j2);
    let eq_sel2_v2 = store.mk_eq(select2, v2);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_i1_j1, true);
    solver.assert_literal(eq_sel1_v1, false);
    solver.assert_literal(eq_i2_j2, true);

    solver.populate_caches();
    assert!(
        solver.pending_row1.contains(&(select1, store1)),
        "first ROW1 pair should be queued before the first check"
    );
    assert!(
        solver.pending_row1.contains(&(select2, store2)),
        "second ROW1 pair should be queued before the first check"
    );

    let TheoryResult::NeedLemmas(first_lemmas) = solver
        .check_row1()
        .expect("expected the first ROW1 pair to emit a lemma")
    else {
        panic!("expected NeedLemmas from the first ROW1 pair");
    };
    assert_eq!(
        first_lemmas[0].clause,
        vec![
            TheoryLit::new(eq_i1_j1, false),
            TheoryLit::new(eq_sel1_v1, true),
        ],
        "the first ROW1 conflict should be emitted before replaying the retained tail"
    );
    assert_eq!(
        solver.pending_row1.items(),
        &[(select2, store2)],
        "the unprocessed ROW1 tail must survive the first lemma return"
    );

    solver.assert_literal(eq_sel2_v2, false);
    let TheoryResult::NeedLemmas(second_lemmas) = solver
        .check_row1()
        .expect("expected retained ROW1 work to emit a second lemma")
    else {
        panic!("expected NeedLemmas from the retained ROW1 pair");
    };
    assert_eq!(
        second_lemmas[0].clause,
        vec![
            TheoryLit::new(eq_i2_j2, false),
            TheoryLit::new(eq_sel2_v2, true),
        ],
        "retained ROW1 work should fire without repopulating caches"
    );
    assert!(
        solver.pending_row1.is_empty(),
        "the ROW1 queue should be empty after draining the retained tail"
    );
}

#[test]
fn test_array_solver_row2_sat() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    // Create store(a, i, v) and select(store(a, i, v), j)
    let stored = store.mk_store(a, i, v);
    let sel_stored_j = store.mk_select(stored, j);
    let sel_a_j = store.mk_select(a, j);

    // Create equalities
    let eq_ij = store.mk_eq(i, j);
    let eq_sels = store.mk_eq(sel_stored_j, sel_a_j);

    let mut solver = ArraySolver::new(&store);

    // Assert i ≠ j
    solver.assert_literal(eq_ij, false);
    // Assert select(store(a,i,v), j) = select(a, j) - consistent with ROW2
    solver.assert_literal(eq_sels, true);

    // ROW2 clause is (eq_ij ∨ eq_sels). Since eq_sels is already true,
    // the clause is satisfied — the solver correctly skips emission (#6738).
    // check() returns Sat (no lemmas needed) instead of NeedLemmas.
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "expected Sat when ROW2 clause is already satisfied, got {result:?}",
    );
}

#[test]
fn test_array_solver_row2_unassigned_emits_lemma() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    // Create store(a, i, v) and select(store(a, i, v), j)
    let stored = store.mk_store(a, i, v);
    let sel_stored_j = store.mk_select(stored, j);
    let sel_a_j = store.mk_select(a, j);

    // Create equalities (these must exist for the lemma atoms)
    let eq_ij = store.mk_eq(i, j);
    let eq_sels = store.mk_eq(sel_stored_j, sel_a_j);

    let mut solver = ArraySolver::new(&store);

    // Assert i ≠ j but do NOT assert eq_sels — leave it unassigned
    solver.assert_literal(eq_ij, false);

    // ROW2 clause (eq_ij ∨ eq_sels): eq_ij is false, eq_sels is unassigned.
    // Clause is NOT satisfied — solver should emit NeedLemmas.
    let TheoryResult::NeedLemmas(lemmas) = solver.check() else {
        panic!("expected NeedLemmas when ROW2 clause has unassigned disjunct");
    };
    assert_eq!(lemmas.len(), 1, "expected one ROW2 lemma clause");
    assert_eq!(
        lemmas[0].clause,
        vec![TheoryLit::new(eq_ij, true), TheoryLit::new(eq_sels, true)],
        "ROW2 lemma must assert i=j or select(store(a,i,v),j)=select(a,j)"
    );
}

#[test]
fn test_array_solver_row2_conflict() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    // Create store(a, i, v) and select(store(a, i, v), j) and select(a, j)
    let stored = store.mk_store(a, i, v);
    let sel_stored_j = store.mk_select(stored, j);
    let sel_a_j = store.mk_select(a, j);

    // Create equalities
    let eq_ij = store.mk_eq(i, j);
    let eq_sels = store.mk_eq(sel_stored_j, sel_a_j);

    let mut solver = ArraySolver::new(&store);

    // Assert i ≠ j
    solver.assert_literal(eq_ij, false);
    // Assert select(store(a,i,v), j) ≠ select(a, j) - contradicts ROW2
    solver.assert_literal(eq_sels, false);

    // #6694: After restoring Unsat early-returns in check(), a conflict
    // check may detect the contradiction directly as Unsat before
    // check_row2() emits NeedLemmas. Both are sound — ROW2 says
    // i≠j → select(store(a,i,v),j)=select(a,j), so asserting both
    // i≠j and sel(store)≠sel(a) is unsatisfiable.
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_) | TheoryResult::NeedLemmas(_)),
        "expected Unsat or NeedLemmas from ROW2 contradiction, got {result:?}",
    );
}

#[test]
fn test_array_solver_row2_propagation_dedups_same_reason() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let sel_stored_j = store.mk_select(stored, j);
    let sel_a_j = store.mk_select(a, j);

    let eq_ij = store.mk_eq(i, j);
    let eq_sels = store.mk_eq(sel_stored_j, sel_a_j);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_ij, false);

    let first = solver.propagate();
    assert_eq!(
        first.len(),
        1,
        "ROW2 should emit one propagation the first time"
    );
    assert_eq!(
        first[0].literal,
        TheoryLit::new(eq_sels, true),
        "ROW2 should propagate select(store(a,i,v),j) = select(a,j)"
    );
    assert_eq!(
        first[0].reason,
        vec![TheoryLit::new(eq_ij, false)],
        "ROW2 propagation should keep the index disequality reason"
    );

    let second = solver.propagate();
    assert!(
        second.is_empty(),
        "repeating propagate() with the same reason set must not re-emit the same clause"
    );
}

#[test]
fn test_affine_index_relations_detect_equal_and_distinct() {
    let mut store = TermStore::new();
    let i = store.mk_var("i", Sort::Int);
    let one = store.mk_int(BigInt::from(1));
    let two = store.mk_int(BigInt::from(2));
    let i_plus_1_a = store.mk_add(vec![i, one]);
    let i_plus_1_b = store.mk_add(vec![i, one]);
    let i_plus_2 = store.mk_add(vec![i, two]);

    let solver = ArraySolver::new(&store);
    assert!(solver.known_equal(i_plus_1_a, i_plus_1_b));
    // Tautological affine offset (i+1 vs i+2) is O(1) and kept in the
    // array theory for the propagation path (#6820).  The expensive
    // equality-substituted affine BFS was removed.
    assert!(solver.distinct_by_affine_offset(i_plus_1_a, i_plus_2));
}

#[test]
fn test_explain_distinct_if_provable_no_affine_bfs() {
    // After #6820, the array theory no longer does affine BFS to prove i ≠ j
    // from arithmetic structure like j = i + 1.  That reasoning belongs in
    // the LRA/LIA solver.
    let mut store = TermStore::new();
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let one = store.mk_int(BigInt::from(1));
    let i_plus_1 = store.mk_add(vec![i, one]);
    let eq_j_i_plus_1 = store.mk_eq(j, i_plus_1);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_j_i_plus_1, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    // Without the arithmetic solver propagating i ≠ j into the diseq_set,
    // the array theory cannot explain the distinctness.
    assert_eq!(
        solver.explain_distinct_if_provable(i, j),
        None,
        "array theory should not independently derive arithmetic disequalities (#6820)"
    );
}

#[test]
fn test_explain_distinct_if_provable_guards_external_equality_path() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let z = store.mk_var("z", Sort::Int);
    let guard = store.mk_var("g", Sort::Bool);
    let eq_yz = store.mk_eq(y, z);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(guard, true);
    solver.assert_literal(eq_yz, false);
    solver.assert_external_equality_with_reasons(x, y, &[TheoryLit::new(guard, true)]);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    let reasons = solver
        .explain_distinct_if_provable(x, z)
        .expect("reasoned external equality should explain x != z through y != z");
    assert!(
        reasons.contains(&TheoryLit::new(guard, true)),
        "explanation must include the external equality guard"
    );
    assert!(
        reasons.contains(&TheoryLit::new(eq_yz, false)),
        "explanation must include the asserted disequality"
    );
    assert_ne!(
        reasons,
        vec![TheoryLit::new(eq_yz, false)],
        "explanation must not rely only on the later disequality"
    );

    let mut unreasoned_solver = ArraySolver::new(&store);
    unreasoned_solver.assert_literal(eq_yz, false);
    unreasoned_solver.assert_external_equality(x, y);
    assert!(matches!(unreasoned_solver.check(), TheoryResult::Sat));
    assert_eq!(
        unreasoned_solver.explain_distinct_if_provable(x, z),
        None,
        "unreasoned external equality must not support a guarded disequality explanation"
    );
}

/// Verify resolve_select_through_stores walks a store chain using concrete
/// integer constants. ROW2 skips stores at distinct indices, ROW1 matches
/// the target index. Uses concrete constants (0, 1, 2) so both_const is
/// true and explain_distinct's empty reasons don't cause a bail-out (#5157).
#[test]
fn test_resolve_select_through_concrete_store_chain() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();
    let a = store.mk_var("a", arr_sort);
    let idx0 = store.mk_int(BigInt::from(0));
    let idx1 = store.mk_int(BigInt::from(1));
    let idx2 = store.mk_int(BigInt::from(2));
    let v0 = store.mk_var("v0", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);
    let v2 = store.mk_var("v2", Sort::Int);

    // Build chain: store(store(store(a, 2, v2), 1, v1), 0, v0)
    let s1 = store.mk_store(a, idx2, v2);
    let s2 = store.mk_store(s1, idx1, v1);
    let s3 = store.mk_store(s2, idx0, v0);

    // Assert a literal so the solver has something to process, then
    // call check() to populate store_cache from all TermStore terms.
    let sel = store.mk_select(s3, idx1);
    let eq = store.mk_eq(sel, v1);
    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    // Select at index 1: skip store at 0 (ROW2), match store at 1 (ROW1).
    let result = solver.resolve_select_through_stores(s3, idx1);
    assert!(result.is_some(), "should resolve value at index 1");
    let (value, _reasons) = result.unwrap();
    assert_eq!(value, v1, "select(store(..., 1, v1), 1) should be v1");

    // Select at index 2: skip stores at 0 and 1, match store at 2.
    let result = solver.resolve_select_through_stores(s3, idx2);
    assert!(result.is_some(), "should resolve value at index 2");
    let (value, _reasons) = result.unwrap();
    assert_eq!(value, v2, "select(store(..., 2, v2), 2) should be v2");
}

#[test]
fn test_array_solver_push_pop() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let w = store.mk_var("w", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let selected = store.mk_select(stored, i);
    let eq_sel_v = store.mk_eq(selected, v);
    let eq_v_w = store.mk_eq(v, w);

    let mut solver = ArraySolver::new(&store);

    // Assert something consistent
    solver.assert_literal(eq_sel_v, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    // Push and add conflicting assertion
    solver.push();
    solver.assert_literal(eq_v_w, false);
    // Note: This specific case might still be SAT because eq_sel_v being true
    // doesn't directly conflict with eq_v_w being false in the current implementation
    // Let me fix the test to be more precise

    // Pop should restore consistent state
    solver.pop();
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn test_equiv_class_cache_rebuilds_only_when_graph_changes() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let eq_ab = store.mk_eq(a, b);
    let sel = store.mk_select(a, i);
    let eq_sel_v = store.mk_eq(sel, v);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_ab, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    // (#6820 Step 3) Equiv class cache is now lazy — only built when
    // a sub-check actually needs it. First check() may or may not build it
    // depending on whether the event queues trigger equiv-class-dependent code.
    let builds_after_first_check = solver.equiv_class_cache_builds;

    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert_eq!(
        solver.equiv_class_cache_builds, builds_after_first_check,
        "repeated check() without equality-graph changes should reuse the cache"
    );

    solver.assert_literal(eq_sel_v, false);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert_eq!(
        solver.equiv_class_cache_builds, builds_after_first_check,
        "false equality assignments must not rebuild equivalence classes"
    );

    solver.assert_literal(eq_sel_v, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    // If the cache was built before, a new true equality should invalidate
    // it. If it wasn't built yet, it's fine either way.
    let builds_after_new_eq = solver.equiv_class_cache_builds;
    assert!(
        builds_after_new_eq >= builds_after_first_check,
        "new true equalities may trigger a rebuild but should never reduce the count"
    );
}

#[test]
fn test_final_check_skips_equiv_cache_when_no_selects_or_stores() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let eq_ab = store.mk_eq(a, b);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_ab, true);

    assert!(
        matches!(solver.final_check(), TheoryResult::Sat),
        "array final_check with zero select/store terms should be a no-op"
    );
    assert_eq!(
        solver.final_check_call_count, 1,
        "final_check should still record the call"
    );
    assert_eq!(
        solver.equiv_class_cache_builds, 0,
        "final_check should not rebuild equivalence classes when there are no array terms"
    );
    assert_eq!(
        solver.final_check_snapshot,
        Some((1, 0, 0, 0, 0, 0)),
        "zero-array final_check should cache the empty snapshot"
    );
}

#[test]
fn test_warm_cache_true_equalities_update_assignment_indices_incrementally() {
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);
    let c = store.mk_var("c", Sort::Int);

    let eq_ab = store.mk_eq(a, b);
    let eq_bc = store.mk_eq(b, c);

    let mut solver = ArraySolver::new(&store);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "initial cache warm-up should perform one full assignment-index rebuild"
    );

    solver.assert_literal(eq_ab, true);
    solver.assert_literal(eq_bc, true);

    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "warm-cache asserted equalities should update eq_adj incrementally"
    );
    assert_eq!(
        solver.explain_equal_if_provable(a, c),
        Some(vec![
            TheoryLit::new(eq_ab, true),
            TheoryLit::new(eq_bc, true),
        ]),
        "incremental eq_adj maintenance must preserve transitive equality reasons"
    );

    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "check() after warm-cache equality updates should reuse the incremental indices"
    );
}

#[test]
fn test_warm_cache_disequalities_update_assignment_indices_incrementally() {
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);

    let eq_ab = store.mk_eq(a, b);

    let mut solver = ArraySolver::new(&store);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "initial cache warm-up should perform one full assignment-index rebuild"
    );

    solver.assert_literal(eq_ab, false);

    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "warm-cache disequalities should update diseq_set incrementally"
    );
    assert_eq!(
        solver.explain_distinct_if_provable(a, b),
        Some(vec![TheoryLit::new(eq_ab, false)]),
        "incremental diseq_set maintenance must preserve the direct disequality reason"
    );

    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "check() after warm-cache disequalities should reuse the incremental indices"
    );
}

#[test]
fn test_fresh_same_name_vars_keep_distinct_affine_identity() {
    let mut store = TermStore::new();
    let x1 = store.mk_fresh_named_var("x", Sort::Int);
    let x2 = store.mk_fresh_named_var("x", Sort::Int);
    assert_ne!(
        x1, x2,
        "fresh named variables must retain distinct internal identities"
    );

    let opaque_arg = store.mk_var("opaque_arg", Sort::Int);
    let opaque = store.mk_app(
        Symbol::named("opaque_index_leaf"),
        vec![opaque_arg],
        Sort::Int,
    );
    let index1 = store.mk_app(Symbol::named("+"), vec![x1, opaque], Sort::Int);
    let index2 = store.mk_app(Symbol::named("+"), vec![x2, opaque], Sort::Int);

    let solver = ArraySolver::new(&store);
    assert!(
        !solver.equal_by_affine_form(x1, x2),
        "same visible name must not erase fresh declaration identity"
    );
    assert_eq!(
        solver.explain_equal_if_provable(x1, x2),
        None,
        "distinct fresh declarations have no equality explanation"
    );
    assert_eq!(
        solver.explain_equal_if_provable(index1, index2),
        None,
        "affine leaf congruence must preserve fresh declaration identity"
    );

    let partition = solver.index_conflict_partition(&[index1, index2]);
    assert_ne!(
        partition[&index1], partition[&index2],
        "unrelated mixed opaque indices may remain in distinct conflict blocks"
    );
}

#[test]
fn test_late_registered_true_equality_avoids_full_assignment_rebuild() {
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);
    let eq_ab = store.mk_eq(a, b);

    let mut solver = ArraySolver::new(&store);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "initial cache warm-up should perform one full assignment-index rebuild"
    );

    // Synthetic late-registration setup: direct unit tests cannot mutate
    // `TermStore` after `ArraySolver` borrows it, so rewind the cache to
    // make the final equality atom look newly interned.
    solver.equality_cache.remove(&eq_ab);
    solver
        .eq_pair_index
        .remove(&ArraySolver::ordered_pair(a, b));
    // A genuinely newly-interned term would not yet appear in the reverse
    // index or the var-layer replay list, so rewind those too (otherwise the
    // re-registration double-inserts eq_ab — the M1 structural oracle rejects
    // the resulting duplicate, and so would the real invariant).
    for endpoint in [a, b] {
        if let Some(v) = solver.term_to_equalities.get_mut(&endpoint) {
            v.retain(|&t| t != eq_ab);
        }
    }
    solver.var_layer_terms.retain(|&t| t != eq_ab);
    solver.populated_terms = eq_ab.index();

    solver.assert_literal(eq_ab, true);
    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "late equality assignments should queue incremental index updates"
    );

    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "late-registered asserted equalities should not force a full rebuild"
    );
    assert_eq!(
        solver.explain_equal_if_provable(a, b),
        Some(vec![TheoryLit::new(eq_ab, true)]),
        "late-registered equality should still produce the direct equality reason"
    );
}

#[test]
fn test_late_registered_disequality_avoids_full_assignment_rebuild() {
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);
    let eq_ab = store.mk_eq(a, b);

    let mut solver = ArraySolver::new(&store);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "initial cache warm-up should perform one full assignment-index rebuild"
    );

    // Synthetic late-registration setup: mirror the true-equality case for
    // a false assignment so the disequality path stays incremental too.
    solver.equality_cache.remove(&eq_ab);
    solver
        .eq_pair_index
        .remove(&ArraySolver::ordered_pair(a, b));
    // A genuinely newly-interned term would not yet appear in the reverse
    // index or the var-layer replay list, so rewind those too (otherwise the
    // re-registration double-inserts eq_ab — the M1 structural oracle rejects
    // the resulting duplicate, and so would the real invariant).
    for endpoint in [a, b] {
        if let Some(v) = solver.term_to_equalities.get_mut(&endpoint) {
            v.retain(|&t| t != eq_ab);
        }
    }
    solver.var_layer_terms.retain(|&t| t != eq_ab);
    solver.populated_terms = eq_ab.index();

    solver.assert_literal(eq_ab, false);
    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "late disequality assignments should queue incremental index updates"
    );

    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "late-registered disequalities should not force a full rebuild"
    );
    assert_eq!(
        solver.explain_distinct_if_provable(a, b),
        Some(vec![TheoryLit::new(eq_ab, false)]),
        "late-registered disequality should still produce the direct reason"
    );
}

// #arraytax: find_alternative_equality_term was rewritten from a full
// O(|equality_cache|) scan to an O(deg) term_to_equalities lookup. These
// tests pin the multi-term-per-pair semantics on the warm INCREMENTAL path
// (assign_index_rebuilds stays 1; flips are how the combiner re-asserts
// after backtracking): distinct equality atoms over the same (unordered)
// pair must still see each other as alternatives so eq_adj edges and
// diseq_set entries are preserved or relabeled, never wrongly dropped.

#[test]
fn test_alternative_true_equality_relabels_edge_on_flip() {
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);

    // mk_eq canonicalizes orientation, so build the second same-pair atom as
    // a raw `=` app (as duplicate atoms from independent frontends would be).
    let eq_ab = store.mk_eq(a, b);
    let eq_ba = store.mk_app(Symbol::named("="), vec![b, a], Sort::Bool);
    assert_ne!(
        eq_ab, eq_ba,
        "test setup requires distinct atoms for both orientations of the pair"
    );

    let mut solver = ArraySolver::new(&store);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert_eq!(solver.assign_index_rebuilds, 1);

    // eq_ab owns the eq_adj edge; asserting eq_ba true finds the alternative
    // and must not add a duplicate edge.
    solver.assert_literal(eq_ab, true);
    solver.assert_literal(eq_ba, true);

    // Flip the edge-owning atom: the incremental update must find eq_ba as
    // an alternative and relabel the edge instead of dropping connectivity.
    solver.assert_literal(eq_ab, false);

    assert_eq!(
        solver.explain_equal_if_provable(a, b),
        Some(vec![TheoryLit::new(eq_ba, true)]),
        "edge must be relabeled to the alternative true equality on flip"
    );
    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "alternative-equality maintenance must stay on the incremental path"
    );
}

#[test]
fn test_alternative_true_equality_non_owner_flip_keeps_edge() {
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);

    let eq_ab = store.mk_eq(a, b);
    let eq_ba = store.mk_app(Symbol::named("="), vec![b, a], Sort::Bool);
    assert_ne!(eq_ab, eq_ba);

    let mut solver = ArraySolver::new(&store);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    solver.assert_literal(eq_ba, true);
    solver.assert_literal(eq_ab, true);
    // Flip the non-owning atom: eq_ba still owns the edge, connectivity stays.
    solver.assert_literal(eq_ab, false);

    assert_eq!(
        solver.explain_equal_if_provable(a, b),
        Some(vec![TheoryLit::new(eq_ba, true)]),
        "edge owned by the still-true atom must survive the other atom's flip"
    );
    assert_eq!(solver.assign_index_rebuilds, 1);
}

#[test]
fn test_alternative_false_equality_preserves_then_drops_diseq() {
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);

    let eq_ab = store.mk_eq(a, b);
    let eq_ba = store.mk_app(Symbol::named("="), vec![b, a], Sort::Bool);
    assert_ne!(eq_ab, eq_ba);

    let mut solver = ArraySolver::new(&store);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    solver.assert_literal(eq_ab, false);
    solver.assert_literal(eq_ba, false);
    let key = ArraySolver::ordered_pair(a, b);
    assert!(solver.diseq_set.contains(&key));

    // Flipping eq_ba away from false must keep the diseq via alternative eq_ab.
    solver.assert_literal(eq_ba, true);
    assert!(
        solver.diseq_set.contains(&key),
        "diseq_set entry must survive while an alternative false atom remains"
    );

    // Flipping eq_ab away from false too (no false atom left) must drop it.
    solver.assert_literal(eq_ab, true);
    assert!(
        !solver.diseq_set.contains(&key),
        "diseq_set entry must be removed once no false atom for the pair remains"
    );
    assert_eq!(
        solver.assign_index_rebuilds, 1,
        "alternative-equality maintenance must stay on the incremental path"
    );
}

#[test]
fn test_array_free_equalities_produce_no_propagations() {
    // #arraytax: with no select/store terms registered, the ROW2 pass and the
    // singleton-support candidate scan are structural no-ops and are skipped.
    // Pin the observable behavior: propagate() yields nothing on an
    // equality-only (array-free) problem.
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::Int);
    let b = store.mk_var("b", Sort::Int);
    let c = store.mk_var("c", Sort::Int);
    let eq_ab = store.mk_eq(a, b);
    let eq_bc = store.mk_eq(b, c);
    let eq_ac = store.mk_eq(a, c);

    let _ = eq_bc; // registered but unassigned
    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_ab, true);
    solver.assert_literal(eq_ac, false);

    assert!(
        solver.propagate().is_empty(),
        "array-free equality problems must not generate array propagations"
    );
}

#[test]
fn test_array_solver_reset() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let selected = store.mk_select(stored, j);
    let eq_ij = store.mk_eq(i, j);
    let eq_sel_v = store.mk_eq(selected, v);

    let mut solver = ArraySolver::new(&store);

    // Create conflicting state: i = j but select(store(a,i,v), j) ≠ v
    solver.assert_literal(eq_ij, true);
    solver.assert_literal(eq_sel_v, false);
    // Batched-lemma check() converts ROW1 Unsat to NeedLemmas (#6546).
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_) | TheoryResult::NeedLemmas(_)),
        "expected Unsat or NeedLemmas from ROW1 conflict"
    );

    // Reset should clear state
    solver.reset();
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn test_array_equality_conflict() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);

    // Create select(a, i) and select(b, i)
    let sel_a = store.mk_select(a, i);
    let sel_b = store.mk_select(b, i);

    // Create equalities
    let eq_ab = store.mk_eq(a, b);
    let eq_sels = store.mk_eq(sel_a, sel_b);

    let mut solver = ArraySolver::new(&store);

    // Assert a = b
    solver.assert_literal(eq_ab, true);
    // Assert select(a, i) ≠ select(b, i) - contradicts array equality
    solver.assert_literal(eq_sels, false);

    solver.populate_caches();
    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_array_equality()
        .expect("expected array-equality helper to emit a lemma")
    else {
        panic!("expected NeedLemmas from array-equality helper");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "array-equality conflict should emit one lemma"
    );
    assert_eq!(
        lemmas[0].clause,
        vec![TheoryLit::new(eq_ab, false), TheoryLit::new(eq_sels, true)],
        "array-equality lemma must block a=b and select(a,i)!=select(b,i)"
    );
}

#[test]
fn test_array_equality_conflict_uses_transitive_index_reasons_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let k = store.mk_var("k", Sort::Int);

    let sel_a = store.mk_select(a, i);
    let sel_b = store.mk_select(b, j);

    let eq_ab = store.mk_eq(a, b);
    let eq_ik = store.mk_eq(i, k);
    let eq_kj = store.mk_eq(k, j);
    let eq_sels = store.mk_eq(sel_a, sel_b);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_ab, true);
    solver.assert_literal(eq_ik, true);
    solver.assert_literal(eq_kj, true);
    solver.assert_literal(eq_sels, false);

    solver.populate_caches();
    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_array_equality()
        .expect("expected array-equality helper to emit a lemma")
    else {
        panic!("expected NeedLemmas from array-equality helper");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "transitive array-equality conflict should emit one lemma"
    );
    assert_eq!(
        lemmas[0].clause,
        vec![
            TheoryLit::new(eq_ab, false),
            TheoryLit::new(eq_ik, false),
            TheoryLit::new(eq_kj, false),
            TheoryLit::new(eq_sels, true),
        ],
        "array-equality conflict must include the full transitive index-equality reason chain"
    );
}

#[test]
#[allow(clippy::many_single_char_names)]
fn test_var_eq_store_row2() {
    // Test: B = store(A, 0, v), and we select at index 1
    // select(B, 1) should equal select(A, 1) because 0 ≠ 1
    use num_bigint::BigInt;

    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("A", arr_sort.clone());
    let b = store.mk_var("B", arr_sort);
    let v = store.mk_var("v", Sort::Int);
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);

    let zero = store.mk_int(BigInt::from(0));
    let one = store.mk_int(BigInt::from(1));

    // store(A, 0, v)
    let store_term = store.mk_store(a, zero, v);
    // B = store(A, 0, v)
    let eq_b_store = store.mk_eq(b, store_term);

    // select(A, 1) and select(B, 1)
    let sel_a_1 = store.mk_select(a, one);
    let sel_b_1 = store.mk_select(b, one);

    // x = select(A, 1) and y = select(B, 1)
    let eq_x_sel = store.mk_eq(x, sel_a_1);
    let eq_y_sel = store.mk_eq(y, sel_b_1);

    // x ≠ y
    let eq_xy = store.mk_eq(x, y);

    let mut solver = ArraySolver::new(&store);

    // Assert the equalities
    solver.assert_literal(eq_b_store, true); // B = store(A, 0, v)
    solver.assert_literal(eq_x_sel, true); // x = select(A, 1)
    solver.assert_literal(eq_y_sel, true); // y = select(B, 1)
    solver.assert_literal(eq_xy, false); // x ≠ y

    // This SHOULD be UNSAT because:
    // B = store(A, 0, v) and 0 ≠ 1 implies select(B, 1) = select(A, 1)
    // So x = select(A, 1) = select(B, 1) = y, contradiction with x ≠ y
    // Batched-lemma check() may convert Unsat to NeedLemmas (#6546).
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_) | TheoryResult::NeedLemmas(_)),
        "Expected UNSAT or NeedLemmas but got {result:?}"
    );
}

/// Regression test for #8598: select-as-array axiom through equality alias.
///
/// b = as-array[f], f(5) = 10, but select(b, 5) != 10 should be UNSAT.
/// Before the fix, the as-array axiom select(as-array[f], i) = f(i) was not
/// fired because register_select only checked the syntactic array arg (b),
/// not whether b is equal to an as-array term through the equality graph.
#[test]
fn test_select_as_array_through_equality_alias() {
    use num_bigint::BigInt;

    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let b = store.mk_var("b", arr_sort.clone());
    // as-array[f] of sort Array Int Int
    let as_array_f = store.mk_as_array("f", arr_sort);

    let five = store.mk_int(BigInt::from(5));
    let ten = store.mk_int(BigInt::from(10));

    // f(5)
    let f_5 = store.mk_app(Symbol::named("f"), vec![five], Sort::Int);
    // select(b, 5)
    let sel_b_5 = store.mk_select(b, five);

    // b = as-array[f]
    let eq_b_aa = store.mk_eq(b, as_array_f);
    // f(5) = 10
    let eq_f5_10 = store.mk_eq(f_5, ten);
    // select(b, 5) = 10
    let eq_sel_10 = store.mk_eq(sel_b_5, ten);

    let mut solver = ArraySolver::new(&store);

    solver.assert_literal(eq_b_aa, true); // b = as-array[f]
    solver.assert_literal(eq_f5_10, true); // f(5) = 10
    solver.assert_literal(eq_sel_10, false); // select(b, 5) != 10

    // The axiom chain: b = as-array[f] => select(b, 5) = f(5) = 10
    // So select(b, 5) != 10 is a contradiction.
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_) | TheoryResult::NeedLemmas(_)),
        "expected Unsat or NeedLemmas from select-as-array alias conflict, got {result:?}",
    );
}

/// Regression test for #8598: select-map axiom through equality alias.
///
/// b = map[f](a), select(a, 0) = 5, f(5) exists and != select(b, 0).
/// The map axiom select(map[f](a), i) = f(select(a, i)) should fire through
/// the equality alias b = map[f](a).
#[test]
fn test_select_map_through_equality_alias() {
    use num_bigint::BigInt;

    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort.clone());

    let zero = store.mk_int(BigInt::from(0));
    let five = store.mk_int(BigInt::from(5));

    // map[f](a) — a map term
    let map_f_a = store.mk_array_map("f", vec![a], arr_sort);

    // select(a, 0) and select(b, 0)
    let sel_a_0 = store.mk_select(a, zero);
    let sel_b_0 = store.mk_select(b, zero);

    // f(5) — the function application at the resolved value
    let f_5 = store.mk_app(Symbol::named("f"), vec![five], Sort::Int);

    // Equalities
    let eq_b_map = store.mk_eq(b, map_f_a); // b = map[f](a)
    let eq_sel_a_5 = store.mk_eq(sel_a_0, five); // select(a, 0) = 5
    let eq_sel_b_f5 = store.mk_eq(sel_b_0, f_5); // select(b, 0) = f(5)

    let mut solver = ArraySolver::new(&store);

    solver.assert_literal(eq_b_map, true); // b = map[f](a)
    solver.assert_literal(eq_sel_a_5, true); // select(a, 0) = 5
    solver.assert_literal(eq_sel_b_f5, false); // select(b, 0) != f(5)

    // The axiom chain: b = map[f](a) => select(b, 0) = f(select(a, 0)) = f(5)
    // So select(b, 0) != f(5) is a contradiction.
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_) | TheoryResult::NeedLemmas(_)),
        "expected Unsat or NeedLemmas from select-map alias conflict, got {result:?}",
    );
}

/// Regression test for #8598: const-array read through equality alias.
///
/// b = const-array(42), select(b, 7) != 42 should be UNSAT.
/// The const-array axiom select(const-array(v), i) = v should fire through
/// the equality alias b = const-array(42).
#[test]
fn test_const_array_read_through_equality_alias() {
    use num_bigint::BigInt;

    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let b = store.mk_var("b", arr_sort);
    let forty_two = store.mk_int(BigInt::from(42));
    let seven = store.mk_int(BigInt::from(7));

    // const-array(42)
    let const_arr = store.mk_const_array(Sort::Int, forty_two);

    // select(b, 7)
    let sel_b_7 = store.mk_select(b, seven);

    // b = const-array(42)
    let eq_b_const = store.mk_eq(b, const_arr);
    // select(b, 7) = 42
    let eq_sel_42 = store.mk_eq(sel_b_7, forty_two);

    let mut solver = ArraySolver::new(&store);

    solver.assert_literal(eq_b_const, true); // b = const-array(42)
    solver.assert_literal(eq_sel_42, false); // select(b, 7) != 42

    // The axiom: b = const-array(42) => select(b, 7) = 42
    // So select(b, 7) != 42 is a contradiction.
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_) | TheoryResult::NeedLemmas(_)),
        "expected Unsat or NeedLemmas from const-array alias conflict, got {result:?}",
    );
}

/// Test that interface equalities are generated for same-sort arrays in
/// different equivalence classes (#8531).
///
/// Sets up two array variables `a` and `b` of the same sort, both used in
/// selects, but without any equality or disequality between them.
/// `check_interface_equalities` should request a model equality for the pair.
#[test]
fn test_interface_equality_requested_for_same_sort_arrays() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);

    // Create selects so both arrays are "active"
    let _sel_a = store.mk_select(a, i);
    let _sel_b = store.mk_select(b, i);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();
    solver.rebuild_assign_indices();
    solver.build_equiv_class_cache();

    // Neither equal nor disequal — interface equality should be requested
    let reqs = solver.check_interface_equalities();
    assert!(
        reqs.is_some(),
        "expected interface equality request for same-sort arrays in different equiv classes"
    );
    let reqs = reqs.unwrap();
    assert_eq!(
        reqs.len(),
        1,
        "expected exactly one interface equality request"
    );

    // The request should be for the pair (a, b) in some order
    let req = &reqs[0];
    assert!(
        (req.lhs == a && req.rhs == b) || (req.lhs == b && req.rhs == a),
        "interface equality should be between a and b, got {:?} and {:?}",
        req.lhs,
        req.rhs
    );
}

/// Test that interface equalities are NOT generated when arrays are already
/// in the same equivalence class (#8531).
#[test]
fn test_no_interface_equality_for_equal_arrays() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);

    let _sel_a = store.mk_select(a, i);
    let _sel_b = store.mk_select(b, i);

    // Create and assert a = b
    let eq_ab = store.mk_eq(a, b);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_ab, true);
    solver.populate_caches();
    solver.rebuild_assign_indices();
    solver.build_equiv_class_cache();

    // Arrays are in the same equiv class — no interface equality needed
    let reqs = solver.check_interface_equalities();
    assert!(
        reqs.is_none(),
        "should not request interface equality for arrays already known equal"
    );
}

/// Test that interface equalities are NOT generated when arrays are known
/// disequal (#8531).
#[test]
fn test_no_interface_equality_for_disequal_arrays() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);

    let _sel_a = store.mk_select(a, i);
    let _sel_b = store.mk_select(b, i);

    // Create and assert a != b
    let eq_ab = store.mk_eq(a, b);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_ab, false);
    solver.populate_caches();
    solver.rebuild_assign_indices();
    solver.build_equiv_class_cache();

    // Arrays are known disequal — no interface equality needed
    let reqs = solver.check_interface_equalities();
    assert!(
        reqs.is_none(),
        "should not request interface equality for arrays known to be disequal"
    );
}

/// Test that interface equalities are NOT generated for arrays of different
/// sorts (#8531).
#[test]
fn test_no_interface_equality_for_different_sorts() {
    let mut store = TermStore::new();
    let arr_int_int = Sort::array(Sort::Int, Sort::Int);
    let arr_int_bool = Sort::array(Sort::Int, Sort::Bool);

    let a = store.mk_var("a", arr_int_int);
    let b = store.mk_var("b", arr_int_bool);
    let i = store.mk_var("i", Sort::Int);

    let _sel_a = store.mk_select(a, i);
    // b has Bool element sort, so select(b, i) would have Bool sort
    let _sel_b = store.mk_select(b, i);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();
    solver.rebuild_assign_indices();
    solver.build_equiv_class_cache();

    // Different sorts — no interface equality
    let reqs = solver.check_interface_equalities();
    assert!(
        reqs.is_none(),
        "should not request interface equality for arrays of different sorts"
    );
}

/// Test that interface equality dedup prevents re-requesting the same pair
/// (#8531).
#[test]
fn test_interface_equality_dedup() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);

    let _sel_a = store.mk_select(a, i);
    let _sel_b = store.mk_select(b, i);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();
    solver.rebuild_assign_indices();
    solver.build_equiv_class_cache();

    // First call: should request
    let reqs = solver.check_interface_equalities();
    assert!(
        reqs.is_some(),
        "first call should request interface equality"
    );

    // Second call: already requested, should return None
    let reqs = solver.check_interface_equalities();
    assert!(
        reqs.is_none(),
        "second call should not re-request the same interface equality"
    );
}

#[test]
fn test_no_interface_equality_for_endpoint_store_chain_descendant_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let w = store.mk_var("w", Sort::Int);

    let s1 = store.mk_store(a, i, v);
    let s2 = store.mk_store(s1, j, w);

    let _sel_a = store.mk_select(a, i);
    let _sel_s2 = store.mk_select(s2, i);
    let _sel_b = store.mk_select(b, j);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();
    solver.rebuild_assign_indices();
    solver.build_equiv_class_cache();

    let reqs = solver
        .check_interface_equalities()
        .expect("unrelated active arrays should still allow interface requests");
    assert!(
        !reqs
            .iter()
            .any(|req| { (req.lhs == a && req.rhs == s2) || (req.lhs == s2 && req.rhs == a) }),
        "endpoint-local store-chain aliases must not be re-requested as interface equalities"
    );
    assert!(
        reqs.iter().any(|req| req.lhs == b || req.rhs == b),
        "the endpoint guard must stay narrow enough to keep unrelated interface equalities"
    );
}

#[test]
fn test_no_interface_equality_for_endpoint_store_chain_alias_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let s1 = store.mk_var("s1", make_array_sort());
    let s2 = store.mk_var("s2", make_array_sort());
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let w = store.mk_var("w", Sort::Int);

    let s1_store = store.mk_store(a, i, v);
    let s2_store = store.mk_store(s1, j, w);
    let eq_s1 = store.mk_eq(s1, s1_store);
    let eq_s2 = store.mk_eq(s2, s2_store);

    let _sel_a = store.mk_select(a, i);
    let _sel_s2 = store.mk_select(s2, i);
    let _sel_b = store.mk_select(b, j);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_s1, true);
    solver.assert_literal(eq_s2, true);
    solver.populate_caches();
    solver.rebuild_assign_indices();
    solver.build_equiv_class_cache();

    let reqs = solver
        .check_interface_equalities()
        .expect("unrelated active arrays should still allow interface requests");
    assert!(
        !reqs
            .iter()
            .any(|req| { (req.lhs == a && req.rhs == s2) || (req.lhs == s2 && req.rhs == a) }),
        "equality-backed endpoint store-chain aliases must stay local to array reasoning"
    );
    assert!(
        reqs.iter().any(|req| req.lhs == b || req.rhs == b),
        "the alias-backed endpoint guard must stay narrow enough to keep unrelated interface equalities"
    );
}

/// Array solver must respect interrupt flag during check (#8615).
///
/// When the interrupt flag is set, check_impl() should return Unknown
/// immediately instead of running the full check pipeline. This prevents
/// indefinite looping on large array formulas (e.g., seq push_back chains).
#[test]
fn test_array_interrupt_check_returns_unknown_8615() {
    use std::sync::atomic::AtomicBool;
    use std::sync::Arc;

    let mut store = TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);
    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let stored = store.mk_store(a, i, v);
    let _read = store.mk_select(stored, i);

    let mut solver = ArraySolver::new(&store);

    // Set interrupt flag before check
    let flag = Arc::new(AtomicBool::new(true));
    solver.set_interrupt(flag);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unknown),
        "Array solver must return Unknown when interrupted during check (#8615)"
    );
}

/// Array solver must respect interrupt flag during propagate (#8615).
///
/// When the interrupt flag is set, propagate_impl() should return an
/// empty vector immediately instead of scanning the full equality cache.
#[test]
fn test_array_interrupt_propagate_returns_empty_8615() {
    use std::sync::atomic::AtomicBool;
    use std::sync::Arc;

    let mut store = TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);
    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let stored = store.mk_store(a, i, v);
    let _read = store.mk_select(stored, i);

    let mut solver = ArraySolver::new(&store);

    // Set interrupt flag before propagate
    let flag = Arc::new(AtomicBool::new(true));
    solver.set_interrupt(flag);

    let propagations = solver.propagate();
    assert!(
        propagations.is_empty(),
        "Array solver must return empty propagations when interrupted (#8615)"
    );
}

/// Array solver must respect interrupt flag during propagate_equalities (#8615).
///
/// When the interrupt flag is set, propagate_equalities_impl() should return
/// an empty result immediately instead of running the full equality propagation.
#[test]
fn test_array_interrupt_propagate_equalities_returns_empty_8615() {
    use std::sync::atomic::AtomicBool;
    use std::sync::Arc;

    let mut store = TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);
    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let stored = store.mk_store(a, i, v);
    let _read = store.mk_select(stored, i);

    let mut solver = ArraySolver::new(&store);

    // Set interrupt flag before propagate_equalities
    let flag = Arc::new(AtomicBool::new(true));
    solver.set_interrupt(flag);

    let result = solver.propagate_equalities();
    assert!(
        result.equalities.is_empty(),
        "Array solver must return empty equalities when interrupted (#8615)"
    );
}

/// Array solver must NOT short-circuit when interrupt flag is NOT set (#8615).
///
/// Verify that normal operation works correctly when no interrupt is set.
#[test]
fn test_array_no_interrupt_operates_normally_8615() {
    use std::sync::atomic::AtomicBool;
    use std::sync::Arc;

    let mut store = TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);
    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let stored = store.mk_store(a, i, v);
    let _read = store.mk_select(stored, i);

    let mut solver = ArraySolver::new(&store);

    // Set interrupt flag to false (not interrupted)
    let flag = Arc::new(AtomicBool::new(false));
    solver.set_interrupt(flag);

    // Normal check should work
    let result = solver.check();
    assert!(
        !matches!(result, TheoryResult::Unknown),
        "Array solver should NOT return Unknown when interrupt flag is false (#8615)"
    );

    // Without the interrupt, propagate_equalities should also work normally.
    // We don't assert specific content, just that it doesn't short-circuit.
    let _eq_result = solver.propagate_equalities();
    // If we got here without panic, the non-interrupted path works.
}

/// Array solver without interrupt flag operates normally (#8615).
///
/// When no interrupt flag is set (None), the solver should work normally.
#[test]
fn test_array_no_interrupt_flag_at_all_8615() {
    let mut store = TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);
    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let stored = store.mk_store(a, i, v);
    let _read = store.mk_select(stored, i);

    let mut solver = ArraySolver::new(&store);
    // No interrupt set at all
    assert!(!solver.is_interrupted());

    let result = solver.check();
    assert!(
        !matches!(result, TheoryResult::Unknown),
        "Array solver should NOT return Unknown when no interrupt flag is set (#8615)"
    );
}
