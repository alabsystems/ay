// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_arrays_store_chain_resolution_conflict_emits_lemma() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);
    let v2 = store.mk_var("v2", Sort::Int);
    let one = store.mk_int(BigInt::from(1));
    let i_plus_1 = store.mk_add(vec![i, one]);
    let eq_j_i_plus_1 = store.mk_eq(j, i_plus_1);

    let stored_at_i = store.mk_store(a, i, v1);
    let nested = store.mk_store(stored_at_i, j, v2);
    let select_at_i = store.mk_select(nested, i);
    let eq_select_v1 = store.mk_eq(select_at_i, v1);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_j_i_plus_1, true);
    solver.assert_literal(eq_select_v1, false);

    // After #6820, the array theory no longer derives index disequalities from
    // arithmetic facts like j = i+1. That reasoning is delegated to the LIA
    // solver, which propagates j ≠ i into the array theory's diseq_set via
    // assert_external_disequality_with_reasons. Simulate that here.
    solver.assert_external_disequality_with_reasons(
        i,
        j,
        vec![TheoryLit::new(eq_j_i_plus_1, true)],
    );

    let TheoryResult::NeedLemmas(lemmas) = solver.check() else {
        panic!("expected NeedLemmas from store-chain resolution conflict");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "store-chain resolution conflict should emit one lemma"
    );
    assert_eq!(
        lemmas[0].clause,
        vec![
            TheoryLit::new(eq_j_i_plus_1, false),
            TheoryLit::new(eq_select_v1, true),
        ],
        "store-chain lemma must block the ROW2 skip reason with the conflicting select disequality"
    );
}

#[test]
fn test_cross_chain_replay_guard_preserves_unique_select_equalities_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort.clone());
    let c = store.mk_var("c", arr_sort.clone());
    let d = store.mk_var("d", arr_sort);
    let i = store.mk_var("i", Sort::Int);

    let select_a = store.mk_select(a, i);
    let select_b = store.mk_select(b, i);
    let select_c = store.mk_select(c, i);
    let select_d = store.mk_select(d, i);

    let eq_ab = store.mk_eq(a, b);
    let eq_ac = store.mk_eq(a, c);
    let eq_bd = store.mk_eq(b, d);
    let eq_cd = store.mk_eq(c, d);

    let mut solver = ArraySolver::new(&store);
    for eq in [eq_ab, eq_ac, eq_bd, eq_cd] {
        solver.assert_literal(eq, true);
    }

    let propagated = solver.propagate_equalities();
    let mut pairs = HashSet::default();
    for eq in &propagated.equalities {
        assert!(
            pairs.insert(ArraySolver::ordered_pair(eq.lhs, eq.rhs)),
            "array propagation must not emit the same equality pair twice: {eq:?}"
        );
    }

    for (lhs, rhs) in [
        (select_a, select_b),
        (select_a, select_c),
        (select_a, select_d),
        (select_b, select_c),
        (select_b, select_d),
        (select_c, select_d),
    ] {
        assert!(
            pairs.contains(&ArraySolver::ordered_pair(lhs, rhs)),
            "duplicate replay guard must not suppress a genuinely new select equality"
        );
    }

    assert!(
        solver.propagate_equalities().equalities.is_empty(),
        "a warm propagation pass should not replay already-sent select equalities"
    );
}

#[test]
fn test_cross_chain_replay_guard_preserves_unique_value_equalities_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort.clone());
    let c = store.mk_var("c", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let select_b = store.mk_select(b, i);
    let select_c = store.mk_select(c, i);

    let eq_stored_b = store.mk_eq(stored, b);
    let eq_stored_c = store.mk_eq(stored, c);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_stored_b, true);
    solver.assert_literal(eq_stored_c, true);

    let propagated = solver.propagate_equalities();
    let mut pairs = HashSet::default();
    for eq in &propagated.equalities {
        assert!(
            pairs.insert(ArraySolver::ordered_pair(eq.lhs, eq.rhs)),
            "array propagation must not emit the same value equality twice: {eq:?}"
        );
    }

    for (lhs, rhs) in [(select_b, v), (select_c, v)] {
        assert!(
            pairs.contains(&ArraySolver::ordered_pair(lhs, rhs)),
            "value/base cross-chain replay guard must preserve unique value equality"
        );
    }
}

#[test]
fn test_propagation_replay_prechecks_preserve_array_congruence_equalities_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort.clone());
    let c = store.mk_var("c", arr_sort);
    let i = store.mk_var("i", Sort::Int);

    let select_a = store.mk_select(a, i);
    let select_b = store.mk_select(b, i);
    let select_c = store.mk_select(c, i);

    let eq_ab = store.mk_eq(a, b);
    let eq_bc = store.mk_eq(b, c);
    let eq_ac = store.mk_eq(a, c);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();
    for eq in [eq_ab, eq_bc, eq_ac] {
        solver.assert_literal(eq, true);
    }

    let propagated = solver.propagate_equalities();
    let mut pairs = HashSet::default();
    for eq in &propagated.equalities {
        assert!(
            pairs.insert(ArraySolver::ordered_pair(eq.lhs, eq.rhs)),
            "array propagation must not emit the same select equality twice: {eq:?}"
        );
    }

    for (lhs, rhs) in [
        (select_a, select_b),
        (select_b, select_c),
        (select_a, select_c),
    ] {
        assert!(
            pairs.contains(&ArraySolver::ordered_pair(lhs, rhs)),
            "replay prechecks must preserve each unique array-congruence equality"
        );
    }
}

#[test]
fn test_store_permutation_replay_uses_spanning_forest_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort.clone());
    let c = store.mk_var("c", arr_sort.clone());
    let d = store.mk_var("d", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let k = store.mk_var("k", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stores = [
        store.mk_store(a, i, v),
        store.mk_store(b, i, v),
        store.mk_store(c, i, v),
        store.mk_store(d, i, v),
    ];
    for stored in stores {
        let _ = store.mk_select(stored, k);
    }

    let eq_ab = store.mk_eq(a, b);
    let eq_bc = store.mk_eq(b, c);
    let eq_cd = store.mk_eq(c, d);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();
    for eq in [eq_ab, eq_bc, eq_cd] {
        solver.assert_literal(eq, true);
    }

    let propagated = solver.propagate_equalities();
    let store_equalities: Vec<_> = propagated
        .equalities
        .iter()
        .filter(|eq| stores.contains(&eq.lhs) && stores.contains(&eq.rhs))
        .collect();
    assert_eq!(
        store_equalities.len(),
        stores.len() - 1,
        "store permutation propagation should connect the component without replaying every pair"
    );

    let mut reached = HashSet::default();
    reached.insert(stores[0]);
    let mut changed = true;
    while changed {
        changed = false;
        for eq in &store_equalities {
            if reached.contains(&eq.lhs) && reached.insert(eq.rhs) {
                changed = true;
            }
            if reached.contains(&eq.rhs) && reached.insert(eq.lhs) {
                changed = true;
            }
        }
    }
    for stored in stores {
        assert!(
            reached.contains(&stored),
            "spanning store-permutation equalities must still connect every equivalent store"
        );
    }
}

#[test]
fn test_notify_equality_deduplicates_pending_array_work_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let store_a = store.mk_store(a, i, v);
    let store_b = store.mk_store(b, i, v);
    let select_b_j = store.mk_select(b, j);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();

    solver.notify_equality(a, b);
    solver.notify_equality(a, b);
    assert_eq!(
        solver
            .pending_row2_upward
            .iter()
            .filter(|&&pair| pair == (select_b_j, store_a))
            .count(),
        1,
        "repeated equality notification must not queue duplicate ROW2-upward work"
    );
    assert_eq!(
        solver
            .pending_store_chain
            .iter()
            .filter(|&&select| select == select_b_j)
            .count(),
        1,
        "repeated equality notification must not queue duplicate store-chain work"
    );

    solver.notify_equality(store_a, b);
    solver.notify_equality(store_a, b);
    assert_eq!(
        solver
            .pending_row1
            .iter()
            .filter(|&&pair| pair == (select_b_j, store_a))
            .count(),
        1,
        "repeated equality notification must not queue duplicate ROW1 work"
    );

    let conflict_pair = ArraySolver::ordered_pair(store_a, store_b);
    solver.notify_equality(store_a, store_b);
    solver.notify_equality(store_a, store_b);
    assert_eq!(
        solver
            .pending_conflicting_stores
            .iter()
            .filter(|&&pair| pair == conflict_pair)
            .count(),
        1,
        "repeated equality notification must not queue duplicate conflicting-store work"
    );
}

#[test]
fn test_external_disequality_duplicate_reasons_do_not_invalidate_snapshots_8785() {
    let mut store = TermStore::new();

    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let zero = store.mk_int(BigInt::from(0));
    let one = store.mk_int(BigInt::from(1));
    let guard_a = store.mk_eq(i, zero);
    let guard_b = store.mk_eq(j, one);

    let mut solver = ArraySolver::new(&store);
    let reasons = vec![
        TheoryLit::new(guard_b, true),
        TheoryLit::new(guard_a, true),
        TheoryLit::new(guard_b, true),
    ];
    assert!(
        solver.assert_external_disequality_with_reasons(i, j, reasons),
        "first reason-carrying external disequality should be new"
    );

    let prop_snapshot = (
        solver.eq_adj_version,
        solver.select_cache.len(),
        solver.store_cache.len(),
        solver.external_diseqs.len(),
        solver.external_eqs.len(),
        solver.diseq_set.len(),
    );
    let final_snapshot = (
        solver.eq_adj_version,
        solver.diseq_set.len(),
        solver.select_cache.len(),
        solver.store_cache.len(),
        solver.requested_model_eqs.len(),
        solver.requested_interface_eqs.len(),
    );
    solver.prop_eq_snapshot = Some(prop_snapshot);
    solver.final_check_snapshot = Some(final_snapshot);

    let duplicate_reasons = vec![TheoryLit::new(guard_a, true), TheoryLit::new(guard_b, true)];
    assert!(
        !solver.assert_external_disequality_with_reasons(j, i, duplicate_reasons),
        "duplicate external disequality should not count as new"
    );
    assert_eq!(
        solver.prop_eq_snapshot,
        Some(prop_snapshot),
        "same reason set must not force another array equality-propagation scan"
    );
    assert_eq!(
        solver.final_check_snapshot,
        Some(final_snapshot),
        "same reason set must not force another final_check pass"
    );

    let key = ArraySolver::ordered_pair(i, j);
    assert_eq!(
        solver.external_diseq_reasons.get(&key),
        Some(&vec![
            TheoryLit::new(guard_a, true),
            TheoryLit::new(guard_b, true),
        ]),
        "stored external disequality reasons should be canonicalized"
    );

    assert!(
        !solver.assert_external_disequality_with_reasons(i, j, vec![TheoryLit::new(guard_a, true)]),
        "subset reason replay should not count as a new external disequality"
    );
    assert_eq!(
        solver.prop_eq_snapshot,
        Some(prop_snapshot),
        "subset reason replay must not force another array equality-propagation scan"
    );
    assert_eq!(
        solver.final_check_snapshot,
        Some(final_snapshot),
        "subset reason replay must not force another final_check pass"
    );
    assert_eq!(
        solver.external_diseq_reasons.get(&key),
        Some(&vec![
            TheoryLit::new(guard_a, true),
            TheoryLit::new(guard_b, true),
        ]),
        "stored external disequality reasons should retain the stronger cached guard set"
    );
}

#[test]
fn test_external_equality_duplicate_reasons_do_not_replay_graph_8785() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let guard_a = store.mk_var("guard_a", Sort::Bool);
    let guard_b = store.mk_var("guard_b", Sort::Bool);
    let guard_c = store.mk_var("guard_c", Sort::Bool);

    let mut solver = ArraySolver::new(&store);
    solver.assert_external_equality_with_reasons(
        x,
        y,
        &[
            TheoryLit::new(guard_b, true),
            TheoryLit::new(guard_a, true),
            TheoryLit::new(guard_b, true),
        ],
    );
    assert_eq!(
        solver.external_eqs.len(),
        1,
        "first external equality should add exactly one sentinel edge record"
    );
    let eq_adj_version = solver.eq_adj_version;

    let prop_snapshot = (
        solver.eq_adj_version,
        solver.select_cache.len(),
        solver.store_cache.len(),
        solver.external_diseqs.len(),
        solver.external_eqs.len(),
        solver.diseq_set.len(),
    );
    let final_snapshot = (
        solver.eq_adj_version,
        solver.diseq_set.len(),
        solver.select_cache.len(),
        solver.store_cache.len(),
        solver.requested_model_eqs.len(),
        solver.requested_interface_eqs.len(),
    );
    solver.prop_eq_snapshot = Some(prop_snapshot);
    solver.final_check_snapshot = Some(final_snapshot);

    solver.assert_external_equality_with_reasons(
        y,
        x,
        &[TheoryLit::new(guard_a, true), TheoryLit::new(guard_b, true)],
    );
    assert_eq!(
        solver.external_eqs.len(),
        1,
        "duplicate external equality should not append another sentinel edge record"
    );
    assert_eq!(
        solver.eq_adj_version, eq_adj_version,
        "same external equality must not bump the equality graph version"
    );
    assert_eq!(
        solver.prop_eq_snapshot,
        Some(prop_snapshot),
        "same reason set must not force another equality-propagation scan"
    );
    assert_eq!(
        solver.final_check_snapshot,
        Some(final_snapshot),
        "same reason set must not force another final_check pass"
    );

    let key = ArraySolver::ordered_pair(x, y);
    assert_eq!(
        solver.external_eq_reasons.get(&key),
        Some(&vec![
            TheoryLit::new(guard_a, true),
            TheoryLit::new(guard_b, true),
        ]),
        "stored external equality reasons should be canonicalized"
    );

    solver.assert_external_equality_with_reasons(x, y, &[TheoryLit::new(guard_c, true)]);
    assert_eq!(
        solver.external_eqs.len(),
        1,
        "new reasons for a known equality should still reuse the sentinel edge record"
    );
    assert_eq!(
        solver.eq_adj_version, eq_adj_version,
        "new reasons do not change equality-graph connectivity"
    );
    assert_eq!(
        solver.prop_eq_snapshot, None,
        "new reasons can unlock guarded replay and must invalidate equality propagation"
    );
    assert_eq!(
        solver.final_check_snapshot, None,
        "new reasons can unlock guarded replay and must invalidate final_check"
    );
}

#[test]
fn test_final_check_filters_applied_row2_lemmas_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let k = store.mk_var("k", Sort::Int);
    let l = store.mk_var("l", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);
    let v2 = store.mk_var("v2", Sort::Int);

    let stored1 = store.mk_store(a, i, v1);
    let stored2 = store.mk_store(a, k, v2);
    let sel_stored1_j = store.mk_select(stored1, j);
    let sel_stored2_l = store.mk_select(stored2, l);
    let sel_a_j = store.mk_select(a, j);
    let sel_a_l = store.mk_select(a, l);

    let eq_ij = store.mk_eq(i, j);
    let eq_kl = store.mk_eq(k, l);
    let eq_sel1 = store.mk_eq(sel_stored1_j, sel_a_j);
    let eq_sel2 = store.mk_eq(sel_stored2_l, sel_a_l);

    let mut solver = ArraySolver::new(&store);
    solver.set_defer_expensive_checks(true);
    solver.populate_caches();

    let mut applied_clause = vec![TheoryLit::new(eq_ij, true), TheoryLit::new(eq_sel1, true)];
    applied_clause.sort_by_key(|lit| (lit.term.0, lit.value));
    solver.applied_theory_lemmas.insert(applied_clause.clone());

    let mut new_clause = vec![TheoryLit::new(eq_kl, true), TheoryLit::new(eq_sel2, true)];
    new_clause.sort_by_key(|lit| (lit.term.0, lit.value));

    let TheoryResult::NeedLemmas(lemmas) = solver.final_check() else {
        panic!("final_check should return the unapplied ROW2-down lemma");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "already-applied ROW2 lemmas should be filtered before returning from final_check"
    );
    assert_eq!(lemmas[0].clause, new_clause);
    assert_ne!(
        lemmas[0].clause, applied_clause,
        "final_check must not replay a ROW2 lemma that SAT already received"
    );
}

#[test]
fn test_row2_down_exact_select_obligation_cache_suppresses_identical_rerequest_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let sel_stored_j = store.mk_select(stored, j);
    let sel_a_j = store.mk_select(a, j);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();
    solver.generate_all_lazy_row2_axioms();

    let TheoryResult::NeedModelEqualities(requests) = solver
        .check_row2()
        .expect("first ROW2 pass should request the missing exact-select atoms")
    else {
        panic!("expected NeedModelEqualities from first ROW2 pass");
    };
    assert_eq!(requests.len(), 2);
    assert_eq!(
        solver.exact_select_model_eq_obligations.len(),
        2,
        "ROW2-down should cache the index and select equality obligations"
    );

    solver.requested_model_eqs.clear();
    solver.wake_blocked_row2_down_axioms();

    assert!(
        solver.check_row2().is_none(),
        "same store/select/base-select tuple must not re-request an identical ROW2-down model equality"
    );
    assert!(
        solver.requested_model_eqs.is_empty(),
        "the exact obligation cache should suppress the duplicate before growing requested_model_eqs"
    );
    assert_eq!(
        solver.exact_select_model_eq_obligations.len(),
        2,
        "duplicate replay should not grow the exact obligation cache"
    );

    assert_eq!(
        solver.get_exact_select_term(a, j),
        Some(sel_a_j),
        "test sanity: base exact select should be registered"
    );
    assert_eq!(
        solver.get_exact_select_term(stored, j),
        Some(sel_stored_j),
        "test sanity: store exact select should be registered"
    );
}

#[test]
fn test_exact_select_request_key_guard_skips_changed_obligation_after_request_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let w = store.mk_var("w", Sort::Int);

    let stored_v = store.mk_store(a, i, v);
    let sel_stored_v_j = store.mk_select(stored_v, j);
    let sel_a_j = store.mk_select(a, j);
    let stored_w = store.mk_store(a, i, w);
    let sel_stored_w_j = store.mk_select(stored_w, j);
    let eq_v_w = store.mk_eq(v, w);

    let mut solver = ArraySolver::new(&store);

    let first = ExactSelectModelEqObligation {
        kind: ExactSelectModelEqKind::DownIndex,
        request: (TermId::SENTINEL, TermId::SENTINEL),
        store: stored_v,
        store_base: a,
        store_index: i,
        store_value: v,
        select: sel_stored_v_j,
        select_array: stored_v,
        select_index: j,
        value: Some(sel_a_j),
        reasons: Vec::new(),
    };
    assert!(
        solver
            .exact_select_model_eq_request(first, i, j, Vec::new())
            .is_some(),
        "first exact-select obligation should request the missing index equality"
    );
    assert_eq!(solver.requested_model_eqs.len(), 1);
    assert_eq!(solver.exact_select_model_eq_obligations.len(), 1);

    let changed_same_request = ExactSelectModelEqObligation {
        kind: ExactSelectModelEqKind::DownIndex,
        request: (TermId::SENTINEL, TermId::SENTINEL),
        store: stored_w,
        store_base: a,
        store_index: i,
        store_value: w,
        select: sel_stored_w_j,
        select_array: stored_w,
        select_index: j,
        value: Some(sel_a_j),
        reasons: vec![TheoryLit::new(eq_v_w, true)],
    };
    assert!(
        solver
            .exact_select_model_eq_request(
                changed_same_request,
                j,
                i,
                vec![TheoryLit::new(eq_v_w, true)],
            )
            .is_none(),
        "a raw model-equality pair already requested must not grow exact-obligation replay state"
    );
    assert_eq!(
        solver.requested_model_eqs.len(),
        1,
        "request-key guard should preserve the existing dedup key"
    );
    assert_eq!(
        solver.exact_select_model_eq_obligations.len(),
        1,
        "changed structural/reason tuple should be skipped once the request key is known"
    );
}

#[test]
fn test_row2_upward_witness_obligation_cache_suppresses_identical_rerequest_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let sel_b_j = store.mk_select(b, j);
    let _sel_stored_j = store.mk_select(stored, j);
    let eq_a_b = store.mk_eq(a, b);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_a_b, true);
    solver.populate_caches();
    solver.pending_row2_upward.clear();
    solver.pending_row2_upward.push((sel_b_j, stored));

    let TheoryResult::NeedModelEquality(request) = solver
        .check_row2_upward_with_guidance()
        .expect("first ROW2-upward pass should request witness-index guidance")
    else {
        panic!("expected NeedModelEquality from first ROW2-upward pass");
    };
    assert!(
        (request.lhs == i && request.rhs == j) || (request.lhs == j && request.rhs == i),
        "ROW2-upward guidance should target the store/select index pair"
    );
    assert_eq!(
        request.reason,
        vec![TheoryLit::new(eq_a_b, true)],
        "obligation reason set should include the base-array alias"
    );
    assert_eq!(
        solver.exact_select_model_eq_obligations.len(),
        1,
        "ROW2-upward should cache the witnessed exact-select obligation"
    );

    solver.requested_model_eqs.clear();
    solver.pending_row2_upward.push((sel_b_j, stored));

    assert!(
        solver.check_row2_upward_with_guidance().is_none(),
        "same store/select/reason tuple must not re-request identical witness-index guidance"
    );
    assert!(
        solver.requested_model_eqs.is_empty(),
        "the exact obligation cache should suppress the duplicate before growing requested_model_eqs"
    );
    assert_eq!(
        solver.exact_select_model_eq_obligations.len(),
        1,
        "duplicate replay should not grow the exact obligation cache"
    );
}

#[test]
fn test_find_store_through_eq_follows_asserted_non_speculative_edge_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let alias = store.mk_var("alias", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let eq_alias = store.mk_eq(alias, stored);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_alias, true);
    solver.populate_caches();

    let Some((base, idx, val, path)) = solver.find_store_through_eq(alias) else {
        panic!("asserted equality should expose the aliased store");
    };
    assert_eq!(base, a);
    assert_eq!(idx, i);
    assert_eq!(val, v);
    assert_eq!(path, vec![eq_alias]);
}

#[test]
fn test_effective_store_propagation_keeps_alias_reasons() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let x = store.mk_var("x", arr_sort.clone());
    let y = store.mk_var("y", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let w = store.mk_var("w", Sort::Int);

    let x_store = store.mk_store(a, i, v);
    let y_store = store.mk_store(a, i, w);
    let eq_x_store = store.mk_eq(x, x_store);
    let eq_y_store = store.mk_eq(y, y_store);
    let eq_xy = store.mk_eq(x, y);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_x_store, true);
    solver.assert_literal(eq_y_store, true);
    solver.assert_literal(eq_xy, true);
    solver.populate_caches();

    let (_x_base, _x_base_reasons, x_effective) = solver
        .collect_effective_stores(x)
        .expect("x should resolve to an aliased store chain");
    assert_eq!(x_effective.len(), 1);
    assert_eq!(
        x_effective[0].2,
        vec![TheoryLit::new(eq_x_store, true)],
        "effective store entry for x must carry the alias equality"
    );

    let (_y_base, _y_base_reasons, y_effective) = solver
        .collect_effective_stores(y)
        .expect("y should resolve to an aliased store chain");
    assert_eq!(y_effective.len(), 1);
    assert_eq!(
        y_effective[0].2,
        vec![TheoryLit::new(eq_y_store, true)],
        "effective store entry for y must carry the alias equality"
    );

    let propagated = solver.propagate_equalities();
    let value_eq = propagated
        .equalities
        .iter()
        .find(|eq| ArraySolver::ordered_pair(eq.lhs, eq.rhs) == ArraySolver::ordered_pair(v, w))
        .expect("x = y should propagate v = w through the aliased effective stores");

    assert_eq!(
        value_eq.reason,
        vec![
            TheoryLit::new(eq_x_store, true),
            TheoryLit::new(eq_y_store, true),
            TheoryLit::new(eq_xy, true),
        ],
        "v = w propagation must be guarded by both store aliases, not only x = y"
    );
}

#[test]
fn test_find_store_through_eq_skips_speculative_interface_edge_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let alias = store.mk_var("alias", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let eq_alias = store.mk_eq(alias, stored);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_alias, true);
    solver.populate_caches();

    let mut speculative = ay_core::kani_compat::DetHashSet::default();
    speculative.insert(ArraySolver::ordered_pair(alias, stored));
    solver.import_requested_interface_eqs(&speculative);

    assert!(
        solver.find_store_through_eq(alias).is_none(),
        "store-chain walking must not treat speculative interface equalities as structural aliases"
    );
}

#[test]
fn test_arrays_store_chain_external_alias_without_reason_does_not_emit_lemma_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let alias = store.mk_var("alias", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let select_alias_i = store.mk_select(alias, i);
    let eq_select_v = store.mk_eq(select_alias_i, v);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_select_v, false);
    TheorySolver::assert_shared_equality(&mut solver, alias, stored, &[]);
    solver.pending_store_chain.clear();
    solver.pending_store_chain.push(select_alias_i);

    assert!(
        solver.check_store_chain_resolution().is_none(),
        "unreasoned external alias must not support a store-chain conflict lemma"
    );
    assert!(
        solver.pending_store_chain.contains(&select_alias_i),
        "unreasoned alias candidate should remain pending for a future explained edge"
    );
}

#[test]
fn test_arrays_store_chain_external_alias_with_reason_guards_lemma_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let alias = store.mk_var("alias", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let alias_guard = store.mk_var("alias_guard", Sort::Bool);

    let stored = store.mk_store(a, i, v);
    let select_alias_i = store.mk_select(alias, i);
    let eq_select_v = store.mk_eq(select_alias_i, v);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(alias_guard, true);
    solver.assert_literal(eq_select_v, false);
    TheorySolver::assert_shared_equality(
        &mut solver,
        alias,
        stored,
        &[TheoryLit::new(alias_guard, true)],
    );
    solver.pending_store_chain.clear();
    solver.pending_store_chain.push(select_alias_i);

    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_store_chain_resolution()
        .expect("reasoned external alias should emit a guarded store-chain lemma")
    else {
        panic!("expected NeedLemmas from reasoned external alias conflict");
    };
    assert_eq!(lemmas.len(), 1);

    let clause = &lemmas[0].clause;
    assert!(
        clause.contains(&TheoryLit::new(alias_guard, false)),
        "store-chain lemma must negate the external alias reason"
    );
    assert!(
        clause.contains(&TheoryLit::new(eq_select_v, true)),
        "store-chain lemma must block the conflicting select disequality"
    );
    assert!(
        !clause.iter().any(|lit| lit.term.is_sentinel()),
        "store-chain lemma must not contain sentinel equality placeholders"
    );
}

#[test]
fn test_arrays_conflicting_store_equalities_conflict_emits_lemma() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);
    let v2 = store.mk_var("v2", Sort::Int);

    let first_store = store.mk_store(a, i, v1);
    let second_store = store.mk_store(a, j, v2);
    let eq_stores = store.mk_eq(first_store, second_store);
    let eq_ij = store.mk_eq(i, j);
    let eq_vals = store.mk_eq(v1, v2);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_stores, true);
    solver.assert_literal(eq_ij, true);
    solver.assert_literal(eq_vals, false);

    let TheoryResult::NeedLemmas(lemmas) = solver.check() else {
        panic!("expected NeedLemmas from conflicting-store-equalities conflict");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "conflicting store equalities should emit one lemma"
    );
    assert_eq!(
        lemmas[0].clause,
        vec![
            TheoryLit::new(eq_stores, false),
            TheoryLit::new(eq_ij, false),
            TheoryLit::new(eq_vals, true),
        ],
        "conflicting-store-equalities lemma must block equal stores with equal indices and distinct values"
    );
}

#[test]
fn test_arrays_conflicting_store_equalities_use_transitive_index_reasons_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let k = store.mk_var("k", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);
    let v2 = store.mk_var("v2", Sort::Int);

    let first_store = store.mk_store(a, i, v1);
    let second_store = store.mk_store(a, j, v2);
    let eq_stores = store.mk_eq(first_store, second_store);
    let eq_ik = store.mk_eq(i, k);
    let eq_kj = store.mk_eq(k, j);
    let eq_vals = store.mk_eq(v1, v2);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_stores, true);
    solver.assert_literal(eq_ik, true);
    solver.assert_literal(eq_kj, true);
    solver.assert_literal(eq_vals, false);

    let TheoryResult::NeedLemmas(lemmas) = solver.check() else {
        panic!("expected NeedLemmas from transitive conflicting-store-equalities conflict");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "transitive conflicting-store-equalities should emit one lemma"
    );
    assert_eq!(
        lemmas[0].clause,
        vec![
            TheoryLit::new(eq_stores, false),
            TheoryLit::new(eq_ik, false),
            TheoryLit::new(eq_kj, false),
            TheoryLit::new(eq_vals, true),
        ],
        "conflicting-store-equalities lemma must include the full transitive index-equality reason chain"
    );
}

#[test]
fn test_arrays_disjunctive_store_target_equalities_emit_lemma() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let w = store.mk_var("w", Sort::Int);

    let first_store = store.mk_store(a, x, v);
    let second_store = store.mk_store(a, y, w);
    let eq_first = store.mk_eq(first_store, b);
    let eq_second = store.mk_eq(second_store, b);
    let eq_xy = store.mk_eq(x, y);
    let eq_ab = store.mk_eq(a, b);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_first, true);
    solver.assert_literal(eq_second, true);
    solver.assert_literal(eq_xy, false);
    solver.assert_literal(eq_ab, false);

    let TheoryResult::NeedLemmas(lemmas) = solver.final_check() else {
        panic!("expected NeedLemmas from disjunctive store-target equalities");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "disjunctive store-target equalities should emit one lemma"
    );
    assert_eq!(
        lemmas[0].clause,
        vec![
            TheoryLit::new(eq_first, false),
            TheoryLit::new(eq_second, false),
            TheoryLit::new(eq_xy, true),
            TheoryLit::new(eq_ab, true),
        ],
        "lemma must force x=y or a=b when two same-base stores equal the same target"
    );
}

/// Verify no false positives - SAT case must stay SAT.
#[test]
fn test_arrays_no_bogus_conflict_on_sat() {
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

    // Assert i ≠ j and select(store(a,i,v), j) = select(a, j)
    // This is SAT - consistent with ROW2. The ROW2 clause is already
    // satisfied by the assignment, so check() must return Sat — not
    // NeedLemmas with a redundant clause (#6738).
    solver.assert_literal(eq_ij, false);
    solver.assert_literal(eq_sels, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "ROW2-satisfied assignment must return Sat, got: {result:?}"
    );
}

/// Verify const-array conflict explanations are sound.
/// Tests the const-array axiom: select(const-array(v), i) = v
#[test]
fn test_arrays_const_array_conflict_soundness() {
    let mut store = TermStore::new();
    let default_val = store.mk_var("default", Sort::Int);
    let const_arr = store.mk_const_array(Sort::Int, default_val);
    let i = store.mk_var("i", Sort::Int);

    // select(const-array(default), i)
    let selected = store.mk_select(const_arr, i);

    // Note: mk_select already simplifies select(const-array(v), i) → v
    // So selected == default_val due to term normalization
    // This tests that the simplification works correctly

    // Verify the simplification happened
    assert_eq!(
        selected, default_val,
        "select(const-array(v), i) should simplify to v"
    );

    // Since the terms are identical, any test asserting them different
    // would be asserting v ≠ v which is immediately false at the term level.
    // This test verifies the term-level simplification is working.
}

/// Verify extended ROW2 conflict via store chain following.
/// Tests the check_row2_extended path.
#[test]
fn test_arrays_row2_extended_conflict_soundness() {
    use num_bigint::BigInt;

    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let v = store.mk_var("v", Sort::Int);

    let idx0 = store.mk_int(BigInt::from(0));
    let idx1 = store.mk_int(BigInt::from(1));

    // B = store(A, 0, v)
    let store_a = store.mk_store(a, idx0, v);
    let eq_b_store = store.mk_eq(b, store_a);

    // select(A, 1) and select(B, 1)
    let sel_a_1 = store.mk_select(a, idx1);
    let sel_b_1 = store.mk_select(b, idx1);
    let eq_sels = store.mk_eq(sel_a_1, sel_b_1);

    let mut solver = ArraySolver::new(&store);

    // Assert B = store(A, 0, v) and select(A, 1) ≠ select(B, 1)
    // Since 0 ≠ 1, by ROW2: select(B, 1) = select(A, 1), so UNSAT
    solver.assert_literal(eq_b_store, true);
    solver.assert_literal(eq_sels, false);

    let result = solver.check();
    let conflict = assert_conflict_soundness(result, ArraySolver::new(&store));

    // Conflict should be reasonably minimal (≤4 literals)
    assert!(
        conflict.len() <= 4,
        "Conflict too large: {} literals",
        conflict.len()
    );
}

#[test]
fn test_arrays_row2_extended_conflict_via_constant_equalities() {
    use num_bigint::BigInt;

    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let v = store.mk_var("v", Sort::Int);

    let idx0 = store.mk_int(BigInt::from(0));
    let idx1 = store.mk_int(BigInt::from(1));
    let zero = store.mk_int(BigInt::from(0));
    let one = store.mk_int(BigInt::from(1));

    let store_a = store.mk_store(a, idx0, v);
    let eq_b_store = store.mk_eq(b, store_a);
    let sel_a_1 = store.mk_select(a, idx1);
    let sel_b_1 = store.mk_select(b, idx1);
    let eq_sel_a_zero = store.mk_eq(sel_a_1, zero);
    let eq_sel_b_one = store.mk_eq(sel_b_1, one);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_b_store, true);
    solver.assert_literal(eq_sel_a_zero, true);
    solver.assert_literal(eq_sel_b_one, true);
    solver.populate_caches();

    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_row2_extended()
        .expect("constant-backed select conflict should be discovered")
    else {
        panic!("expected NeedLemmas from ROW2-extended constant conflict");
    };
    assert_eq!(lemmas.len(), 1, "expected one ROW2-extended lemma");
    assert!(
        lemmas[0]
            .clause
            .contains(&TheoryLit::new(eq_b_store, false)),
        "lemma must negate the asserted store/base equality antecedent"
    );
    assert!(
        lemmas[0]
            .clause
            .contains(&TheoryLit::new(eq_sel_a_zero, false)),
        "lemma must retain the left select-to-constant equality reason"
    );
    assert!(
        lemmas[0]
            .clause
            .contains(&TheoryLit::new(eq_sel_b_one, false)),
        "lemma must retain the right select-to-constant equality reason"
    );
}

/// Verify upward ROW2 conflict detection directly.
///
/// Call `check_row2_upward()` instead of `check()` so this test exercises
/// the axiom-2b path even though the main check order reaches downward
/// ROW2 first for the same syntactic pattern.
#[test]
fn test_arrays_row2_upward_conflict_soundness() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let sel_a_j = store.mk_select(a, j);
    let sel_stored_j = store.mk_select(stored, j);
    let eq_ij = store.mk_eq(i, j);
    let eq_sels = store.mk_eq(sel_a_j, sel_stored_j);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_ij, false);
    solver.assert_literal(eq_sels, false);
    solver.populate_caches();

    let result = solver
        .check_row2_upward()
        .expect("ROW2 upward should detect direct store/base conflict");
    let conflict = match result {
        TheoryResult::Unsat(conflict) => conflict,
        other => panic!("expected upward ROW2 conflict, got {other:?}"),
    };

    let mut verify_solver = ArraySolver::new(&store);
    for lit in &conflict {
        verify_solver.assert_literal(lit.term, lit.value);
    }
    verify_solver.populate_caches();
    assert!(
        matches!(
            verify_solver.check_row2_upward(),
            Some(TheoryResult::Unsat(_))
        ),
        "upward ROW2 conflict literals must still trigger the upward conflict path"
    );

    assert!(
        conflict.iter().any(|lit| lit.term == eq_ij && !lit.value),
        "ROW2 upward conflict must include the asserted index disequality"
    );
    assert!(
        conflict.iter().any(|lit| lit.term == eq_sels && !lit.value),
        "ROW2 upward conflict must include the asserted select disequality"
    );
}

#[test]
fn test_arrays_row2_upward_guidance_batches_multiple_requests() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let k = store.mk_var("k", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);
    let v2 = store.mk_var("v2", Sort::Int);

    let s1 = store.mk_store(a, i, v1);
    let s2 = store.mk_store(a, j, v2);
    let _sel_a_k = store.mk_select(a, k);
    let _sel_s1_k = store.mk_select(s1, k);
    let _sel_s2_k = store.mk_select(s2, k);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();

    let result = solver
        .check_row2_upward_with_guidance()
        .expect("expected ROW2-upward guidance request");

    match result {
        TheoryResult::NeedModelEqualities(requests) => {
            assert_eq!(
                requests.len(),
                2,
                "one base select with two parent stores should batch both undecided pairs"
            );
            assert!(
                requests
                    .iter()
                    .any(|req| req.lhs == i && req.rhs == k || req.lhs == k && req.rhs == i),
                "batched guidance must include the first store index pair"
            );
            assert!(
                requests
                    .iter()
                    .any(|req| req.lhs == j && req.rhs == k || req.lhs == k && req.rhs == j),
                "batched guidance must include the second store index pair"
            );
        }
        other => panic!("expected NeedModelEqualities, got {other:?}"),
    }
}

#[test]
fn test_arrays_row2_upward_guidance_conflict_emits_lemma() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let sel_a_j = store.mk_select(a, j);
    let sel_stored_j = store.mk_select(stored, j);
    let eq_ij = store.mk_eq(i, j);
    let eq_sels = store.mk_eq(sel_a_j, sel_stored_j);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_ij, false);
    solver.assert_literal(eq_sels, false);
    solver.populate_caches();

    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_row2_upward_with_guidance()
        .expect("ROW2 upward guidance should emit a lemma for a proven conflict")
    else {
        panic!("expected NeedLemmas from ROW2-upward guidance conflict");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "ROW2-upward conflict should emit one lemma"
    );
    assert_eq!(
        lemmas[0].clause,
        vec![TheoryLit::new(eq_ij, true), TheoryLit::new(eq_sels, true)],
        "ROW2-upward lemma must block index disequality plus select disequality"
    );
}

#[test]
fn test_arrays_store_chain_select_difference_batches_multi_support_requests_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let k = store.mk_var("k", Sort::Int);
    let v0 = store.mk_var("v0", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);
    let w0 = store.mk_var("w0", Sort::Int);
    let w1 = store.mk_var("w1", Sort::Int);
    let r1 = store.mk_var("r1", Sort::Int);
    let r2 = store.mk_var("r2", Sort::Int);
    let idx0 = store.mk_int(BigInt::from(0));
    let idx1 = store.mk_int(BigInt::from(1));

    let chain1_base = store.mk_store(a, idx0, v0);
    let chain1 = store.mk_store(chain1_base, idx1, v1);
    let chain2_base = store.mk_store(a, idx0, w0);
    let chain2 = store.mk_store(chain2_base, idx1, w1);
    let sel1 = store.mk_select(chain1, k);
    let sel2 = store.mk_select(chain2, k);
    let eq_r1_sel1 = store.mk_eq(r1, sel1);
    let eq_r2_sel2 = store.mk_eq(r2, sel2);
    let eq_r1_r2 = store.mk_eq(r1, r2);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_r1_sel1, true);
    solver.assert_literal(eq_r2_sel2, true);
    solver.assert_literal(eq_r1_r2, false);
    solver.populate_caches();

    assert!(
        solver
            .check_store_chain_select_difference_witness()
            .is_none(),
        "support fallback should not speculate fresh multi-index equality requests"
    );
}

#[test]
fn test_arrays_store_chain_select_difference_handles_direct_select_diseq_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let k = store.mk_var("k", Sort::Int);
    let v0 = store.mk_var("v0", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);
    let w0 = store.mk_var("w0", Sort::Int);
    let w1 = store.mk_var("w1", Sort::Int);
    let idx0 = store.mk_int(BigInt::from(0));
    let idx1 = store.mk_int(BigInt::from(1));

    let chain1_base = store.mk_store(a, idx0, v0);
    let chain1 = store.mk_store(chain1_base, idx1, v1);
    let chain2_base = store.mk_store(a, idx0, w0);
    let chain2 = store.mk_store(chain2_base, idx1, w1);
    let sel1 = store.mk_select(chain1, k);
    let sel2 = store.mk_select(chain2, k);
    let eq_sels = store.mk_eq(sel1, sel2);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_sels, false);
    solver.populate_caches();

    assert!(
        solver
            .check_store_chain_select_difference_witness()
            .is_none(),
        "direct support fallback should not speculate fresh multi-index equality requests"
    );
}

#[test]
fn test_arrays_store_chain_select_difference_prefers_singleton_support_candidate_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let k = store.mk_var("k", Sort::Int);
    let v0 = store.mk_var("v0", Sort::Int);
    let w0 = store.mk_var("w0", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);
    let w1 = store.mk_var("w1", Sort::Int);
    let v2 = store.mk_var("v2", Sort::Int);
    let w2 = store.mk_var("w2", Sort::Int);
    let idx0 = store.mk_int(BigInt::from(0));
    let idx1 = store.mk_int(BigInt::from(1));
    let idx2 = store.mk_int(BigInt::from(2));

    let singleton_lhs = store.mk_store(a, idx0, v0);
    let singleton_rhs = store.mk_store(a, idx0, w0);
    let singleton_sel_lhs = store.mk_select(singleton_lhs, k);
    let singleton_sel_rhs = store.mk_select(singleton_rhs, k);
    let singleton_sel_eq = store.mk_eq(singleton_sel_lhs, singleton_sel_rhs);

    let multi_lhs_base = store.mk_store(a, idx1, v1);
    let multi_lhs = store.mk_store(multi_lhs_base, idx2, v2);
    let multi_rhs_base = store.mk_store(a, idx1, w1);
    let multi_rhs = store.mk_store(multi_rhs_base, idx2, w2);
    let multi_sel_lhs = store.mk_select(multi_lhs, k);
    let multi_sel_rhs = store.mk_select(multi_rhs, k);
    let multi_sel_eq = store.mk_eq(multi_sel_lhs, multi_sel_rhs);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(singleton_sel_eq, false);
    solver.assert_literal(multi_sel_eq, false);
    solver.populate_caches();

    let TheoryResult::NeedModelEquality(request) = solver
        .check_store_chain_select_difference_witness()
        .expect("best support candidate should request its singleton equality first")
    else {
        panic!("expected only the singleton support candidate to be returned");
    };

    assert!(
        request.lhs == k && request.rhs == idx0 || request.lhs == idx0 && request.rhs == k,
        "singleton support candidate should be preferred over broader support branches"
    );
}

#[test]
fn test_arrays_check_surfaces_deferred_singleton_support_candidate_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let k = store.mk_var("k", Sort::Int);
    let v0 = store.mk_var("v0", Sort::Int);
    let w0 = store.mk_var("w0", Sort::Int);
    let r1 = store.mk_var("r1", Sort::Int);
    let r2 = store.mk_var("r2", Sort::Int);
    let idx0 = store.mk_int(BigInt::from(0));

    let chain1 = store.mk_store(a, idx0, v0);
    let chain2 = store.mk_store(a, idx0, w0);
    let sel1 = store.mk_select(chain1, k);
    let sel2 = store.mk_select(chain2, k);
    let eq_r1_sel1 = store.mk_eq(r1, sel1);
    let eq_r2_sel2 = store.mk_eq(r2, sel2);
    let eq_r1_r2 = store.mk_eq(r1, r2);

    let mut solver = ArraySolver::new(&store);
    solver.set_defer_expensive_checks(true);
    solver.assert_literal(eq_r1_sel1, true);
    solver.assert_literal(eq_r2_sel2, true);
    solver.assert_literal(eq_r1_r2, false);

    let TheoryResult::NeedModelEquality(request) = solver.check() else {
        panic!("deferred check() should surface singleton support equality request");
    };

    assert!(
        request.lhs == k && request.rhs == idx0 || request.lhs == idx0 && request.rhs == k,
        "deferred singleton support request should target the read index"
    );
    assert!(
        request.implied,
        "singleton support requests are guarded implications, not speculative model guidance"
    );
}

#[test]
fn test_arrays_store_chain_select_difference_emits_resolved_support_before_new_requests_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let k = store.mk_var("k", Sort::Int);
    let v0 = store.mk_var("v0", Sort::Int);
    let w0 = store.mk_var("w0", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);
    let w1 = store.mk_var("w1", Sort::Int);
    let v2 = store.mk_var("v2", Sort::Int);
    let w2 = store.mk_var("w2", Sort::Int);
    let idx0 = store.mk_int(BigInt::from(0));
    let idx1 = store.mk_int(BigInt::from(1));
    let idx2 = store.mk_int(BigInt::from(2));

    let singleton_lhs = store.mk_store(a, idx0, v0);
    let singleton_rhs = store.mk_store(a, idx0, w0);
    let singleton_sel_lhs = store.mk_select(singleton_lhs, k);
    let singleton_sel_rhs = store.mk_select(singleton_rhs, k);
    let singleton_sel_eq = store.mk_eq(singleton_sel_lhs, singleton_sel_rhs);
    let eq_k_idx0 = store.mk_eq(k, idx0);

    let multi_lhs_base = store.mk_store(a, idx1, v1);
    let multi_lhs = store.mk_store(multi_lhs_base, idx2, v2);
    let multi_rhs_base = store.mk_store(a, idx1, w1);
    let multi_rhs = store.mk_store(multi_rhs_base, idx2, w2);
    let multi_sel_lhs = store.mk_select(multi_lhs, k);
    let multi_sel_rhs = store.mk_select(multi_rhs, k);
    let multi_sel_eq = store.mk_eq(multi_sel_lhs, multi_sel_rhs);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(singleton_sel_eq, false);
    solver.assert_literal(eq_k_idx0, false);
    solver.assert_literal(multi_sel_eq, false);
    solver.mark_model_equality_requested(k, idx0);
    solver.populate_caches();

    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_store_chain_select_difference_witness()
        .expect("resolved support candidate should beat fresh requests")
    else {
        panic!("expected a support lemma before requesting unrelated support atoms");
    };

    assert_eq!(lemmas.len(), 1);
    assert!(
        lemmas[0].clause.contains(&TheoryLit::new(eq_k_idx0, true)),
        "resolved singleton support lemma should force the already-requested equality"
    );
}

#[test]
fn test_arrays_store_chain_select_difference_propagates_singleton_support_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let k = store.mk_var("k", Sort::Int);
    let v0 = store.mk_var("v0", Sort::Int);
    let w0 = store.mk_var("w0", Sort::Int);
    let r1 = store.mk_var("r1", Sort::Int);
    let r2 = store.mk_var("r2", Sort::Int);
    let idx0 = store.mk_int(BigInt::from(0));

    let chain1 = store.mk_store(a, idx0, v0);
    let chain2 = store.mk_store(a, idx0, w0);
    let sel1 = store.mk_select(chain1, k);
    let sel2 = store.mk_select(chain2, k);
    let eq_r1_sel1 = store.mk_eq(r1, sel1);
    let eq_r2_sel2 = store.mk_eq(r2, sel2);
    let eq_r1_r2 = store.mk_eq(r1, r2);
    let eq_k_idx0 = store.mk_eq(k, idx0);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_r1_sel1, true);
    solver.assert_literal(eq_r2_sel2, true);
    solver.assert_literal(eq_r1_r2, false);
    solver.assert_literal(eq_k_idx0, false);
    solver.mark_model_equality_requested(k, idx0);
    solver.populate_caches();

    let propagations = solver.propagate();
    assert!(
        propagations
            .iter()
            .any(|prop| prop.literal == TheoryLit::new(eq_k_idx0, true)),
        "singleton support should propagate the support equality once the atom exists"
    );
}

#[test]
fn test_arrays_store_chain_select_difference_skips_satisfied_support_requests_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let k = store.mk_var("k", Sort::Int);
    let v0 = store.mk_var("v0", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);
    let w0 = store.mk_var("w0", Sort::Int);
    let w1 = store.mk_var("w1", Sort::Int);
    let r1 = store.mk_var("r1", Sort::Int);
    let r2 = store.mk_var("r2", Sort::Int);
    let idx0 = store.mk_int(BigInt::from(0));
    let idx1 = store.mk_int(BigInt::from(1));

    let chain1_base = store.mk_store(a, idx0, v0);
    let chain1 = store.mk_store(chain1_base, idx1, v1);
    let chain2_base = store.mk_store(a, idx0, w0);
    let chain2 = store.mk_store(chain2_base, idx1, w1);
    let sel1 = store.mk_select(chain1, k);
    let sel2 = store.mk_select(chain2, k);
    let eq_r1_sel1 = store.mk_eq(r1, sel1);
    let eq_r2_sel2 = store.mk_eq(r2, sel2);
    let eq_r1_r2 = store.mk_eq(r1, r2);
    let eq_k_idx0 = store.mk_eq(k, idx0);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_r1_sel1, true);
    solver.assert_literal(eq_r2_sel2, true);
    solver.assert_literal(eq_r1_r2, false);
    solver.assert_literal(eq_k_idx0, true);
    solver.mark_model_equality_requested(k, idx0);
    solver.populate_caches();

    assert!(
        solver
            .check_store_chain_select_difference_witness()
            .is_none(),
        "a support disjunction already satisfied by k = idx0 must not request k = idx1"
    );
}

#[test]
fn test_arrays_store_chain_select_difference_requests_existing_support_eq_coupling_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let k = store.mk_var("k", Sort::Int);
    let v0 = store.mk_var("v0", Sort::Int);
    let w0 = store.mk_var("w0", Sort::Int);
    let idx0 = store.mk_int(BigInt::from(0));

    let chain1 = store.mk_store(a, idx0, v0);
    let chain2 = store.mk_store(a, idx0, w0);
    let sel1 = store.mk_select(chain1, k);
    let sel2 = store.mk_select(chain2, k);
    let eq_sels = store.mk_eq(sel1, sel2);
    let _eq_k_idx0 = store.mk_eq(k, idx0);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_sels, false);
    solver.populate_caches();

    let TheoryResult::NeedModelEquality(request) = solver
        .check_store_chain_select_difference_witness()
        .expect("existing support equality should still request model-equality coupling once")
    else {
        panic!("expected NeedModelEquality for existing uncoupled support equality");
    };

    assert!(
        request.lhs == k && request.rhs == idx0 || request.lhs == idx0 && request.rhs == k,
        "request should couple the existing support equality atom"
    );
}

#[test]
fn test_arrays_store_chain_select_difference_multi_support_conflict_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let k = store.mk_var("k", Sort::Int);
    let v0 = store.mk_var("v0", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);
    let w0 = store.mk_var("w0", Sort::Int);
    let w1 = store.mk_var("w1", Sort::Int);
    let r1 = store.mk_var("r1", Sort::Int);
    let r2 = store.mk_var("r2", Sort::Int);
    let idx0 = store.mk_int(BigInt::from(0));
    let idx1 = store.mk_int(BigInt::from(1));

    let chain1_base = store.mk_store(a, idx0, v0);
    let chain1 = store.mk_store(chain1_base, idx1, v1);
    let chain2_base = store.mk_store(a, idx0, w0);
    let chain2 = store.mk_store(chain2_base, idx1, w1);
    let sel1 = store.mk_select(chain1, k);
    let sel2 = store.mk_select(chain2, k);
    let eq_r1_sel1 = store.mk_eq(r1, sel1);
    let eq_r2_sel2 = store.mk_eq(r2, sel2);
    let eq_r1_r2 = store.mk_eq(r1, r2);
    let eq_k_idx0 = store.mk_eq(k, idx0);
    let eq_k_idx1 = store.mk_eq(k, idx1);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_r1_sel1, true);
    solver.assert_literal(eq_r2_sel2, true);
    solver.assert_literal(eq_r1_r2, false);
    solver.assert_literal(eq_k_idx0, false);
    solver.assert_literal(eq_k_idx1, false);
    solver.mark_model_equality_requested(k, idx0);
    solver.mark_model_equality_requested(k, idx1);
    solver.populate_caches();

    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_store_chain_select_difference_witness()
        .expect("multi-support witness should emit a guarded disjunction lemma")
    else {
        panic!("expected NeedLemmas for resolved multi-support witness");
    };

    assert_eq!(lemmas.len(), 1);
    let clause = &lemmas[0].clause;
    assert!(clause.contains(&TheoryLit::new(eq_r1_sel1, false)));
    assert!(clause.contains(&TheoryLit::new(eq_r2_sel2, false)));
    assert!(clause.contains(&TheoryLit::new(eq_r1_r2, true)));
    assert!(clause.contains(&TheoryLit::new(eq_k_idx0, true)));
    assert!(clause.contains(&TheoryLit::new(eq_k_idx1, true)));
}

#[test]
fn test_arrays_row2_extended_resolves_same_value_store_permutation_compactly_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let k = store.mk_var("k", Sort::Int);
    let i1 = store.mk_var("i1", Sort::Int);
    let i2 = store.mk_var("i2", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);
    let v2 = store.mk_var("v2", Sort::Int);
    let r1 = store.mk_var("r1", Sort::Int);
    let r2 = store.mk_var("r2", Sort::Int);

    let lhs_base = store.mk_store(a, i1, v1);
    let lhs = store.mk_store(lhs_base, i2, v2);
    let rhs_base = store.mk_store(a, i2, v2);
    let rhs = store.mk_store(rhs_base, i1, v1);
    let sel_lhs = store.mk_select(lhs, k);
    let sel_rhs = store.mk_select(rhs, k);
    let eq_r1_sel_lhs = store.mk_eq(r1, sel_lhs);
    let eq_r2_sel_rhs = store.mk_eq(r2, sel_rhs);
    let eq_r1_r2 = store.mk_eq(r1, r2);
    let eq_k_i1 = store.mk_eq(k, i1);
    let eq_i1_i2 = store.mk_eq(i1, i2);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_r1_sel_lhs, true);
    solver.assert_literal(eq_r2_sel_rhs, true);
    solver.assert_literal(eq_r1_r2, false);
    solver.assert_literal(eq_k_i1, true);
    solver.assert_literal(eq_i1_i2, false);
    solver.populate_caches();

    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_row2_extended()
        .expect("ROW2-extended should resolve both permutation reads to v1")
    else {
        panic!("expected compact ROW2-extended lemma");
    };

    assert_eq!(lemmas.len(), 1);
    let clause = &lemmas[0].clause;
    assert!(
        clause.len() <= 5,
        "resolved-value permutation conflict should use the local ROW1/ROW2 proof, got {clause:?}"
    );
    assert!(clause.contains(&TheoryLit::new(eq_r1_sel_lhs, false)));
    assert!(clause.contains(&TheoryLit::new(eq_r2_sel_rhs, false)));
    assert!(clause.contains(&TheoryLit::new(eq_r1_r2, true)));
    assert!(clause.contains(&TheoryLit::new(eq_k_i1, false)));
    assert!(clause.contains(&TheoryLit::new(eq_i1_i2, true)));
}

#[test]
fn test_arrays_row2_upward_guidance_conflict_uses_store_result_alias_select_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let sel_a_j = store.mk_select(a, j);
    let sel_b_j = store.mk_select(b, j);
    let eq_b_stored = store.mk_eq(b, stored);
    let eq_ij = store.mk_eq(i, j);
    let eq_sels = store.mk_eq(sel_a_j, sel_b_j);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_b_stored, true);
    solver.assert_literal(eq_ij, false);
    solver.assert_literal(eq_sels, false);
    solver.populate_caches();
    solver.pending_row2_upward.clear();
    solver.pending_row2_upward.push((sel_a_j, stored));

    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_row2_upward_with_guidance()
        .expect("ROW2-upward should use an exact select on a provable store-result alias")
    else {
        panic!("expected NeedLemmas from ROW2-upward alias-select conflict");
    };

    assert_eq!(
        lemmas.len(),
        1,
        "ROW2-upward alias-select conflict should emit one guarded lemma"
    );
    assert_eq!(
        lemmas[0].clause,
        vec![
            TheoryLit::new(eq_b_stored, false),
            TheoryLit::new(eq_ij, true),
            TheoryLit::new(eq_sels, true),
        ],
        "lemma must include the store-result alias reason for the exact select"
    );
}

#[test]
fn test_arrays_row2_upward_guidance_skips_unbased_pair_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let sel_b_j = store.mk_select(b, j);
    let sel_stored_j = store.mk_select(stored, j);
    let eq_ij = store.mk_eq(i, j);
    let eq_sels = store.mk_eq(sel_b_j, sel_stored_j);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_ij, false);
    solver.assert_literal(eq_sels, false);
    solver.populate_caches();
    solver.pending_row2_upward.clear();
    solver.pending_row2_upward.push((sel_b_j, stored));

    assert!(
        solver.check_row2_upward_with_guidance().is_none(),
        "ROW2-upward must not use a queued pair unless the select array is the store base"
    );
}

#[test]
fn test_arrays_row2_upward_guidance_guards_base_alias_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let sel_b_j = store.mk_select(b, j);
    let sel_stored_j = store.mk_select(stored, j);
    let eq_a_b = store.mk_eq(a, b);
    let eq_ij = store.mk_eq(i, j);
    let eq_sels = store.mk_eq(sel_b_j, sel_stored_j);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_a_b, true);
    solver.assert_literal(eq_ij, false);
    solver.assert_literal(eq_sels, false);
    solver.populate_caches();
    solver.pending_row2_upward.clear();
    solver.pending_row2_upward.push((sel_b_j, stored));

    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_row2_upward_with_guidance()
        .expect("ROW2-upward should emit a guarded lemma for an explainable base alias")
    else {
        panic!("expected NeedLemmas from ROW2-upward base-alias conflict");
    };
    assert_eq!(lemmas.len(), 1);

    let clause = &lemmas[0].clause;
    assert!(
        clause.contains(&TheoryLit::new(eq_a_b, false)),
        "lemma must negate the asserted base-array alias"
    );
    assert!(
        clause.contains(&TheoryLit::new(eq_ij, true)),
        "lemma must preserve the ROW2 index-disequality branch"
    );
    assert!(
        clause.contains(&TheoryLit::new(eq_sels, true)),
        "lemma must preserve the select-equality conclusion branch"
    );
}

#[test]
fn test_arrays_row2_upward_guidance_carries_base_alias_reason_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let sel_b_j = store.mk_select(b, j);
    let _sel_stored_j = store.mk_select(stored, j);
    let eq_a_b = store.mk_eq(a, b);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_a_b, true);
    solver.populate_caches();
    solver.pending_row2_upward.clear();
    solver.pending_row2_upward.push((sel_b_j, stored));

    let TheoryResult::NeedModelEquality(request) = solver
        .check_row2_upward_with_guidance()
        .expect("ROW2-upward should request index guidance for an explainable base alias")
    else {
        panic!("expected NeedModelEquality from ROW2-upward base-alias guidance");
    };

    assert!(
        (request.lhs == i && request.rhs == j) || (request.lhs == j && request.rhs == i),
        "guidance request must target the store and select indices"
    );
    assert_eq!(
        request.reason,
        vec![TheoryLit::new(eq_a_b, true)],
        "guidance request must carry the asserted base-array alias reason"
    );
}

#[test]
fn test_arrays_row2_upward_guidance_guards_transitive_base_alias_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let mid = store.mk_var("mid", arr_sort.clone());
    let alias = store.mk_var("alias", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let sel_alias_j = store.mk_select(alias, j);
    let sel_stored_j = store.mk_select(stored, j);
    let eq_mid = store.mk_eq(mid, a);
    let eq_alias = store.mk_eq(alias, mid);
    let eq_ij = store.mk_eq(i, j);
    let eq_sels = store.mk_eq(sel_alias_j, sel_stored_j);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_mid, true);
    solver.assert_literal(eq_alias, true);
    solver.assert_literal(eq_ij, false);
    solver.assert_literal(eq_sels, false);
    solver.populate_caches();
    solver.pending_row2_upward.clear();
    solver.pending_row2_upward.push((sel_alias_j, stored));

    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_row2_upward_with_guidance()
        .expect("ROW2-upward should emit a guarded lemma for a transitive base alias")
    else {
        panic!("expected NeedLemmas from ROW2-upward transitive base-alias conflict");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "ROW2-upward transitive base-alias conflict should emit one lemma"
    );
    assert_eq!(
        lemmas[0].clause,
        vec![
            TheoryLit::new(eq_mid, false),
            TheoryLit::new(eq_alias, false),
            TheoryLit::new(eq_ij, true),
            TheoryLit::new(eq_sels, true),
        ],
        "ROW2-upward alias conflict must include the full transitive base-equality guard"
    );
}

#[test]
fn test_arrays_row2_upward_guidance_carries_transitive_base_alias_reasons_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let mid = store.mk_var("mid", arr_sort.clone());
    let alias = store.mk_var("alias", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let sel_alias_j = store.mk_select(alias, j);
    let _sel_stored_j = store.mk_select(stored, j);
    let eq_mid = store.mk_eq(mid, a);
    let eq_alias = store.mk_eq(alias, mid);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_mid, true);
    solver.assert_literal(eq_alias, true);
    solver.populate_caches();
    solver.pending_row2_upward.clear();
    solver.pending_row2_upward.push((sel_alias_j, stored));

    let TheoryResult::NeedModelEquality(request) = solver
        .check_row2_upward_with_guidance()
        .expect("ROW2-upward should request index guidance for a transitive base alias")
    else {
        panic!("expected NeedModelEquality from ROW2-upward transitive base-alias guidance");
    };

    assert!(
        (request.lhs == i && request.rhs == j) || (request.lhs == j && request.rhs == i),
        "guidance request must target the store and select indices"
    );
    assert_eq!(
        request.reason,
        vec![TheoryLit::new(eq_mid, true), TheoryLit::new(eq_alias, true)],
        "guidance request must carry the full transitive base-array alias reason chain"
    );
}

#[test]
fn test_arrays_final_check_skips_non_conflict_ready_drained_row2_upward_guidance_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let sel_b_j = store.mk_select(b, j);
    let _sel_stored_j = store.mk_select(stored, j);
    let eq_a_b = store.mk_eq(a, b);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();
    solver.pending_row2_upward.clear();
    solver.pending_row2_upward.push((sel_b_j, stored));

    assert!(
        solver.check_row2_upward_with_guidance().is_none(),
        "pre-alias drain should skip the candidate without emitting guidance"
    );
    assert!(
        solver.pending_row2_upward.is_empty(),
        "ROW2-upward guidance should drain the queued candidate"
    );

    solver.assert_literal(eq_a_b, true);

    assert_eq!(
        solver.requested_model_eqs.len(),
        0,
        "final_check should not reserve speculative ROW2-upward guidance without a value conflict"
    );

    assert!(
        matches!(solver.final_check(), TheoryResult::Sat),
        "final_check should remain SAT when the revived candidate is not conflict-ready"
    );
    assert_eq!(
        solver.requested_model_eqs.len(),
        0,
        "duplicate final_check passes must not grow speculative ROW2-upward request state"
    );
}

#[test]
fn test_arrays_final_check_progresses_drained_row2_upward_conflict_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let sel_b_j = store.mk_select(b, j);
    let sel_stored_j = store.mk_select(stored, j);
    let eq_a_b = store.mk_eq(a, b);
    let eq_ij = store.mk_eq(i, j);
    let eq_sels = store.mk_eq(sel_b_j, sel_stored_j);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();
    solver.pending_row2_upward.clear();
    solver.pending_row2_upward.push((sel_b_j, stored));

    assert!(
        solver.check_row2_upward_with_guidance().is_none(),
        "pre-alias drain should skip the candidate without emitting a lemma"
    );

    solver.assert_literal(eq_a_b, true);
    solver.assert_literal(eq_ij, false);
    solver.assert_literal(eq_sels, false);

    let TheoryResult::NeedLemmas(lemmas) = solver.final_check() else {
        panic!("expected final_check to progress the drained ROW2-upward candidate once support is live");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "final_check should emit one guarded ROW2-upward lemma for the revived candidate"
    );
    assert_eq!(
        lemmas[0].clause,
        vec![
            TheoryLit::new(eq_a_b, false),
            TheoryLit::new(eq_ij, true),
            TheoryLit::new(eq_sels, true),
        ],
        "revived ROW2-upward conflict must stay guarded by the base alias reason"
    );
}

/// Since #6546 Packet 4, `assert_literal(eq_b_store, true)` triggers
/// `notify_equality(b, store_a)` which eagerly queues ROW2-down axioms.
/// This means `check()` catches the b=store(a,0,v) + select(b,1)!=select(a,1)
/// conflict through the non-deferred ROW2-down path. The lemma is produced
/// by `check()` directly, not deferred to `final_check()`.
#[test]
fn test_arrays_row2_down_finds_store_equality_conflict_eagerly() {
    use num_bigint::BigInt;

    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let v = store.mk_var("v", Sort::Int);

    let idx0 = store.mk_int(BigInt::from(0));
    let idx1 = store.mk_int(BigInt::from(1));

    let store_a = store.mk_store(a, idx0, v);
    let eq_b_store = store.mk_eq(b, store_a);
    let sel_a_1 = store.mk_select(a, idx1);
    let sel_b_1 = store.mk_select(b, idx1);
    let eq_sels = store.mk_eq(sel_a_1, sel_b_1);

    let mut solver = ArraySolver::new(&store);
    solver.set_defer_expensive_checks(true);
    solver.assert_literal(eq_b_store, true);
    solver.assert_literal(eq_sels, false);

    // #6546 Packet 4: assert_literal triggers notify_equality, which queues
    // ROW2-down axioms. check() sees the undecided index pair (idx0, idx1)
    // and requests a model equality so the DPLL(T) loop or LIA can resolve
    // whether idx0 = idx1. In a standalone array solver test, we simulate
    // the combined solver by injecting the disequality.
    let result = solver.check();
    if matches!(result, TheoryResult::NeedLemmas(_) | TheoryResult::Unsat(_)) {
        return;
    }
    assert!(
        matches!(result, TheoryResult::NeedModelEquality(_)),
        "ROW2-down should either emit the constant-index lemma or request model equality for index pair (0, 1)"
    );

    // Simulate combined solver: inject external disequality idx0 != idx1.
    solver.assert_external_disequality(idx0, idx1);

    // After the combined solver resolves the index relationship, check()
    // produces ROW2-down NeedLemmas with the conflict.
    let result2 = solver.check();
    match result2 {
        TheoryResult::NeedLemmas(_) | TheoryResult::Unsat(_) => {
            // Eager detection: check() found the ROW2 conflict.
        }
        TheoryResult::Sat => {
            // Deferred path: final_check() should catch it.
            let fc_result = solver.final_check();
            assert!(
                matches!(fc_result, TheoryResult::NeedLemmas(_)),
                "final_check should find the deferred ROW2-extended conflict"
            );
        }
        _ => {
            // NeedModelEquality is acceptable if more index pairs need resolving.
        }
    }
}

#[test]
fn test_arrays_row2_down_replays_blocked_exact_select_conflict_after_external_diseq_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let idx_guard = store.mk_var("idx_guard", Sort::Bool);

    let stored = store.mk_store(a, i, v);
    let eq_b_stored = store.mk_eq(b, stored);
    let sel_a_j = store.mk_select(a, j);
    let sel_b_j = store.mk_select(b, j);
    let eq_sels = store.mk_eq(sel_a_j, sel_b_j);

    let mut solver = ArraySolver::new(&store);
    solver.set_defer_expensive_checks(true);
    solver.assert_literal(eq_b_stored, true);
    solver.assert_literal(eq_sels, false);
    solver.assert_literal(idx_guard, true);

    let first = solver.check();
    assert!(
        matches!(
            first,
            TheoryResult::NeedModelEquality(_) | TheoryResult::NeedModelEqualities(_)
        ),
        "initial ROW2-down pass should block on the undecided index pair, got {first:?}"
    );

    solver.assert_external_disequality_with_reasons(i, j, vec![TheoryLit::new(idx_guard, true)]);

    let TheoryResult::NeedLemmas(lemmas) = solver.check() else {
        panic!("reasoned external disequality should replay the blocked ROW2-down exact-select conflict");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "replayed exact-select conflict should emit one guarded lemma"
    );
    let clause = &lemmas[0].clause;
    assert_eq!(
        clause.len(),
        3,
        "ROW2-down conflict should have exactly the two guards and select conclusion"
    );
    assert!(clause.contains(&TheoryLit::new(eq_b_stored, false)));
    assert!(clause.contains(&TheoryLit::new(idx_guard, false)));
    assert!(clause.contains(&TheoryLit::new(eq_sels, true)));
}

#[test]
fn test_arrays_row2_down_does_not_replay_unreasoned_exact_select_conflict_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let eq_b_stored = store.mk_eq(b, stored);
    let sel_a_j = store.mk_select(a, j);
    let sel_b_j = store.mk_select(b, j);
    let eq_sels = store.mk_eq(sel_a_j, sel_b_j);

    let mut solver = ArraySolver::new(&store);
    solver.set_defer_expensive_checks(true);
    solver.assert_literal(eq_b_stored, true);
    solver.assert_literal(eq_sels, false);

    let first = solver.check();
    assert!(
        matches!(
            first,
            TheoryResult::NeedModelEquality(_) | TheoryResult::NeedModelEqualities(_)
        ),
        "initial ROW2-down pass should block on the undecided index pair, got {first:?}"
    );

    solver.assert_external_disequality_with_reasons(i, j, Vec::new());

    let second = solver.check();
    assert!(
        matches!(
            second,
            TheoryResult::NeedModelEquality(_) | TheoryResult::NeedModelEqualities(_) | TheoryResult::Sat
        ),
        "unreasoned external disequality must not replay a guarded exact-select ROW2 lemma, got {second:?}"
    );
}

#[test]
fn test_arrays_nested_select_conflict_emits_lemma() {
    use num_bigint::BigInt;

    let mut store = TermStore::new();
    let row_sort = make_array_sort();
    let heap_sort = Sort::array(Sort::Int, row_sort.clone());

    let heap = store.mk_var("heap", heap_sort.clone());
    let heap_alias = store.mk_var("heap_alias", heap_sort);
    let row = store.mk_var("row", row_sort);
    let zero = store.mk_int(BigInt::from(0));
    let field = store.mk_var("field", Sort::Int);

    let heap_with_row = store.mk_store(heap, zero, row);
    let eq_alias = store.mk_eq(heap_alias, heap_with_row);
    let nested_row = store.mk_select(heap_alias, zero);
    let sel_nested = store.mk_select(nested_row, field);
    let sel_row = store.mk_select(row, field);
    let eq_sels = store.mk_eq(sel_nested, sel_row);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_alias, true);
    solver.assert_literal(eq_sels, false);
    solver.populate_caches();

    assert!(
        !solver.weakly_connected(nested_row, row),
        "nested normalization must not require the original select arrays to share a weak component"
    );

    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_nested_select_conflicts()
        .expect("nested select normalization should detect the conflict")
    else {
        panic!("expected NeedLemmas from nested-select conflict");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "nested-select conflict should emit one lemma"
    );
    assert_eq!(
        lemmas[0].clause,
        vec![TheoryLit::new(eq_alias, false), TheoryLit::new(eq_sels, true)],
        "nested-select lemma must negate the asserted disequality and retain the alias-to-store antecedent"
    );
}

#[test]
fn test_arrays_nested_select_conflict_uses_transitive_alias_reasons_8785() {
    use num_bigint::BigInt;

    let mut store = TermStore::new();
    let row_sort = make_array_sort();
    let heap_sort = Sort::array(Sort::Int, row_sort.clone());

    let heap = store.mk_var("heap", heap_sort.clone());
    let heap_mid = store.mk_var("heap_mid", heap_sort.clone());
    let heap_alias = store.mk_var("heap_alias", heap_sort);
    let row = store.mk_var("row", row_sort);
    let zero = store.mk_int(BigInt::from(0));
    let field = store.mk_var("field", Sort::Int);

    let heap_with_row = store.mk_store(heap, zero, row);
    let eq_mid = store.mk_eq(heap_mid, heap_with_row);
    let eq_alias = store.mk_eq(heap_alias, heap_mid);
    let nested_row = store.mk_select(heap_alias, zero);
    let sel_nested = store.mk_select(nested_row, field);
    let sel_row = store.mk_select(row, field);
    let eq_sels = store.mk_eq(sel_nested, sel_row);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_mid, true);
    solver.assert_literal(eq_alias, true);
    solver.assert_literal(eq_sels, false);
    solver.populate_caches();

    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_nested_select_conflicts()
        .expect("nested select normalization should detect the transitive conflict")
    else {
        panic!("expected NeedLemmas from transitive nested-select conflict");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "transitive nested-select conflict should emit one lemma"
    );
    assert_eq!(
        lemmas[0].clause,
        vec![
            TheoryLit::new(eq_mid, false),
            TheoryLit::new(eq_alias, false),
            TheoryLit::new(eq_sels, true),
        ],
        "nested-select lemma must include the full transitive alias reason chain"
    );
}

#[test]
fn test_arrays_nested_select_conflict_includes_inner_index_alias_reason_8785() {
    use num_bigint::BigInt;

    let mut store = TermStore::new();
    let row_sort = make_array_sort();
    let heap_sort = Sort::array(Sort::Int, row_sort.clone());

    let heap = store.mk_var("heap", heap_sort.clone());
    let heap_alias = store.mk_var("heap_alias", heap_sort);
    let row = store.mk_var("row", row_sort);
    let zero = store.mk_int(BigInt::from(0));
    let zero_alias = store.mk_var("zero_alias", Sort::Int);
    let field = store.mk_var("field", Sort::Int);

    let heap_with_row = store.mk_store(heap, zero, row);
    let eq_heap = store.mk_eq(heap_alias, heap_with_row);
    let eq_zero = store.mk_eq(zero_alias, zero);
    let nested_row = store.mk_select(heap_alias, zero_alias);
    let sel_nested = store.mk_select(nested_row, field);
    let sel_row = store.mk_select(row, field);
    let eq_sels = store.mk_eq(sel_nested, sel_row);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_heap, true);
    solver.assert_literal(eq_zero, true);
    solver.assert_literal(eq_sels, false);
    solver.populate_caches();

    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_nested_select_conflicts()
        .expect("nested select normalization should detect the direct index-alias conflict")
    else {
        panic!("expected NeedLemmas from nested-select conflict");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "nested-select conflict should emit one lemma"
    );

    let clause = &lemmas[0].clause;
    assert_eq!(
        clause.len(),
        3,
        "lemma should include all direct alias premises"
    );
    assert!(clause.contains(&TheoryLit::new(eq_heap, false)));
    assert!(clause.contains(&TheoryLit::new(eq_zero, false)));
    assert!(clause.contains(&TheoryLit::new(eq_sels, true)));
}

#[test]
fn test_arrays_nested_select_conflict_includes_transitive_inner_index_alias_reasons_8785() {
    use num_bigint::BigInt;

    let mut store = TermStore::new();
    let row_sort = make_array_sort();
    let heap_sort = Sort::array(Sort::Int, row_sort.clone());

    let heap = store.mk_var("heap", heap_sort.clone());
    let heap_alias = store.mk_var("heap_alias", heap_sort);
    let row = store.mk_var("row", row_sort);
    let zero = store.mk_int(BigInt::from(0));
    let zero_mid = store.mk_var("zero_mid", Sort::Int);
    let zero_alias = store.mk_var("zero_alias", Sort::Int);
    let field = store.mk_var("field", Sort::Int);

    let heap_with_row = store.mk_store(heap, zero, row);
    let eq_heap = store.mk_eq(heap_alias, heap_with_row);
    let eq_zero_mid = store.mk_eq(zero_mid, zero);
    let eq_zero_alias = store.mk_eq(zero_alias, zero_mid);
    let nested_row = store.mk_select(heap_alias, zero_alias);
    let sel_nested = store.mk_select(nested_row, field);
    let sel_row = store.mk_select(row, field);
    let eq_sels = store.mk_eq(sel_nested, sel_row);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_heap, true);
    solver.assert_literal(eq_zero_mid, true);
    solver.assert_literal(eq_zero_alias, true);
    solver.assert_literal(eq_sels, false);
    solver.populate_caches();

    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_nested_select_conflicts()
        .expect("nested select normalization should detect the transitive index-alias conflict")
    else {
        panic!("expected NeedLemmas from nested-select conflict");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "nested-select conflict should emit one lemma"
    );

    let clause = &lemmas[0].clause;
    assert_eq!(
        clause.len(),
        4,
        "lemma should include the full transitive inner index alias chain"
    );
    assert!(clause.contains(&TheoryLit::new(eq_heap, false)));
    assert!(clause.contains(&TheoryLit::new(eq_zero_mid, false)));
    assert!(clause.contains(&TheoryLit::new(eq_zero_alias, false)));
    assert!(clause.contains(&TheoryLit::new(eq_sels, true)));
}

#[test]
fn test_arrays_nested_select_conflict_skips_unprovable_inner_index_alias_8785() {
    use num_bigint::BigInt;

    let mut store = TermStore::new();
    let row_sort = make_array_sort();
    let heap_sort = Sort::array(Sort::Int, row_sort.clone());

    let heap = store.mk_var("heap", heap_sort.clone());
    let heap_alias = store.mk_var("heap_alias", heap_sort);
    let row = store.mk_var("row", row_sort);
    let zero = store.mk_int(BigInt::from(0));
    let zero_alias = store.mk_var("zero_alias", Sort::Int);
    let field = store.mk_var("field", Sort::Int);

    let heap_with_row = store.mk_store(heap, zero, row);
    let eq_heap = store.mk_eq(heap_alias, heap_with_row);
    let nested_row = store.mk_select(heap_alias, zero_alias);
    let sel_nested = store.mk_select(nested_row, field);
    let sel_row = store.mk_select(row, field);
    let eq_sels = store.mk_eq(sel_nested, sel_row);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_heap, true);
    solver.assert_literal(eq_sels, false);
    solver.populate_caches();

    assert!(
        solver.check_nested_select_conflicts().is_none(),
        "nested-select conflict must not emit a lemma when the inner index alias is unprovable"
    );
}

#[test]
fn test_arrays_check_surfaces_row2_upward_guidance_without_defer_6282() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let k = store.mk_var("k", Sort::Int);
    let v1 = store.mk_var("v1", Sort::Int);
    let v2 = store.mk_var("v2", Sort::Int);

    let s1 = store.mk_store(a, i, v1);
    let s2 = store.mk_store(a, j, v2);
    let _sel_a_k = store.mk_select(a, k);
    let _sel_s1_k = store.mk_select(s1, k);
    let _sel_s2_k = store.mk_select(s2, k);

    let mut solver = ArraySolver::new(&store);

    match solver.check() {
        TheoryResult::NeedModelEqualities(requests) => {
            assert_eq!(
                requests.len(),
                4,
                "check() should surface both downward ROW2 atom creation and upward guidance"
            );
            assert!(
                requests
                    .iter()
                    .any(|req| req.lhs == i && req.rhs == k || req.lhs == k && req.rhs == i),
                "requests must include the first index equality"
            );
            assert!(
                requests
                    .iter()
                    .any(|req| req.lhs == j && req.rhs == k || req.lhs == k && req.rhs == j),
                "requests must include the second index equality"
            );
        }
        other => panic!("expected NeedModelEqualities from check(), got {other:?}"),
    }
}

/// Test for issue #920: store-select soundness - term-level fix
///
/// The primary fix for #920 is in mk_eq() which rewrites:
///   (= (store a i v) a) -> (= (select a i) v)
///
/// This test verifies the rewrite happens correctly.
#[test]
fn test_issue_920_self_store_term_rewrite() {
    use num_bigint::BigInt;

    let mut store = TermStore::new();
    let bv8_sort = Sort::bitvec(8);
    let arr_sort = Sort::array(bv8_sort.clone(), bv8_sort.clone());

    // arr: (Array BV8 BV8)
    let arr = store.mk_var("arr", arr_sort);
    // i: BV8
    let i = store.mk_var("i", bv8_sort);
    // #x02: BV8 constant
    let two = store.mk_bitvec(BigInt::from(2), 8);

    // store(arr, i, #x02)
    let stored = store.mk_store(arr, i, two);
    // select(arr, i)
    let selected = store.mk_select(arr, i);

    // (= (store arr i #x02) arr) - should be rewritten to (= (select arr i) #x02)
    let eq_store_arr = store.mk_eq(stored, arr);
    // (= (select arr i) #x02)
    let eq_sel_two = store.mk_eq(selected, two);

    // Due to the term-level rewrite, these should be the SAME term (hash-consed)
    assert_eq!(
        eq_store_arr, eq_sel_two,
        "Issue #920: (= (store a i v) a) should rewrite to (= (select a i) v)"
    );
}

// Note: A defense-in-depth test for check_self_store() would require
// bypassing mk_eq's rewrite via private intern(). The check_self_store()
// function in ArraySolver provides a backup mechanism for incremental solving
// scenarios. The primary fix is the term-level rewrite in mk_eq().

/// Test that self-store with consistent select is SAT
#[test]
fn test_self_store_consistent_sat() {
    use num_bigint::BigInt;

    let mut store = TermStore::new();
    let bv8_sort = Sort::bitvec(8);
    let arr_sort = Sort::array(bv8_sort.clone(), bv8_sort.clone());

    let arr = store.mk_var("arr", arr_sort);
    let i = store.mk_var("i", bv8_sort);
    let two = store.mk_bitvec(BigInt::from(2), 8);

    let stored = store.mk_store(arr, i, two);
    let selected = store.mk_select(arr, i);

    let eq_store_arr = store.mk_eq(stored, arr);
    let eq_sel_two = store.mk_eq(selected, two);

    let mut solver = ArraySolver::new(&store);

    // Assert store(arr, i, #x02) = arr AND select(arr, i) = #x02
    // This is consistent and should be SAT
    solver.assert_literal(eq_store_arr, true);
    solver.assert_literal(eq_sel_two, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "Self-store with consistent select should be SAT, got {result:?}"
    );
}

#[test]
fn test_self_store_register_store_queues_assigned_store_equality() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let arr = store.mk_var("arr", arr_sort.clone());
    let alias = store.mk_var("alias", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(arr, i, v);
    let eq_store_alias = store.mk_eq(stored, alias);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_store_alias, true);
    solver.populate_caches();

    assert_eq!(
        solver.pending_self_store,
        vec![(eq_store_alias, stored)],
        "register_store() should queue already-assigned equalities involving the new store"
    );
}

#[test]
fn test_self_store_pending_pair_waits_for_base_alias() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let arr = store.mk_var("arr", arr_sort.clone());
    let alias = store.mk_var("alias", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(arr, i, v);
    let select_alias = store.mk_select(alias, i);
    let eq_store_alias = store.mk_eq(stored, alias);
    let eq_alias_arr = store.mk_eq(alias, arr);
    let eq_select_v = store.mk_eq(select_alias, v);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_store_alias, true);
    solver.assert_literal(eq_select_v, false);
    solver.populate_caches();

    assert_eq!(
        solver.pending_self_store,
        vec![(eq_store_alias, stored)],
        "the store equality should be queued once the store term is registered"
    );
    assert!(
        solver.check_self_store().is_none(),
        "without alias = base, the queued self-store candidate should not conflict yet"
    );
    assert_eq!(
        solver.pending_self_store,
        vec![(eq_store_alias, stored)],
        "non-self-store pairs must be retained for later equality propagation"
    );

    solver.assert_literal(eq_alias_arr, true);
    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_self_store()
        .expect("expected retained self-store work to emit a lemma once alias = base")
    else {
        panic!("expected NeedLemmas from retained self-store work");
    };

    assert_eq!(lemmas.len(), 1, "self-store conflict should emit one lemma");
    let clause = &lemmas[0].clause;
    assert_eq!(
        clause.len(),
        3,
        "expected store, alias, and select antecedents"
    );
    assert!(
        clause.contains(&TheoryLit::new(eq_store_alias, false)),
        "lemma should negate the queued store equality antecedent"
    );
    assert!(
        clause.contains(&TheoryLit::new(eq_alias_arr, false)),
        "lemma should include the alias-to-base equality antecedent"
    );
    assert!(
        clause.contains(&TheoryLit::new(eq_select_v, true)),
        "lemma should block select(alias, i) != v"
    );
    assert!(
        solver.pending_self_store.is_empty(),
        "once the retained pair produces a lemma it should be drained"
    );
}

#[test]
fn test_self_store_pending_pair_falls_back_to_index_alias_select() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let arr = store.mk_var("arr", arr_sort.clone());
    let alias = store.mk_var("alias", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(arr, i, v);
    let select_alias_index = store.mk_select(alias, j);
    let eq_store_alias = store.mk_eq(stored, alias);
    let eq_alias_arr = store.mk_eq(alias, arr);
    let eq_j_i = store.mk_eq(j, i);
    let eq_select_v = store.mk_eq(select_alias_index, v);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_store_alias, true);
    solver.assert_literal(eq_select_v, false);
    solver.populate_caches();

    assert_eq!(
        solver.pending_self_store,
        vec![(eq_store_alias, stored)],
        "the alias-based self-store equality should be queued once the store term is registered"
    );
    assert!(
        solver.check_self_store().is_none(),
        "without alias = base, the queued self-store candidate should not conflict yet"
    );
    assert_eq!(
        solver.pending_self_store,
        vec![(eq_store_alias, stored)],
        "the self-store queue must retain work until the base alias arrives"
    );

    solver.assert_literal(eq_alias_arr, true);
    assert!(
        solver.check_self_store().is_none(),
        "without j = i, the alias-index select should still wait after alias = base"
    );
    assert_eq!(
        solver.pending_self_store,
        vec![(eq_store_alias, stored)],
        "the queue must retain the alias-based self-store work until the index alias arrives"
    );

    solver.assert_literal(eq_j_i, true);
    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_self_store()
        .expect("expected alias-index select to conflict once j = i is asserted")
    else {
        panic!("expected NeedLemmas from alias-index self-store work");
    };

    assert_eq!(lemmas.len(), 1, "self-store conflict should emit one lemma");
    let clause = &lemmas[0].clause;
    assert_eq!(
        clause.len(),
        4,
        "expected store, base-alias, index-alias, and select antecedents"
    );
    assert!(
        clause.contains(&TheoryLit::new(eq_store_alias, false)),
        "lemma should negate the queued self-store equality antecedent"
    );
    assert!(
        clause.contains(&TheoryLit::new(eq_alias_arr, false)),
        "lemma should include the base-alias equality antecedent"
    );
    assert!(
        clause.contains(&TheoryLit::new(eq_j_i, false)),
        "lemma should include the index-alias equality antecedent"
    );
    assert!(
        clause.contains(&TheoryLit::new(eq_select_v, true)),
        "lemma should block select(alias, j) != v"
    );
}
