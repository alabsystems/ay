// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::TheorySolver;
use num_bigint::BigInt;

// ========================================================================
// Conflict soundness tests (Part of #298)
// These tests verify that conflict explanations are semantically sound:
// re-solving with just the conflict literals must still be UNSAT.
// ========================================================================

/// Verify ROW1 conflict explanations are sound.
/// ROW1: select(store(a, i, v), i) = v
#[test]
fn test_arrays_row1_conflict_soundness() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    // store(a, i, v) and select(store(a, i, v), j)
    let stored = store.mk_store(a, i, v);
    let selected = store.mk_select(stored, j);

    let eq_ij = store.mk_eq(i, j);
    let eq_sel_v = store.mk_eq(selected, v);

    let mut solver = ArraySolver::new(&store);

    // Assert i = j (so ROW1 applies) and select(...) ≠ v (contradiction)
    solver.assert_literal(eq_ij, true);
    solver.assert_literal(eq_sel_v, false);

    solver.populate_caches();
    let result = solver
        .check_row1()
        .expect("expected ROW1 helper to emit a lemma");
    assert!(
        matches!(&result, TheoryResult::NeedLemmas(_)),
        "ROW1 helper should now route through lemma emission, got {result:?}"
    );
    assert_conflict_soundness(result, ArraySolver::new(&store));
}

/// Verify ROW2 conflict explanations are sound.
/// ROW2: i ≠ j → select(store(a, i, v), j) = select(a, j)
#[test]
fn test_arrays_row2_conflict_soundness() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    // store(a, i, v), select(store(a, i, v), j), and select(a, j)
    let stored = store.mk_store(a, i, v);
    let sel_stored_j = store.mk_select(stored, j);
    let sel_a_j = store.mk_select(a, j);

    let eq_ij = store.mk_eq(i, j);
    let eq_sels = store.mk_eq(sel_stored_j, sel_a_j);

    let mut solver = ArraySolver::new(&store);

    // Assert i ≠ j and select(store(a,i,v), j) ≠ select(a, j) (contradicts ROW2)
    solver.assert_literal(eq_ij, false);
    solver.assert_literal(eq_sels, false);

    // #6694: After restoring Unsat early-returns in check(), a conflict
    // check (store-chain resolution or nested-select) may detect the
    // contradiction directly as Unsat before check_row2() emits NeedLemmas.
    // Both are sound — ROW2 says i≠j → select(store(a,i,v),j)=select(a,j),
    // so asserting both i≠j and sel(store)≠sel(a) is unsatisfiable.
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_) | TheoryResult::NeedLemmas(_)),
        "expected Unsat or NeedLemmas from ROW2 contradiction, got {result:?}",
    );
}

#[test]
fn test_arrays_row2_direct_conflict_soundness() {
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
    solver.assert_literal(eq_sels, false);
    solver.populate_caches();

    // #8141: Lazy axiom generation — ROW2 axioms are no longer queued
    // during populate_caches(). Call generate_all_lazy_row2_axioms() to
    // populate pending_axioms before checking.
    solver.generate_all_lazy_row2_axioms();

    assert_eq!(
        solver.pending_axioms,
        vec![PendingAxiom::Row2Down {
            store: stored,
            select: sel_stored_j,
        }],
        "ROW2 direct check should consume the registered store/select pair"
    );

    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_row2()
        .expect("ROW2 direct path should emit one permanent clause")
    else {
        panic!("expected NeedLemmas from ROW2 direct path");
    };
    assert_eq!(
        lemmas.len(),
        1,
        "expected one ROW2 clause for the queued pair"
    );
    assert_eq!(
        lemmas[0].clause,
        vec![TheoryLit::new(eq_ij, true), TheoryLit::new(eq_sels, true)],
        "ROW2 clause must assert i=j or select(store(a,i,v),j)=select(a,j)"
    );
}

#[test]
fn test_arrays_row2_batches_multiple_lemmas() {
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
    solver.assert_literal(eq_ij, false);
    solver.assert_literal(eq_sel1, false);
    solver.assert_literal(eq_kl, false);
    solver.assert_literal(eq_sel2, false);
    solver.populate_caches();
    // #8141: Lazy axiom generation — generate ROW2 axioms explicitly.
    solver.generate_all_lazy_row2_axioms();

    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_row2()
        .expect("expected batched ROW2 lemmas for two queued pairs")
    else {
        panic!("expected NeedLemmas from batched ROW2");
    };

    assert_eq!(lemmas.len(), 2, "expected one lemma per violated ROW2 pair");

    let clauses: HashSet<Vec<(TermId, bool)>> = lemmas
        .iter()
        .map(|lemma| {
            lemma
                .clause
                .iter()
                .map(|lit| (lit.term, lit.value))
                .collect::<Vec<_>>()
        })
        .collect();

    assert!(
        clauses.contains(&vec![(eq_ij, true), (eq_sel1, true)]),
        "first ROW2 clause should assert i=j or select(store(a,i,v1),j)=select(a,j)"
    );
    assert!(
        clauses.contains(&vec![(eq_kl, true), (eq_sel2, true)]),
        "second ROW2 clause should assert k=l or select(store(a,k,v2),l)=select(a,l)"
    );
    // After emitting lemmas, axioms are drained — second call returns None.
    // DpllT applies NeedLemmas as permanent SAT clauses in-place, so
    // re-emitting is redundant (#6546).
    assert!(
        solver.check_row2().is_none(),
        "emitted ROW2 axioms should be drained after first lemma emit"
    );
}

/// Verify that check_row2 drains axioms after emitting their lemma clause.
/// DpllT applies NeedLemmas as permanent clauses in-place, so re-emitting
/// is redundant. The drain avoids O(total_axioms) re-scanning (#6546).
#[test]
fn test_arrays_row2_drains_after_lemma_emit() {
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
    solver.assert_literal(eq_sels, false);
    solver.populate_caches();
    // #8141: Lazy axiom generation — generate ROW2 axioms explicitly.
    solver.generate_all_lazy_row2_axioms();

    let TheoryResult::NeedLemmas(lemmas) =
        solver.check_row2().expect("expected ROW2 lemma request")
    else {
        panic!("expected NeedLemmas from ROW2 check");
    };
    assert_eq!(lemmas.len(), 1, "expected one ROW2 lemma clause");

    // After emitting the lemma, the axiom is drained — second call returns None.
    // The lazy generator won't re-queue because the fingerprint is already set.
    solver.generate_all_lazy_row2_axioms();
    assert!(
        solver.check_row2().is_none(),
        "emitted ROW2 axiom should be drained after first lemma emit"
    );
}

#[test]
fn test_arrays_row2_dirty_rebuild_does_not_requeue_emitted_axiom() {
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
    solver.assert_literal(eq_sels, false);
    solver.populate_caches();
    // #8141: Lazy axiom generation — generate ROW2 axioms explicitly.
    solver.generate_all_lazy_row2_axioms();

    let TheoryResult::NeedLemmas(lemmas) = solver
        .check_row2()
        .expect("expected ROW2 lemma request before dirty rebuild")
    else {
        panic!("expected NeedLemmas from ROW2 check");
    };
    assert_eq!(lemmas.len(), 1, "expected one emitted ROW2 lemma clause");
    assert!(
        solver.pending_axioms.is_empty(),
        "emitted ROW2 axiom should be drained before the rebuild"
    );

    // Simulate the split-loop dirty rebuild that repopulates array caches
    // after the SAT solver has already installed the permanent clause.
    solver.dirty = true;
    solver.populate_caches();
    // Even with lazy generation, re-running should not requeue emitted axioms.
    solver.generate_all_lazy_row2_axioms();

    assert!(
        solver.pending_axioms.is_empty(),
        "dirty rebuild must not requeue a ROW2 axiom whose fingerprint already exists"
    );
    assert!(
        solver.check_row2().is_none(),
        "dirty rebuild must not re-emit an already-applied ROW2 lemma"
    );
}

#[test]
fn test_arrays_row2_reset_requeues_unemitted_axiom() {
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
    // #8141: Lazy axiom generation — generate ROW2 axioms explicitly.
    solver.generate_all_lazy_row2_axioms();

    assert_eq!(
        solver.pending_axioms,
        vec![PendingAxiom::Row2Down {
            store: stored,
            select: sel_stored_j,
        }],
        "baseline ROW2 pair should be queued before reset"
    );

    // No clause was emitted yet, so reset must not leave behind a stale
    // fingerprint that suppresses re-queuing the same structural pair.
    solver.reset();
    solver.populate_caches();
    // After reset, fingerprints are cleared so lazy generation finds the pair again.
    solver.generate_all_lazy_row2_axioms();

    assert_eq!(
        solver.pending_axioms,
        vec![PendingAxiom::Row2Down {
            store: stored,
            select: sel_stored_j,
        }],
        "reset must requeue un-emitted ROW2 axioms on the rebuilt problem state"
    );
    assert_eq!(
        solver.row2_down_clause_terms(stored, sel_stored_j),
        Some((i, j, sel_a_j)),
        "rebuilt caches must still recover the ROW2 base-select clause terms"
    );
    assert!(
        solver.requested_model_eqs.is_empty(),
        "reset must clear model-equality request dedup before ROW2 re-check"
    );

    let TheoryResult::NeedModelEqualities(requests) = solver
        .check_row2()
        .expect("re-queued ROW2 pair should request the missing clause atoms")
    else {
        panic!("expected NeedModelEqualities after reset re-queued the ROW2 pair");
    };
    assert_eq!(
        requests.len(),
        2,
        "reset should restore both missing ROW2 equality requests"
    );
}

#[test]
fn test_arrays_row2_requests_missing_clause_atoms_once() {
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
    // #8141: Lazy axiom generation — generate ROW2 axioms explicitly.
    solver.generate_all_lazy_row2_axioms();

    let TheoryResult::NeedModelEqualities(requests) = solver
        .check_row2()
        .expect("missing equality atoms should be requested before ROW2 clause emission")
    else {
        panic!("expected NeedModelEqualities for missing ROW2 clause atoms");
    };
    assert_eq!(
        requests.len(),
        2,
        "expected index and value equality requests"
    );
    assert!(
        requests
            .iter()
            .any(|request| request.lhs == i && request.rhs == j),
        "ROW2 should request the missing index equality atom"
    );
    assert!(
        requests
            .iter()
            .any(|request| request.lhs == sel_stored_j && request.rhs == sel_a_j),
        "ROW2 should request the missing select equality atom"
    );

    // Lazy generation won't re-queue due to fingerprint.
    solver.generate_all_lazy_row2_axioms();
    assert!(
        solver.check_row2().is_none(),
        "duplicate missing equality requests should be suppressed until new atoms appear"
    );
}

#[test]
fn test_arrays_requested_model_eqs_import_export_suppresses_row2_rerequests_8594() {
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
        .expect("first solver should request the missing ROW2 equality atoms")
    else {
        panic!("expected NeedModelEqualities from first solver ROW2 check");
    };
    assert_eq!(requests.len(), 2);

    let exported = solver.export_requested_model_eqs();
    assert_eq!(
        exported.len(),
        2,
        "exported requested_model_eqs should retain both missing ROW2 atoms"
    );
    assert!(exported.contains(&ArraySolver::ordered_pair(i, j)));
    assert!(exported.contains(&ArraySolver::ordered_pair(sel_stored_j, sel_a_j)));

    let mut fresh = ArraySolver::new(&store);
    fresh.import_requested_model_eqs(&exported);
    fresh.populate_caches();
    fresh.generate_all_lazy_row2_axioms();

    assert!(
        fresh.check_row2().is_none(),
        "fresh solver must not re-request ROW2 clause atoms after importing requested_model_eqs"
    );
    assert_eq!(
        fresh.export_requested_model_eqs(),
        exported,
        "fresh solver should preserve the imported dedup set without growing it"
    );
}

#[test]
fn test_arrays_requested_model_eqs_import_export_suppresses_row2_upward_rerequests_8594() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let _sel_b_j = store.mk_select(b, j);
    let _sel_stored_j = store.mk_select(stored, j);
    let eq_a_b = store.mk_eq(a, b);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_a_b, true);

    let TheoryResult::NeedModelEquality(request) = solver
        .check_row2_upward_with_guidance()
        .expect("first solver should request upward ROW2 guidance")
    else {
        panic!("expected NeedModelEquality from first solver ROW2-upward check");
    };
    assert!(
        (request.lhs == i && request.rhs == j) || (request.lhs == j && request.rhs == i),
        "upward guidance should request the store/select index pair"
    );
    assert_eq!(
        request.reason,
        vec![TheoryLit::new(eq_a_b, true)],
        "upward guidance should carry the asserted base-alias reason"
    );

    let exported = solver.export_requested_model_eqs();
    assert_eq!(
        exported,
        [ArraySolver::ordered_pair(i, j)].into_iter().collect(),
        "exported requested_model_eqs should retain the upward guidance pair"
    );

    let mut fresh = ArraySolver::new(&store);
    fresh.import_requested_model_eqs(&exported);
    fresh.assert_literal(eq_a_b, true);

    assert!(
        fresh.check_row2_upward_with_guidance().is_none(),
        "fresh solver must not re-request ROW2-upward guidance after importing requested_model_eqs"
    );
    assert_eq!(
        fresh.export_requested_model_eqs(),
        exported,
        "fresh solver should preserve the imported upward dedup set without growing it"
    );
}

#[test]
fn test_arrays_exact_select_keys_import_export_suppresses_row2_rerequests_8785() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let _sel_stored_j = store.mk_select(stored, j);
    let _sel_a_j = store.mk_select(a, j);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();
    solver.generate_all_lazy_row2_axioms();

    let TheoryResult::NeedModelEqualities(requests) = solver
        .check_row2()
        .expect("first solver should request missing exact-select ROW2 atoms")
    else {
        panic!("expected NeedModelEqualities from first solver ROW2 check");
    };
    assert_eq!(requests.len(), 2);

    let exported = solver.export_exact_select_model_eq_keys();
    assert_eq!(
        exported.len(),
        2,
        "ROW2-down should export both exact-select duplicate-suppression keys"
    );

    let mut fresh = ArraySolver::new(&store);
    fresh.import_exact_select_model_eq_keys(&exported);
    fresh.populate_caches();
    fresh.generate_all_lazy_row2_axioms();

    assert!(
        fresh.check_row2().is_none(),
        "fresh solver must not re-request ROW2 exact-select atoms after importing exact-select keys"
    );
    assert!(
        fresh.export_requested_model_eqs().is_empty(),
        "exact-select key import should suppress before growing requested_model_eqs"
    );
}

#[test]
fn test_arrays_row2_skips_same_index_alias_branch() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let sel_b_i = store.mk_select(b, i);
    let eq_b_store = store.mk_eq(b, stored);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_b_store, true);
    solver.populate_caches();

    assert!(
        solver.pending_row1.contains(&(sel_b_i, stored)),
        "same-index alias should stay on the ROW1 path"
    );
    assert_eq!(
        solver.pending_axioms,
        vec![PendingAxiom::Row2Down {
            store: stored,
            select: sel_b_i,
        }],
        "equality merge still queues the structural ROW2 candidate"
    );

    assert!(
        solver.check_row2().is_none(),
        "ROW2 must not request clause atoms or model equalities when the indices are already equal"
    );
    assert!(
        solver.pending_axioms.is_empty(),
        "same-index ROW2 candidates should be dropped from the current queue"
    );
    assert!(
        solver.blocked_axioms.is_empty(),
        "same-index ROW2 must not be moved into the blocked missing-atom queue"
    );
    assert!(
        solver.requested_model_eqs.is_empty(),
        "same-index ROW2 must not request spurious model equalities"
    );
    assert!(
        !solver.axiom_fingerprints.contains(&(stored, i)),
        "same-index ROW2 must forget its exact fingerprint so future non-equal branches can requeue it"
    );
}

#[test]
fn test_arrays_registered_atom_scope_filters_dead_assumption_terms() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort.clone());
    let c = store.mk_var("c", arr_sort);
    let zero = store.mk_int(BigInt::from(0));
    let ten = store.mk_int(BigInt::from(10));
    let twenty = store.mk_int(BigInt::from(20));
    let thirty = store.mk_int(BigInt::from(30));

    let sel_a_0 = store.mk_select(a, zero);
    let base_eq = store.mk_eq(sel_a_0, ten);

    let dead_store = store.mk_store(a, zero, twenty);
    let dead_eq = store.mk_eq(b, dead_store);
    let dead_sel = store.mk_select(b, zero);
    let dead_sel_eq = store.mk_eq(dead_sel, ten);

    let live_store = store.mk_store(a, zero, thirty);
    let live_eq = store.mk_eq(c, live_store);
    let live_sel = store.mk_select(c, zero);
    let live_sel_eq = store.mk_eq(live_sel, thirty);

    let mut solver = ArraySolver::new(&store);
    solver.enable_registered_atom_scope(true);
    TheorySolver::register_atom(&mut solver, base_eq);
    TheorySolver::register_atom(&mut solver, live_eq);
    TheorySolver::register_atom(&mut solver, live_sel_eq);
    solver.assert_literal(base_eq, true);
    solver.assert_literal(live_eq, true);
    solver.assert_literal(live_sel_eq, true);

    solver.populate_caches();

    assert!(
        solver.store_cache.contains_key(&live_store),
        "live store from the current assumption set must stay visible"
    );
    assert!(
        solver.select_cache.contains_key(&live_sel),
        "live select from the current assumption set must stay visible"
    );
    assert!(
        !solver.store_cache.contains_key(&dead_store),
        "dead store from an inactive assumption set must be excluded"
    );
    assert!(
        !solver.select_cache.contains_key(&dead_sel),
        "dead select from an inactive assumption set must be excluded"
    );
    assert!(
        !solver.equality_cache.contains_key(&dead_eq)
            && !solver.equality_cache.contains_key(&dead_sel_eq),
        "dead assumption equalities must not be indexed into the scoped caches"
    );

    let mut term_values = HashMap::default();
    term_values.insert(zero, "0".to_string());
    term_values.insert(ten, "10".to_string());
    term_values.insert(thirty, "30".to_string());
    term_values.insert(sel_a_0, "10".to_string());
    term_values.insert(live_sel, "30".to_string());
    let model = solver.extract_model(&term_values);

    let live_interp = model.array_values.get(&c).expect(
        "live alias array should retain its store interpretation under registered-atom scoping",
    );
    assert_eq!(
        live_interp.stores,
        vec![("0".to_string(), "30".to_string())],
        "live alias array should inherit the scoped store interpretation"
    );
    assert!(
        !model.array_values.contains_key(&b),
        "dead alias arrays from inactive assumptions must stay out of the extracted model"
    );
}

#[test]
fn test_array_var_tracking_registers_store_select_relationships() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let select_on_store = store.mk_select(stored, j);
    let select_on_base = store.mk_select(a, j);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();

    let base_data = solver
        .array_vars
        .get(&a)
        .expect("base array should be tracked");
    assert_eq!(
        base_data.parent_selects,
        vec![select_on_base],
        "base array should track its parent select"
    );
    assert_eq!(
        base_data.parent_stores,
        vec![stored],
        "base array should track parent stores that read from it"
    );
    assert!(
        base_data.prop_upward,
        "base array with both a parent store and parent select must request upward ROW2 work"
    );

    let result_data = solver
        .array_vars
        .get(&stored)
        .expect("store result array should be tracked");
    assert_eq!(
        result_data.stores_as_result,
        vec![stored],
        "store result should track itself as a result array"
    );
    assert_eq!(
        result_data.parent_selects,
        vec![select_on_store],
        "store result should track selects over the stored array"
    );
    assert_eq!(
        solver.get_exact_select_term(a, j),
        Some(select_on_base),
        "exact select lookup should recover the base-array select term"
    );
    assert_eq!(
        solver.get_exact_select_term(stored, j),
        Some(select_on_store),
        "exact select lookup should recover the store-result select term"
    );

    // #8141: Lazy axiom generation — ROW2 axioms are no longer queued
    // during populate_caches(). Call generate_all_lazy_row2_axioms() to test.
    assert!(
        solver.pending_axioms.is_empty(),
        "populate_caches should not eagerly queue ROW2 axioms (#8141)"
    );
    solver.generate_all_lazy_row2_axioms();
    assert_eq!(
        solver.pending_axioms,
        vec![PendingAxiom::Row2Down {
            store: stored,
            select: select_on_store,
        }],
        "one ROW2-down axiom should be queued after lazy generation"
    );
    assert!(
        solver.axiom_fingerprints.contains(&(stored, j)),
        "ROW2 fingerprint should be keyed by the store term and select index"
    );
    assert_eq!(
        solver.populated_terms,
        store.len(),
        "populate_caches should advance the high-water mark"
    );
}

#[test]
fn test_array_var_tracking_repopulate_is_idempotent() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let select_on_store = store.mk_select(stored, j);
    let select_on_base = store.mk_select(a, j);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();
    // #8141: Lazy axiom generation — populate caches, then generate
    // axioms to test idempotency of both steps.
    solver.generate_all_lazy_row2_axioms();
    let expected_vars = solver.array_vars.clone();
    let expected_axioms = solver.pending_axioms.clone();
    let expected_fingerprints = solver.axiom_fingerprints.clone();

    solver.populate_caches();
    solver.generate_all_lazy_row2_axioms();

    assert_eq!(
        solver.array_vars, expected_vars,
        "re-running populate_caches without new terms must not duplicate per-array tracking"
    );
    assert_eq!(
        solver.pending_axioms, expected_axioms,
        "re-running lazy generation without new terms must not queue duplicate axioms"
    );
    assert_eq!(
        solver.axiom_fingerprints, expected_fingerprints,
        "re-running lazy generation without new terms must not add duplicate fingerprints"
    );
    assert!(
        solver
            .array_vars
            .get(&a)
            .is_some_and(|data| data.parent_selects == vec![select_on_base]),
        "base array tracking should remain stable across repeated cache populations"
    );
    assert!(
        solver
            .array_vars
            .get(&stored)
            .is_some_and(|data| data.parent_selects == vec![select_on_store]),
        "store-result tracking should remain stable across repeated cache populations"
    );
}

#[test]
fn test_row2_fingerprint_dedups_equal_index_aliases() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let k = store.mk_var("k", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let select_j = store.mk_select(stored, j);
    let select_k = store.mk_select(stored, k);
    let eq_jk = store.mk_eq(j, k);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();
    solver.pending_axioms.clear();
    solver.axiom_fingerprints.clear();
    solver.row2_fingerprint_indices.clear();

    solver.queue_row2_down_axiom(stored, select_j);
    assert_eq!(
        solver.pending_axioms,
        vec![PendingAxiom::Row2Down {
            store: stored,
            select: select_j,
        }],
        "first ROW2 candidate should be queued exactly once"
    );

    solver.assert_literal(eq_jk, true);
    solver.queue_row2_down_axiom(stored, select_k);

    assert_eq!(
        solver.pending_axioms,
        vec![PendingAxiom::Row2Down {
            store: stored,
            select: select_j,
        }],
        "current-equality dedup should suppress a second ROW2 axiom for an alias-equivalent index"
    );
    assert_eq!(
        solver
            .row2_fingerprint_indices
            .get(&stored)
            .cloned()
            .unwrap_or_default(),
        vec![j],
        "only the exact queued index should be kept in the persistent fingerprint history"
    );
}

#[test]
fn test_row2_fingerprint_dedup_is_backtrack_safe() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let k = store.mk_var("k", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let stored = store.mk_store(a, i, v);
    let select_j = store.mk_select(stored, j);
    let select_k = store.mk_select(stored, k);
    let eq_jk = store.mk_eq(j, k);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();
    solver.pending_axioms.clear();
    solver.axiom_fingerprints.clear();
    solver.row2_fingerprint_indices.clear();

    solver.queue_row2_down_axiom(stored, select_j);
    solver.push();
    solver.assert_literal(eq_jk, true);
    solver.queue_row2_down_axiom(stored, select_k);
    assert_eq!(
        solver.pending_axioms.len(),
        1,
        "branch-local equality should suppress alias-equivalent ROW2 work"
    );

    solver.pop();
    solver.populate_caches();
    solver.queue_row2_down_axiom(stored, select_k);

    assert_eq!(
        solver.pending_axioms,
        vec![PendingAxiom::Row2Down {
            store: stored,
            select: select_k,
        }],
        "after backtracking the alias equality away, the distinct exact index must queue normally"
    );
    assert_eq!(
        solver
            .row2_fingerprint_indices
            .get(&stored)
            .cloned()
            .unwrap_or_default(),
        vec![j, k],
        "persistent fingerprint history should retain both exact indices once they are queued in distinct branches"
    );
}

#[test]
fn test_array_var_tracking_notify_equality_repopulate_keeps_merged_state() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let select_on_a = store.mk_select(a, j);
    let store_on_b = store.mk_store(b, i, v);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();
    solver.notify_equality(a, b);

    let merged = solver
        .array_vars
        .get(&a)
        .expect("notify_equality should preserve merged array data");
    assert_eq!(
        merged.parent_selects,
        vec![select_on_a],
        "target array should keep its original parent select"
    );
    assert_eq!(
        merged.parent_stores,
        vec![store_on_b],
        "target array should inherit parent stores from the equal array"
    );
    assert!(
        merged.prop_upward,
        "merged array data should request upward ROW2 when stores and selects come from different equal arrays"
    );

    solver.populate_caches();

    let merged = solver
        .array_vars
        .get(&a)
        .expect("merged array data should survive repopulation");
    assert_eq!(
        merged.parent_selects,
        vec![select_on_a],
        "repopulation must preserve the target array's parent select"
    );
    assert_eq!(
        merged.parent_stores,
        vec![store_on_b],
        "repopulation must preserve equality-driven parent stores"
    );
    assert!(
        merged.prop_upward,
        "repopulation must not drop upward ROW2 eligibility derived from merged data"
    );
}

#[test]
fn test_array_var_tracking_assert_literal_true_queues_cross_equal_row2() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let select_on_a = store.mk_select(a, j);
    let store_on_b = store.mk_store(b, i, v);
    let eq_ab = store.mk_eq(a, b);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_ab, true);

    let merged = solver
        .array_vars
        .get(&a)
        .expect("asserted array equality should merge direct ArrayVarData");
    assert_eq!(
        merged.parent_selects,
        vec![select_on_a],
        "direct array equality should preserve target parent selects"
    );
    assert_eq!(
        merged.parent_stores,
        vec![store_on_b],
        "direct array equality should inherit parent stores from the equal array"
    );
    assert!(
        merged.prop_upward,
        "direct array equality should mark the merged array for upward ROW2"
    );
    assert!(
        solver.pending_axioms.contains(&PendingAxiom::Row2Down {
            store: store_on_b,
            select: select_on_a,
        }),
        "direct array equality should queue the cross-array ROW2 axiom"
    );
    assert!(
        solver.axiom_fingerprints.contains(&(store_on_b, j)),
        "queued direct-equality ROW2 work should record its fingerprint"
    );
}

#[test]
fn test_array_var_tracking_assert_literal_unwraps_not_equalities() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let select_on_a = store.mk_select(a, j);
    let store_on_b = store.mk_store(b, i, v);
    let eq_ab = store.mk_eq(a, b);
    let not_eq_ab = store.mk_not(eq_ab);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(not_eq_ab, false);

    let merged = solver
        .array_vars
        .get(&a)
        .expect("false on not(= a b) should be treated as a = b");
    assert_eq!(
        merged.parent_selects,
        vec![select_on_a],
        "negated equality literal should unwrap before merging parent selects"
    );
    assert_eq!(
        merged.parent_stores,
        vec![store_on_b],
        "negated equality literal should unwrap before merging parent stores"
    );
    assert!(
        solver.pending_axioms.contains(&PendingAxiom::Row2Down {
            store: store_on_b,
            select: select_on_a,
        }),
        "negated equality literal should still queue the direct-equality ROW2 axiom"
    );
}

#[test]
fn test_disjunctive_store_target_guidance_tracks_direct_store_equalities_6885() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let w = store.mk_var("w", Sort::Int);

    let store_x = store.mk_store(a, x, v);
    let store_y = store.mk_store(a, y, w);
    let eq_store_x_b = store.mk_eq(store_x, b);
    let eq_store_y_b = store.mk_eq(store_y, b);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_store_x_b, true);
    solver.assert_literal(eq_store_y_b, true);

    let result = solver.check_disjunctive_store_target_equalities();
    // #8596: Array-sorted model equality requests are now skipped because
    // array equality is handled by extensionality axioms, not N-O speculation.
    // So only the index equality (x, y) is requested, not (a, b).
    let TheoryResult::NeedModelEquality(request) =
        result.expect("dual store equalities should request disjunctive guidance")
    else {
        panic!("expected NeedModelEquality for store-index guidance (array base-target pair skipped per #8596)");
    };

    assert_eq!(
        ArraySolver::ordered_pair(request.lhs, request.rhs),
        ArraySolver::ordered_pair(x, y),
        "must request the store-index equality branch (base-target skipped for Array sort per #8596)"
    );
}

/// Verify array equality conflict explanations are sound.
/// If a = b, then select(a, i) = select(b, i)
#[test]
fn test_arrays_equality_conflict_soundness() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let i = store.mk_var("i", Sort::Int);

    let sel_a = store.mk_select(a, i);
    let sel_b = store.mk_select(b, i);

    let eq_ab = store.mk_eq(a, b);
    let eq_sels = store.mk_eq(sel_a, sel_b);

    let mut solver = ArraySolver::new(&store);

    // Assert a = b and select(a, i) ≠ select(b, i) (contradiction)
    solver.assert_literal(eq_ab, true);
    solver.assert_literal(eq_sels, false);

    solver.populate_caches();
    let result = solver
        .check_array_equality()
        .expect("expected array-equality helper to emit a lemma");
    assert!(
        matches!(&result, TheoryResult::NeedLemmas(_)),
        "array-equality helper should now route through lemma emission, got {result:?}"
    );
    assert_conflict_soundness(result, ArraySolver::new(&store));
}

/// #select-read-conflict-fail-closed regression: two committed reads of ONE
/// (base, index-value) cell that DISAGREE (e.g. a ground read and a read at a
/// symbolic index the model evaluates to the same value, whose merged
/// completion went stale) must DROP the cell from the extracted
/// interpretation — a partial interp is the fail-closed posture — instead of
/// baking the first writer in as the model's committed truth (which the
/// validators and the independent model-check gate then wrongly refute a
/// genuine `Sat` against: the tla-ay seq-concat regression).
#[test]
fn test_extract_model_conflicting_select_reads_drop_the_cell() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let one = store.mk_int(BigInt::from(1));
    let i = store.mk_var("i", Sort::Int); // symbolic index, model gives 1
    let sel_ground = store.mk_select(a, one);
    let sel_symbolic = store.mk_select(a, i);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();
    assert!(
        solver.select_cache.contains_key(&sel_ground)
            && solver.select_cache.contains_key(&sel_symbolic),
        "both reads must be tracked for the extraction to see the conflict"
    );

    let mut term_values = HashMap::default();
    term_values.insert(one, "1".to_string());
    term_values.insert(i, "1".to_string()); // collides with the ground read
    term_values.insert(sel_ground, "10".to_string());
    term_values.insert(sel_symbolic, "0".to_string()); // disagreeing read

    let model = solver.extract_model(&term_values);
    if let Some(interp) = model.array_values.get(&a) {
        assert!(
            !interp.stores.iter().any(|(k, _)| k == "1"),
            "a cell with two disagreeing committed reads must be dropped \
             (fail closed), not first-writer-win; got stores {:?}",
            interp.stores
        );
    }
}

/// Control for `test_extract_model_conflicting_select_reads_drop_the_cell`:
/// two AGREEING reads of one cell keep it (the #7022 select-derived path is
/// not weakened).
#[test]
fn test_extract_model_agreeing_select_reads_keep_the_cell() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let one = store.mk_int(BigInt::from(1));
    let i = store.mk_var("i", Sort::Int);
    let sel_ground = store.mk_select(a, one);
    let sel_symbolic = store.mk_select(a, i);

    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();
    assert!(
        solver.select_cache.contains_key(&sel_ground)
            && solver.select_cache.contains_key(&sel_symbolic)
    );

    let mut term_values = HashMap::default();
    term_values.insert(one, "1".to_string());
    term_values.insert(i, "1".to_string());
    term_values.insert(sel_ground, "10".to_string());
    term_values.insert(sel_symbolic, "10".to_string()); // agrees

    let model = solver.extract_model(&term_values);
    let interp = model
        .array_values
        .get(&a)
        .expect("agreeing select-derived reads must yield an interpretation");
    assert_eq!(
        interp.stores.iter().filter(|(k, _)| k == "1").count(),
        1,
        "the agreed cell must be kept exactly once; got stores {:?}",
        interp.stores
    );
    assert_eq!(
        interp
            .stores
            .iter()
            .find(|(k, _)| k == "1")
            .map(|(_, v)| v.as_str()),
        Some("10")
    );
}

/// A committed scalar value for `(default a)` is the semantic else-value of
/// `a`; extraction must not leave it stranded in the EUF/LIA term map.
#[test]
fn test_extract_model_materializes_symbolic_array_default() {
    let mut store = TermStore::new();
    let a = store.mk_var("a", make_array_sort());
    let default = store.mk_array_default(a);
    let mut solver = ArraySolver::new(&store);
    solver.populate_caches();

    let term_values = HashMap::from_iter([(default, "7".to_string())]);
    let model = solver.extract_model(&term_values);
    let interp = model
        .array_values
        .get(&a)
        .expect("a committed default term must create an array interpretation");
    assert_eq!(interp.default.as_deref(), Some("7"));
    assert_eq!(interp.index_sort.as_ref(), Some(&Sort::Int));
    assert_eq!(interp.element_sort.as_ref(), Some(&Sort::Int));
}

/// Assigning an already-registered equality atom while newer terms are still
/// pending registration must stay on the incremental warm path and must not
/// force a full assignment-index rebuild.
#[test]
fn test_old_atom_assignment_with_pending_terms_stays_incremental() {
    let mut store = TermStore::new();
    let x0 = store.mk_var("x0", Sort::Int);
    let x1 = store.mk_var("x1", Sort::Int);
    let x2 = store.mk_var("x2", Sort::Int);
    let eq01 = store.mk_eq(x0, x1);
    let eq12 = store.mk_eq(x1, x2);
    // This pure scalar has no cache effect when registered, so it can safely
    // represent the pending suffix in this focused regression.
    let _trailing = store.mk_var("trailing", Sort::Int);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq01, true);
    solver.populate_caches();
    assert!(solver.get_equiv_class(x0).contains(&x1));

    solver.populated_terms = store.len() - 1;
    assert!(solver.populated_terms < store.len());

    let rebuilds_before = solver.assign_index_rebuilds;
    solver.assert_literal(eq12, true);
    assert!(
        !solver.assign_dirty,
        "old-atom assignment with pending terms must not force assign_dirty"
    );
    solver.populate_caches();
    assert_eq!(
        solver.assign_index_rebuilds, rebuilds_before,
        "the incremental warm path must avoid a full rebuild_assign_indices"
    );
    assert!(solver.get_equiv_class(x0).contains(&x2));
}
