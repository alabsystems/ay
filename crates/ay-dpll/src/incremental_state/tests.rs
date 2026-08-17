// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::Symbol;
use ay_core::{Sort, TheoryLemma, TheoryLit};
use num_bigint::BigInt;

#[test]
fn collect_active_theory_atoms_filters_boolean_structure_but_keeps_bool_equalities() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));

    let lt = terms.mk_app(Symbol::named("<"), vec![x, five], Sort::Bool);
    let eq_xy = terms.mk_app(Symbol::named("="), vec![x, y], Sort::Bool);

    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let eq_bool = terms.mk_app(Symbol::named("="), vec![p, q], Sort::Bool);

    let and_term = terms.mk_app(Symbol::named("and"), vec![lt, eq_bool], Sort::Bool);
    let assertions = [and_term, eq_xy];

    let atoms = collect_active_theory_atoms(&terms, &assertions);
    // Bool-Bool equality (= p q) IS now a theory atom (#6869):
    // EUF must see all equalities to propagate alias chains.
    assert_eq!(atoms.len(), 3);
    assert!(atoms.contains(&lt));
    assert!(atoms.contains(&eq_xy));
    assert!(atoms.contains(&eq_bool));
    assert!(!atoms.contains(&and_term));
}

/// The high-water-mark Bool-UF-arg cache must produce byte-for-byte identical
/// results to the from-scratch (cache: None) scan, even when the TermStore
/// grows incrementally between calls (the incremental check-sat scenario).
#[test]
fn bool_uf_arg_cache_matches_full_scan_across_growth() {
    let mut terms = TermStore::new();
    // Round 1: a UF app with a Bool arg, plus some non-UF structure.
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let n = terms.mk_var("n", Sort::Int);
    // f(p, n) : Bool arg p must be collected as a theory atom.
    let f_pn = terms.mk_app(Symbol::named("f"), vec![p, n], Sort::Int);
    let assert1 = terms.mk_app(Symbol::named("="), vec![f_pn, n], Sort::Bool);

    let mut cache = BoolUfArgCache::default();
    let cached1 = collect_active_theory_atoms_cached(&terms, &[assert1], Some(&mut cache));
    let full1 = collect_active_theory_atoms(&terms, &[assert1]);
    assert_eq!(cached1, full1, "round 1: cached must equal full scan");
    assert_eq!(cache.hwm, terms.len(), "hwm must advance to terms.len()");
    assert!(cache.bool_args.contains(&p), "p is a Bool UF arg");

    // Round 2: grow the TermStore with another UF app carrying a new Bool arg.
    let g_qn = terms.mk_app(Symbol::named("g"), vec![q, n], Sort::Int);
    let assert2 = terms.mk_app(Symbol::named("="), vec![g_qn, n], Sort::Bool);

    let cached2 = collect_active_theory_atoms_cached(&terms, &[assert1, assert2], Some(&mut cache));
    let full2 = collect_active_theory_atoms(&terms, &[assert1, assert2]);
    assert_eq!(
        cached2, full2,
        "round 2 (after growth): cached must equal full scan"
    );
    assert_eq!(cache.hwm, terms.len());
    // Both Bool args must be retained across rounds (monotonic union).
    assert!(cache.bool_args.contains(&p));
    assert!(cache.bool_args.contains(&q));

    // Round 3: no growth — cached result must still match full scan exactly.
    let cached3 = collect_active_theory_atoms_cached(&terms, &[assert1, assert2], Some(&mut cache));
    let full3 = collect_active_theory_atoms(&terms, &[assert1, assert2]);
    assert_eq!(
        cached3, full3,
        "round 3 (no growth): cached must equal full"
    );
}

/// Defensive guard: if the cache is ever reused with a smaller TermStore, it
/// must fall back to a full re-scan rather than trusting stale TermIds.
#[test]
fn bool_uf_arg_cache_resets_on_shrunk_termstore() {
    let mut big = TermStore::new();
    let p = big.mk_var("p", Sort::Bool);
    let n = big.mk_var("n", Sort::Int);
    let f_pn = big.mk_app(Symbol::named("f"), vec![p, n], Sort::Int);
    let _a = big.mk_app(Symbol::named("="), vec![f_pn, n], Sort::Bool);

    let mut cache = BoolUfArgCache::default();
    let _ = collect_active_theory_atoms_cached(&big, &[_a], Some(&mut cache));
    assert!(cache.hwm > 0);

    // Fresh, smaller TermStore reuses the same cache. The guard must reset.
    let mut small = TermStore::new();
    let q = small.mk_var("q", Sort::Bool);
    let m = small.mk_var("m", Sort::Int);
    let g_qm = small.mk_app(Symbol::named("g"), vec![q, m], Sort::Int);
    let b = small.mk_app(Symbol::named("="), vec![g_qm, m], Sort::Bool);

    let cached = collect_active_theory_atoms_cached(&small, &[b], Some(&mut cache));
    let full = collect_active_theory_atoms(&small, &[b]);
    assert_eq!(cached, full, "after shrink, cached must equal full re-scan");
    assert_eq!(cache.hwm, small.len());
    assert!(cache.bool_args.contains(&q));
    let _ = p; // (silence unused in case the var optimizes away)
}

#[test]
fn incremental_bv_state_push_pop_tracks_pending_when_solver_missing() {
    let mut st = IncrementalBvState::new();
    assert_eq!(st.scope_depth, 0);
    assert_eq!(st.pending_pushes, 0);

    st.push();
    assert_eq!(st.scope_depth, 1);
    assert_eq!(st.pending_pushes, 1);

    assert!(st.pop());
    assert_eq!(st.scope_depth, 0);
    assert_eq!(st.pending_pushes, 0);
    assert!(!st.pop());
}

#[test]
fn incremental_bv_state_pop_invalidates_sat_when_present() {
    let mut st = IncrementalBvState::new();
    st.persistent_sat = Some(SatSolver::new(0));
    st.term_to_bits
        .insert(TermId::new(1), vec![1, 2, 3, 4, 5, 6, 7, 8]);
    st.encoded_assertions.insert(TermId::new(2), 9);

    st.push();
    assert_eq!(st.scope_depth, 1);
    assert_eq!(st.pending_pushes, 0);
    assert_eq!(st.persistent_sat.as_ref().unwrap().scope_depth(), 1);

    assert!(st.pop());
    assert_eq!(st.scope_depth, 0);
    assert_eq!(st.pending_pushes, 0);
    assert!(st.persistent_sat.is_none());
    assert!(st.term_to_bits.is_empty());
    assert!(st.encoded_assertions.is_empty());
}

#[test]
fn incremental_bv_state_sync_tseitin_and_bv_vars_include_scope_selectors() {
    let mut st = IncrementalBvState::new();

    let mut sat = SatSolver::new(0);
    sat.push(); // adds an internal scope selector variable

    let total = sat.total_num_vars() as u32;
    st.persistent_sat = Some(sat);
    st.tseitin_state.next_var = 1;
    st.next_bv_var = 1;

    st.sync_tseitin_next_var();
    assert!(
        st.tseitin_state.next_var > total,
        "expected tseitin next_var > total_num_vars"
    );

    st.sync_next_bv_var();
    assert!(
        st.next_bv_var > total,
        "expected bv next_var > total_num_vars"
    );
}

#[test]
fn incremental_theory_state_push_pop_tracks_pending_before_solver_creation() {
    let mut st = IncrementalTheoryState::new();
    assert_eq!(st.scope_depth, 0);
    assert_eq!(st.pending_push, 0);
    assert!(!st.needs_activation_reassert);

    st.push();
    st.push();
    assert_eq!(st.scope_depth, 2);
    assert_eq!(st.pending_push, 2);

    assert!(st.pop());
    assert_eq!(st.scope_depth, 1);
    assert_eq!(st.pending_push, 1);
    assert!(st.needs_activation_reassert);
}

#[test]
fn incremental_theory_state_push_pop_delegates_to_sat_when_present() {
    let mut st = IncrementalTheoryState::new();
    st.persistent_sat = Some(SatSolver::new(0));
    st.lia_persistent_sat = Some(SatSolver::new(0));
    assert!(!st.needs_activation_reassert);

    st.push();
    assert_eq!(st.scope_depth, 1);
    assert_eq!(st.pending_push, 0);
    assert_eq!(st.persistent_sat.as_ref().unwrap().scope_depth(), 1);
    assert_eq!(st.lia_persistent_sat.as_ref().unwrap().scope_depth(), 1);

    assert!(st.pop());
    assert_eq!(st.scope_depth, 0);
    assert_eq!(st.persistent_sat.as_ref().unwrap().scope_depth(), 0);
    assert_eq!(st.lia_persistent_sat.as_ref().unwrap().scope_depth(), 0);
    assert!(st.needs_activation_reassert);
}

#[test]
fn incremental_theory_state_pop_retains_lower_scope_lemmas() {
    let mut st = IncrementalTheoryState::new();

    // Add a lemma at scope 0 (global)
    let global_lemma = TheoryLemma::new(vec![TheoryLit::new(TermId::new(1), true)]);
    st.theory_lemmas.push((global_lemma.clone(), 0));
    st.theory_lemma_keys.insert(global_lemma.clause.clone());

    st.push(); // scope 1
               // Add a lemma at scope 1
    let scoped_lemma = TheoryLemma::new(vec![TheoryLit::new(TermId::new(2), false)]);
    st.theory_lemmas.push((scoped_lemma.clone(), 1));
    st.theory_lemma_keys.insert(scoped_lemma.clause.clone());
    st.original_clause_theory_proofs.push(None);
    st.original_clause_theory_proofs.push(None);

    assert!(st.pop()); // back to scope 0
                       // Global lemma survives in the replay ledger; scoped lemma is removed (#8157)
    assert_eq!(st.theory_lemmas.len(), 1);
    assert_eq!(st.theory_lemmas[0].0, global_lemma);
    assert_eq!(st.theory_lemmas[0].1, 0);
    // Dedup key set is cleared entirely after pop because the SAT solver's
    // pop invalidates all scoped clauses, and retained lemmas need to be
    // re-added as SAT clauses if re-derived by the theory.
    assert!(st.theory_lemma_keys.is_empty());
    // #8572: Proof annotation ledgers are now trimmed on pop to match
    // OriginalLedger truncation (#8472). Entries added at scope 1 are removed.
    assert_eq!(st.original_clause_theory_proofs.len(), 0);
}

#[test]
fn incremental_theory_state_pop_clears_all_lemmas_when_all_scoped() {
    let mut st = IncrementalTheoryState::new();
    st.push(); // scope 1
    st.theory_lemmas.push((
        TheoryLemma::new(vec![TheoryLit::new(TermId::new(1), true)]),
        1,
    ));
    st.theory_lemmas.push((
        TheoryLemma::new(vec![TheoryLit::new(TermId::new(2), false)]),
        1,
    ));

    assert!(st.pop());
    assert!(st.theory_lemmas.is_empty());
    assert!(st.theory_lemma_keys.is_empty());
}

#[test]
fn incremental_theory_state_nested_push_pop_retains_correct_scopes() {
    let mut st = IncrementalTheoryState::new();

    // Lemma at scope 0
    let l0 = TheoryLemma::new(vec![TheoryLit::new(TermId::new(10), true)]);
    st.theory_lemmas.push((l0.clone(), 0));
    st.theory_lemma_keys.insert(l0.clause.clone());

    st.push(); // scope 1
    let l1 = TheoryLemma::new(vec![TheoryLit::new(TermId::new(20), true)]);
    st.theory_lemmas.push((l1.clone(), 1));
    st.theory_lemma_keys.insert(l1.clause.clone());

    st.push(); // scope 2
    let l2 = TheoryLemma::new(vec![TheoryLit::new(TermId::new(30), true)]);
    st.theory_lemmas.push((l2.clone(), 2));
    st.theory_lemma_keys.insert(l2.clause.clone());

    // Pop scope 2 -> scope 1: retains l0 and l1, removes l2
    assert!(st.pop());
    assert_eq!(st.theory_lemmas.len(), 2);
    assert_eq!(st.theory_lemmas[0].0, l0);
    assert_eq!(st.theory_lemmas[1].0, l1);
    // Keys cleared on pop (SAT clauses invalidated)
    assert!(st.theory_lemma_keys.is_empty());

    // Pop scope 1 -> scope 0: retains only l0
    assert!(st.pop());
    assert_eq!(st.theory_lemmas.len(), 1);
    assert_eq!(st.theory_lemmas[0].0, l0);
    assert!(st.theory_lemma_keys.is_empty());

    // Pop scope 0 -> underflow returns false
    assert!(!st.pop());
    // Scope 0 lemma is still there (pop didn't execute)
    assert_eq!(st.theory_lemmas.len(), 1);
}

#[test]
fn incremental_theory_state_retain_encoded_assertions_keeps_only_active() {
    let mut st = IncrementalTheoryState::new();
    st.encoded_assertions.insert(TermId::new(1), 101);
    st.encoded_assertions.insert(TermId::new(2), 102);
    st.encoded_assertions.insert(TermId::new(3), 103);
    st.assertion_activation_scope.insert(TermId::new(1), 1);
    st.assertion_activation_scope.insert(TermId::new(2), 0);
    st.assertion_activation_scope.insert(TermId::new(3), 2);

    st.retain_encoded_assertions(&[TermId::new(2), TermId::new(4)]);

    assert_eq!(st.encoded_assertions.len(), 1);
    assert!(st.encoded_assertions.contains_key(&TermId::new(2)));
    assert_eq!(st.assertion_activation_scope.len(), 1);
    assert_eq!(st.assertion_activation_scope.get(&TermId::new(2)), Some(&0));
}

#[test]
fn incremental_theory_state_sync_tseitin_next_var_uses_total_num_vars() {
    let mut st = IncrementalTheoryState::new();

    let mut sat = SatSolver::new(0);
    sat.push(); // internal selector, total_num_vars increases
    let total = sat.total_num_vars() as u32;
    assert_eq!(sat.user_num_vars(), 0);
    assert_eq!(sat.scope_depth(), 1);

    st.persistent_sat = Some(sat);
    st.tseitin_state.next_var = 1;

    st.sync_tseitin_next_var();
    assert!(
        st.tseitin_state.next_var > total,
        "expected tseitin next_var > total_num_vars"
    );
}

#[test]
fn incremental_bv_state_reset_clears_all_state() {
    let mut st = IncrementalBvState::new();

    // Modify all fields from their defaults
    // BvBits is just Vec<i32> (CnfLit), so use vec!
    st.term_to_bits
        .insert(TermId::new(1), vec![1, 2, 3, 4, 5, 6, 7, 8]);
    st.next_bv_var = 100;
    st.scope_depth = 3;
    st.pending_pushes = 2;
    st.persistent_sat = Some(SatSolver::new(10));
    st.tseitin_state.next_var = 50;
    st.encoded_assertions.insert(TermId::new(1), 5);
    st.sat_num_vars = 20;
    st.bv_var_offset = Some(10);
    st.predicate_to_var.insert(TermId::new(2), 7);
    st.bool_to_var.insert(TermId::new(3), 8);
    st.linked_equivalence_terms.insert(TermId::new(4));
    st.assertion_activation_scope.insert(TermId::new(9), 2);
    st.emitted_bv_eq_congruence_pairs
        .insert((TermId::new(10), TermId::new(11)));

    // Reset
    st.reset();

    // Verify all fields are reset to initial state
    assert!(st.term_to_bits.is_empty());
    assert_eq!(st.next_bv_var, 1);
    assert_eq!(st.scope_depth, 0);
    assert_eq!(st.pending_pushes, 0);
    assert!(st.persistent_sat.is_none());
    assert_eq!(st.tseitin_state.next_var, 1);
    assert!(st.encoded_assertions.is_empty());
    assert!(st.assertion_activation_scope.is_empty());
    assert_eq!(st.sat_num_vars, 0);
    assert!(st.bv_var_offset.is_none());
    assert!(st.emitted_bv_eq_congruence_pairs.is_empty());
    assert!(st.predicate_to_var.is_empty());
    assert!(st.bool_to_var.is_empty());
    assert!(st.linked_equivalence_terms.is_empty());
}

#[test]
fn incremental_bv_state_rebuild_reset_preserves_scope_depth() {
    let mut st = IncrementalBvState::new();
    st.scope_depth = 3;
    st.pending_pushes = 1;
    st.term_to_bits
        .insert(TermId::new(1), vec![1, 2, 3, 4, 5, 6, 7, 8]);
    st.persistent_sat = Some(SatSolver::new(10));
    st.tseitin_state.next_var = 12;
    st.encoded_assertions.insert(TermId::new(2), 4);
    st.bv_var_offset = Some(9);
    st.predicate_to_var.insert(TermId::new(3), 11);
    st.bool_to_var.insert(TermId::new(4), 12);
    st.linked_equivalence_terms.insert(TermId::new(5));
    st.assertion_activation_scope.insert(TermId::new(6), 3);
    st.emitted_bv_eq_congruence_pairs
        .insert((TermId::new(7), TermId::new(8)));

    st.reset_sat_encoding_for_rebuild();

    assert_eq!(st.scope_depth, 3);
    assert_eq!(st.pending_pushes, 3);
    assert!(st.term_to_bits.is_empty());
    assert_eq!(st.next_bv_var, 1);
    assert!(st.persistent_sat.is_none());
    assert_eq!(st.tseitin_state.next_var, 1);
    assert!(st.encoded_assertions.is_empty());
    assert!(st.assertion_activation_scope.is_empty());
    assert_eq!(st.sat_num_vars, 0);
    assert!(st.bv_var_offset.is_none());
    assert!(st.emitted_bv_eq_congruence_pairs.is_empty());
    assert!(st.predicate_to_var.is_empty());
    assert!(st.bool_to_var.is_empty());
    assert!(st.linked_equivalence_terms.is_empty());
    assert!(st.bv_ite_conditions.is_empty());
    assert!(st.delayed_ops.is_empty());
}

#[test]
fn incremental_bv_state_pop_drops_stale_solver_but_keeps_remaining_depth() {
    let mut st = IncrementalBvState::new();
    st.scope_depth = 2;
    st.pending_pushes = 0;
    st.term_to_bits
        .insert(TermId::new(1), vec![1, 2, 3, 4, 5, 6, 7, 8]);
    let mut sat = SatSolver::new(10);
    sat.push();
    sat.push();
    st.persistent_sat = Some(sat);
    st.tseitin_state.next_var = 12;
    st.encoded_assertions.insert(TermId::new(2), 4);
    st.bv_var_offset = Some(9);
    st.predicate_to_var.insert(TermId::new(3), 11);
    st.bool_to_var.insert(TermId::new(4), 12);
    st.linked_equivalence_terms.insert(TermId::new(5));
    st.bv_ite_conditions.insert(TermId::new(6));
    st.assertion_activation_scope.insert(TermId::new(7), 2);
    st.emitted_bv_eq_congruence_pairs
        .insert((TermId::new(8), TermId::new(9)));

    assert!(st.pop());

    assert_eq!(st.scope_depth, 1);
    assert_eq!(st.pending_pushes, 1);
    assert!(st.term_to_bits.is_empty());
    assert_eq!(st.next_bv_var, 1);
    assert!(st.persistent_sat.is_none());
    assert_eq!(st.tseitin_state.next_var, 1);
    assert!(st.encoded_assertions.is_empty());
    assert!(st.assertion_activation_scope.is_empty());
    assert_eq!(st.sat_num_vars, 0);
    assert!(st.bv_var_offset.is_none());
    assert!(st.emitted_bv_eq_congruence_pairs.is_empty());
    assert!(st.predicate_to_var.is_empty());
    assert!(st.bool_to_var.is_empty());
    assert!(st.linked_equivalence_terms.is_empty());
    assert!(st.bv_ite_conditions.is_empty());
    assert!(st.delayed_ops.is_empty());
}

mod theory_scope_cleanup;
