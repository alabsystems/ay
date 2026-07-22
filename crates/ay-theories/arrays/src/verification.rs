// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::Sort;

/// Create a minimal TermStore with array terms for testing
fn make_test_store() -> (TermStore, Sort) {
    let store = TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);
    (store, arr_sort)
}

/// Proof: known_equal is reflexive - a term is always equal to itself
#[kani::proof]
fn proof_known_equal_reflexive() {
    let (store, _) = make_test_store();
    let solver = ArraySolver::new(&store);

    // For any term ID, known_equal(t, t) must be true
    let term_id: u32 = kani::any();
    kani::assume(term_id < 100);
    let t = TermId(term_id);

    assert!(solver.known_equal(t, t), "known_equal must be reflexive");
}

/// Proof: known_distinct is anti-reflexive - a term is never distinct from itself
#[kani::proof]
fn proof_known_distinct_antireflexive() {
    let (store, _) = make_test_store();
    let solver = ArraySolver::new(&store);

    // For any term ID, known_distinct(t, t) must be false
    let term_id: u32 = kani::any();
    kani::assume(term_id < 100);
    let t = TermId(term_id);

    assert!(
        !solver.known_distinct(t, t),
        "known_distinct must be anti-reflexive"
    );
}

/// Proof: push/pop maintains scope stack consistency
///
/// Uses fixed push/push/pop/pop sequence to avoid hashbrown HashMap
/// operations in ArraySolver making symbolic loops intractable for CBMC.
#[kani::proof]
#[kani::unwind(4)]
fn proof_push_pop_scope_depth() {
    let (store, _) = make_test_store();
    let mut solver = ArraySolver::new(&store);

    let initial_depth = solver.scopes.len();

    solver.push();
    kani::assert(
        solver.scopes.len() == initial_depth + 1,
        "push must increment scope depth",
    );

    solver.push();
    kani::assert(
        solver.scopes.len() == initial_depth + 2,
        "second push must increment scope depth",
    );

    solver.pop();
    kani::assert(
        solver.scopes.len() == initial_depth + 1,
        "pop must decrement scope depth",
    );

    solver.pop();
    kani::assert(
        solver.scopes.len() == initial_depth,
        "second pop must restore original depth",
    );
}

/// Proof: pop on empty scopes is safe (no-op)
#[kani::proof]
fn proof_pop_empty_is_safe() {
    let (store, _) = make_test_store();
    let mut solver = ArraySolver::new(&store);

    // Pop on empty scopes should do nothing
    let trail_len_before = solver.trail.len();
    let assigns_len_before = solver.assigns.len();

    solver.pop();

    // State should be unchanged
    assert_eq!(solver.trail.len(), trail_len_before);
    assert_eq!(solver.assigns.len(), assigns_len_before);
    assert!(solver.scopes.is_empty());
}

/// Proof: reset clears all mutable state
#[kani::proof]
fn proof_reset_clears_state() {
    let (store, _) = make_test_store();
    let mut solver = ArraySolver::new(&store);

    // Add some state by simulating assignments
    let term_id: u32 = kani::any();
    kani::assume(term_id < 100);
    let value: bool = kani::any();

    solver.record_assignment(TermId(term_id), value);
    solver.push();
    solver.record_assignment(TermId(term_id.wrapping_add(1) % 100), !value);

    // Reset should clear everything
    solver.reset();

    assert!(solver.assigns.is_empty(), "reset must clear assigns");
    assert!(solver.trail.is_empty(), "reset must clear trail");
    assert!(solver.scopes.is_empty(), "reset must clear scopes");
    assert!(solver.dirty, "reset must set dirty flag");
}

/// Proof: record_assignment maintains trail consistency
#[kani::proof]
fn proof_record_assignment_trail_consistency() {
    let (store, _) = make_test_store();
    let mut solver = ArraySolver::new(&store);

    let term_id: u32 = kani::any();
    kani::assume(term_id < 100);
    let t = TermId(term_id);
    let value: bool = kani::any();

    let trail_len_before = solver.trail.len();
    let prev_value = solver.assigns.get(&t).copied();

    solver.record_assignment(t, value);

    // After assignment, the value should be stored
    assert_eq!(solver.assigns.get(&t), Some(&value));

    // If value changed, trail should have grown
    if prev_value != Some(value) {
        assert_eq!(solver.trail.len(), trail_len_before + 1);
        // Trail should contain the previous value
        let (trail_term, trail_prev) = solver.trail.last().unwrap();
        assert_eq!(*trail_term, t);
        assert_eq!(*trail_prev, prev_value);
    }
}

/// Proof: pop correctly restores previous assignment values
#[kani::proof]
#[kani::unwind(5)]
fn proof_pop_restores_assignments() {
    let (store, _) = make_test_store();
    let mut solver = ArraySolver::new(&store);

    let term_id: u32 = kani::any();
    kani::assume(term_id < 100);
    let t = TermId(term_id);

    // Record initial state
    solver.push();
    let initial_value = solver.assigns.get(&t).copied();

    // Make a new assignment
    let new_value: bool = kani::any();
    solver.record_assignment(t, new_value);

    // Pop should restore
    solver.pop();

    // Value should be restored to initial state
    assert_eq!(solver.assigns.get(&t).copied(), initial_value);
}

/// Proof: duplicate assignment is idempotent (no trail growth)
#[kani::proof]
fn proof_duplicate_assignment_idempotent() {
    let (store, _) = make_test_store();
    let mut solver = ArraySolver::new(&store);

    let term_id: u32 = kani::any();
    kani::assume(term_id < 100);
    let t = TermId(term_id);
    let value: bool = kani::any();

    // First assignment
    solver.record_assignment(t, value);
    let trail_len_after_first = solver.trail.len();

    // Duplicate assignment with same value
    solver.record_assignment(t, value);

    // Trail should not grow for duplicate
    assert_eq!(solver.trail.len(), trail_len_after_first);
}

/// Proof: nested push/pop maintains correct scope markers
#[kani::proof]
#[kani::unwind(6)]
fn proof_nested_push_pop_markers() {
    let (store, _) = make_test_store();
    let mut solver = ArraySolver::new(&store);

    let depth: u8 = kani::any();
    kani::assume(depth > 0 && depth <= 5);

    // Push multiple times, recording expected markers
    let mut expected_markers: Vec<usize> = Vec::new();
    for _ in 0..depth {
        expected_markers.push(solver.trail.len());
        solver.push();
    }

    // Verify scope markers are correct
    assert_eq!(solver.scopes.len(), depth as usize);
    for i in 0..depth as usize {
        assert_eq!(solver.scopes[i], expected_markers[i]);
    }
}

/// Proof: dirty flag is set after pop
#[kani::proof]
fn proof_dirty_flag_after_pop() {
    let (store, _) = make_test_store();
    let mut solver = ArraySolver::new(&store);

    // Clear dirty flag by populating caches
    solver.populate_caches();
    assert!(!solver.dirty);

    // Push and pop
    solver.push();
    solver.pop();

    // Dirty flag should be set after pop
    assert!(
        solver.dirty,
        "pop must set dirty flag for cache invalidation"
    );
}

/// Proof: pop clears all theory-level dedup and event-driven queues.
///
/// This is the critical invariant for #7024: after backtracking, all axiom
/// dedup gates must be reset so store/select axioms can be re-requested in
/// subsequent search branches. Without this clearing, axioms are silently
/// suppressed after push/pop boundaries, leading to unsound results.
///
/// Existing proofs (proof_pop_restores_assignments, proof_push_pop_scope_depth)
/// verify assignment restoration and scope depth. This proof covers the
/// complementary invariant: theory-internal caches that gate axiom instantiation.
#[kani::proof]
#[kani::unwind(4)]
fn proof_pop_clears_axiom_dedup_state() {
    let (store, _) = make_test_store();
    let mut solver = ArraySolver::new(&store);

    // Push a scope
    solver.push();

    // Simulate theory operations by populating dedup/event queues.
    // In normal operation, these are filled during check() and
    // propagate_equalities(). We populate them directly to verify
    // that pop() clears them regardless of content.
    let t0 = TermId(0);
    let t1 = TermId(1);
    let t2 = TermId(2);

    // Axiom dedup gate: if not cleared, axioms won't be re-requested (#7024)
    solver
        .applied_theory_lemmas
        .insert(vec![TheoryLit::new(t0, true)]);

    // Event-driven queues: if not cleared, stale candidates corrupt next branch
    solver.pending_row1.push((t0, t1));
    solver.pending_row2_upward.push((t1, t2));
    solver.pending_self_store.push((t0, t2));
    solver.pending_registered_equalities.push(t0);

    // Equality propagation dedup: if not cleared, equalities are silently dropped
    solver.sent_equalities.insert((t0, t1));
    solver
        .sent_propagations
        .insert((TheoryLit::new(t0, true), vec![TheoryLit::new(t1, false)]));

    // External facts from combined solver (#4665)
    solver.external_eqs.push((t0, t1));
    solver
        .external_eq_reasons
        .insert((t0, t1), vec![TheoryLit::new(t2, true)]);
    solver.external_diseqs.insert((t1, t2));

    // Set snapshot caches (simulating a check() that computed them)
    solver.prop_eq_snapshot = Some((1, 1, 1, 1, 1, 1));
    solver.final_check_snapshot = Some((1, 1, 1, 1, 1));

    // Clear dirty flags (simulating a cache rebuild before pop)
    solver.dirty = false;
    solver.assign_dirty = false;

    // === Pop must reset all theory-level state ===
    solver.pop();

    // Axiom dedup gates must be reset (#7024 root cause: applied_theory_lemmas
    // persisted across pop, suppressing ROW2 re-instantiation)
    kani::assert(
        solver.applied_theory_lemmas.is_empty(),
        "pop must clear applied_theory_lemmas for axiom re-request",
    );

    // Event-driven queues must be cleared (stale candidates from prior branch)
    kani::assert(
        solver.pending_row1.is_empty(),
        "pop must clear pending_row1",
    );
    kani::assert(
        solver.pending_row2_upward.is_empty(),
        "pop must clear pending_row2_upward",
    );
    kani::assert(
        solver.pending_self_store.is_empty(),
        "pop must clear pending_self_store",
    );
    kani::assert(
        solver.pending_registered_equalities.is_empty(),
        "pop must clear pending_registered_equalities",
    );

    // Equality propagation dedup must be cleared
    kani::assert(
        solver.sent_equalities.is_empty(),
        "pop must clear sent_equalities",
    );
    kani::assert(
        solver.sent_propagations.is_empty(),
        "pop must clear sent_propagations",
    );

    // External facts must be cleared (#4665)
    kani::assert(
        solver.external_eqs.is_empty(),
        "pop must clear external_eqs",
    );
    kani::assert(
        solver.external_eq_reasons.is_empty(),
        "pop must clear external_eq_reasons",
    );
    kani::assert(
        solver.external_diseqs.is_empty(),
        "pop must clear external_diseqs",
    );

    // Dirty flags must be set for cache invalidation
    kani::assert(solver.dirty, "pop must set dirty flag");
    kani::assert(solver.assign_dirty, "pop must set assign_dirty flag");

    // Snapshot caches must be invalidated (#6546)
    kani::assert(
        solver.prop_eq_snapshot.is_none(),
        "pop must invalidate prop_eq_snapshot",
    );
    kani::assert(
        solver.final_check_snapshot.is_none(),
        "pop must invalidate final_check_snapshot",
    );
}
