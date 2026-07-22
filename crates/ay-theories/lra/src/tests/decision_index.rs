// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! STAGE B: tests for the incremental decision-candidate index that backs the
//! fast `suggest_decision_atom` path (`AY_LRA_FAST_DECISION`).
//!
//! The index is soundness-neutral — it only reorders decision *suggestions* —
//! so the properties under test are structural: (1) the compact set primitive
//! is a correct swap-remove set; (2) the fast path returns a member of the same
//! candidate set (same priority tier, unasserted, with a phase hint) as the
//! legacy scan; (3) the index invariant holds across assert/pop.

use super::*;

// ---------------------------------------------------------------------------
// Test helpers
// ---------------------------------------------------------------------------

/// Whether `atom` is registered as an equality atom (priority-1 candidate).
fn is_eq_atom(solver: &LraSolver, atom: TermId) -> bool {
    matches!(solver.atom_cache.get(&atom), Some(Some(info)) if info.is_eq)
}

/// Whether `atom` is currently a member of either decision-candidate list.
fn index_contains(solver: &LraSolver, atom: TermId) -> bool {
    solver.decision_index.eq.items().contains(&atom)
        || solver.decision_index.ineq.items().contains(&atom)
}

/// Recompute the index invariant from first principles and assert the
/// incrementally-maintained index matches it exactly (and has no duplicates).
///
/// Invariant: index == { registered, non-distinct atom terms with parsed info
/// that are NOT in `asserted` }, partitioned by is_eq. This is precisely what
/// `rebuild_decision_index` produces, so a match proves the incremental
/// register/assert/pop hooks stayed in sync with a from-scratch rebuild.
fn assert_index_matches_invariant(solver: &LraSolver) {
    use std::collections::BTreeSet;
    let mut expected_eq: BTreeSet<u32> = BTreeSet::new();
    let mut expected_ineq: BTreeSet<u32> = BTreeSet::new();
    for &atom in solver.registered_atoms.iter() {
        if solver.asserted.contains_key(&atom) {
            continue;
        }
        match solver.atom_cache.get(&atom) {
            Some(Some(info)) if !info.is_distinct => {
                if info.is_eq {
                    expected_eq.insert(atom.0);
                } else {
                    expected_ineq.insert(atom.0);
                }
            }
            _ => {}
        }
    }
    let eq_items = solver.decision_index.eq.items();
    let ineq_items = solver.decision_index.ineq.items();
    let got_eq: BTreeSet<u32> = eq_items.iter().map(|t| t.0).collect();
    let got_ineq: BTreeSet<u32> = ineq_items.iter().map(|t| t.0).collect();
    assert_eq!(
        got_eq, expected_eq,
        "eq index must match recomputed invariant"
    );
    assert_eq!(
        got_ineq, expected_ineq,
        "ineq index must match recomputed invariant"
    );
    assert_eq!(
        eq_items.len(),
        got_eq.len(),
        "eq index must have no duplicate entries"
    );
    assert_eq!(
        ineq_items.len(),
        got_ineq.len(),
        "ineq index must have no duplicate entries"
    );
}

/// Build the term DAG for the big-solver tests: 110 inequality atoms and 5
/// equality atoms, each over its own fresh variable. Returns the `TermStore`
/// plus the eq/ineq atom term lists.
///
/// The solver is created by the caller (via [`register_big_solver`]) so the
/// `TermStore` is never moved after `LraSolver::new` pins a raw pointer to it —
/// `LraSolver` holds `terms_ptr` (#6590), so a post-construction move would
/// dangle it and segfault on the next `terms()` deref.
fn build_big_terms() -> (TermStore, Vec<TermId>, Vec<TermId>) {
    let mut terms = TermStore::new();
    let mut ineq_atoms = Vec::new();
    let mut eq_atoms = Vec::new();
    for i in 0..110 {
        let v = terms.mk_var(format!("x{i}"), Sort::Real);
        let c = terms.mk_rational(BigRational::from(BigInt::from(i as i64 + 1)));
        ineq_atoms.push(terms.mk_le(v, c)); // x_i <= i+1
    }
    for i in 0..5 {
        let v = terms.mk_var(format!("e{i}"), Sort::Real);
        let c = terms.mk_rational(BigRational::from(BigInt::from(i as i64)));
        eq_atoms.push(terms.mk_eq(v, c)); // e_i = i
    }
    (terms, eq_atoms, ineq_atoms)
}

/// Create and populate the solver against a `terms` pinned in the caller's
/// frame, registering every eq and ineq atom.
fn register_big_solver(terms: &TermStore, eq_atoms: &[TermId], ineq_atoms: &[TermId]) -> LraSolver {
    let mut solver = LraSolver::new(terms);
    for &a in ineq_atoms {
        solver.register_atom(a);
    }
    for &a in eq_atoms {
        solver.register_atom(a);
    }
    solver
}

// ---------------------------------------------------------------------------
// CompactAtomSet primitive
// ---------------------------------------------------------------------------

/// The swap-remove set must keep `items()` dense and membership correct across
/// duplicate inserts, middle removal (which triggers the swap-with-last),
/// absent removal, full drain, and re-insertion after empty.
#[test]
fn test_compact_atom_set_swap_remove_correctness() {
    let mut s = CompactAtomSet::default();
    let (a, b, c, d) = (TermId(10), TermId(20), TermId(30), TermId(40));
    s.insert(a);
    s.insert(b);
    s.insert(c);
    s.insert(d);
    s.insert(b); // duplicate insert is a no-op
    assert_eq!(s.items().len(), 4, "duplicate insert must not grow the set");

    // Remove a middle element: last element swaps into the hole.
    s.remove(b);
    assert_eq!(s.items().len(), 3);
    assert!(!s.items().contains(&b), "removed element must be gone");
    for x in [a, c, d] {
        assert!(s.items().contains(&x), "survivor {x:?} must remain");
    }

    // Removing an absent element is a no-op.
    s.remove(TermId(999));
    assert_eq!(s.items().len(), 3);

    // Removing the swapped-in element again keeps pos map consistent.
    s.remove(d);
    assert_eq!(s.items().len(), 2);
    assert!(s.items().contains(&a) && s.items().contains(&c));

    // Full drain, then re-insert after empty works.
    s.remove(a);
    s.remove(c);
    assert_eq!(s.items().len(), 0);
    s.insert(a);
    assert_eq!(s.items(), &[a], "re-insert after empty must work");

    s.clear();
    assert_eq!(s.items().len(), 0, "clear empties the set");
}

// ---------------------------------------------------------------------------
// Fast vs slow parity + priority ordering
// ---------------------------------------------------------------------------

/// The fast path and the legacy scan must agree on candidate *existence* and
/// *priority tier*, and each must return a valid candidate: an unasserted atom
/// whose returned phase equals its phase-hint-cache entry. When unasserted
/// equality atoms exist, both must return an equality atom (priority 1); once
/// all equalities are asserted, both fall to an inequality (priority 2).
#[test]
fn test_fast_slow_decision_parity_and_priority() {
    let (terms, eq_atoms, ineq_atoms) = build_big_terms();
    let mut solver = register_big_solver(&terms, &eq_atoms, &ineq_atoms);
    assert!(
        solver.registered_atoms.len() >= 100,
        "need >= 100 atoms to exercise suggest_decision_atom"
    );
    // Feasible model (all atoms unasserted) → phase_hint_cache populated.
    assert!(is_sat_like(&solver.check()));

    // Priority 1: unasserted equality atoms exist → both paths pick an eq atom.
    let fast = solver.suggest_decision_atom_fast();
    let slow = solver.suggest_decision_atom_slow();
    assert!(fast.is_some(), "fast path must find a candidate");
    assert_eq!(
        fast.is_some(),
        slow.is_some(),
        "fast and slow must agree on candidate existence"
    );
    let (fa, fp) = fast.unwrap();
    let (sa, _sp) = slow.unwrap();
    assert!(
        is_eq_atom(&solver, fa),
        "priority 1: fast returns an eq atom"
    );
    assert!(
        is_eq_atom(&solver, sa),
        "priority 1: slow returns an eq atom"
    );
    // Returned atom is a genuine candidate: unasserted, with a phase hint that
    // matches the returned phase.
    assert!(
        !solver.asserted.contains_key(&fa),
        "candidate is unasserted"
    );
    assert_eq!(
        solver.phase_hint_cache.get(&fa),
        Some(&fp),
        "returned phase must equal the phase-hint-cache entry"
    );

    // Assert every equality atom → priority 1 is now exhausted.
    for &a in &eq_atoms {
        solver.assert_literal(a, true);
    }
    assert!(is_sat_like(&solver.check()));
    let fast2 = solver.suggest_decision_atom_fast();
    let slow2 = solver.suggest_decision_atom_slow();
    assert!(
        fast2.is_some() && slow2.is_some(),
        "unasserted inequality candidates remain"
    );
    assert!(
        !is_eq_atom(&solver, fast2.unwrap().0),
        "priority 2: fast falls through to an inequality atom"
    );
    assert!(
        !is_eq_atom(&solver, slow2.unwrap().0),
        "priority 2: slow falls through to an inequality atom"
    );
}

/// A fully-asserted problem has no decision candidates: both paths return None.
#[test]
fn test_fast_slow_none_when_all_asserted() {
    let (terms, eq_atoms, ineq_atoms) = build_big_terms();
    let mut solver = register_big_solver(&terms, &eq_atoms, &ineq_atoms);
    for &a in ineq_atoms.iter().chain(eq_atoms.iter()) {
        solver.assert_literal(a, true);
    }
    assert!(is_sat_like(&solver.check()));
    assert!(
        solver.suggest_decision_atom_fast().is_none(),
        "no candidate when everything is asserted (fast)"
    );
    assert!(
        solver.suggest_decision_atom_slow().is_none(),
        "no candidate when everything is asserted (slow)"
    );
    assert_index_matches_invariant(&solver);
}

// ---------------------------------------------------------------------------
// Index invariant across assert / pop
// ---------------------------------------------------------------------------

/// The incrementally-maintained index must equal the from-scratch invariant at
/// every point: after registration, after assertion (candidates leave), and
/// after pop (candidates return).
#[test]
fn test_decision_index_invariant_across_assert_pop() {
    let (terms, eq_atoms, ineq_atoms) = build_big_terms();
    let mut solver = register_big_solver(&terms, &eq_atoms, &ineq_atoms);
    // After registration only.
    assert_index_matches_invariant(&solver);
    assert!(index_contains(&solver, ineq_atoms[0]));
    assert!(index_contains(&solver, eq_atoms[0]));

    // Assert some atoms inside a scope → they leave the candidate index.
    solver.push();
    solver.assert_literal(ineq_atoms[0], true);
    solver.assert_literal(ineq_atoms[7], true);
    solver.assert_literal(eq_atoms[0], true);
    assert!(
        !index_contains(&solver, ineq_atoms[0]),
        "asserted inequality left the index"
    );
    assert!(
        !index_contains(&solver, eq_atoms[0]),
        "asserted equality left the index"
    );
    assert_index_matches_invariant(&solver);

    // Pop → the asserted atoms become candidates again.
    solver.pop();
    assert!(
        index_contains(&solver, ineq_atoms[0]),
        "popped inequality returned to the index"
    );
    assert!(
        index_contains(&solver, ineq_atoms[7]),
        "popped inequality returned to the index"
    );
    assert!(
        index_contains(&solver, eq_atoms[0]),
        "popped equality returned to the index"
    );
    assert_index_matches_invariant(&solver);
}

/// A from-scratch rebuild must reproduce the incrementally-maintained index
/// bit-for-bit (this is the safety net used at reset/snapshot boundaries).
#[test]
fn test_rebuild_matches_incremental_index() {
    let (terms, eq_atoms, ineq_atoms) = build_big_terms();
    let mut solver = register_big_solver(&terms, &eq_atoms, &ineq_atoms);
    solver.push();
    solver.assert_literal(ineq_atoms[3], true);
    solver.assert_literal(eq_atoms[1], true);

    // Snapshot the incremental index, force a rebuild, compare.
    let inc_eq: Vec<TermId> = {
        let mut v: Vec<TermId> = solver.decision_index.eq.items().to_vec();
        v.sort_unstable_by_key(|t| t.0);
        v
    };
    let inc_ineq: Vec<TermId> = {
        let mut v: Vec<TermId> = solver.decision_index.ineq.items().to_vec();
        v.sort_unstable_by_key(|t| t.0);
        v
    };
    solver.rebuild_decision_index();
    let mut reb_eq: Vec<TermId> = solver.decision_index.eq.items().to_vec();
    reb_eq.sort_unstable_by_key(|t| t.0);
    let mut reb_ineq: Vec<TermId> = solver.decision_index.ineq.items().to_vec();
    reb_ineq.sort_unstable_by_key(|t| t.0);
    assert_eq!(inc_eq, reb_eq, "rebuild reproduces incremental eq index");
    assert_eq!(
        inc_ineq, reb_ineq,
        "rebuild reproduces incremental ineq index"
    );
}
