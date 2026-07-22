// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for decompose (SCC) rewrite edge cases:
//! Unit, Empty, Satisfied, Tautology outcomes from rewrite_clauses,
//! and assigned/eliminated variable SCC traversal skipping.

use crate::clause_arena::ClauseArena;
use crate::decompose::{rewrite_clauses, ClauseMutation, Decompose};
use crate::solver::lifecycle::VarState;
use crate::test_util::lit;
use crate::watched::{ClauseRef, WatchedLists, Watcher};

/// Build binary watches for all binary clauses in the arena.
fn build_binary_watches(arena: &ClauseArena, num_vars: usize) -> WatchedLists {
    let mut watches = WatchedLists::new(num_vars);
    for idx in arena.indices() {
        if arena.is_empty_clause(idx) || arena.len_of(idx) != 2 {
            continue;
        }
        let l0 = arena.literal(idx, 0);
        let l1 = arena.literal(idx, 1);
        let cref = ClauseRef(idx as u32);
        watches.add_watch(l0, Watcher::binary(cref, l1));
        watches.add_watch(l1, Watcher::binary(cref, l0));
    }
    watches
}

/// rewrite_clauses must produce a Unit action when substitution + root-false
/// vals reduce a binary clause to a single literal.
///
/// Setup: reprs maps x1→x0, vals has x2=false.
/// Clause (x1 ∨ x2) → substitution → (x0 ∨ x2) → vals filter → (x0) → Unit.
#[test]
fn test_rewrite_produces_unit_from_substitution_and_root_false() {
    let mut arena = ClauseArena::new();
    arena.add(&[lit(1, true), lit(2, true)], false);

    let num_lits = 6; // 3 vars
    let mut reprs: Vec<_> = (0..num_lits as u32).map(crate::literal::Literal).collect();
    reprs[lit(1, true).index()] = lit(0, true); // x1 → x0
    reprs[lit(1, false).index()] = lit(0, false); // ¬x1 → ¬x0

    // x2 assigned false.
    let mut vals = vec![0i8; num_lits];
    vals[lit(2, true).index()] = -1; // x2_pos = false
    vals[lit(2, false).index()] = 1; // x2_neg = true

    let result = rewrite_clauses(&arena, &reprs, &vals);
    assert!(!result.is_unsat, "should not be UNSAT");
    assert_eq!(
        result.removed, 1,
        "unit clause should be counted as removed"
    );
    let unit_actions: Vec<_> = result
        .actions
        .iter()
        .filter(|a| matches!(a, ClauseMutation::Unit { .. }))
        .collect();
    assert_eq!(
        unit_actions.len(),
        1,
        "should produce exactly one Unit action"
    );
    match &unit_actions[0] {
        ClauseMutation::Unit { unit, .. } => {
            assert_eq!(
                *unit,
                lit(0, true),
                "unit literal should be x0 (after x1→x0 substitution)"
            );
        }
        _ => unreachable!(),
    }
}

/// rewrite_clauses must detect UNSAT (Empty) when substitution + root-false
/// vals remove all literals from a clause.
///
/// Setup: reprs maps x1→x0, both x0 and x2 assigned false.
/// Clause (x1 ∨ x2) → (x0 ∨ x2) → both false → Empty → is_unsat=true.
#[test]
fn test_rewrite_produces_empty_derives_unsat() {
    let mut arena = ClauseArena::new();
    arena.add(&[lit(1, true), lit(2, true)], false);

    let num_lits = 6;
    let mut reprs: Vec<_> = (0..num_lits as u32).map(crate::literal::Literal).collect();
    reprs[lit(1, true).index()] = lit(0, true);
    reprs[lit(1, false).index()] = lit(0, false);

    // Both x0 and x2 assigned false.
    let mut vals = vec![0i8; num_lits];
    vals[lit(0, true).index()] = -1; // x0 = false
    vals[lit(0, false).index()] = 1;
    vals[lit(2, true).index()] = -1; // x2 = false
    vals[lit(2, false).index()] = 1;

    let result = rewrite_clauses(&arena, &reprs, &vals);
    assert!(
        result.is_unsat,
        "all literals false after substitution must derive UNSAT"
    );
}

/// rewrite_clauses must delete a clause when a substituted literal
/// is root-true (Satisfied outcome).
///
/// Setup: reprs maps x1→x0, x0 assigned true.
/// Clause (x1 ∨ x2) → (x0 ∨ x2) → x0 is true → Satisfied → Deleted.
#[test]
fn test_rewrite_satisfied_from_root_true_deletes_clause() {
    let mut arena = ClauseArena::new();
    arena.add(&[lit(1, true), lit(2, true)], false);

    let num_lits = 6;
    let mut reprs: Vec<_> = (0..num_lits as u32).map(crate::literal::Literal).collect();
    reprs[lit(1, true).index()] = lit(0, true);
    reprs[lit(1, false).index()] = lit(0, false);

    // x0 assigned true.
    let mut vals = vec![0i8; num_lits];
    vals[lit(0, true).index()] = 1; // x0 = true
    vals[lit(0, false).index()] = -1;

    let result = rewrite_clauses(&arena, &reprs, &vals);
    assert!(!result.is_unsat);
    assert!(result.removed > 0, "satisfied clause should be removed");
    let deleted = result
        .actions
        .iter()
        .filter(|a| matches!(a, ClauseMutation::Deleted { .. }))
        .count();
    assert_eq!(
        deleted, 1,
        "satisfied clause should produce exactly one Deleted action"
    );
}

/// rewrite_clauses must detect tautology when a negated equivalence creates
/// complementary literals (x ∨ ¬x) in the same clause.
///
/// Setup: reprs maps x1→¬x0 (negated equivalence).
/// Clause (x0 ∨ x1 ∨ x2) → (x0 ∨ ¬x0 ∨ x2) → tautology → Deleted.
#[test]
fn test_rewrite_tautology_from_negated_equivalence() {
    let mut arena = ClauseArena::new();
    arena.add(&[lit(0, true), lit(1, true), lit(2, true)], false);

    let num_lits = 6;
    let mut reprs: Vec<_> = (0..num_lits as u32).map(crate::literal::Literal).collect();
    reprs[lit(1, true).index()] = lit(0, false); // x1 → ¬x0
    reprs[lit(1, false).index()] = lit(0, true); // ¬x1 → x0

    let vals = vec![0i8; num_lits]; // all unassigned

    let result = rewrite_clauses(&arena, &reprs, &vals);
    assert!(!result.is_unsat);
    assert!(result.removed > 0, "tautological clause should be removed");
    let deleted = result
        .actions
        .iter()
        .filter(|a| matches!(a, ClauseMutation::Deleted { .. }))
        .count();
    assert_eq!(
        deleted, 1,
        "tautology should produce exactly one Deleted action"
    );
}

/// SCC traversal must skip assigned variables, preventing false equivalences.
///
/// Setup: binary clauses establish x0≡x1, but x0 is assigned true.
/// SCC should skip x0 (vals[var*2] != 0), finding no equivalences.
#[test]
fn test_scc_skips_assigned_variable_no_equivalence() {
    let mut arena = ClauseArena::new();
    arena.add(&[lit(0, false), lit(1, true)], false); // ¬x0 ∨ x1 (x0→x1)
    arena.add(&[lit(1, false), lit(0, true)], false); // ¬x1 ∨ x0 (x1→x0)

    let num_vars = 2;
    let watches = build_binary_watches(&arena, num_vars);

    // x0 assigned true.
    let mut vals = vec![0i8; num_vars * 2];
    vals[0] = 1; // x0_pos = true
    vals[1] = -1; // x0_neg = false

    let frozen = vec![0u32; num_vars];
    let var_states = vec![VarState::Active; num_vars];

    let mut decompose = Decompose::new(num_vars);
    let result = decompose.run(&watches, num_vars, &vals, &frozen, &var_states, true);

    assert!(!result.unsat);
    assert_eq!(
        result.substituted, 0,
        "assigned x0 should be skipped in SCC, preventing x0≡x1 equivalence"
    );
}

/// SCC traversal must skip eliminated (removed) variables.
///
/// Setup: binary clauses establish x0≡x1, but x0 is Eliminated.
/// SCC should skip x0, finding no equivalences.
#[test]
fn test_scc_skips_eliminated_variable_no_equivalence() {
    let mut arena = ClauseArena::new();
    arena.add(&[lit(0, false), lit(1, true)], false);
    arena.add(&[lit(1, false), lit(0, true)], false);

    let num_vars = 2;
    let watches = build_binary_watches(&arena, num_vars);

    let vals = vec![0i8; num_vars * 2]; // all unassigned
    let frozen = vec![0u32; num_vars];
    let mut var_states = vec![VarState::Active; num_vars];
    var_states[0] = VarState::Eliminated; // x0 eliminated by BVE

    let mut decompose = Decompose::new(num_vars);
    let result = decompose.run(&watches, num_vars, &vals, &frozen, &var_states, true);

    assert!(!result.unsat);
    assert_eq!(
        result.substituted, 0,
        "eliminated x0 should be skipped in SCC, preventing x0≡x1 equivalence"
    );
}
