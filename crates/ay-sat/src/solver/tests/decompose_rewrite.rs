// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for decompose (SCC) rewrite edge cases:
//! Unit, Empty, Satisfied, Tautology outcomes from rewrite_clauses,
//! and assigned/eliminated variable SCC traversal skipping.

use crate::clause_arena::ClauseArena;
use crate::decompose::{rewrite_clauses, BinaryGraph, ClauseMutation, Decompose};
use crate::literal::{Literal, Variable};
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
    let graph = BinaryGraph::new(&watches, &arena);
    let result = decompose.run(graph, num_vars, &vals, &frozen, &var_states, true);

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
    let graph = BinaryGraph::new(&watches, &arena);
    let result = decompose.run(graph, num_vars, &vals, &frozen, &var_states, true);

    assert!(!result.unsat);
    assert_eq!(
        result.substituted, 0,
        "eliminated x0 should be skipped in SCC, preventing x0≡x1 equivalence"
    );
}

/// Watches for exactly the listed `(clause, literal)` pairs: each pair puts
/// the clause's other literal on `literal`'s list. A test can leave a binary
/// with one watch, as eager subsumption followed by a targeted flush does.
fn watches_for(arena: &ClauseArena, num_vars: usize, entries: &[(usize, Literal)]) -> WatchedLists {
    let mut watches = WatchedLists::new(num_vars);
    for &(idx, on) in entries {
        let (l0, l1) = (arena.literal(idx, 0), arena.literal(idx, 1));
        let other = if on == l0 { l1 } else { l0 };
        watches.add_watch(on, Watcher::binary(ClauseRef(idx as u32), other));
    }
    watches
}

/// Three variables a < b < c: live binaries a -> b and b <-> c, and one more
/// binary b -> a watched only on the list that carries b -> a, not on the one
/// that carries its contrapositive.
fn one_sided_b_to_a(garbage_learned: bool) -> (ClauseArena, WatchedLists) {
    let (a, b, c) = (Variable(0), Variable(1), Variable(2));
    let (pos, neg) = (Literal::positive, Literal::negative);
    let mut arena = ClauseArena::new();
    let a_to_b = arena.add(&[neg(a), pos(b)], false);
    let b_to_c = arena.add(&[neg(b), pos(c)], false);
    let c_to_b = arena.add(&[neg(c), pos(b)], false);
    let b_to_a = arena.add(&[neg(b), pos(a)], garbage_learned);
    if garbage_learned {
        arena.mark_garbage_keep_data(b_to_a);
    }
    let entries = [
        (a_to_b, neg(a)),
        (a_to_b, pos(b)),
        (b_to_c, neg(b)),
        (b_to_c, pos(c)),
        (c_to_b, neg(c)),
        (c_to_b, pos(b)),
        (b_to_a, neg(b)),
    ];
    let watches = watches_for(&arena, 3, &entries);
    (arena, watches)
}

/// Every literal maps to a representative that maps to itself.
fn assert_single_step(reprs: &[Literal]) {
    for (li, &repr) in reprs.iter().enumerate() {
        assert_eq!(
            reprs[repr.index()],
            repr,
            "literal {li} maps to a substituted {repr:?}"
        );
    }
}

/// SAT-COMP 5314fd6c's failure (2026-09-14) in three variables. The garbage
/// learned binary b -> a had lost the watch carrying its contrapositive.
/// Counting it merged a with b on the positive side only, and the map chained
/// c -> b -> a: the rewrite left clauses on the substituted b, and the
/// reconstruction broke the model. Only live binaries count: a stays itself,
/// and c maps straight to b.
#[test]
fn test_half_removed_garbage_binary_is_not_an_implication() {
    let (arena, watches) = one_sided_b_to_a(true);
    let (a, b, c) = (Variable(0), Variable(1), Variable(2));
    let vals = vec![0i8; 6];
    let frozen = vec![0u32; 3];
    let var_states = vec![VarState::Active; 3];
    for need_chains in [false, true] {
        let mut decompose = Decompose::new(3);
        let graph = BinaryGraph::new(&watches, &arena);
        let result = decompose.run(graph, 3, &vals, &frozen, &var_states, need_chains);
        assert!(!result.unsat);
        assert_eq!(decompose.stats.stale_binary_watches_skipped, 1);
        assert_eq!(decompose.stats.chained_representatives, 0);
        assert_single_step(&result.reprs);
        let repr = |lit: Literal| result.reprs[lit.index()];
        assert_eq!(
            repr(Literal::positive(a)),
            Literal::positive(a),
            "a == b rests on garbage"
        );
        assert_eq!(repr(Literal::positive(c)), Literal::positive(b));
        assert_eq!(repr(Literal::negative(c)), Literal::negative(b));
    }
}

/// The second guard, reached only through a broken watch invariant: here
/// b -> a is live but watched on one side. The chain c -> b -> a is sound
/// (every link is a live binary), so without LRAT the map is composed to one
/// step; the LRAT chains cover one link only, so under LRAT the round is
/// refused.
#[test]
fn test_chained_representatives_are_composed_or_refused() {
    let (arena, watches) = one_sided_b_to_a(false);
    let (a, c) = (Variable(0), Variable(2));
    let vals = vec![0i8; 6];
    let frozen = vec![0u32; 3];
    let var_states = vec![VarState::Active; 3];

    let graph = BinaryGraph::new(&watches, &arena);
    let mut decompose = Decompose::new(3);
    let composed = decompose.run(graph, 3, &vals, &frozen, &var_states, false);
    assert!(!composed.unsat && composed.substituted > 0);
    // c and ¬c pointed at b and ¬b; b already pointed straight at a.
    assert_eq!(decompose.stats.chained_representatives, 2);
    assert_single_step(&composed.reprs);
    assert_eq!(
        composed.reprs[Literal::positive(c).index()],
        Literal::positive(a)
    );
    assert_eq!(
        composed.reprs[Literal::negative(c).index()],
        Literal::negative(a)
    );

    let mut decompose = Decompose::new(3);
    let refused = decompose.run(graph, 3, &vals, &frozen, &var_states, true);
    assert!(!refused.unsat);
    assert_eq!(refused.substituted, 0);
    assert_eq!(decompose.stats.chained_rounds_refused, 1);
    assert!(refused
        .reprs
        .iter()
        .enumerate()
        .all(|(li, r)| r.index() == li));
}
