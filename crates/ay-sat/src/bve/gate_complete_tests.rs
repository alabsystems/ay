// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn lit(dimacs: i32) -> Literal {
    let var = Variable(dimacs.unsigned_abs() - 1);
    if dimacs > 0 {
        Literal::positive(var)
    } else {
        Literal::negative(var)
    }
}

/// Add `clauses` (DIMACS literals) to a fresh arena; returns it and the indices.
fn arena(clauses: &[&[i32]]) -> (ClauseArena, Vec<usize>) {
    let mut arena = ClauseArena::new();
    let ids = clauses
        .iter()
        .map(|c| arena.add(&c.iter().map(|&l| lit(l)).collect::<Vec<_>>(), false))
        .collect();
    (arena, ids)
}

const X: Variable = Variable(0);

fn sound(clauses: &[&[i32]], gate: &[usize], resolve_pairs: bool, vals: &[i8], pure: bool) -> bool {
    let (arena, ids) = arena(clauses);
    let defining: Vec<usize> = gate.iter().map(|&i| ids[i]).collect();
    gate_restriction_is_sound(X, &arena, &defining, resolve_pairs, vals, pure) == GateVerdict::Sound
}

#[test]
fn a_ternary_xor_is_a_complete_gate_beside_other_clauses() {
    // x = 2 ^ 3 (the four gate clauses), plus x's second XOR 1 ^ 4 ^ 5 = 0.
    let clauses: &[&[i32]] = &[
        &[1, -2, 3],
        &[1, 2, -3],
        &[-1, 2, 3],
        &[-1, -2, -3],
        &[1, 4, -5],
        &[1, -4, 5],
        &[-1, 4, 5],
        &[-1, -4, -5],
    ];
    assert!(sound(clauses, &[0, 1, 2, 3], false, &[], false));
    // The other XOR is a gate as well.
    assert!(sound(clauses, &[4, 5, 6, 7], false, &[], false));
}

#[test]
fn an_and_gate_is_complete() {
    // x = 2 & 3, and x in a clause of its own.
    let clauses: &[&[i32]] = &[&[-1, 2], &[-1, 3], &[1, -2, -3], &[1, 4]];
    assert!(sound(clauses, &[0, 1, 2], false, &[], false));
}

#[test]
fn an_incomplete_gate_is_refused() {
    // Pairs clash on 2, but E = {2 | 3}, D = {-2 | 4} is satisfiable.
    let clauses: &[&[i32]] = &[&[1, 2, 3], &[-1, -2, 4], &[1, 5]];
    assert!(!sound(clauses, &[0, 1], false, &[], false));
    // Resolving gate pairs does not make it complete.
    assert!(!sound(clauses, &[0, 1], true, &[], false));
}

#[test]
fn unresolved_non_tautological_gate_pairs_are_refused_even_when_pure() {
    // E = {2}, D = {3, -2 | -3} is unsatisfiable, but (x | 2) and (-x | 3)
    // resolve to (2 | 3), which is not tautological.
    let clauses: &[&[i32]] = &[&[1, 2], &[-1, 3], &[-1, -2, -3]];
    assert!(!sound(clauses, &[0, 1, 2], false, &[], true));
    assert!(sound(clauses, &[0, 1, 2], true, &[], true));
    assert!(sound(clauses, &[0, 1, 2], true, &[], false));
}

#[test]
fn a_root_false_literal_reads_as_absent() {
    // x = 2 & 3 with the gate clause (-x | 2 | 4) and 4 false at the root: a
    // root assignment holds in every model, so the gate is complete.
    let clauses: &[&[i32]] = &[&[-1, 2, 4], &[-1, 3], &[1, -2, -3], &[1, 5]];
    let mut vals = vec![0i8; 10];
    vals[lit(-4).index()] = 1;
    vals[lit(4).index()] = -1;
    assert!(sound(clauses, &[0, 1, 2], false, &vals, false));
    // Without the root assignment, (2 | 4), 3, (-2 | -3) is satisfiable.
    assert!(!sound(clauses, &[0, 1, 2], false, &[], false));
}

#[test]
fn a_root_satisfied_gate_clause_forces_nothing() {
    // x = 2 & 3, but (x | -2 | -3 | 4) is satisfied by root-true 4: without it
    // the rest is satisfiable, so the gate is not complete.
    let clauses: &[&[i32]] = &[&[-1, 2], &[-1, 3], &[1, -2, -3, 4], &[1, 5]];
    let mut vals = vec![0i8; 10];
    vals[lit(4).index()] = 1;
    vals[lit(-4).index()] = -1;
    assert!(!sound(clauses, &[0, 1, 2], false, &vals, false));
}

#[test]
fn a_five_input_xor_is_refuted_within_budget() {
    // All 32 sign patterns over five variables: unsatisfiable.
    let clauses: Vec<Vec<u32>> = (0..32u32)
        .map(|mask| (0..5).map(|v| 2 * v + ((mask >> v) & 1)).collect())
        .collect();
    let mut budget = GATE_CHECK_NODE_BUDGET;
    let mut assignment = vec![0i8; 5];
    assert_eq!(
        dpll_refutes(&clauses, &mut assignment, &mut budget),
        Some(true)
    );
    assert!(assignment.iter().all(|&v| v == 0));
    // Drop one pattern: a model exists.
    let mut budget = GATE_CHECK_NODE_BUDGET;
    assert_eq!(
        dpll_refutes(&clauses[1..], &mut assignment, &mut budget),
        Some(false)
    );
}

#[test]
fn an_exhausted_budget_proves_nothing() {
    let clauses: Vec<Vec<u32>> = (0..32u32)
        .map(|mask| (0..5).map(|v| 2 * v + ((mask >> v) & 1)).collect())
        .collect();
    let mut budget = 3;
    let mut assignment = vec![0i8; 5];
    assert_eq!(dpll_refutes(&clauses, &mut assignment, &mut budget), None);
}
