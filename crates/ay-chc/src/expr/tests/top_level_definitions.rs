// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `eliminate_top_level_definitions` / `eliminate_definitions_per_disjunct`:
//! every definition goes, chains included; growth is capped; disjuncts are
//! eliminated separately and never across.

use super::*;

fn bv(value: u128) -> ChcExpr {
    ChcExpr::BitVec(value, 64)
}

fn bv_var(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::BitVec(64))
}

fn bvadd(a: ChcExpr, b: ChcExpr) -> ChcExpr {
    ChcExpr::Op(ChcOp::BvAdd, vec![Arc::new(a), Arc::new(b)])
}

/// `x0 = 0`, `x(i+1) = x(i) + 1`, `x(n) = target`: a chain far longer than
/// the eight substitutions the transition validation used to stop at.
fn counter_chain(n: usize, target: u128) -> ChcExpr {
    let x = |i: usize| ChcExpr::var(bv_var(&format!("x{i}")));
    let mut conjuncts = vec![ChcExpr::eq(x(0), bv(0))];
    conjuncts.extend((0..n).map(|i| ChcExpr::eq(x(i + 1), bvadd(x(i), bv(1)))));
    conjuncts.push(ChcExpr::eq(x(n), bv(target)));
    ChcExpr::and_all(conjuncts)
}

#[test]
fn a_long_definition_chain_is_eliminated_to_a_verdict() {
    assert_eq!(
        counter_chain(20, 21).eliminate_top_level_definitions(),
        ChcExpr::Bool(false)
    );
    assert_eq!(
        counter_chain(20, 20).eliminate_top_level_definitions(),
        ChcExpr::Bool(true)
    );
}

#[test]
fn a_doubling_chain_stops_at_the_node_cap() {
    // x(i+1) = x(i) + x(i): every substitution doubles the right-hand side,
    // 2^40 nodes in full. The elimination must stop near the cap instead.
    let x = |i: usize| ChcExpr::var(bv_var(&format!("x{i}")));
    let mut conjuncts: Vec<ChcExpr> = (0..40)
        .map(|i| ChcExpr::eq(x(i + 1), bvadd(x(i), x(i))))
        .collect();
    conjuncts.push(ChcExpr::bv_ule(x(40), bv(7)));
    let formula = ChcExpr::and_all(conjuncts);
    let start = formula.node_count(1_000_000);
    let eliminated = formula.eliminate_top_level_definitions();
    let cap = (start * 4).max(4096);
    assert!(
        eliminated.node_count(1_000_000) <= cap,
        "{} nodes past the cap {cap}",
        eliminated.node_count(1_000_000)
    );
}

#[test]
fn a_variable_in_its_own_right_hand_side_is_not_a_definition() {
    // y = 1 is a definition; after it, x = x + 1 is not one (x occurs on both
    // sides) and must survive, or the unsatisfiable constraint would be lost.
    let x = ChcExpr::var(bv_var("x"));
    let y = ChcExpr::var(bv_var("y"));
    let formula = ChcExpr::and_all([
        ChcExpr::eq(x.clone(), bvadd(x.clone(), y.clone())),
        ChcExpr::eq(y, bv(1)),
        ChcExpr::bv_ule(x, bv(3)),
    ]);
    let eliminated = formula.eliminate_top_level_definitions();
    let vars = eliminated.vars();
    assert!(!vars.contains(&bv_var("y")), "{eliminated}");
    assert!(
        vars.contains(&bv_var("x")) || eliminated == ChcExpr::Bool(false),
        "{eliminated}"
    );
}

#[test]
fn each_disjunct_is_eliminated_on_its_own() {
    let x = ChcExpr::var(bv_var("x"));
    // (x = 1 ∧ x = 2) ∨ (x = 3 ∧ x <= 3): the first disjunct is refuted, the
    // second holds. A definition of one disjunct must not leak into the
    // other: substituting x = 1 across the disjunction would refute both.
    let first = ChcExpr::and(ChcExpr::eq(x.clone(), bv(1)), ChcExpr::eq(x.clone(), bv(2)));
    let second = ChcExpr::and(ChcExpr::eq(x.clone(), bv(3)), ChcExpr::bv_ule(x, bv(3)));
    let formula = ChcExpr::or(first.clone(), second);
    assert_eq!(
        formula.eliminate_definitions_per_disjunct(),
        ChcExpr::Bool(true)
    );
    let refuted = ChcExpr::or(first.clone(), first);
    assert_eq!(
        refuted.eliminate_definitions_per_disjunct(),
        ChcExpr::Bool(false)
    );
}

/// `x(i) = x(i+1) + … + x(n)` for `i < n`: every definition mentions all the
/// later variables, so a round takes only the first remaining one, and each
/// round shrinks the formula by one definition only.
fn dense_chain(n: usize) -> ChcExpr {
    let x = |i: usize| ChcExpr::var(ChcVar::new(format!("x{i}"), ChcSort::Int));
    let sum = |i: usize| ChcExpr::Op(ChcOp::Add, ((i + 1)..=n).map(|j| Arc::new(x(j))).collect());
    ChcExpr::and_all((1..n).map(|i| ChcExpr::eq(x(i), sum(i))))
}

#[test]
fn a_dense_chain_stops_at_the_work_bound() {
    // Without the work bound all 159 rounds run, each over most of the
    // formula (cubic work, and the round count alone grows with the
    // variables); with it the rounds stop once their sizes sum past twice
    // the node cap, a handful of rounds here.
    let n = 160;
    let eliminated = dense_chain(n).eliminate_top_level_definitions();
    let left = eliminated.vars().len();
    assert!(left >= n / 2, "{left} of {n} variables left");
    assert!(left < n, "the first rounds still run");
}
