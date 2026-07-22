// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used)]

use crate::pdr::solver::test_helpers::solver_from_str;
use crate::ChcExpr;
use ntest::timeout;

/// Test that discover_sum_invariants finds A + B = 0 for a counter pair
/// init: A=0, B=0; transition: A'=A+1, B'=B-1
/// The sum A+B is preserved (0+0=0, and delta_A + delta_B = 1 + (-1) = 0).
#[test]
#[timeout(10_000)]
fn discover_sum_invariant_counter_pair() {
    let input = r#"(set-logic HORN)
(declare-fun inv ( Int Int ) Bool)
(assert (forall ( (A Int) (B Int) )
    (=> (and (= A 0) (= B 0)) (inv A B))))
(assert (forall ( (A Int) (B Int) (A1 Int) (B1 Int) )
    (=> (and (inv A B) (= A1 (+ A 1)) (= B1 (- B 1))) (inv A1 B1))))
(assert (forall ( (A Int) (B Int) )
    (=> (and (inv A B) (not (>= (+ A B) 0))) false)))
(check-sat)
(exit)"#;

    let mut solver = solver_from_str(input);
    solver.discover_sum_invariants();

    let pred = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "inv")
        .expect("inv predicate")
        .id;
    let vars = solver.canonical_vars(pred).expect("canonical vars");
    assert_eq!(vars.len(), 2);

    // Expect A + B = 0
    let expected = ChcExpr::eq(
        ChcExpr::add(ChcExpr::var(vars[0].clone()), ChcExpr::var(vars[1].clone())),
        ChcExpr::Int(0),
    );
    let lemmas: Vec<_> = solver.frames[1]
        .lemmas
        .iter()
        .filter(|l| l.predicate == pred)
        .collect();
    assert!(
        lemmas.iter().any(|l| l.formula == expected),
        "Expected sum invariant A + B = 0, got: {:?}",
        lemmas.iter().map(|l| &l.formula).collect::<Vec<_>>()
    );
}

/// Test that discover_sum_invariants does NOT produce a sum invariant
/// when the sum is not preserved.
/// init: A=0, B=0; transition: A'=A+1, B'=B+1 (sum increases each step)
#[test]
#[timeout(10_000)]
fn discover_sum_invariant_not_preserved() {
    let input = r#"(set-logic HORN)
(declare-fun inv ( Int Int ) Bool)
(assert (forall ( (A Int) (B Int) )
    (=> (and (= A 0) (= B 0)) (inv A B))))
(assert (forall ( (A Int) (B Int) (A1 Int) (B1 Int) )
    (=> (and (inv A B) (= A1 (+ A 1)) (= B1 (+ B 1))) (inv A1 B1))))
(assert (forall ( (A Int) (B Int) )
    (=> (and (inv A B) (< A 0)) false)))
(check-sat)
(exit)"#;

    let mut solver = solver_from_str(input);
    solver.discover_sum_invariants();

    let pred = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "inv")
        .expect("inv predicate")
        .id;

    // Should NOT produce A + B = 0 since sum is not preserved
    let vars = solver.canonical_vars(pred).expect("canonical vars");
    let bad_invariant = ChcExpr::eq(
        ChcExpr::add(ChcExpr::var(vars[0].clone()), ChcExpr::var(vars[1].clone())),
        ChcExpr::Int(0),
    );
    let sum_lemmas: Vec<_> = solver.frames[1]
        .lemmas
        .iter()
        .filter(|l| l.predicate == pred && l.formula == bad_invariant)
        .collect();
    assert!(
        sum_lemmas.is_empty(),
        "Should not discover sum invariant when sum is not preserved"
    );
}

/// Test sum invariant with nonzero initial sum.
/// init: A=3, B=7; transition: A'=A+2, B'=B-2
/// Expected: A + B = 10
#[test]
#[timeout(10_000)]
fn discover_sum_invariant_nonzero_init() {
    let input = r#"(set-logic HORN)
(declare-fun inv ( Int Int ) Bool)
(assert (forall ( (A Int) (B Int) )
    (=> (and (= A 3) (= B 7)) (inv A B))))
(assert (forall ( (A Int) (B Int) (A1 Int) (B1 Int) )
    (=> (and (inv A B) (= A1 (+ A 2)) (= B1 (- B 2))) (inv A1 B1))))
(assert (forall ( (A Int) (B Int) )
    (=> (and (inv A B) (< A 0)) false)))
(check-sat)
(exit)"#;

    let mut solver = solver_from_str(input);
    solver.discover_sum_invariants();

    let pred = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "inv")
        .expect("inv predicate")
        .id;
    let vars = solver.canonical_vars(pred).expect("canonical vars");

    let expected = ChcExpr::eq(
        ChcExpr::add(ChcExpr::var(vars[0].clone()), ChcExpr::var(vars[1].clone())),
        ChcExpr::Int(10),
    );
    let lemmas: Vec<_> = solver.frames[1]
        .lemmas
        .iter()
        .filter(|l| l.predicate == pred)
        .collect();
    assert!(
        lemmas.iter().any(|l| l.formula == expected),
        "Expected sum invariant A + B = 10, got: {:?}",
        lemmas.iter().map(|l| &l.formula).collect::<Vec<_>>()
    );
}

/// Ensure triple-sum discovery can propagate to derived predicates:
/// pre: A+B+C=D, edge constrains A=0, target post should learn B+C=D.
#[test]
#[timeout(10_000)]
fn discover_triple_sum_propagates_sum_eq_var_to_target_predicate() {
    let input = r#"(set-logic HORN)
(declare-fun pre ( Int Int Int Int ) Bool)
(declare-fun post ( Int Int Int ) Bool)
(assert (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=> (and (= A 0) (= B 0) (= C 0) (= D 0)) (pre A B C D))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) )
    (=> (and (pre A B C D) (= A1 A) (= B1 (+ B 1)) (= C1 (- C 1)) (= D1 D))
        (pre A1 B1 C1 D1))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=> (and (pre A B C D) (= A 0)) (post B C D))))
(assert (forall ( (X Int) (Y Int) (Z Int) (X1 Int) (Y1 Int) (Z1 Int) )
    (=> (and (post X Y Z) (= X1 (+ X 1)) (= Y1 (- Y 1)) (= Z1 Z))
        (post X1 Y1 Z1))))
(assert (forall ( (X Int) (Y Int) (Z Int) )
    (=> (and (post X Y Z) (not (= (+ X Y) Z))) false)))
(check-sat)
(exit)"#;

    let mut solver = solver_from_str(input);
    solver.discover_triple_sum_invariants();

    let post = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "post")
        .expect("post predicate")
        .id;
    let vars = solver.canonical_vars(post).expect("canonical vars");
    assert_eq!(vars.len(), 3);

    let expected = ChcExpr::eq(
        ChcExpr::add(ChcExpr::var(vars[0].clone()), ChcExpr::var(vars[1].clone())),
        ChcExpr::var(vars[2].clone()),
    );

    let post_lemmas: Vec<_> = solver.frames[1]
        .lemmas
        .iter()
        .filter(|l| l.predicate == post)
        .collect();
    assert!(
        post_lemmas.iter().any(|l| l.formula == expected),
        "Expected propagated post invariant X + Y = Z, got: {:?}",
        post_lemmas.iter().map(|l| &l.formula).collect::<Vec<_>>()
    );
}

/// Regression test for s_multipl_18: sum preservation with variable offsets
/// and OR-branching. The transition alternates ±E based on sign of A.
/// init: v1=0, v2=0; transition: (A<0 → C=B+E, D=A-E) OR (A≥0 → C=B-E, D=A+E)
/// Expected invariant: a0 + a1 = 0 (the sum is preserved by both branches)
#[test]
#[timeout(10_000)]
fn discover_sum_invariant_s_multipl_18_pattern() {
    let input = r#"(set-logic HORN)
(declare-fun |PRE| ( Int Int Int ) Bool)
(assert
  (forall ( (A Int) (v_1 Int) (v_2 Int) )
    (=>
      (and (= 0 v_1) (= 0 v_2))
      (PRE v_1 v_2 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and
        (PRE B A E)
        (or
          (and (not (<= 0 A)) (= C (+ B E)) (= D (+ A (* (- 1) E))))
          (and (>= A 0) (= C (+ B (* (- 1) E))) (= D (+ A E))))
      )
      (PRE C D E)
    )
  )
)
(assert (forall ( (A Int) (B Int) ) (=> (and (PRE A B 0) (not (= (+ A B) 0))) false)))
(check-sat)
(exit)"#;

    let mut solver = solver_from_str(input);
    solver.discover_sum_invariants();

    let pred = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "PRE")
        .expect("PRE predicate")
        .id;
    let vars = solver.canonical_vars(pred).expect("canonical vars");
    assert_eq!(vars.len(), 3, "PRE has 3 args");

    // Expect a0 + a1 = 0
    let expected = ChcExpr::eq(
        ChcExpr::add(ChcExpr::var(vars[0].clone()), ChcExpr::var(vars[1].clone())),
        ChcExpr::Int(0),
    );
    let lemmas: Vec<_> = solver.frames[1]
        .lemmas
        .iter()
        .filter(|l| l.predicate == pred)
        .collect();
    assert!(
        lemmas.iter().any(|l| l.formula == expected),
        "Expected sum invariant a0 + a1 = 0 for s_multipl_18 pattern, got: {:?}",
        lemmas.iter().map(|l| &l.formula).collect::<Vec<_>>()
    );
}
