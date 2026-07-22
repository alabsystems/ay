// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::pdr::solver::test_helpers::solver_from_str;
use crate::ChcExpr;
use ntest::timeout;

/// Test relational invariant: A <= B.
/// init: A=0, B=5; transition: A'=A+1, B'=B+2
/// A starts below B and the gap only grows, so A <= B is preserved.
#[test]
#[timeout(10_000)]
fn discover_relational_le_preserved() {
    let input = r#"(set-logic HORN)
(declare-fun inv ( Int Int ) Bool)
(assert (forall ( (A Int) (B Int) )
(=> (and (= A 0) (= B 5)) (inv A B))))
(assert (forall ( (A Int) (B Int) (A1 Int) (B1 Int) )
(=> (and (inv A B) (= A1 (+ A 1)) (= B1 (+ B 2))) (inv A1 B1))))
(assert (forall ( (A Int) (B Int) )
(=> (and (inv A B) (> A B)) false)))
(check-sat)
(exit)"#;

    let mut solver = solver_from_str(input);
    solver.discover_relational_invariants();

    let pred = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "inv")
        .expect("inv predicate")
        .id;
    let vars = solver.canonical_vars(pred).expect("canonical vars");
    assert_eq!(vars.len(), 2);

    // Expect A <= B
    let expected = ChcExpr::le(ChcExpr::var(vars[0].clone()), ChcExpr::var(vars[1].clone()));
    let lemmas: Vec<_> = solver.frames[1]
        .lemmas
        .iter()
        .filter(|l| l.predicate == pred)
        .collect();
    assert!(
        lemmas.iter().any(|l| l.formula == expected),
        "Expected relational invariant A <= B, got: {:?}",
        lemmas.iter().map(|l| &l.formula).collect::<Vec<_>>()
    );
}

/// Test relational invariant is NOT discovered when init violates it.
/// init: A=10, B=0; transition: A'=A+1, B'=B+2
/// Initially A > B, so A <= B is false at init.
#[test]
#[timeout(10_000)]
fn discover_relational_le_fails_init() {
    let input = r#"(set-logic HORN)
(declare-fun inv ( Int Int ) Bool)
(assert (forall ( (A Int) (B Int) )
(=> (and (= A 10) (= B 0)) (inv A B))))
(assert (forall ( (A Int) (B Int) (A1 Int) (B1 Int) )
(=> (and (inv A B) (= A1 (+ A 1)) (= B1 (+ B 2))) (inv A1 B1))))
(assert (forall ( (A Int) (B Int) )
(=> (and (inv A B) (< A 0)) false)))
(check-sat)
(exit)"#;

    let mut solver = solver_from_str(input);
    solver.discover_relational_invariants();

    let pred = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "inv")
        .expect("inv predicate")
        .id;
    let vars = solver.canonical_vars(pred).expect("canonical vars");

    // Should NOT produce A <= B since init has A=10 > B=0
    let bad_invariant = ChcExpr::le(ChcExpr::var(vars[0].clone()), ChcExpr::var(vars[1].clone()));
    let le_lemmas: Vec<_> = solver.frames[1]
        .lemmas
        .iter()
        .filter(|l| l.predicate == pred && l.formula == bad_invariant)
        .collect();
    assert!(
        le_lemmas.is_empty(),
        "Should not discover A <= B when init has A=10 > B=0"
    );
}

/// Test relational invariant: A >= B.
/// init: A=5, B=0; transition: A'=A+2, B'=B+1
/// A starts above B and the gap grows.
#[test]
#[timeout(10_000)]
fn discover_relational_ge_preserved() {
    let input = r#"(set-logic HORN)
(declare-fun inv ( Int Int ) Bool)
(assert (forall ( (A Int) (B Int) )
(=> (and (= A 5) (= B 0)) (inv A B))))
(assert (forall ( (A Int) (B Int) (A1 Int) (B1 Int) )
(=> (and (inv A B) (= A1 (+ A 2)) (= B1 (+ B 1))) (inv A1 B1))))
(assert (forall ( (A Int) (B Int) )
(=> (and (inv A B) (< A B)) false)))
(check-sat)
(exit)"#;

    let mut solver = solver_from_str(input);
    solver.discover_relational_invariants();

    let pred = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "inv")
        .expect("inv predicate")
        .id;
    let vars = solver.canonical_vars(pred).expect("canonical vars");

    // Expect A >= B
    let expected = ChcExpr::ge(ChcExpr::var(vars[0].clone()), ChcExpr::var(vars[1].clone()));
    let lemmas: Vec<_> = solver.frames[1]
        .lemmas
        .iter()
        .filter(|l| l.predicate == pred)
        .collect();
    assert!(
        lemmas.iter().any(|l| l.formula == expected),
        "Expected relational invariant A >= B, got: {:?}",
        lemmas.iter().map(|l| &l.formula).collect::<Vec<_>>()
    );
}
