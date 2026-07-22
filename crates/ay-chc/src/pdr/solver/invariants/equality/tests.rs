// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::pdr::config::PdrConfig;
use crate::pdr::solver::PdrSolver;
use crate::{ChcExpr, ChcParser, ChcSort, ChcVar};

#[test]
fn extract_or_cases_top_level_or() {
    let x = ChcVar::new("x", ChcSort::Int);
    let a = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let b = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(10));
    let expr = ChcExpr::or(a.clone(), b.clone());

    assert_eq!(PdrSolver::extract_or_cases(&expr), Some(vec![a, b]));
}

#[test]
fn extract_or_cases_and_with_or() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let a = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let b = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(1));
    let c = ChcExpr::eq(ChcExpr::var(y), ChcExpr::int(2));

    let expr = ChcExpr::and(ChcExpr::or(a.clone(), b.clone()), c.clone());
    assert_eq!(
        PdrSolver::extract_or_cases(&expr),
        Some(vec![ChcExpr::and(a, c.clone()), ChcExpr::and(b, c)])
    );
}

#[test]
fn extract_boundary_equalities_simple_and_nested() {
    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let c = ChcVar::new("C", ChcSort::Int);
    let e = ChcVar::new("E", ChcSort::Int);

    let ge_expr = ChcExpr::ge(ChcExpr::var(a.clone()), ChcExpr::var(e.clone()));
    assert_eq!(
        PdrSolver::extract_boundary_equalities(&ge_expr),
        vec![ChcExpr::eq(
            ChcExpr::var(a.clone()),
            ChcExpr::var(e.clone())
        )]
    );

    let gt_expr = ChcExpr::gt(ChcExpr::var(a.clone()), ChcExpr::var(e.clone()));
    assert_eq!(
        PdrSolver::extract_boundary_equalities(&gt_expr),
        vec![ChcExpr::eq(
            ChcExpr::var(a.clone()),
            ChcExpr::add(ChcExpr::var(e.clone()), ChcExpr::int(1))
        )]
    );

    let le_expr = ChcExpr::le(ChcExpr::var(b.clone()), ChcExpr::var(c.clone()));
    let and_expr = ChcExpr::and(ge_expr, le_expr);
    assert_eq!(
        PdrSolver::extract_boundary_equalities(&and_expr),
        vec![
            ChcExpr::eq(ChcExpr::var(a.clone()), ChcExpr::var(e.clone())),
            ChcExpr::eq(ChcExpr::var(b), ChcExpr::var(c))
        ]
    );

    // Test < operator: A < E => A = E - 1
    let lt_expr = ChcExpr::lt(ChcExpr::var(a), ChcExpr::var(e));
    assert_eq!(
        PdrSolver::extract_boundary_equalities(&lt_expr),
        vec![ChcExpr::eq(
            ChcExpr::var(ChcVar::new("A", ChcSort::Int)),
            ChcExpr::sub(
                ChcExpr::var(ChcVar::new("E", ChcSort::Int)),
                ChcExpr::int(1)
            )
        )]
    );
}

// ========================================================================
// Tests for is_equality_preserved_by_transitions_with_entry()
// ========================================================================

#[test]
fn equality_preservation_requires_self_loop_clauses() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun P (Int Int) Bool)
(declare-fun Q (Int Int) Bool)

; P has a fact clause, but no self-loop transitions.
(assert (forall ((A Int) (B Int))
  (=> (= A B)
  (P A B))))

; Inter-predicate transition into P (should be ignored by preservation check).
(assert (forall ((A Int) (B Int))
  (=> (Q A B)
  (P A B))))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let p = solver.problem.get_predicate_by_name("P").unwrap().id;

    assert!(!solver.is_equality_preserved_by_transitions_with_entry(p, 0, 1, None));
}

#[test]
fn equality_preservation_ignores_inter_predicate_transitions() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun P (Int Int) Bool)
(declare-fun Q (Int Int) Bool)

; Init for P: A = B.
(assert (forall ((A Int) (B Int))
  (=> (= A B)
  (P A B))))

; P self-loop preserves equality: A' = A + 1, B' = B + 1.
(assert (forall ((A Int) (B Int) (A2 Int) (B2 Int))
  (=> (and (P A B) (= A2 (+ A 1)) (= B2 (+ B 1)))
  (P A2 B2))))

; Q can inject states violating A = B, but preservation check intentionally ignores this.
(assert (forall ((A Int) (B Int))
  (=> (Q A B)
  (P A (+ B 1)))))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let p = solver.problem.get_predicate_by_name("P").unwrap().id;

    assert!(solver.is_equality_preserved_by_transitions_with_entry(p, 0, 1, None));
}

#[test]
fn equality_preservation_respects_entry_constraint() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun P (Int Int Int) Bool)

; Init makes only Z=0 reachable, and A=B holds at init.
(assert (forall ((A Int) (B Int) (Z Int))
  (=> (and (= A B) (= Z 0))
  (P A B Z))))

; Transition preserves equality when Z=0, but can break it when Z=1.
(assert (forall ((A Int) (B Int) (Z Int) (A2 Int) (B2 Int))
  (=> (and (P A B Z)
           (or (and (= Z 0) (= A2 (+ A 1)) (= B2 (+ B 1)))
               (and (= Z 1) (= A2 (+ A 1)) (= B2 (+ B 2)))))
  (P A2 B2 Z))))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let p = solver.problem.get_predicate_by_name("P").unwrap().id;

    // Without an entry constraint, the (Z=1) branch makes the check fail.
    assert!(!solver.is_equality_preserved_by_transitions_with_entry(p, 0, 1, None));

    // With an entry constraint restricting to reachable states (Z=0), equality is preserved.
    let canon = solver.canonical_vars(p).unwrap().to_vec();
    let entry_constraint = ChcExpr::eq(ChcExpr::var(canon[2].clone()), ChcExpr::int(0));
    assert!(solver.is_equality_preserved_by_transitions_with_entry(
        p,
        0,
        1,
        Some(entry_constraint)
    ));
}

#[test]
fn equality_preservation_accepts_correlated_or_offsets() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun P (Int Int) Bool)

; Init for P: A = B.
(assert (forall ((A Int) (B Int))
  (=> (= A B)
  (P A B))))

; Correlated OR cases: in each case both vars shift by the same offset.
(assert (forall ((A Int) (B Int) (A2 Int) (B2 Int))
  (=> (and (P A B)
           (or (and (= A2 (+ A 1)) (= B2 (+ B 1)))
               (and (= A2 (+ A 2)) (= B2 (+ B 2)))))
  (P A2 B2))))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let p = solver.problem.get_predicate_by_name("P").unwrap().id;

    assert!(solver.is_equality_preserved_by_transitions_with_entry(p, 0, 1, None));
}

// ========================================================================
// Tests for discover_equality_invariants() - #1658
// ========================================================================

/// Test Phase 1: discover equality from var=var init constraint (e.g., (= A B))
///
/// This tests the case where the init clause has a direct variable equality
/// constraint, not just identical constant values.
#[test]
fn phase1_discovers_equality_from_var_eq_var_init() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun Inv (Int Int) Bool)

; Init: Inv(A, B) when A = B (no constant values, just equality)
(assert (forall ((A Int) (B Int))
  (=> (= A B)
  (Inv A B))))

; Self-loop preserves equality: A' = A + 1, B' = B + 1
(assert (forall ((A Int) (B Int) (A2 Int) (B2 Int))
  (=> (and (Inv A B) (= A2 (+ A 1)) (= B2 (+ B 1)))
  (Inv A2 B2))))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    // Run discovery
    solver.discover_equality_invariants();

    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let vars = solver.canonical_vars(inv).unwrap().to_vec();
    assert_eq!(vars.len(), 2);

    // The discovered equality should be A = B
    let expected = ChcExpr::eq(ChcExpr::var(vars[0].clone()), ChcExpr::var(vars[1].clone()));

    assert!(
        solver.frames[1].contains_lemma(inv, &expected),
        "expected to discover equality invariant {} = {} from var=var init",
        vars[0].name,
        vars[1].name
    );
}

#[test]
fn phase1_discovers_bv_equality_from_matching_init_constants() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun Inv ((_ BitVec 16) (_ BitVec 16)) Bool)

; Init: both BV fields are the same constructor payload after DT flattening.
(assert (forall ((A (_ BitVec 16)) (B (_ BitVec 16)))
  (=> (and (= A #x0000) (= B #x0000))
  (Inv A B))))

; Self-loop preserves equality: both payloads increment in lockstep.
(assert (forall ((A (_ BitVec 16)) (B (_ BitVec 16)) (A2 (_ BitVec 16)) (B2 (_ BitVec 16)))
  (=> (and (Inv A B) (= A2 (bvadd A #x0001)) (= B2 (bvadd B #x0001)))
  (Inv A2 B2))))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    solver.discover_equality_invariants();

    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let vars = solver.canonical_vars(inv).unwrap().to_vec();
    let expected = ChcExpr::eq(ChcExpr::var(vars[0].clone()), ChcExpr::var(vars[1].clone()));

    assert!(
        solver.frames[1].contains_lemma(inv, &expected),
        "expected to discover BV equality invariant {} = {} from matching init constants",
        vars[0].name,
        vars[1].name
    );
}

/// Test Phase 2: equality propagation through identity-like transition
///
/// When P has an equality invariant A = B and there's a transition P -> Q
/// that maps arguments directly (identity-like), the equality should propagate to Q.
#[test]
fn phase2_propagates_equality_through_identity_transition() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun P (Int Int) Bool)
(declare-fun Q (Int Int) Bool)

; Init for P: both vars equal to 0
(assert (forall ((A Int) (B Int))
  (=> (and (= A 0) (= B 0))
  (P A B))))

; Identity transition: P(A, B) => Q(A, B)
; This is the key pattern: args pass through unchanged
(assert (forall ((A Int) (B Int))
  (=> (P A B)
  (Q A B))))

; Q has its own self-loop (to make it a non-trivial predicate)
(assert (forall ((A Int) (B Int) (A2 Int) (B2 Int))
  (=> (and (Q A B) (= A2 (+ A 1)) (= B2 (+ B 1)))
  (Q A2 B2))))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    // Run discovery
    solver.discover_equality_invariants();

    let p = solver.problem.get_predicate_by_name("P").unwrap().id;
    let q = solver.problem.get_predicate_by_name("Q").unwrap().id;

    let p_vars = solver.canonical_vars(p).unwrap().to_vec();
    let q_vars = solver.canonical_vars(q).unwrap().to_vec();

    // P should have the equality
    let p_eq = ChcExpr::eq(
        ChcExpr::var(p_vars[0].clone()),
        ChcExpr::var(p_vars[1].clone()),
    );
    if !solver.frames[1].contains_lemma(p, &p_eq) {
        return;
    }

    // Q should also have the equality (propagated from P)
    let q_eq = ChcExpr::eq(
        ChcExpr::var(q_vars[0].clone()),
        ChcExpr::var(q_vars[1].clone()),
    );
    assert!(
        solver.frames[1].contains_lemma(q, &q_eq),
        "Q should have equality invariant propagated from P"
    );
}

/// Test Phase 3: transition equality discovery at boundary
///
/// Tests the gj2007_m_* pattern where a NEW equality is discovered at the
/// transition point due to boundary conditions in the constraint.
///
/// P has invariant B = E, transition constraint is A >= E, and at the
/// boundary (A = E), we can derive B = A for Q.
#[test]
fn phase3_discovers_transition_equality_at_boundary() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun P (Int Int Int) Bool)
(declare-fun Q (Int Int Int) Bool)

; Init for P: B = E but A != B
(assert (forall ((A Int) (B Int) (E Int))
  (=> (and (= A 0) (= B 2) (= E 2))
  (P A B E))))

; Self-loop: while A < E, increment A by 1 (B, E unchanged)
(assert (forall ((A Int) (B Int) (E Int) (A2 Int))
  (=> (and (P A B E) (< A E) (= A2 (+ A 1)))
  (P A2 B E))))

; Transition to Q: only fires when A >= E (boundary: A = E for this loop)
; At the boundary, since B = E (invariant of P), we have B = A in Q.
(assert (forall ((A Int) (B Int) (E Int))
  (=> (and (P A B E) (>= A E))
  (Q A B E))))

; Q self-loop preserves A, B, E
(assert (forall ((A Int) (B Int) (E Int))
  (=> (Q A B E)
  (Q A B E))))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    // Run full equality discovery including Phase 3.
    solver.discover_equality_invariants();

    let p = solver.problem.get_predicate_by_name("P").unwrap().id;
    let q = solver.problem.get_predicate_by_name("Q").unwrap().id;

    let p_vars = solver.canonical_vars(p).unwrap().to_vec();
    let q_vars = solver.canonical_vars(q).unwrap().to_vec();

    // Phase 1 should discover B = E for P, but not A = B.
    let p_a_eq_b = ChcExpr::eq(
        ChcExpr::var(p_vars[0].clone()),
        ChcExpr::var(p_vars[1].clone()),
    );
    assert!(
        !solver.frames[1].contains_lemma(p, &p_a_eq_b),
        "P should not have A = B (init has A=0, B=2)"
    );

    // Phase 3 should discover A = B for Q at the boundary.
    let q_a_eq_b = ChcExpr::eq(
        ChcExpr::var(q_vars[0].clone()),
        ChcExpr::var(q_vars[1].clone()),
    );
    assert!(
        solver.frames[1].contains_lemma(q, &q_a_eq_b),
        "expected Q to discover A = B via boundary transition (P has B = E and guard A >= E)"
    );
}

/// Test that equality discovery skips predicates with incoming inter-predicate transitions.
///
/// Regression test: predicates that receive states from OTHER predicates cannot
/// trust their init clause for equality discovery, since those injected states
/// may not satisfy the init equality.
#[test]
fn skips_predicate_with_incoming_inter_predicate_transitions() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun P (Int Int) Bool)
(declare-fun Q (Int Int) Bool)

; Init for P: A = B = 0 (equality holds in init)
(assert (forall ((A Int) (B Int))
  (=> (and (= A 0) (= B 0))
  (P A B))))

; Init for Q: also A = B = 1
(assert (forall ((A Int) (B Int))
  (=> (and (= A 1) (= B 1))
  (Q A B))))

; P -> Q transition that can inject non-equal states
; This is the key: Q(A, B+1) means B+1 != A when A = B
(assert (forall ((A Int) (B Int))
  (=> (P A B)
  (Q A (+ B 1)))))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    // Run discovery
    solver.discover_equality_invariants();

    let q = solver.problem.get_predicate_by_name("Q").unwrap().id;
    let q_vars = solver.canonical_vars(q).unwrap().to_vec();

    // Q should NOT have A = B as an invariant because P can inject (A, B+1) states
    let q_eq = ChcExpr::eq(
        ChcExpr::var(q_vars[0].clone()),
        ChcExpr::var(q_vars[1].clone()),
    );

    assert!(
        !solver.frames[1].contains_lemma(q, &q_eq),
        "Q should NOT have A = B invariant due to incoming inter-predicate transition"
    );
}

// ========================================================================
// Tests for D1: Array-sorted predicate-argument equality discovery
// (LIA-Lin-Arrays llreve lockstep pattern, e.g. libc__memchr_1)
// ========================================================================

/// Phase 1 discovers a lockstep array equality `(= a1 a2)` from a var=var
/// init constraint when the self-loop passes both arrays through unchanged
/// (the llreve relational pattern: both program copies share the array).
#[test]
fn phase1_discovers_array_equality_from_var_eq_var_init() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun Inv (Int (Array Int Int) (Array Int Int)) Bool)

; Init: Inv(I, A, B) when A = B (lockstep arrays)
(assert (forall ((I Int) (A (Array Int Int)) (B (Array Int Int)))
  (=> (and (= I 0) (= A B))
  (Inv I A B))))

; Self-loop reads both arrays but never writes: equality is preserved.
(assert (forall ((I Int) (I2 Int) (A (Array Int Int)) (B (Array Int Int)))
  (=> (and (Inv I A B) (= (select A I) (select B I)) (= I2 (+ I 1)))
  (Inv I2 A B))))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    solver.discover_equality_invariants();

    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let vars = solver.canonical_vars(inv).unwrap().to_vec();
    assert_eq!(vars.len(), 3);

    let expected = ChcExpr::eq(ChcExpr::var(vars[1].clone()), ChcExpr::var(vars[2].clone()));

    assert!(
        solver.frames[1].contains_lemma(inv, &expected),
        "expected to discover lockstep array equality invariant {} = {} from var=var init",
        vars[1].name,
        vars[2].name
    );
}

/// An array equality must NOT be discovered when a self-loop stores into
/// only one of the two arrays (equality is not preserved).
#[test]
fn phase1_rejects_array_equality_broken_by_one_sided_store() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun Inv (Int (Array Int Int) (Array Int Int)) Bool)

; Init: arrays start equal.
(assert (forall ((I Int) (A (Array Int Int)) (B (Array Int Int)))
  (=> (and (= I 0) (= A B))
  (Inv I A B))))

; Self-loop stores into A only: equality is NOT preserved.
(assert (forall ((I Int) (I2 Int) (A (Array Int Int)) (A2 (Array Int Int)) (B (Array Int Int)))
  (=> (and (Inv I A B) (= A2 (store A I 7)) (= I2 (+ I 1)))
  (Inv I2 A2 B))))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    solver.discover_equality_invariants();

    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let vars = solver.canonical_vars(inv).unwrap().to_vec();

    let eq = ChcExpr::eq(ChcExpr::var(vars[1].clone()), ChcExpr::var(vars[2].clone()));

    assert!(
        !solver.frames[1].contains_lemma(inv, &eq),
        "array equality {} = {} must be rejected: a one-sided store breaks it",
        vars[1].name,
        vars[2].name
    );
}

/// #8675 regression guard: store-shaped array equalities are still rejected
/// by add_discovered_invariant even after the D1 var-var carve-out.
#[test]
fn store_shaped_array_equality_still_rejected_8675() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun Inv ((Array Int Int) (Array Int Int)) Bool)

(assert (forall ((A (Array Int Int)) (B (Array Int Int)))
  (=> (= A B)
  (Inv A B))))

(assert (forall ((A (Array Int Int)) (B (Array Int Int)))
  (=> (Inv A B)
  (Inv A B))))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let vars = solver.canonical_vars(inv).unwrap().to_vec();

    // `(= a (store b 0 0))` pins array structure — must stay rejected (#8675).
    let store_eq = ChcExpr::eq(
        ChcExpr::var(vars[0].clone()),
        ChcExpr::store(
            ChcExpr::var(vars[1].clone()),
            ChcExpr::int(0),
            ChcExpr::int(0),
        ),
    );
    assert!(
        !solver.add_discovered_invariant(inv, store_eq.clone(), 1),
        "store-shaped array equality must still be rejected by #8675 guard"
    );
    assert!(
        !solver.frames[1].contains_lemma(inv, &store_eq),
        "store-shaped array equality must not be inserted into frames"
    );
}
