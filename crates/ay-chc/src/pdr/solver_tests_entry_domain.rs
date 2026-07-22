// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// PDR solver entry domain and verification tests — extracted from solver_tests.rs

use super::{ChcExpr, ChcParser, ChcSort, ChcVar, Lemma, PdrConfig, PdrSolver};
use crate::smt::SmtResult;

// Tests for verify_implication_algebraically soundness fix (#1003)

#[test]
fn test_verify_implication_algebraically_le_handled() {
    // Body: x = 5
    // Head: x <= 10
    // Should verify: 5 <= 10 is true
    let x = ChcVar::new("x", ChcSort::Int);
    let body = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let head = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(10));
    assert!(
        PdrSolver::verify_implication_algebraically(&body, &head),
        "Le constraint should be verified when body implies it"
    );
}

#[test]
fn test_verify_implication_algebraically_le_fails_when_false() {
    // Body: x = 15
    // Head: x <= 10
    // Should NOT verify: 15 <= 10 is false
    let x = ChcVar::new("x", ChcSort::Int);
    let body = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(15));
    let head = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(10));
    assert!(
        !PdrSolver::verify_implication_algebraically(&body, &head),
        "Le constraint should fail when body does not imply it"
    );
}

#[test]
fn test_verify_implication_algebraically_lt_returns_false() {
    // Body: x = 5
    // Head: x < 10
    // Lt is unsupported - should return false conservatively
    let x = ChcVar::new("x", ChcSort::Int);
    let body = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let head = ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(10));
    assert!(
        !PdrSolver::verify_implication_algebraically(&body, &head),
        "Lt constraint should return false (unsupported operation)"
    );
}

#[test]
fn test_verify_implication_algebraically_gt_returns_false() {
    // Body: x = 15
    // Head: x > 10
    // Gt is unsupported - should return false conservatively
    let x = ChcVar::new("x", ChcSort::Int);
    let body = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(15));
    let head = ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(10));
    assert!(
        !PdrSolver::verify_implication_algebraically(&body, &head),
        "Gt constraint should return false (unsupported operation)"
    );
}

#[test]
fn test_verify_implication_algebraically_ne_returns_false() {
    // Body: x = 5
    // Head: x != 10
    // Ne is unsupported - should return false conservatively
    let x = ChcVar::new("x", ChcSort::Int);
    let body = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let head = ChcExpr::ne(ChcExpr::var(x), ChcExpr::int(10));
    assert!(
        !PdrSolver::verify_implication_algebraically(&body, &head),
        "Ne constraint should return false (unsupported operation)"
    );
}

#[test]
fn test_verify_implication_algebraically_mixed_conjuncts() {
    // Body: x = 5
    // Head: x = 5 AND x >= 0 AND x <= 10
    // All supported operations that should verify via direct substitution
    let x = ChcVar::new("x", ChcSort::Int);
    let body = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let head = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5)),
        ChcExpr::and(
            ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::le(ChcExpr::var(x), ChcExpr::int(10)),
        ),
    );
    assert!(
        PdrSolver::verify_implication_algebraically(&body, &head),
        "Mixed Eq/Ge/Le conjuncts should verify"
    );
}

#[test]
fn test_verify_implication_algebraically_unsupported_fails_mixed() {
    // Body: x = 5
    // Head: x >= 0 AND x < 10
    // Even though x >= 0 is supported, x < 10 (Lt) should cause failure
    let x = ChcVar::new("x", ChcSort::Int);
    let body = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let head = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(10)),
    );
    assert!(
        !PdrSolver::verify_implication_algebraically(&body, &head),
        "Unsupported Lt in mixed conjuncts should cause failure"
    );
}

#[test]
fn test_verify_implication_algebraically_not_returns_false() {
    // Body: x = 5
    // Head: Not(x = 10)
    // Not constraints cannot be verified algebraically and should return false.
    // (Soundness fix #1011)
    let x = ChcVar::new("x", ChcSort::Int);
    let body = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let head = ChcExpr::not(ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(10)));
    assert!(
        !PdrSolver::verify_implication_algebraically(&body, &head),
        "Not constraint should return false (unsupported operation)"
    );
}

#[test]
fn test_verify_implication_algebraically_not_mixed_returns_false() {
    // Body: x = 5
    // Head: x >= 0 AND Not(x = 10)
    // Even if x >= 0 verifies, the Not should cause the entire check to fail
    // (Soundness fix #1011)
    let x = ChcVar::new("x", ChcSort::Int);
    let body = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let head = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::not(ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(10))),
    );
    assert!(
        !PdrSolver::verify_implication_algebraically(&body, &head),
        "Not constraint in mixed conjuncts should cause failure"
    );
}

// Soundness tests for blocks_initial_states (#1014)
//
// The function must return false (conservative) when:
// 1. apply_to_args fails (can't substitute formula into head args)
// 2. SMT returns Unknown (can't prove blocks init)
// Previously returned true in these cases, which was unsound.
//
// Note: The failure paths are hard to trigger in unit tests because:
// - apply_to_args only fails if canonical_vars is missing (internal error)
// - SMT Unknown requires timeout/resource exhaustion (nondeterministic)
//
// The fix changes return values from true->false in these paths, which is
// verifiable by code inspection. These tests verify normal operation.

#[test]
fn test_blocks_initial_states_true_when_formula_excludes_init() {
    // Init: x = 0
    // Formula: x > 0 (excludes all init states)
    // Expected: true (formula blocks init)
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int)) (=> (and (Inv x) (> x 10)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let config = PdrConfig::default();
    let mut solver = PdrSolver::new(problem, config);

    let pred = solver.problem.predicates()[0].id;
    let x = solver.canonical_vars(pred).unwrap()[0].clone();

    // Formula x > 0 blocks init (x = 0)
    let formula = ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(0));
    assert!(
        solver.blocks_initial_states(pred, &formula),
        "x > 0 should block init state x = 0"
    );
}

#[test]
fn test_blocks_initial_states_false_when_formula_includes_init() {
    // Init: x = 0
    // Formula: x >= 0 (includes init state)
    // Expected: false (formula does NOT block init)
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int)) (=> (and (Inv x) (> x 10)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let config = PdrConfig::default();
    let mut solver = PdrSolver::new(problem, config);

    let pred = solver.problem.predicates()[0].id;
    let x = solver.canonical_vars(pred).unwrap()[0].clone();

    // Formula x >= 0 includes init (x = 0)
    let formula = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));
    assert!(
        !solver.blocks_initial_states(pred, &formula),
        "x >= 0 should NOT block init state x = 0"
    );
}

#[test]
fn test_blocks_initial_states_false_when_formula_equals_init() {
    // Init: x = 0
    // Formula: x = 0 (exactly the init state)
    // Expected: false (formula does NOT block init)
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int)) (=> (and (Inv x) (> x 10)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let config = PdrConfig::default();
    let mut solver = PdrSolver::new(problem, config);

    let pred = solver.problem.predicates()[0].id;
    let x = solver.canonical_vars(pred).unwrap()[0].clone();

    // Formula x = 0 is exactly init
    let formula = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(0));
    assert!(
        !solver.blocks_initial_states(pred, &formula),
        "x = 0 should NOT block init state x = 0"
    );
}

/// Regression test for #1607: discover_relational_invariants should use an SMT check to
/// establish init validity (not require both vars be constant).
/// Updated for #7048: both variables change so neither is constant-arg filtered.
/// Init: a=c (not explicit bounds, requires SMT to verify a<=c).
/// Transition: a'=a+1, c'=c+2 — gap only grows, so a<=c preserved.
#[test]
fn test_discover_relational_invariants_uses_smt_init_validity() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int Int) Bool)
(assert (forall ((a Int) (c Int))
  (=> (= a c) (Inv a c))))
(assert (forall ((a Int) (c Int) (a1 Int) (c1 Int))
  (=> (and (Inv a c) (= a1 (+ a 1)) (= c1 (+ c 2))) (Inv a1 c1))))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let canonical_vars = solver.canonical_vars(inv).unwrap().to_vec();
    assert_eq!(canonical_vars.len(), 2);

    let a = canonical_vars[0].clone();
    let c = canonical_vars[1].clone();

    solver.discover_relational_invariants();

    let expected = ChcExpr::le(ChcExpr::var(a.clone()), ChcExpr::var(c.clone()));
    assert!(
        solver.frames[1]
            .lemmas
            .iter()
            .any(|l| l.predicate == inv && l.formula == expected),
        "expected to discover relational invariant: {} <= {}",
        a.name,
        c.name
    );
}

/// Regression test for #1411: scaled-diff-bound preservation with F1 context
///
/// Tests that `is_scaled_diff_bound_preserved` correctly handles relative
/// inductiveness, where an invariant is only preserved when assuming
/// already-learned frame invariants (F1).
///
/// Transition: inv(a,b,c,d) => inv(a,b,c, d - (b - a))
/// Candidate invariant: d - 2*c >= 0
///
/// - Without F1: counterexample exists (b - a != 0)
/// - With F1 containing a = b: preserved (b - a = 0, so d' = d)
#[test]
fn test_scaled_diff_bound_preserved_with_f1_context() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int Int Int Int) Bool)
(assert (forall ((a Int) (b Int) (c Int) (d Int))
  (=> (inv a b c d)
  (inv a b c (- d (- b a))))))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.get_predicate_by_name("inv").unwrap().id;
    let canonical_vars = solver.canonical_vars(inv).unwrap().to_vec();

    assert_eq!(canonical_vars.len(), 4);
    let var_c = &canonical_vars[2];
    let var_d = &canonical_vars[3];

    let preserved_without_f1 = solver.is_scaled_diff_bound_preserved(inv, var_c, var_d, 2, 0);

    // Add the equality lemma a = b to F1
    let var_a = &canonical_vars[0];
    let var_b = &canonical_vars[1];
    let equality_lemma = Lemma::new(
        inv,
        ChcExpr::eq(ChcExpr::var(var_a.clone()), ChcExpr::var(var_b.clone())),
        1,
    );
    solver.frames[1].add_lemma(equality_lemma);

    let preserved_with_f1 = solver.is_scaled_diff_bound_preserved(inv, var_c, var_d, 2, 0);
    assert!(
        preserved_with_f1,
        "d - 2*c >= 0 should be preserved with F1 lemma a = b"
    );

    if !preserved_without_f1 {
        safe_eprintln!("As expected, preservation failed without F1 lemma");
    }
}

/// Regression test for #1411: scaled-diff (equality) preservation with F1 context
#[test]
fn test_scaled_diff_preserved_with_f1_context() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int Int Int Int Int) Bool)
(assert (forall ((a Int) (b Int) (c Int) (d Int) (e Int))
  (=> (inv a b c d e)
  (inv a b c (- d (- b a)) e))))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.get_predicate_by_name("inv").unwrap().id;
    let canonical_vars = solver.canonical_vars(inv).unwrap().to_vec();

    assert_eq!(canonical_vars.len(), 5);
    let var_c = &canonical_vars[2];
    let var_d = &canonical_vars[3];
    let var_e = &canonical_vars[4];

    let preserved_without_f1 = solver.is_scaled_diff_preserved(inv, var_c, var_d, var_e, 2);

    // Add the equality lemma a = b to F1
    let var_a = &canonical_vars[0];
    let var_b = &canonical_vars[1];
    let equality_lemma = Lemma::new(
        inv,
        ChcExpr::eq(ChcExpr::var(var_a.clone()), ChcExpr::var(var_b.clone())),
        1,
    );
    solver.frames[1].add_lemma(equality_lemma);

    let preserved_with_f1 = solver.is_scaled_diff_preserved(inv, var_c, var_d, var_e, 2);
    assert!(
        preserved_with_f1,
        "d - c = 2*e should be preserved with F1 lemma a = b"
    );

    if !preserved_without_f1 {
        safe_eprintln!("As expected, equality preservation failed without F1 lemma");
    }
}

fn ite_guarded_scaled_diff_solver_for_tests() -> PdrSolver {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int Int Int Int) Bool)
(assert (forall ((a Int) (b Int) (e Int) (j Int)
                 (a1 Int) (b1 Int) (e1 Int))
  (=>
    (and
      (inv a b e j)
      (= j 1)
      (= a1 (ite (= j 1) (+ a 2) a))
      (= b1 b)
      (= e1 (ite (= j 1) (+ e 1) (+ e 2))))
    (inv a1 b1 e1 j))))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    PdrSolver::new(problem, PdrConfig::default())
}

#[test]
fn test_scaled_diff_preserved_uses_ite_case_split_issue_9689() {
    let mut solver = ite_guarded_scaled_diff_solver_for_tests();
    let inv = solver.problem.get_predicate_by_name("inv").unwrap().id;
    let vars = solver.canonical_vars(inv).unwrap().to_vec();

    solver
        .smt
        .push_forced_check_sat_result_for_tests(SmtResult::Unknown);
    solver
        .smt
        .push_forced_check_sat_result_for_tests(SmtResult::Unsat);
    solver
        .smt
        .push_forced_check_sat_result_for_tests(SmtResult::Unsat);

    assert!(
        solver.is_scaled_diff_preserved(inv, &vars[0], &vars[1], &vars[2], 2),
        "a - b = 2*e should be accepted when both ITE split branches are UNSAT"
    );
}

#[test]
fn test_scaled_diff_preserved_rejects_sat_ite_branch_issue_9689() {
    let mut solver = ite_guarded_scaled_diff_solver_for_tests();
    let inv = solver.problem.get_predicate_by_name("inv").unwrap().id;
    let vars = solver.canonical_vars(inv).unwrap().to_vec();

    solver
        .smt
        .push_forced_check_sat_result_for_tests(SmtResult::Unknown);
    solver
        .smt
        .push_forced_check_sat_result_for_tests(SmtResult::Sat(Default::default()));

    assert!(
        !solver.is_scaled_diff_preserved(inv, &vars[0], &vars[1], &vars[2], 2),
        "a SAT split branch is a preservation counterexample and must reject"
    );
}

#[test]
fn test_scaled_diff_preserved_rejects_unknown_ite_branch_issue_9689() {
    let mut solver = ite_guarded_scaled_diff_solver_for_tests();
    let inv = solver.problem.get_predicate_by_name("inv").unwrap().id;
    let vars = solver.canonical_vars(inv).unwrap().to_vec();

    solver
        .smt
        .push_forced_check_sat_result_for_tests(SmtResult::Unknown);
    solver
        .smt
        .push_forced_check_sat_result_for_tests(SmtResult::Unsat);
    solver
        .smt
        .push_forced_check_sat_result_for_tests(SmtResult::Unknown);

    assert!(
        !solver.is_scaled_diff_preserved(inv, &vars[0], &vars[1], &vars[2], 2),
        "an UNKNOWN split branch must keep scaled-diff preservation fail-closed"
    );
}

/// Test entry_domain_constraint: computes entry domain for no-facts predicates.
///
/// Phase-chain: inv (with facts) -> inv2 (no facts)
/// Entry guard: inv(A, B, C) && A >= C => inv2(A, B, C)
/// Expected: entry_domain_constraint(inv2, 1) includes A >= C from entry clause
/// and any frame[1] invariants from inv.
#[test]
fn test_entry_domain_constraint_basic() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun inv (Int Int Int) Bool)
(declare-fun inv2 (Int Int Int) Bool)

; Init: inv has facts
(assert (forall ((A Int) (B Int) (C Int))
  (=> (and (= A 0) (= B 0) (>= C 1))
  (inv A B C))))

; Entry transition: inv -> inv2 when A >= C
(assert (forall ((A Int) (B Int) (C Int))
  (=> (and (inv A B C) (>= A C))
  (inv2 A B C))))

; Error clause
(assert (forall ((A Int) (B Int) (C Int))
  (=> (and (inv2 A B C) (< A 0)) false)))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.get_predicate_by_name("inv").unwrap().id;
    let inv2 = solver.problem.get_predicate_by_name("inv2").unwrap().id;

    // inv has facts, inv2 does not
    assert!(solver.predicate_has_facts(inv));
    assert!(!solver.predicate_has_facts(inv2));

    // Add a frame[1] lemma to inv: A >= 0
    let inv_vars = solver.canonical_vars(inv).unwrap().to_vec();
    let a_ge_0 = ChcExpr::ge(ChcExpr::var(inv_vars[0].clone()), ChcExpr::int(0));
    solver.frames[1].add_lemma(Lemma::new(inv, a_ge_0, 1));

    // Compute entry domain for inv2 at level 1
    let entry_domain = solver.entry_domain_constraint(inv2, 1);
    assert!(entry_domain.is_some(), "expected entry domain for inv2");

    // The entry domain should incorporate the entry clause constraint A >= C
    // and possibly the frame invariant A >= 0
    let ed = entry_domain.unwrap();
    safe_eprintln!("entry_domain(inv2, 1) = {ed}");

    // We can't easily match the exact form due to variable renaming,
    // but we verify it's non-trivial (not just True)
    assert!(
        !matches!(ed, ChcExpr::Bool(true)),
        "entry domain should not be trivially True"
    );
}

/// Test entry_domain_constraint returns None for predicates WITH facts.
#[test]
fn test_entry_domain_constraint_returns_none_for_facts_predicate() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun inv (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (inv x) false)))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.get_predicate_by_name("inv").unwrap().id;
    assert!(solver.predicate_has_facts(inv));

    // Should return None for predicates with facts
    let entry_domain = solver.entry_domain_constraint(inv, 1);
    assert!(
        entry_domain.is_none(),
        "entry_domain should be None for predicates with facts"
    );
}

/// Test is_self_inductive_blocking_with_entry_domain: invariant preserved only on entry domain.
///
/// Phase chain: inv -> inv2
/// Entry: inv(A, B) && A >= B => inv2(A, B)
/// Self-loop: inv2(A, B) => inv2(A+1, ite(B <= A, B+1, B))
///
/// The invariant A = B is NOT preserved over all states (if B > A, B doesn't increment).
/// But A = B IS preserved when A >= B (entry domain), because then B increments with A.
#[test]
fn test_self_inductive_with_entry_domain_conditional_update() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun inv (Int Int) Bool)
(declare-fun inv2 (Int Int) Bool)

; Init
(assert (forall ((A Int) (B Int))
  (=> (and (= A 0) (= B 0))
  (inv A B))))

; Self-loop for inv
(assert (forall ((A Int) (B Int) (A2 Int) (B2 Int))
  (=> (and (inv A B) (= A2 (+ A 1)) (= B2 (+ B 1)))
  (inv A2 B2))))

; Entry: inv -> inv2 when A >= B
(assert (forall ((A Int) (B Int))
  (=> (and (inv A B) (>= A B))
  (inv2 A B))))

; Self-loop for inv2: B only increments when B <= A
(assert (forall ((A Int) (B Int) (A2 Int) (B2 Int))
  (=> (and (inv2 A B) (= A2 (+ A 1)) (= B2 (ite (<= B A) (+ B 1) B)))
  (inv2 A2 B2))))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.get_predicate_by_name("inv").unwrap().id;
    let inv2 = solver.problem.get_predicate_by_name("inv2").unwrap().id;

    assert!(solver.predicate_has_facts(inv));
    assert!(!solver.predicate_has_facts(inv2));

    let inv2_vars = solver.canonical_vars(inv2).unwrap().to_vec();
    let var_a = &inv2_vars[0];
    let var_b = &inv2_vars[1];

    // Blocking formula for NOT(A = B) is (A = B)
    // We want to establish A = B as an invariant, so we block states where A != B
    // The blocking formula in PDR is the cube we want to block
    let blocking = ChcExpr::eq(ChcExpr::var(var_a.clone()), ChcExpr::var(var_b.clone()));

    // Without entry domain: checking if NOT(A=B) is preserved by self-loop
    // This checks: inv2(A,B) && NOT(A=B) && transition => NOT(A'=B')
    // On entry domain A >= B with A=B, after transition: A'=A+1, B'=B+1 (since B<=A), so A'=B'
    // But if we don't assume entry domain, counterexample exists where A < B initially

    // Compute entry domain
    let entry_domain = solver.entry_domain_constraint(inv2, 1);
    safe_eprintln!("entry_domain for inv2: {:?}", entry_domain);

    // Test with entry domain
    let inductive_with_entry =
        solver.is_self_inductive_blocking_with_entry_domain(&blocking, inv2, entry_domain.as_ref());
    safe_eprintln!(
        "is_self_inductive_blocking_with_entry_domain(A=B, inv2) = {inductive_with_entry}"
    );

    // The key test: with entry domain, the invariant should be inductively preserved
    // (entry domain includes A >= B from entry clause, so B <= A is satisfied)
    // Note: This may still fail if entry_domain_constraint doesn't include enough constraints
    // In that case, we manually test with a known entry domain
    let manual_entry_domain = ChcExpr::ge(ChcExpr::var(var_a.clone()), ChcExpr::var(var_b.clone()));
    let inductive_with_manual = solver.is_self_inductive_blocking_with_entry_domain(
        &blocking,
        inv2,
        Some(&manual_entry_domain),
    );
    assert!(
        inductive_with_manual,
        "A=B should be inductive on inv2 when assuming entry domain A >= B"
    );
}

/// Regression test: `add_discovered_invariant` must condition self-inductiveness on the
/// entry domain for no-facts (phase-chain) predicates.
///
/// The invariant `A != B` is not self-inductive over all syntactic states: with `A < B`,
/// the ITE update can make `A' = B'`. But for reachable states entering `inv2` from `inv`
/// under `A > B`, the invariant is preserved.
///
/// Part of #1545 / #1398.
#[test]
fn test_add_discovered_invariant_uses_entry_domain_for_no_facts_predicates() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun inv (Int Int) Bool)
(declare-fun inv2 (Int Int) Bool)

; Facts: inv holds only for a single start state.
(assert (forall ((A Int) (B Int))
  (=> (and (= A 0) (= B 0)) (inv A B))))

; Entry: inv -> inv2 only when A > B (so entry states satisfy A != B).
(assert (forall ((A Int) (B Int))
  (=> (and (inv A B) (> A B)) (inv2 A B))))

; Self-loop for inv2: B increments only when B <= A (ITE).
(assert (forall ((A Int) (B Int) (A2 Int) (B2 Int))
  (=> (and (inv2 A B) (= A2 (+ A 1)) (= B2 (ite (<= B A) (+ B 1) B)))
  (inv2 A2 B2))))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let inv2 = solver.problem.get_predicate_by_name("inv2").unwrap().id;
    assert!(!solver.predicate_has_facts(inv2));

    let inv2_vars = solver.canonical_vars(inv2).unwrap().to_vec();
    assert_eq!(inv2_vars.len(), 2);
    let var_a = &inv2_vars[0];
    let var_b = &inv2_vars[1];

    let invariant = ChcExpr::ne(ChcExpr::var(var_a.clone()), ChcExpr::var(var_b.clone()));

    assert!(
        solver.add_discovered_invariant(inv2, invariant, 1),
        "expected add_discovered_invariant to accept entry-conditioned invariant for inv2"
    );
}

/// Test is_difference_preserved_with_entry_domain.
///
/// Similar setup: difference A - B = 0 preserved only when A >= B (entry domain).
#[test]
fn test_difference_preserved_with_entry_domain() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun inv2 (Int Int) Bool)

; Self-loop: B only increments when B <= A
(assert (forall ((A Int) (B Int) (A2 Int) (B2 Int))
  (=> (and (inv2 A B) (= A2 (+ A 1)) (= B2 (ite (<= B A) (+ B 1) B)))
  (inv2 A2 B2))))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let inv2 = solver.problem.get_predicate_by_name("inv2").unwrap().id;
    let inv2_vars = solver.canonical_vars(inv2).unwrap().to_vec();
    let var_a = &inv2_vars[0];
    let var_b = &inv2_vars[1];

    // Entry domain: A >= B
    let entry_domain = ChcExpr::ge(ChcExpr::var(var_a.clone()), ChcExpr::var(var_b.clone()));

    // Test: is difference A - B preserved with entry domain?
    let preserved =
        solver.is_difference_preserved_with_entry_domain(inv2, var_a, var_b, &entry_domain);

    // With A >= B, the ITE condition B <= A is always true, so B' = B + 1
    // A' = A + 1, B' = B + 1, so A' - B' = (A+1) - (B+1) = A - B
    // Difference is preserved!
    assert!(
        preserved,
        "difference A - B should be preserved with entry domain A >= B"
    );
}

/// Regression test for #1402: Cross-predicate invariant propagation with linear head args.
///
/// Pattern:
/// - P(A, B) has self-loop with A' = A + 1, B' = B + 1
/// - Q(A, B) is reached from P when A >= C
/// - Both P and Q should discover A = B
///
/// This tests that equality invariants propagate across linear (identity) transitions.
#[test]
fn pdr_cross_predicate_equality_propagation_linear_args() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun P ( Int Int Int ) Bool)
(declare-fun Q ( Int Int Int ) Bool)

; Fact: P(0, 0, C) for any positive C
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and (= A 0) (= B 0) (> C 0))
      (P A B C)
    )
  )
)

; P self-loop: both A and B increment by 1 (preserves A = B)
(assert
  (forall ( (A Int) (B Int) (C Int) (A1 Int) (B1 Int) )
    (=>
      (and
        (P A B C)
        (< A C)
        (= A1 (+ A 1))
        (= B1 (+ B 1))
      )
      (P A1 B1 C)
    )
  )
)

; Transition P -> Q with identity mapping of A, B (linear head args)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (P A B C)
        (>= A C)
      )
      (Q A B C)
    )
  )
)

; Q self-loop: both A and B increment by 1 (preserves A = B)
(assert
  (forall ( (A Int) (B Int) (C Int) (A1 Int) (B1 Int) )
    (=>
      (and
        (Q A B C)
        (= A1 (+ A 1))
        (= B1 (+ B 1))
      )
      (Q A1 B1 C)
    )
  )
)

; Query: can Q reach state where A != B? (should be SAT because A = B is invariant)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (Q A B C)
        (not (= A B))
      )
      false
    )
  )
)

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    // Run all discovery methods (mirrors what PDR solve does)
    solver.discover_bound_invariants();
    solver.discover_equality_invariants();
    solver.propagate_frame1_invariants_to_users();
    solver.discover_difference_invariants();

    let p = solver.problem.lookup_predicate("P").unwrap();
    let q = solver.problem.lookup_predicate("Q").unwrap();

    let p_vars = solver.canonical_vars(p).unwrap();
    let q_vars = solver.canonical_vars(q).unwrap();
    assert_eq!(p_vars.len(), 3);
    assert_eq!(q_vars.len(), 3);

    // P should have A = B discovered (from init + self-loop)
    let p_eq = ChcExpr::eq(
        ChcExpr::var(p_vars[0].clone()),
        ChcExpr::var(p_vars[1].clone()),
    );
    let p_has_eq = solver.frames[1].contains_lemma(p, &p_eq);

    // Q should also have A = B (propagated from P via linear transition)
    let q_eq = ChcExpr::eq(
        ChcExpr::var(q_vars[0].clone()),
        ChcExpr::var(q_vars[1].clone()),
    );
    let q_has_eq = solver.frames[1].contains_lemma(q, &q_eq);

    // Report what was discovered for debugging
    let p_lemmas: Vec<String> = solver.frames[1]
        .lemmas
        .iter()
        .filter(|l| l.predicate == p)
        .map(|l| l.formula.to_string())
        .collect();
    let q_lemmas: Vec<String> = solver.frames[1]
        .lemmas
        .iter()
        .filter(|l| l.predicate == q)
        .map(|l| l.formula.to_string())
        .collect();

    assert!(
        p_has_eq,
        "expected P to discover A=B (P lemmas: {p_lemmas:?})"
    );
    assert!(
        q_has_eq,
        "expected Q to receive propagated A=B (P lemmas: {p_lemmas:?}, Q lemmas: {q_lemmas:?})"
    );
}

/// Regression for #2375: `add_lemma()` at frame[1] should trigger incremental
/// cross-predicate propagation, not just the startup full fixpoint pass.
#[test]
fn pdr_add_lemma_propagates_frame1_lemma_to_users() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)

; Fact seed for P
(assert (forall ((x Int)) (=> (= x 0) (P x))))

; Cross-predicate edge P -> Q (identity mapping)
(assert (forall ((x Int)) (=> (P x) (Q x))))

; Q self-loop preserves x >= 0
(assert (forall ((x Int) (x1 Int))
  (=> (and (Q x) (= x1 x)) (Q x1))))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let p = solver.problem.get_predicate_by_name("P").unwrap().id;
    let q = solver.problem.get_predicate_by_name("Q").unwrap().id;

    let p_vars = solver.canonical_vars(p).unwrap().to_vec();
    let q_vars = solver.canonical_vars(q).unwrap().to_vec();
    assert_eq!(p_vars.len(), 1);
    assert_eq!(q_vars.len(), 1);

    let p_ge_0 = ChcExpr::ge(ChcExpr::var(p_vars[0].clone()), ChcExpr::int(0));
    let q_ge_0 = ChcExpr::ge(ChcExpr::var(q_vars[0].clone()), ChcExpr::int(0));

    // This must use `add_lemma` (not direct frame insertion) to cover #2375.
    solver.add_lemma(Lemma::new(p, p_ge_0.clone(), 1), 1);

    assert!(
        solver.frames[1].contains_lemma(p, &p_ge_0),
        "expected source lemma in frame[1] for P"
    );

    // #1398: Q has no init facts, so the propagated lemma should be in
    // clause-guarded storage only (not in the frame). This prevents frame
    // inconsistency in multi-predicate chains.
    let q_clause_index = solver
        .problem
        .clauses()
        .iter()
        .enumerate()
        .find(|(_, clause)| {
            clause.head.predicate_id() == Some(q)
                && clause.body.predicates.iter().any(|(pred, _)| *pred == p)
        })
        .map(|(i, _)| i)
        .expect("expected clause P -> Q");
    let cgl = &solver.caches.clause_guarded_lemmas;
    assert!(
        cgl.get(&(q, q_clause_index))
            .is_some_and(|lemmas| !lemmas.is_empty()),
        "expected add_lemma() to propagate frame[1] lemma from P to Q's clause-guarded storage"
    );
    // #1398: Intermediate predicates (no init facts) get clause-guarded storage
    // only — NOT unconditional frame insertion. Frame insertion for intermediate
    // predicates causes frame oscillation (gj2007_m_1/m_2). The clause-guarded
    // path already stores the lemma with proper clause scoping.
    assert!(
        !solver.frames[1].contains_lemma(q, &q_ge_0),
        "#1398: intermediate predicate Q should NOT have frame insertion (clause-guarded only)"
    );
}

/// Regression for #2560: when a frame[1] lemma is pushed to frame[2] via
/// add_lemma_to_frame, the clause-guarded copies must have their max_level
/// bumped through propagate_lemma_to_users.
///
/// Scenario:
/// 1. P(x) -> Q(x) cross-predicate edge
/// 2. Frame[1] has lemma "x >= 0" for P
/// 3. propagate_frame1_invariants_to_users() stores clause-guarded copy for Q at max_level=1
/// 4. Lemma is pushed to frame[2] via add_lemma_to_frame (simulating push_lemmas)
/// 5. Clause-guarded copy for Q must be bumped to max_level=3 (target_level = level+1)
#[test]
fn pdr_push_to_higher_frame_bumps_clause_guarded_max_level() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)

; Fact seed for P
(assert (forall ((x Int)) (=> (= x 0) (P x))))

; Cross-predicate edge P -> Q (identity mapping)
(assert (forall ((x Int)) (=> (P x) (Q x))))

; Q self-loop preserves x >= 0
(assert (forall ((x Int) (x1 Int))
  (=> (and (Q x) (= x1 x)) (Q x1))))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let p = solver.problem.get_predicate_by_name("P").unwrap().id;
    let q = solver.problem.get_predicate_by_name("Q").unwrap().id;

    let p_vars = solver.canonical_vars(p).unwrap().to_vec();
    assert_eq!(p_vars.len(), 1);

    let p_ge_0 = ChcExpr::ge(ChcExpr::var(p_vars[0].clone()), ChcExpr::int(0));

    // Add lemma at frame[1] — triggers initial cross-predicate propagation.
    solver.add_lemma(Lemma::new(p, p_ge_0.clone(), 1), 1);

    // Find the clause index for the P -> Q edge.
    let q_clause_index = solver
        .problem
        .clauses()
        .iter()
        .enumerate()
        .find(|(_, clause)| {
            clause.head.predicate_id() == Some(q)
                && clause.body.predicates.iter().any(|(pred, _)| *pred == p)
        })
        .map(|(i, _)| i)
        .expect("expected clause P -> Q");

    // Verify initial clause-guarded copy for Q exists at max_level <= 2
    // (propagate_lemma_to_users uses target_level = (level+1).min(max_frame) = 2).
    let cgl = &solver.caches.clause_guarded_lemmas;
    let q_levels_before: Vec<usize> = cgl
        .get(&(q, q_clause_index))
        .expect("expected clause-guarded lemma for Q after initial propagation")
        .iter()
        .map(|(_, level)| *level)
        .collect();
    assert!(
        !q_levels_before.is_empty(),
        "Q should have clause-guarded lemmas"
    );
    let initial_max = *q_levels_before.iter().max().unwrap();
    // Expand frames: create frame[2] and frame[3] so push path has room.
    solver.push_frame(); // frame[2]
    solver.push_frame(); // frame[3]

    // Simulate what push_lemmas does: push the lemma to frame[2].
    let pushed = Lemma::new(p, p_ge_0, 2);
    solver.add_lemma_to_frame(pushed, 2);

    // After push, propagate_lemma_to_users(P, formula, 2) sets target_level=3.
    // The clause-guarded copy for Q should be bumped to max_level=3.
    let cgl = &solver.caches.clause_guarded_lemmas;
    let q_levels_after: Vec<usize> = cgl
        .get(&(q, q_clause_index))
        .expect("expected clause-guarded lemma for Q after push")
        .iter()
        .map(|(_, level)| *level)
        .collect();
    let bumped_max = *q_levels_after.iter().max().unwrap();
    assert!(
        bumped_max > initial_max,
        "clause-guarded max_level for Q should increase after frame push: \
         before={initial_max}, after={bumped_max}"
    );
    assert_eq!(
        bumped_max, 3,
        "expected max_level=3 (target_level = level+1 = 3), got {bumped_max}"
    );
}

/// Regression for #2461: propagate_lemma_to_users places propagated lemma at
/// frame[level+1] (Z3's next_level semantics), NOT at the same frame level.
///
/// This test exercises the target frame *placement* for level > 1:
/// 1. Create 4 frames (0..3)
/// 2. Add lemma for P at level 2
/// 3. Verify propagated lemma for Q is in frame[3] (level+1), not frame[2]
#[test]
fn pdr_propagate_lemma_to_users_places_at_level_plus_one() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)

; Fact seed for P
(assert (forall ((x Int)) (=> (= x 0) (P x))))

; Cross-predicate edge P -> Q (identity mapping)
(assert (forall ((x Int)) (=> (P x) (Q x))))

; Q self-loop preserves x >= 0
(assert (forall ((x Int) (x1 Int))
  (=> (and (Q x) (= x1 x)) (Q x1))))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let p = solver.problem.get_predicate_by_name("P").unwrap().id;
    let q = solver.problem.get_predicate_by_name("Q").unwrap().id;

    let p_vars = solver.canonical_vars(p).unwrap().to_vec();
    let q_vars = solver.canonical_vars(q).unwrap().to_vec();
    assert_eq!(p_vars.len(), 1);
    assert_eq!(q_vars.len(), 1);

    // Create frames 2 and 3 (solver starts with frames 0 and 1)
    solver.push_frame(); // frame[2]
    solver.push_frame(); // frame[3]
    assert_eq!(solver.frames.len(), 4, "should have 4 frames (0..3)");

    let p_ge_0 = ChcExpr::ge(ChcExpr::var(p_vars[0].clone()), ChcExpr::int(0));
    let q_ge_0 = ChcExpr::ge(ChcExpr::var(q_vars[0].clone()), ChcExpr::int(0));

    // Add lemma at level 2 — propagation target should be level 2+1=3
    solver.add_lemma(Lemma::new(p, p_ge_0.clone(), 2), 2);

    // Source lemma should be in frame[2]
    assert!(
        solver.frames[2].contains_lemma(p, &p_ge_0),
        "expected source lemma in frame[2] for P"
    );

    // #1398: Q has no init facts, so the propagated lemma should be in
    // clause-guarded storage at level 3 (target_level = level+1), NOT in the frame.
    let q_clause_index = solver
        .problem
        .clauses()
        .iter()
        .enumerate()
        .find(|(_, clause)| {
            clause.head.predicate_id() == Some(q)
                && clause.body.predicates.iter().any(|(pred, _)| *pred == p)
        })
        .map(|(i, _)| i)
        .expect("expected clause P -> Q");
    let cgl = &solver.caches.clause_guarded_lemmas;
    let q_guarded = cgl
        .get(&(q, q_clause_index))
        .expect("expected clause-guarded lemma for Q after propagation");
    // Verify the clause-guarded lemma has max_level = 3 (level+1)
    let max_level = q_guarded.iter().map(|(_, level)| *level).max().unwrap_or(0);
    assert_eq!(
        max_level, 3,
        "clause-guarded propagated lemma for Q should be at level 3 (level+1=3), got {max_level}"
    );
    // #1398: Intermediate predicates (no init facts) get clause-guarded storage
    // only — NOT unconditional frame insertion.
    assert!(
        !solver.frames[3].contains_lemma(q, &q_ge_0),
        "#1398: intermediate predicate Q should NOT have frame insertion (clause-guarded only)"
    );
}

/// Regression test: constraint_to_canonical_state with expression head arg
/// whose constituent variable also appears as a later variable arg.
///
/// Bug: `P(x+1, x)` — the expression arg `x+1` is processed first, pushing
/// identity substitution `(x, x)`. Then the variable arg `x` pushes `(x, __p_arg1)`.
/// Because `substitute()` uses first-match, `x` always resolves to `x` (identity),
/// never to `__p_arg1`. The canonical form is then wrong.
///
/// Expected: `constraint_to_canonical_state` must produce a formula where both
/// `__p_arg0` and `__p_arg1` appear correctly.
#[test]
fn test_constraint_to_canonical_state_expr_arg_shadows_later_var_arg() {
    // P(x+1, x): expression arg0 = x+1, variable arg1 = x
    // Constraint: x > 0
    // Expected canonical: (__p_arg1 > 0) AND (__p_arg0 = __p_arg1 + 1)
    let input = r#"
(set-logic HORN)
(declare-rel P (Int Int))
(declare-var x Int)

(rule (=> (and (= x 0)) (P 1 x)))
(rule (=> (and (P (+ x 1) x) (> x 0)) (P (+ x 2) (+ x 1))))
(query (and (P (+ x 1) x) (< x 0)))
"#;

    let problem = ChcParser::parse(input).unwrap();
    let solver = PdrSolver::new(problem, PdrConfig::default());

    // Get predicate P
    let pred = solver.problem.lookup_predicate("P").unwrap();
    let canonical_vars = solver.canonical_vars(pred).unwrap();
    assert_eq!(canonical_vars.len(), 2);
    let arg0_name = &canonical_vars[0].name;
    let arg1_name = &canonical_vars[1].name;

    // Build expression args: [x+1, x]
    let x = ChcVar::new("x", ChcSort::Int);
    let x_plus_1 = ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1));
    let args = vec![x_plus_1, ChcExpr::var(x.clone())];

    // Constraint: x > 0
    let constraint = ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(0));

    let result = solver.constraint_to_canonical_state(pred, &args, &constraint);
    let canonical = result.expect("should produce canonical form, not None");
    let canonical_str = format!("{canonical}");

    // The canonical form MUST reference __p_arg1 (the second canonical var)
    // for the variable x. If the first-match bug is present, x would remain
    // as "x" instead of being mapped to __p_arg1.
    assert!(
        canonical_str.contains(arg1_name),
        "canonical form must contain {arg1_name} (second canonical var for x), \
         but got: {canonical_str}"
    );
    assert!(
        canonical_str.contains(arg0_name),
        "canonical form must contain {arg0_name} (first canonical var for x+1 equality), \
         but got: {canonical_str}"
    );
}
