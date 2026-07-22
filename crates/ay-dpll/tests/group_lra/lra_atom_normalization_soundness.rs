// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(deprecated)]
#![allow(clippy::panic)]

//! Soundness regression tests for LRA atom normalization (#4919).
//!
//! The atom normalization feature registers compound atoms (multi-variable
//! expressions) in atom_index via slack variables at registration time.
//! These tests verify that atom normalization does not cause false UNSAT
//! on satisfiable formulas, particularly:
//!
//! - Compound atoms with implications (vacuously true guard)
//! - Negative integer models where normalization interacts with bound axioms
//! - Mixed single/compound atom formulas
//!
//! Root cause: W2 commits f093253b7 and 1b158fc80 introduced equality-to-bound
//! axiom generation and compound atom registration that can interact incorrectly
//! with multi-variable formulas, causing false UNSAT.

use ntest::timeout;

/// Minimal reproduction of #2671: proxy variable with implication and negative
/// integers. The implication guard is false at the satisfying assignment, making
/// the implication body vacuously true.
///
/// SAT at: i=-1, n=-1, proxy=0
#[test]
#[timeout(5_000)]
fn test_atom_norm_proxy_implication_negative_ints() {
    let smt = r#"
(set-logic QF_LIA)
(declare-const i Int)
(declare-const n Int)
(declare-const proxy Int)
(assert (<= i n))
(assert (= proxy (+ i 1)))
(assert (=> (>= i 0) (<= proxy n)))
(assert (not (<= (+ i 1) n)))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "Proxy + implication + negative ints must be SAT (model: i=-1, n=-1, proxy=0)"
    );
}

/// Compound atom with equality and bound: three variables with a sum constraint
/// where negative values satisfy the formula. Tests that atom normalization
/// doesn't over-constrain when slack variables interact with equality axioms.
#[test]
#[timeout(5_000)]
fn test_atom_norm_three_var_sum_negative_sat() {
    let smt = r#"
(set-logic QF_LIA)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert (= (+ a b) c))
(assert (<= a (- 1)))
(assert (<= b (- 1)))
(assert (>= c (- 3)))
(assert (<= c (- 1)))
(check-sat)
"#;
    // SAT at: a=-1, b=-1, c=-2 (or a=-2, b=-1, c=-3, etc.)
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "Three-var sum with negative bounds must be SAT"
    );
}

/// Mixed compound/simple atoms: compound inequality with single-variable bounds.
/// The compound atom `x + y <= 10` should coexist with simple bounds without
/// generating spurious UNSAT from atom normalization.
#[test]
#[timeout(5_000)]
fn test_atom_norm_compound_with_simple_bounds() {
    let smt = r#"
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (>= x 3))
(assert (<= x 7))
(assert (>= y 3))
(assert (<= y 7))
(assert (<= (+ x y) 10))
(assert (>= (+ x y) 6))
(check-sat)
"#;
    // SAT at: x=3, y=3 (sum=6, within [6,10])
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "Compound + simple bounds must be SAT (e.g. x=3, y=3)"
    );
}

/// Implication with compound atom in body: the guard may be false,
/// making the body vacuously true. Atom normalization must not
/// unconditionally assert the body's bound.
#[test]
#[timeout(5_000)]
fn test_atom_norm_implication_vacuous_guard() {
    let smt = r#"
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (>= x (- 5)))
(assert (<= x 5))
(assert (>= y (- 5)))
(assert (<= y 5))
; Guard is false when x < 0
(assert (=> (>= x 0) (<= (+ x y) 3)))
; Force x negative so guard is false
(assert (< x 0))
; Force sum large (violates body, but guard is false so OK)
(assert (> (+ x y) 3))
(check-sat)
"#;
    // SAT at: x=-1, y=5 (sum=4 > 3, but guard x>=0 is false)
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "Vacuous implication guard with compound body must be SAT (x=-1, y=5)"
    );
}

/// Disequality with compound expression: (not (= (+ a b) c)).
/// The negated equality becomes a disequality constraint. Atom normalization
/// must handle this correctly — the slack for (+ a b) - c should not generate
/// equality axioms that force a particular value.
#[test]
#[timeout(5_000)]
fn test_atom_norm_compound_disequality() {
    let smt = r#"
(set-logic QF_LIA)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert (not (= (+ a b) c)))
(assert (>= a 0))
(assert (<= a 2))
(assert (>= b 0))
(assert (<= b 2))
(assert (>= c 0))
(assert (<= c 2))
(check-sat)
"#;
    // SAT at: a=0, b=0, c=1 (or many others where a+b != c)
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "Compound disequality must be SAT");
}

/// UNSAT sanity check: atom normalization should not make UNSAT formulas SAT.
/// x + y = 10, x = 3, y = 3 → contradiction.
#[test]
#[timeout(5_000)]
fn test_atom_norm_genuine_unsat() {
    let smt = r#"
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ x y) 10))
(assert (= x 3))
(assert (= y 3))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "x+y=10, x=3, y=3 is genuinely UNSAT (3+3=6≠10)"
    );
}

// ============================================================================
// API path regression tests (#2671).
//
// The API `Solver` constructs terms via builder methods (eq, le, implies, not)
// which may create term IDs in a different order than the SMT-LIB parser.
// Different term construction orders affect atom_cache/atom_index population,
// which can cause the equality-to-bound axiom generator to produce unsound
// axioms. These tests exercise the same formulas via the API path.
// ============================================================================

use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

/// API path reproduction of #2671: proxy variable with implication and negative
/// integers. This is the exact formula from the #2671 test that fails via the
/// Solver API, but passes via the Executor+parser path.
///
/// SAT at: i=-1, n=-1, proxy=0
#[test]
#[timeout(5_000)]
fn test_atom_norm_api_path_proxy_implication_2671() {
    let mut solver = Solver::new(Logic::QfLia);
    let i = solver.declare_const("i", Sort::Int);
    let n = solver.declare_const("n", Sort::Int);
    let proxy = solver.declare_const("proxy", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);

    // i <= n
    let c1 = solver.le(i, n);
    solver.assert_term(c1);

    // proxy = i + 1
    let i_plus_1 = solver.add(i, one);
    let c2 = solver.eq(proxy, i_plus_1);
    solver.assert_term(c2);

    // (i >= 0) => (proxy <= n)
    let guard = solver.ge(i, zero);
    let body = solver.le(proxy, n);
    let c3 = solver.implies(guard, body);
    solver.assert_term(c3);

    // NOT(i + 1 <= n)
    let i_plus_1_again = solver.add(i, one);
    let le_term = solver.le(i_plus_1_again, n);
    let c4 = solver.not(le_term);
    solver.assert_term(c4);

    assert_eq!(
        *solver.check_sat().result(),
        SolveResult::Sat,
        "#2671: proxy + implication + negative ints via API must be SAT"
    );
}

/// API path: simple AUFLIA formula with arrays and arithmetic.
/// x=10, y=20, x+y=30, select(a,x)=y — clearly SAT.
#[test]
#[timeout(5_000)]
fn test_atom_norm_api_path_auflia_arrays_sat() {
    let mut solver = Solver::new(Logic::QfAuflia);
    let int_sort = Sort::Int;
    let array_sort = Sort::array(Sort::Int, Sort::Int);

    let a = solver.declare_const("a", array_sort);
    let x = solver.declare_const("x", int_sort.clone());
    let y = solver.declare_const("y", int_sort);

    // x = 10
    let ten = solver.int_const(10);
    let c1 = solver.eq(x, ten);
    solver.assert_term(c1);

    // y = 20
    let twenty = solver.int_const(20);
    let c2 = solver.eq(y, twenty);
    solver.assert_term(c2);

    // x + y = 30
    let sum = solver.add(x, y);
    let thirty = solver.int_const(30);
    let c3 = solver.eq(sum, thirty);
    solver.assert_term(c3);

    // select(a, x) = y
    let sel = solver.select(a, x);
    let c4 = solver.eq(sel, y);
    solver.assert_term(c4);

    assert_eq!(
        *solver.check_sat().result(),
        SolveResult::Sat,
        "#6193: AUFLIA with arrays and arithmetic via API must be SAT"
    );
}

/// API path: equality with compound expression and bound.
/// Tests that the equality-to-bound axiom doesn't cause false UNSAT
/// when variable values are negative.
#[test]
#[timeout(5_000)]
fn test_atom_norm_api_path_negative_equality_bound() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let zero = solver.int_const(0);
    let neg5 = solver.int_const(-5);

    // x >= -5
    let c1 = solver.ge(x, neg5);
    solver.assert_term(c1);

    // x <= 0
    let c2 = solver.le(x, zero);
    solver.assert_term(c2);

    // y = x + 1
    let one = solver.int_const(1);
    let x_plus_1 = solver.add(x, one);
    let c3 = solver.eq(y, x_plus_1);
    solver.assert_term(c3);

    // y >= 0
    let c4 = solver.ge(y, zero);
    solver.assert_term(c4);

    // SAT at: x=-1, y=0
    assert_eq!(
        *solver.check_sat().result(),
        SolveResult::Sat,
        "Negative equality with bound via API must be SAT (x=-1, y=0)"
    );
}
