// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for QF_LIA timeout on equality chains through addition (#2830).
//!
//! The solver must handle the pattern:
//!   b = d, a = b + 2, c = d + 2, NOT(a = c)
//!
//! This is trivially UNSAT: from b = d we get b + 2 = d + 2, so a = c.
//!
//! The root cause was that `VariableSubstitution` used TermId ordering to
//! prevent cycles, which was too restrictive: it rejected `a -> (+ b 2)` when
//! b had a higher TermId than a. The fix uses graph-based cycle detection.

#![allow(deprecated)]

use ntest::timeout;

/// Exact reproducer from #2830: b=d, a=b+2, c=d+2, NOT(a=c).
#[test]
#[timeout(5_000)]
fn test_equality_chain_addition_4var_2830() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (declare-const d Int)

        ; b = d
        (assert (= b d))

        ; a = b + 2
        (assert (= a (+ b 2)))

        ; c = d + 2
        (assert (= c (+ d 2)))

        ; NOT(a = c) — trivially UNSAT via: b=d → b+2=d+2 → a=c
        (assert (not (= a c)))

        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Same pattern via the Rust API (the path reported in #2830).
#[test]
#[timeout(5_000)]
fn test_equality_chain_addition_api_2830() {
    use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

    let mut solver = Solver::new(Logic::QfLia);
    let a = solver.declare_const("a", Sort::Int);
    let b = solver.declare_const("b", Sort::Int);
    let c = solver.declare_const("c", Sort::Int);
    let d = solver.declare_const("d", Sort::Int);

    let two = solver.int_const(2);

    // b = d
    let eq_bd = solver.eq(b, d);
    solver.assert_term(eq_bd);

    // a = b + 2
    let b_plus_2 = solver.add(b, two);
    let eq_a = solver.eq(a, b_plus_2);
    solver.assert_term(eq_a);

    // c = d + 2
    let two2 = solver.int_const(2);
    let d_plus_2 = solver.add(d, two2);
    let eq_c = solver.eq(c, d_plus_2);
    solver.assert_term(eq_c);

    // NOT(a = c)
    let eq_ac = solver.eq(a, c);
    let neg = solver.not(eq_ac);
    solver.assert_term(neg);

    let result = solver.check_sat();
    assert_eq!(
        result,
        SolveResult::unsat(),
        "b=d, a=b+2, c=d+2, NOT(a=c) should be UNSAT"
    );
}

/// Longer chain: a=b, c=a+1, d=b+1, e=c+d, NOT(e=2*b+2).
/// Tests that substitution handles multi-hop chains correctly.
#[test]
#[timeout(5_000)]
fn test_equality_chain_multihop() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (declare-const d Int)
        (declare-const e Int)

        (assert (= a b))
        (assert (= c (+ a 1)))
        (assert (= d (+ b 1)))
        (assert (= e (+ c d)))
        (assert (not (= e (+ (* 2 b) 2))))

        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}
