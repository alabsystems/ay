// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for QF_LIA timeout on doubling equality chain (#2832).
//!
//! The solver must handle equality chains involving self-addition:
//!   acc = i + i, i' = i + 1, acc' = acc + 2
//!   NOT(acc' = i' + i')
//!
//! This is trivially UNSAT: acc=2i, acc'=2i+2, i'=i+1, i'+i'=2i+2=acc'.
//! Z3 solves this instantly. AY was timing out.

#![allow(deprecated)]

use ay_dpll::api::{Logic, SolveResult, Solver, Sort};
use ntest::timeout;

/// 4-variable doubling chain: the core pattern from verification-consumer loop preservation VCs.
/// acc = i + i, i' = i + 1, acc' = acc + 2, NOT(acc' = i' + i')
#[test]
#[timeout(5_000)]
fn test_doubling_chain_unsat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const i Int)
        (declare-const acc Int)
        (declare-const i_prime Int)
        (declare-const acc_prime Int)
        (assert (= acc (+ i i)))
        (assert (= i_prime (+ i 1)))
        (assert (= acc_prime (+ acc 2)))
        (assert (not (= acc_prime (+ i_prime i_prime))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Same formula with 2*i instead of i+i — should also be UNSAT.
#[test]
#[timeout(5_000)]
fn test_doubling_chain_mul_unsat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const i Int)
        (declare-const acc Int)
        (declare-const i_prime Int)
        (declare-const acc_prime Int)
        (assert (= acc (* 2 i)))
        (assert (= i_prime (+ i 1)))
        (assert (= acc_prime (+ acc 2)))
        (assert (not (= acc_prime (* 2 i_prime))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Incremental context: same formula with push/pop.
#[test]
#[timeout(5_000)]
fn test_doubling_chain_incremental_unsat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const i Int)
        (declare-const acc Int)
        (declare-const i_prime Int)
        (declare-const acc_prime Int)
        (assert (= acc (+ i i)))
        (assert (= i_prime (+ i 1)))
        (assert (= acc_prime (+ acc 2)))
        (push 1)
        (assert (not (= acc_prime (+ i_prime i_prime))))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= acc_prime (+ i_prime i_prime)))
        (check-sat)
        (pop 1)
    "#;
    let output = crate::common::solve(smt);
    let lines: Vec<&str> = output
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .collect();
    assert_eq!(lines, vec!["unsat", "sat"]);
}

/// Same formula built via Solver API — must also return UNSAT within 3s.
#[test]
#[timeout(5_000)]
fn test_doubling_chain_solver_api_unsat() {
    let mut s = Solver::new(Logic::QfLia);
    s.set_timeout(Some(std::time::Duration::from_secs(3)));
    let i = s.declare_const("i", Sort::Int);
    let acc = s.declare_const("acc", Sort::Int);
    let i_prime = s.declare_const("i_prime", Sort::Int);
    let acc_prime = s.declare_const("acc_prime", Sort::Int);
    let one = s.int_const(1);
    let two = s.int_const(2);

    // acc = i + i
    let i_plus_i = s.add(i, i);
    let eq1 = s.eq(acc, i_plus_i);
    s.assert_term(eq1);
    // i_prime = i + 1
    let i_plus_one = s.add(i, one);
    let eq2 = s.eq(i_prime, i_plus_one);
    s.assert_term(eq2);
    // acc_prime = acc + 2
    let acc_plus_two = s.add(acc, two);
    let eq3 = s.eq(acc_prime, acc_plus_two);
    s.assert_term(eq3);
    // NOT(acc_prime = i_prime + i_prime)
    let ip_plus_ip = s.add(i_prime, i_prime);
    let eq4 = s.eq(acc_prime, ip_plus_ip);
    let neg = s.not(eq4);
    s.assert_term(neg);

    let result = s.check_sat();
    assert_eq!(
        result,
        SolveResult::unsat(),
        "Expected UNSAT but got {result:?}"
    );
}
