// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #ufnia-symdiv-decomp-routing: the symbolic-div
//! decomposition equality `(= a (+ (* (p 3) q) r))` generated for
//! `(mod a (p 3))` was routed to EUF only by the combined UF+arith
//! adapters. It is not LIA-relevant (a UF leaf `(p 3)` sits inside the
//! product) and not a UF equality (the right side is a compound `+`),
//! so neither `involves_int_arithmetic` nor `is_uf_int_equality`
//! claimed it, the arithmetic side never learned the dividend
//! relation, and its relaxation model (`r = 0`, `b = 0`) was rejected
//! by the model gates on trivially satisfiable goals — but only when
//! the trail also decided the divisor-zero atom (`(not (= (p 3) 0))`
//! or an ite on it), which is why the bare `(= b (mod a (p 3)))` shape
//! passed. Equalites/distincts with a compound arithmetic side now
//! route to the arithmetic solver (UF leaves intern as opaque vars,
//! exactly as comparisons already route by sort alone); bare UF sides
//! keep the shared-equality channel. Measured against the SMT-LIB
//! 2025 file `QF_UFNIA/201903-Zohar-ic/int_check_bvslt_bvadd_rtl.smt2`
//! (z3 `sat`), whose `intmodtotal` ite-on-divisor-zero shape is the
//! second test below.

use crate::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn run(input: &str) -> Vec<String> {
    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("execute succeeds")
}

/// The divisor-zero disequality decided beside the mod: the minimal
/// trigger. Without `(not (= (p 3) 0))` the same goal already passed.
#[test]
#[timeout(30000)]
fn symdiv_decomp_reaches_arith_with_decided_divisor_zero_atom() {
    let outputs = run(r#"
        (set-logic QF_UFNIA)
        (declare-fun p (Int) Int)
        (declare-const a Int)
        (declare-const b Int)
        (assert (= (p 3) 8))
        (assert (not (= (p 3) 0)))
        (assert (= b (mod a (p 3))))
        (assert (= a 11))
        (check-sat)
        (get-value (b))
    "#);
    assert_eq!(outputs[0], "sat");
    assert_eq!(outputs[1], "((b 3))");
}

/// The `intmodtotal` shape from int_check_bvslt: divisor-zero guarded
/// by ite around the symbolic mod.
#[test]
#[timeout(30000)]
fn symdiv_decomp_reaches_arith_under_ite_guard() {
    let outputs = run(r#"
        (set-logic QF_UFNIA)
        (declare-fun p (Int) Int)
        (declare-const a Int)
        (declare-const b Int)
        (assert (= (p 3) 8))
        (assert (= b (ite (= (p 3) 0) a (mod a (p 3)))))
        (assert (= a 11))
        (check-sat)
        (get-value (b))
    "#);
    assert_eq!(outputs[0], "sat");
    assert_eq!(outputs[1], "((b 3))");
}

/// Guard: the decomposition relation must also refute — no `b` can be
/// both the remainder of 11 mod 8 and 4.
#[test]
#[timeout(30000)]
fn symdiv_decomp_contradiction_stays_unsat() {
    let outputs = run(r#"
        (set-logic QF_UFNIA)
        (declare-fun p (Int) Int)
        (declare-const a Int)
        (declare-const b Int)
        (assert (= (p 3) 8))
        (assert (not (= (p 3) 0)))
        (assert (= b (mod a (p 3))))
        (assert (= a 11))
        (assert (= b 4))
        (check-sat)
    "#);
    assert_eq!(outputs[0], "unsat");
}

/// Real mirror: a compound Real equality with a UF leaf inside a
/// product routes to the Real side in QF_UFNRA.
#[test]
#[timeout(30000)]
fn real_compound_equality_with_uf_leaf_routes_to_arith() {
    let outputs = run(r#"
        (set-logic QF_UFNRA)
        (declare-fun p (Real) Real)
        (declare-const a Real)
        (declare-const b Real)
        (assert (= (p 3.0) 8.0))
        (assert (not (= (p 3.0) 0.0)))
        (assert (= a (+ (* (p 3.0) b) 3.0)))
        (assert (= a 11.0))
        (check-sat)
        (get-value (b))
    "#);
    assert_eq!(outputs[0], "sat");
    assert_eq!(outputs[1], "((b 1.0))");
}
