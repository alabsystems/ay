// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #compound-side-bv2nat-channel: an equality between an uninterpreted
//! application and a compound arithmetic term reaches the arithmetic solver.
//! The compound-side rule (a628c3b2a, #ufnia-symdiv-decomp-routing) routes
//! these; its `bv2nat` exemption must not reach them. A rule that claims an
//! equality only when every side is arithmetic leaves all three `unknown`
//! (`Incomplete`). Ground truth: z3 5.1.0.
//!
//! The exemption's own pins are `bv_lia_int_blast_lane` (group_regression)
//! and `term_helpers::tests::compound_side_routes_unless_a_side_is_bv2nat`.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn run(smt: &str) -> Vec<String> {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"))
}

/// The symbolic-div decomposition `(= (f 0) (+ (* (p 3) q) r))` with a UF
/// dividend, beside the decided divisor-zero atom.
const UF_DIVIDEND: &str = "(set-logic QF_UFNIA)
(declare-fun p (Int) Int)
(declare-fun f (Int) Int)
(declare-const b Int)
(assert (= (p 3) 8))
(assert (not (= (p 3) 0)))
(assert (= b (mod (f 0) (p 3))))
(assert (= (f 0) 11))";

#[test]
#[timeout(30_000)]
fn a_uf_dividend_decomposition_reaches_arithmetic() {
    let out = run(&format!("{UF_DIVIDEND}\n(check-sat)\n(get-value (b))"));
    assert_eq!(out, ["sat", "((b 3))"], "11 mod 8 is 3");
}

#[test]
#[timeout(30_000)]
fn a_uf_dividend_decomposition_refutes_a_wrong_remainder() {
    let out = run(&format!("{UF_DIVIDEND}\n(assert (= b 4))\n(check-sat)"));
    assert_eq!(out, ["unsat"], "11 mod 8 is not 4");
}

/// `(f x)` equated to two compound terms: `x * x = x + 2` has no root above 2.
#[test]
#[timeout(30_000)]
fn a_uf_side_against_compound_sides_is_refuted() {
    let out = run("(set-logic QF_UFNIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(assert (= (f x) (* x x)))
(assert (= (f x) (+ x 2)))
(assert (> x 2))
(check-sat)");
    assert_eq!(out, ["unsat"]);
}
