// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Wrong-UNSAT regression: a divisor that an asserted `(= y 0)` substitutes
//! to 0 must leave `(div t 0)` and `(mod t 0)` unspecified.
//!
//! SMT-LIB gives `(div t 0)` and `(mod t 0)` no value; each is an
//! uninterpreted function of the dividend. The int-constant substitution that
//! the UFNIA and AUFLIA preprocessors share rewrote a substituted
//! `(div t 0)` to `0` and `(mod t 0)` to `t`, so every problem below that z3
//! answers `sat` was answered `unsat`. Through Verus this verified
//! `requires y == 0 { assert(y * (x / y) == x - x % y) }`.
//!
//! Each `sat` case has an `unsat` twin that differs only in a nonzero
//! divisor (and, where the twin needs it, a pinned dividend), so the
//! substitution is still exercised on the path where folding is sound.
//! `unknown` on a `sat` case is a completeness loss, reported but not wrong;
//! `unsat` is the regression.

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn solve(input: &str, shed_proof_cycle: bool) -> String {
    let commands = parse(input).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = Executor::new();
    exec.set_competition_mode(shed_proof_cycle);
    exec.set_timeout(Some(Duration::from_secs(30)));
    exec.set_memory_limit(Some(4 << 30));
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"));
    outputs
        .iter()
        .rev()
        .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .cloned()
        .unwrap_or_default()
}

fn assert_never_unsat(name: &str, input: &str) {
    for shed in [false, true] {
        let verdict = solve(input, shed);
        assert_ne!(
            verdict, "unsat",
            "{name} (shed_proof_cycle={shed}) is satisfiable: z3 answers sat \
             with the zero-divisor application chosen freely"
        );
    }
}

fn assert_unsat(name: &str, input: &str) {
    for shed in [false, true] {
        let verdict = solve(input, shed);
        assert_eq!(
            verdict, "unsat",
            "{name} (shed_proof_cycle={shed}) has a nonzero divisor and is \
             unsatisfiable (z3: unsat)"
        );
    }
}

const PRELUDE: &str = "(set-logic QF_UFNIA)(declare-const y Int)(declare-const x Int)\
                       (declare-fun g (Int) Int)";

fn ufnia(body: &str) -> String {
    format!("{PRELUDE}{body}(check-sat)")
}

#[test]
#[timeout(180_000)]
fn div_by_substituted_zero_is_not_zero() {
    assert_never_unsat(
        "div-eq-7",
        &ufnia("(assert (= y 0))(assert (= (div (g x) y) 7))"),
    );
    assert_unsat(
        "div-eq-7 twin",
        &ufnia("(assert (= y 3))(assert (= (g x) 5))(assert (= (div (g x) y) 7))"),
    );
}

#[test]
#[timeout(180_000)]
fn div_by_substituted_zero_may_be_nonzero() {
    assert_never_unsat(
        "div-ne-0",
        &ufnia("(assert (= y 0))(assert (not (= (div (g x) y) 0)))"),
    );
    assert_unsat(
        "div-ne-0 twin",
        &ufnia("(assert (= y 3))(assert (= (g x) 2))(assert (not (= (div (g x) y) 0)))"),
    );
}

#[test]
#[timeout(180_000)]
fn mod_by_substituted_zero_is_not_the_dividend() {
    assert_never_unsat(
        "mod-ne-dividend",
        &ufnia("(assert (= y 0))(assert (not (= (mod (g x) y) (g x))))"),
    );
    assert_unsat(
        "mod-ne-dividend twin",
        &ufnia("(assert (= y 3))(assert (= (g x) 5))(assert (not (= (mod (g x) y) 2)))"),
    );
}

#[test]
#[timeout(180_000)]
fn div_by_substituted_zero_differs_across_dividends() {
    assert_never_unsat(
        "div-distinct-dividends",
        &ufnia("(assert (= y 0))(assert (not (= (div (g x) y) (div (+ (g x) 1) y))))"),
    );
    assert_unsat(
        "div-distinct-dividends twin",
        &ufnia(
            "(assert (= y 3))(assert (= (g x) 3))\
             (assert (not (= (div (g x) y) (div (+ (g x) 1) y))))",
        ),
    );
}

/// The shape Verus emits for `requires y == 0 { assert(y * (x / y) == x - x % y) }`.
#[test]
#[timeout(180_000)]
fn euclidean_identity_under_zero_divisor_is_not_valid() {
    assert_never_unsat(
        "mul-div-mod",
        &ufnia("(assert (= y 0))(assert (not (= (* y (div (g x) y)) (- (g x) (mod (g x) y)))))"),
    );
    assert_unsat(
        "mul-div-mod twin",
        &ufnia("(assert (= y 3))(assert (not (= (* y (div (g x) y)) (- (g x) (mod (g x) y)))))"),
    );
}

#[test]
#[timeout(180_000)]
fn ite_divisor_substituted_to_zero_is_not_folded() {
    assert_never_unsat(
        "ite-divisor",
        "(set-logic QF_UFNIA)(declare-const y Int)(declare-const b Bool)(declare-const x Int)\
         (declare-fun g (Int) Int)(assert (= y 0))(assert (= (div (g x) (ite b y 0)) 7))\
         (check-sat)",
    );
    assert_unsat(
        "ite-divisor twin",
        "(set-logic QF_UFNIA)(declare-const y Int)(declare-const b Bool)(declare-const x Int)\
         (declare-fun g (Int) Int)(assert b)(assert (= y 3))(assert (= (g x) 5))\
         (assert (= (div (g x) (ite b y 0)) 7))(check-sat)",
    );
}

/// The query Verus sends for the proof above, with its prelude.
#[test]
#[timeout(300_000)]
fn verus_query_with_zero_divisor_requirement_is_not_verified() {
    assert_never_unsat(
        "sat_verus_zero_divisor_after_int_const_subst",
        include_str!(
            "../../../../benchmarks/smt/wrong-verdict/sat_verus_zero_divisor_after_int_const_subst.smt2"
        ),
    );
    assert_unsat(
        "unsat_verus_zero_divisor_after_int_const_subst_twin",
        include_str!(
            "../../../../benchmarks/smt/wrong-verdict/unsat_verus_zero_divisor_after_int_const_subst_twin.smt2"
        ),
    );
}

/// The same fold through the other declared logics that reach the
/// substitution: an array read or a UF application as the dividend.
#[test]
#[timeout(300_000)]
fn zero_divisor_after_substitution_in_other_logics() {
    let uf_mod = (
        "(declare-const x Int)(declare-fun f (Int) Int)",
        "(assert (not (= (mod (f x) y) (f x))))",
        "(assert (= (f x) 5))(assert (not (= (mod (f x) y) 2)))",
    );
    let array_div = (
        "(declare-const a (Array Int Int))",
        "(assert (= (div (select a 0) y) 7))",
        "(assert (= (select a 0) 5))(assert (= (div (select a 0) y) 7))",
    );
    for (logic, (decls, sat_body, twin_body)) in [
        ("AUFNIRA", uf_mod),
        ("AUFNIRA", array_div),
        ("QF_AUFNIA", uf_mod),
        ("QF_AUFNIA", array_div),
        ("QF_UFNIRA", uf_mod),
    ] {
        let sat_case = format!(
            "(set-logic {logic})(declare-const y Int){decls}(assert (= y 0)){sat_body}(check-sat)"
        );
        assert_never_unsat(&format!("{logic} {sat_body}"), &sat_case);
        let twin = format!(
            "(set-logic {logic})(declare-const y Int){decls}(assert (= y 3)){twin_body}(check-sat)"
        );
        assert_unsat(&format!("{logic} {twin_body} twin"), &twin);
    }
}
