// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An UNQUOTED `-N` is the number in every scope; only `|-N|` is a symbol.
//!
//! z3 5.1.0 (and 4.16), cvc5 1.4.1 and pinned Carcara 1.1.0 scan an unquoted
//! `-1` as the negative numeral even where `|-1|` is declared, defined or
//! bound (MEASURED 2026-10-02: `(declare-const |-1| Int) (assert (= |-1| 5))
//! (assert (= -1 5))` is `unsat` to z3, and `(declare-const -1 Int)` is "invalid
//! constant declaration, symbol expected"). AY read the bare spelling as
//! whatever symbol the scope held, which flipped verdicts against z3.

use super::*;
use num_bigint::BigInt;
use num_rational::BigRational;

fn elaborate(input: &str) -> Context {
    let mut ctx = Context::new();
    for command in parse(input).unwrap_or_else(|e| panic!("{input}: {e}")) {
        ctx.process_command(&command)
            .unwrap_or_else(|e| panic!("{input}: {e}"));
    }
    ctx
}

fn elaboration_error(input: &str) -> bool {
    let Ok(commands) = parse(input) else {
        return true;
    };
    let mut ctx = Context::new();
    commands
        .iter()
        .any(|command| ctx.process_command(command).is_err())
}

#[test]
fn a_signed_decimal_keeps_its_sign_on_the_whole_value() {
    let ctx = elaborate(
        "(declare-const x Real)
         (assert (= x -2.5))
         (assert (= x -0.5))
         (assert (= x -007.25))",
    );
    let expected = [
        BigRational::new(BigInt::from(-5), BigInt::from(2)),
        BigRational::new(BigInt::from(-1), BigInt::from(2)),
        BigRational::new(BigInt::from(-29), BigInt::from(4)),
    ];
    for (assertion, value) in ctx.assertions.iter().zip(expected) {
        let TermData::App(_, args) = ctx.terms.get(*assertion) else {
            panic!("not an equality");
        };
        let constant = args
            .iter()
            .find_map(|&arg| match ctx.terms.get(arg) {
                TermData::Const(ay_core::Constant::Rational(r)) => Some(r.0.clone()),
                _ => None,
            })
            .expect("a rational operand");
        assert_eq!(constant, value);
    }
}

/// a01 / p1: the declared `|-2|` does not capture the bare `-2`.
#[test]
fn a_declared_signed_name_does_not_capture_the_bare_number() {
    let ctx = elaborate(
        "(declare-const |-2| Int)
         (assert (= |-2| 5))
         (assert (= -2 5))
         (assert (= -2 (- 2)))",
    );
    assert!(!ctx.terms.is_false(ctx.assertions[0]));
    assert!(ctx.terms.is_false(ctx.assertions[1]), "-2 is the number");
    assert!(ctx.terms.is_true(ctx.assertions[2]), "-2 is (- 2)");
}

/// p3 / p7 / a15: a binder named `|-1|` binds only its quoted occurrences.
#[test]
fn a_binder_named_like_the_number_does_not_capture_it() {
    let bound = elaborate(
        "(declare-const x Int)
         (assert (let ((|-1| (+ x 1))) (< x -1)))
         (define-fun f ((|-1| Int)) Int (+ |-1| -1))
         (assert (= (f 3) 2))
         (assert (< x (- 1)))",
    );
    assert_eq!(
        bound.assertions[0], bound.assertions[2],
        "the bare -1 under the let is (- 1), not the bound (+ x 1)"
    );
    assert!(bound.terms.is_true(bound.assertions[1]), "(f 3) is 3 + -1");
}

/// a24 / p5: a function named `|-1|` (or a macro `|-5|` with parameters)
/// leaves the bare `-1` a number instead of "requires arguments".
#[test]
fn a_function_named_like_the_number_leaves_the_bare_number_alone() {
    let ctx = elaborate(
        "(declare-fun |-1| (Int) Int)
         (define-fun |-5| ((a Int)) Int a)
         (declare-const x Int)
         (assert (= (|-1| x) -1))
         (assert (= x -5))",
    );
    assert_eq!(ctx.assertions.len(), 2);
}

/// z3: "symbol expected" wherever a symbol is declared or bound; an
/// undeclared quoted `|-1|` is an unknown constant.
#[test]
fn the_unquoted_spelling_cannot_be_declared_or_bound() {
    for input in [
        "(declare-const -1 Int)",
        "(declare-fun -1 (Int) Int)",
        "(define-fun -1 () Int 5)",
        "(declare-const x Int) (assert (let ((-1 5)) (= x -1)))",
        "(assert (forall ((-1 Int)) (= -1 -1)))",
        "(declare-const x Int) (assert (= x |-1|))",
    ] {
        assert!(elaboration_error(input), "{input}");
    }
    for input in [
        "(declare-const |-1| Int) (assert (= |-1| -1))",
        "(declare-const x Int) (assert (let ((|-1| 5)) (= x |-1|)))",
        "(assert (forall ((|-1| Int)) (> |-1| -1)))",
    ] {
        assert!(!elaboration_error(input), "{input}");
    }
}
