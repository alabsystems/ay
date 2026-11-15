// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `(^ base 0)` is `(ite (= base 0) <0^0> 1)` with one private `0^0` constant
//! per base sort, folded to `1` for a nonzero numeral base (T5 P0 Q7, design
//! §2.9 "Power").
//!
//! libz3 5.1.0 keeps `0^0` as its uninterpreted `^0` (T5 P0 implementer-Y pin
//! script `ypins.py`, case `q7_text`, and `~/ay-bench/t5-p0fix/probe_q7.py`):
//! `(assert (= r (^ 0.0 0.0))) (assert (not (= r 1.0)))`, the same with
//! `(^ 0 0)` over Int or `(^ a 0.0)` under `a = 0`, and `(not (= (^ x 0)
//! 1.0))` are `sat`; `(^ 2.0 0.0)`, and `(^ a 0.0)` under `a != 0`, with
//! `r != 1` are `unsat`; `(^ 0.0 0.0)` twice is one value (`unsat` for their
//! disequality), and `(^ 0 0)` over Int and `(^ 0.0 0.0)` are independent
//! (`sat` with 5 and 7). Folding every `x^0` to `1` answered the `sat` rows
//! `unsat`; keeping the raw `^` for a possibly-zero base answered every row
//! but `(^ 2.0 0.0)` `unknown`, the `a != 0` row included.

use ay_core::{Sort, Symbol, TermData, TermId, TermStore};

use super::zero_power_of_zero;
use crate::elaborate::Context;
use crate::parser::parse;

fn elaborate(input: &str) -> Context {
    let commands = parse(input).expect("test input parses");
    let mut ctx = Context::new();
    for command in &commands {
        ctx.process_command(command).expect("test input elaborates");
    }
    ctx
}

/// Whether `term` holds a raw `^` application or the `0^0` constant named
/// `zero_power`, reporting them as `(raw, zero_power)`.
fn power_parts(terms: &TermStore, term: TermId, zero_power: &str) -> (bool, bool) {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), _) if name == "^" => (true, false),
        TermData::Var(name, _) => (false, name == zero_power),
        TermData::App(_, args) => args.iter().fold((false, false), |acc, &arg| {
            let (raw, zero) = power_parts(terms, arg, zero_power);
            (acc.0 || raw, acc.1 || zero)
        }),
        TermData::Not(inner) => power_parts(terms, *inner, zero_power),
        TermData::Ite(c, t, e) => [*c, *t, *e].iter().fold((false, false), |acc, &arg| {
            let (raw, zero) = power_parts(terms, arg, zero_power);
            (acc.0 || raw, acc.1 || zero)
        }),
        _ => (false, false),
    }
}

#[test]
fn zero_power_of_a_symbolic_base_is_guarded_by_the_zero_power_constant() {
    let ctx = elaborate("(declare-const x Real) (assert (= (^ x 0) 1.0))");
    assert_eq!(ctx.assertions.len(), 1);
    assert!(!ctx.terms.is_true(ctx.assertions[0]), "x may be 0");
    let (raw, zero) = power_parts(
        &ctx.terms,
        ctx.assertions[0],
        &zero_power_of_zero(&Sort::Real),
    );
    assert!(
        !raw,
        "no raw `^` survives: the executor answers unknown for one"
    );
    assert!(zero, "the zero-base case is the private 0^0 constant");
}

#[test]
fn zero_power_of_zero_is_the_zero_power_constant_of_its_sort() {
    for (input, sort) in [
        (
            "(declare-const r Real) (assert (= r (^ 0.0 0.0)))",
            Sort::Real,
        ),
        (
            "(declare-const r Real) (assert (= r (^ 0.0 0)))",
            Sort::Real,
        ),
        ("(declare-const r Int) (assert (= r (^ 0 0)))", Sort::Int),
    ] {
        let ctx = elaborate(input);
        let (raw, zero) = power_parts(&ctx.terms, ctx.assertions[0], &zero_power_of_zero(&sort));
        assert!(!raw && zero, "{input}");
    }
}

#[test]
fn zero_power_of_zero_is_one_value_per_sort() {
    // Every `0^0` of one sort is the same term, so `(^ 0.0 0.0)` twice and
    // `(^ a 0)` at `a = 0` agree with it (libz3 5.1.0: unsat).
    let mut ctx = elaborate(
        "(declare-const a Real) (declare-const n Int) \
         (assert (= (^ a 0) (^ 0.0 0.0))) (assert (= (^ n 0) (^ 0 0)))",
    );
    let real = ctx
        .terms
        .mk_var(zero_power_of_zero(&Sort::Real), Sort::Real);
    let int = ctx.terms.mk_var(zero_power_of_zero(&Sort::Int), Sort::Int);
    assert_ne!(
        real, int,
        "Int and Real 0^0 are independent, as z3's two ^0 are"
    );
    for &assertion in &ctx.assertions {
        assert!(!ctx.terms.is_true(assertion));
    }
    assert_eq!(
        zero_power_of_zero(&Sort::Real),
        "!ay.zero-power-of-zero.Real"
    );
    assert!(!zero_power_of_zero(&Sort::Int).starts_with("__ay_"));
}

#[test]
fn zero_power_of_a_nonzero_numeral_is_one() {
    for input in [
        "(assert (= (^ 2.0 0) 1.0))",
        "(assert (= (^ 2.0 0.0) 1.0))",
        "(assert (= (^ (- 3) 0) 1))",
        "(assert (= (^ 0.5 0) 1.0))",
    ] {
        let ctx = elaborate(input);
        assert!(ctx.terms.is_true(ctx.assertions[0]), "{input}");
    }
}

#[test]
fn the_zero_power_constant_cannot_be_declared_by_source_text() {
    let commands = parse("(declare-const !ay.zero-power-of-zero.Real Real)").expect("parses");
    let mut ctx = Context::new();
    let declared = commands
        .iter()
        .all(|command| ctx.process_command(command).is_ok());
    assert!(
        !declared,
        "source text cannot declare a name of the `!ay.` namespace"
    );
}
