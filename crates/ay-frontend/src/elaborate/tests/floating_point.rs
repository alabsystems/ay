// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for SMT-LIB FloatingPoint-theory sort abbreviations.
//!
//! Background (false-SAT soundness bug): the SMT-LIB FloatingPoint theory
//! defines the sort abbreviations `Float16/Float32/Float64/Float128`. These
//! were not expanded by `elaborate_sort`, so `(declare-fun x () Float32)` gave
//! `x` the sort `Uninterpreted("Float32")` instead of `FloatingPoint(8, 24)`.
//! Because the eager FP-to-BV bit-blaster gates the structural-`=` branch on
//! `Sort::FloatingPoint(..)`, the mis-sorted variable never got bit-blasted,
//! and symbolic-variable conflicts such as `x = 1.0 AND x = 2.0` escaped as a
//! false-SAT. These tests pin the correct sort mapping.

use super::*;
use crate::command;
use ay_core::{Sort, Symbol};

#[test]
fn float_abbreviations_elaborate_to_floating_point() {
    let mut ctx = Context::new();
    assert_eq!(
        ctx.elaborate_sort(&command::Sort::Simple("Float16".to_string()))
            .unwrap(),
        Sort::FloatingPoint(5, 11)
    );
    assert_eq!(
        ctx.elaborate_sort(&command::Sort::Simple("Float32".to_string()))
            .unwrap(),
        Sort::FloatingPoint(8, 24)
    );
    assert_eq!(
        ctx.elaborate_sort(&command::Sort::Simple("Float64".to_string()))
            .unwrap(),
        Sort::FloatingPoint(11, 53)
    );
    assert_eq!(
        ctx.elaborate_sort(&command::Sort::Simple("Float128".to_string()))
            .unwrap(),
        Sort::FloatingPoint(15, 113)
    );
}

#[test]
fn invalid_or_unrepresentable_fp_formats_fail_before_bitblasting() {
    for input in [
        "(declare-const x (_ FloatingPoint 1 24))",
        "(declare-const x (_ FloatingPoint 8 1))",
        "(declare-const x (_ FloatingPoint 32 24))",
        "(declare-const x (_ FloatingPoint 8 1048577))",
        "(assert (= (_ +zero 32 24) (_ +zero 32 24)))",
    ] {
        let commands = parse(input).expect("syntax parses");
        let mut ctx = Context::new();
        let result = commands
            .iter()
            .try_for_each(|cmd| ctx.process_command(cmd).map(|_| ()));
        assert!(result.is_err(), "expected format rejection for {input}");
    }
}

#[test]
fn builtin_fp_simple_sorts_cannot_be_redeclared_or_redefined() {
    for name in ["RoundingMode", "Float16", "Float32", "Float64", "Float128"] {
        for input in [
            format!("(declare-sort {name} 0)"),
            format!("(define-sort {name} () Bool)"),
            format!("(declare-datatype {name} ((mk-{name})))"),
            format!(
                "(declare-datatypes ((Other{name} 0) ({name} 0)) \
                 (((mk-other-{name})) ((mk-group-{name}))))"
            ),
        ] {
            let commands = parse(&input).expect("sort command parses");
            let mut ctx = Context::new();
            let error = ctx
                .process_command(&commands[0])
                .expect_err("builtin FP sort names must remain reserved");
            assert!(
                matches!(error, ElaborateError::ReservedSymbol(ref actual) if actual == name),
                "expected ReservedSymbol({name}) for `{input}`, got {error:?}"
            );
        }
    }
}

#[test]
fn declared_float32_var_has_floating_point_sort() {
    // The same shape as the false-SAT repro: a Float32-declared variable
    // constrained by structural `=` to two distinct FP constants. The variable
    // must elaborate to FloatingPoint(8, 24) so the assertion routes through
    // the FP bit-blaster (rather than Uninterpreted, which silently dropped
    // the constraint and produced false-SAT).
    let input = r#"
            (set-logic QF_FP)
            (declare-fun x () Float32)
            (assert (= x ((_ to_fp 8 24) #x3f800000)))
            (assert (= x ((_ to_fp 8 24) #x40000000)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 2);

    // Locate the `x` variable inside the first assertion and confirm its sort.
    let mut found = false;
    for &assertion in &ctx.assertions {
        if let TermData::App(_, args) = ctx.terms.get(assertion) {
            for &arg in args {
                if let TermData::Var(name, _) = ctx.terms.get(arg) {
                    if name == "x" {
                        assert_eq!(
                            *ctx.terms.sort(arg),
                            Sort::FloatingPoint(8, 24),
                            "Float32 variable must elaborate to FloatingPoint(8, 24), \
                             not Uninterpreted (false-SAT root cause)"
                        );
                        found = true;
                    }
                }
            }
        }
    }
    assert!(found, "expected to find variable x in the assertions");
}

#[test]
fn chainable_fp_comparison_expands_to_conjunction() {
    // The SMT-LIB FloatingPoint theory declares fp.eq/lt/leq/gt/geq `:chainable`,
    // so `(fp.leq a b c)` means `(and (fp.leq a b) (fp.leq b c))`. Before the fix
    // AY rejected any 3+-arg application with an elaboration error (exit 1, no
    // verdict) on well-formed benchmarks z3 solves. This pins the n-ary unfold.
    for op in ["fp.eq", "fp.lt", "fp.leq", "fp.gt", "fp.geq"] {
        let input = format!(
            r#"
            (set-logic QF_FP)
            (declare-fun a () Float32)
            (declare-fun b () Float32)
            (declare-fun c () Float32)
            (assert ({op} a b c))
        "#
        );
        let commands = parse(&input).unwrap();
        let mut ctx = Context::new();
        for cmd in &commands {
            ctx.process_command(cmd).unwrap();
        }
        assert_eq!(ctx.assertions.len(), 1, "{op}: one assertion expected");
        let root = ctx.assertions[0];
        let TermData::App(Symbol::Named(and_name), and_args) = ctx.terms.get(root) else {
            panic!("{op}: chained application must elaborate to an `and`, got {root:?}");
        };
        assert_eq!(and_name, "and", "{op}: top node must be `and`");
        assert_eq!(
            and_args.len(),
            2,
            "{op}: two adjacent-pair conjuncts expected"
        );
        for &conj in and_args.clone().iter() {
            let TermData::App(Symbol::Named(inner), inner_args) = ctx.terms.get(conj) else {
                panic!("{op}: each conjunct must be a binary {op} application");
            };
            assert_eq!(inner, op, "{op}: conjunct operator mismatch");
            assert_eq!(inner_args.len(), 2, "{op}: each conjunct must be binary");
        }
    }
}

#[test]
fn single_arg_fp_comparison_is_rejected() {
    // One-argument fp.leq is an error in z3 too — must not silently succeed.
    let input = r#"
            (set-logic QF_FP)
            (declare-fun a () Float32)
            (assert (fp.leq a))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let mut saw_err = false;
    for cmd in &commands {
        if ctx.process_command(cmd).is_err() {
            saw_err = true;
        }
    }
    assert!(saw_err, "single-arg fp.leq must be rejected");
}
