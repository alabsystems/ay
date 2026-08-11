// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Elaboration of SMT-LIB / Z3 pseudo-boolean & cardinality operators:
//! `(_ at-most k)`, `(_ at-least k)`, `(_ pble k c..)`, `(_ pbge ..)`,
//! `(_ pbeq ..)`. Each desugars to the integer-arithmetic form
//! `(cmp (Σ cᵢ·(ite xᵢ 1 0)) k)`, decided by the LIA path. These tests pin the
//! desugared shape; end-to-end verdict parity vs z3 lives in the FFI and Python
//! suites.

use super::*;

/// Parse + elaborate a script that must yield exactly one hard assertion.
fn elaborate_one(input: &str) -> (Context, TermId) {
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd)
            .unwrap_or_else(|e| panic!("elaboration failed: {e:?}"));
    }
    assert_eq!(ctx.assertions.len(), 1, "expected a single assertion");
    let a = ctx.assertions[0];
    (ctx, a)
}

/// Number of `ite` indicator summands reachable from `t` (one per PB literal).
fn count_ites(terms: &TermStore, t: TermId) -> usize {
    match terms.get(t) {
        TermData::Ite(c, th, el) => {
            1 + count_ites(terms, *c) + count_ites(terms, *th) + count_ites(terms, *el)
        }
        TermData::App(_, args) => args.iter().map(|&a| count_ites(terms, a)).sum(),
        TermData::Not(inner) => count_ites(terms, *inner),
        _ => 0,
    }
}

/// Top-level operator name of an `App`, if any.
fn top_op(terms: &TermStore, t: TermId) -> Option<String> {
    match terms.get(t) {
        TermData::App(Symbol::Named(name), _) => Some(name.clone()),
        _ => None,
    }
}

#[test]
fn test_at_most_desugars_to_le_sum() {
    // ((_ at-most 1) a b c)  ===  (<= (Σ (ite · 1 0)) 1)
    let (ctx, a) = elaborate_one(
        "(declare-const a Bool)(declare-const b Bool)(declare-const c Bool)\
         (assert ((_ at-most 1) a b c))",
    );
    assert_eq!(top_op(&ctx.terms, a).as_deref(), Some("<="));
    assert_eq!(count_ites(&ctx.terms, a), 3, "one indicator per literal");
    assert_eq!(*ctx.terms.sort(a), Sort::Bool);
}

#[test]
fn test_at_least_desugars_to_comparison() {
    // ((_ at-least 2) a b c): mk_ge normalizes (>= s k) to (<= k s).
    let (ctx, a) = elaborate_one(
        "(declare-const a Bool)(declare-const b Bool)(declare-const c Bool)\
         (assert ((_ at-least 2) a b c))",
    );
    assert_eq!(top_op(&ctx.terms, a).as_deref(), Some("<="));
    assert_eq!(count_ites(&ctx.terms, a), 3);
    assert_eq!(*ctx.terms.sort(a), Sort::Bool);
}

#[test]
fn test_pble_pbge_pbeq_desugar() {
    // pble -> <= ; pbge -> <= (normalized) ; pbeq -> = , all over 2 indicators.
    let (ctx_le, le) = elaborate_one(
        "(declare-const a Bool)(declare-const b Bool)\
         (assert ((_ pble 3 2 3) a b))",
    );
    assert_eq!(top_op(&ctx_le.terms, le).as_deref(), Some("<="));
    assert_eq!(count_ites(&ctx_le.terms, le), 2);

    let (ctx_ge, ge) = elaborate_one(
        "(declare-const a Bool)(declare-const b Bool)\
         (assert ((_ pbge 3 2 3) a b))",
    );
    assert_eq!(top_op(&ctx_ge.terms, ge).as_deref(), Some("<="));
    assert_eq!(count_ites(&ctx_ge.terms, ge), 2);

    let (ctx_eq, eq) = elaborate_one(
        "(declare-const a Bool)(declare-const b Bool)\
         (assert ((_ pbeq 5 2 3) a b))",
    );
    assert_eq!(top_op(&ctx_eq.terms, eq).as_deref(), Some("="));
    assert_eq!(count_ites(&ctx_eq.terms, eq), 2);
}

#[test]
fn test_pb_signed_coefficients_preserve_the_z3_extension() {
    let (ctx, assertion) = elaborate_one(
        "(declare-const a Bool)(declare-const b Bool)\
         (assert ((_ pble -1 -2 3) a b))",
    );
    assert_eq!(top_op(&ctx.terms, assertion).as_deref(), Some("<="));
    assert_eq!(count_ites(&ctx.terms, assertion), 2);

    let commands = parse(
        "(declare-const a Bool)\
         (assert ((_ pble |1| 1) a))",
    )
    .expect("quoted symbol index parses");
    let mut ctx = Context::new();
    ctx.process_command(&commands[0]).expect("declaration");
    assert!(
        ctx.process_command(&commands[1]).is_err(),
        "quoted positive symbol must not become a PB numeral"
    );
}

#[test]
fn test_pb_over_negated_literals_elaborates() {
    // Negated literals are ordinary Bool terms; each still yields one indicator.
    let (ctx, a) = elaborate_one(
        "(declare-const a Bool)(declare-const b Bool)(declare-const c Bool)\
         (assert ((_ at-most 1) (not a) (not b) (not c)))",
    );
    assert_eq!(top_op(&ctx.terms, a).as_deref(), Some("<="));
    assert_eq!(count_ites(&ctx.terms, a), 3);
}

#[test]
fn test_at_most_rejects_non_bool_argument() {
    let commands = parse(
        "(declare-const x Int)(declare-const b Bool)\
         (assert ((_ at-most 1) x b))",
    )
    .unwrap();
    let mut ctx = Context::new();
    let mut err = None;
    for cmd in &commands {
        if let Err(e) = ctx.process_command(cmd) {
            err = Some(e);
        }
    }
    assert!(
        matches!(err, Some(ElaborateError::SortMismatch { .. })),
        "at-most over a non-Bool arg must be a sort mismatch, got {err:?}"
    );
}

#[test]
fn test_pble_rejects_wrong_coefficient_count() {
    // pble needs one threshold + one coefficient per argument; here 2 args but
    // only 1 coefficient after the threshold.
    let commands = parse(
        "(declare-const a Bool)(declare-const b Bool)\
         (assert ((_ pble 3 2) a b))",
    )
    .unwrap();
    let mut ctx = Context::new();
    let mut err = None;
    for cmd in &commands {
        if let Err(e) = ctx.process_command(cmd) {
            err = Some(e);
        }
    }
    assert!(
        matches!(err, Some(ElaborateError::InvalidConstant(_))),
        "pble with mismatched coefficient count must error, got {err:?}"
    );
}

#[test]
fn z3_500_pb_operators_reject_missing_arguments() {
    for input in [
        "(assert ((_ at-most 0)))",
        "(assert ((_ at-least 0)))",
        "(assert ((_ pble 0)))",
        "(assert ((_ pbge 0)))",
        "(assert ((_ pbeq 0)))",
    ] {
        let error = parse(input).expect_err("PB operator without a literal must be rejected");
        assert_eq!(
            error.message, "invalid function application, arguments missing",
            "{input}"
        );
    }
}

#[test]
fn z3_500_pb_plugin_source_owners_have_closed_semantics() {
    for predicate in [
        "((_ at-least 2) true true false)",
        "((_ at-most 1) true false false)",
        "((_ pbeq 0.5 0.25 0.25) true true)",
        "((_ pbge -0.5 -0.25) true)",
        "((_ pble 0.5 0.25) true)",
    ] {
        let (ctx, assertion) = elaborate_one(&format!("(assert {predicate})"));
        assert!(ctx.terms.is_true(assertion), "{predicate}");
    }
}

#[test]
fn z3_500_pb_plugin_is_available_only_in_its_registered_logics() {
    for logic in ["QF_FD", "ALL", "HORN"] {
        let script = format!("(set-logic {logic})(assert ((_ at-most 1) true))");
        let (ctx, assertion) = elaborate_one(&script);
        assert!(ctx.terms.is_true(assertion), "{logic}");
    }
    let (ctx, assertion) = elaborate_one("(assert ((_ at-most 1) true))");
    assert!(ctx.terms.is_true(assertion));

    for logic in ["QF_LIA", "QF_UF"] {
        let script = format!("(set-logic {logic})(assert ((_ at-most 1) true))");
        let commands = parse(&script).unwrap();
        let mut ctx = Context::new();
        ctx.process_command(&commands[0]).unwrap();
        assert!(matches!(
            ctx.process_command(&commands[1]),
            Err(ElaborateError::UndefinedSymbol(ref name)) if name == "at-most"
        ));
    }
}

#[test]
fn z3_500_cardinality_bound_is_a_nonnegative_machine_int() {
    for invalid in [
        "(assert ((_ at-most -1) true))",
        "(assert ((_ at-least 1.0) true))",
        "(assert ((_ at-most 2147483648) true))",
        "(assert ((_ at-least #x80000000) true))",
    ] {
        let commands = parse(invalid).unwrap();
        let mut ctx = Context::new();
        assert!(ctx.process_command(&commands[0]).is_err(), "{invalid}");
    }

    for valid in [
        "(assert ((_ at-most 2147483647) true))",
        "(assert ((_ at-least #x00000001) true))",
    ] {
        let (ctx, assertion) = elaborate_one(valid);
        assert!(ctx.terms.is_true(assertion), "{valid}");
    }
}

#[test]
fn z3_500_pb_rationals_and_unsigned_parameter_wrap_are_exact() {
    for predicate in [
        "((_ pble 0.5 0.25) true)",
        "((_ pbge -0.5 -0.25) true)",
        "((_ pbeq 0.5 0.25 0.25) true true)",
        // Z3 5.0.0's indexed parser stores an unsigned-fitting numeral in a
        // signed parameter: 2^32-1 therefore denotes -1 in this exact build.
        "((_ pble 0 4294967295) true)",
        // Values above u32 remain rational parameters and do not wrap.
        "(not ((_ pble 0 4294967296) true))",
        "((_ pble #x01 #b1) true)",
    ] {
        let (ctx, assertion) = elaborate_one(&format!("(assert {predicate})"));
        assert!(ctx.terms.is_true(assertion), "{predicate}");
    }
}
