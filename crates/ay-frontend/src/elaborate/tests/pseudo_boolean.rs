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
