// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Elaboration of Z3's special-relations indexed identifiers:
//! `(_ partial-order N)`, `(_ linear-order N)`, `(_ tree-order N)`,
//! `(_ piecewise-linear-order N)`. Each denotes a distinct uninterpreted binary
//! relation (one per kind, index, and argument sort) whose order axioms are
//! injected on first use. This is the encoding Verus's prelude emits for its
//! well-founded `height` ordering (`height_le = (_ partial-order 0)`).
//!
//! These tests pin the ELABORATION contract — that a use lowers to an
//! application of a fresh predicate, that the correct number of order axioms is
//! asserted, and that memoization by `(kind, sort, index)` shares one predicate
//! while distinct keys do not. End-to-end sat/unsat verdict parity (reflexive,
//! antisymmetric, transitive; totality only for `linear-order`; non-totality
//! stays sat) lives in the solver-level integration test
//! `crates/ay-dpll/tests/special_relations_verdicts.rs`.

use super::*;

/// Parse + elaborate a full script, returning the resulting context.
fn elaborate(input: &str) -> Context {
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd)
            .unwrap_or_else(|e| panic!("elaboration failed: {e:?}"));
    }
    ctx
}

/// The head symbol name of the single hard assertion's application, plus the
/// full assertion count. A special-relation use `(assert ((_ partial-order 0) a b))`
/// leaves N order axioms followed by the use itself.
fn assertion_head(ctx: &Context, idx: usize) -> Option<String> {
    match ctx.terms.get(ctx.assertions[idx]) {
        TermData::App(Symbol::Named(name), _) => Some(name.clone()),
        _ => None,
    }
}

#[test]
fn partial_order_lowers_to_fresh_predicate_plus_three_axioms() {
    // reflexive + antisymmetric + transitive = 3 axioms, then the use itself.
    let ctx = elaborate(
        "(declare-sort H 0)(declare-const a H)(declare-const b H)\
         (assert ((_ partial-order 0) a b))",
    );
    assert_eq!(ctx.assertions.len(), 4, "3 order axioms + the relation use");
    // The use lowers to an application of a fresh internal predicate, NOT a
    // literal `partial-order` symbol.
    let head = assertion_head(&ctx, 3).expect("use is an application");
    assert!(
        head.starts_with("__ay_order"),
        "use lowers to a fresh internal predicate, got {head}"
    );
    // All three axioms are universally quantified over the predicate.
    for i in 0..3 {
        assert!(
            matches!(ctx.terms.get(ctx.assertions[i]), TermData::Forall(..)),
            "axiom {i} is a forall"
        );
    }
}

#[test]
fn linear_order_adds_totality_axiom() {
    // partial(3) + totality(1) = 4 axioms.
    let ctx = elaborate(
        "(declare-sort H 0)(declare-const a H)(declare-const b H)\
         (assert ((_ linear-order 0) a b))",
    );
    assert_eq!(ctx.assertions.len(), 5, "4 order axioms + the use");
}

#[test]
fn tree_order_adds_left_linear_axiom() {
    // partial(3) + left-linear(1) = 4 axioms.
    let ctx = elaborate(
        "(declare-sort H 0)(declare-const a H)(declare-const b H)\
         (assert ((_ tree-order 0) a b))",
    );
    assert_eq!(ctx.assertions.len(), 5, "4 order axioms + the use");
}

#[test]
fn piecewise_linear_order_adds_both_directional_axioms() {
    // partial(3) + left-linear(1) + right-linear(1) = 5 axioms.
    let ctx = elaborate(
        "(declare-sort H 0)(declare-const a H)(declare-const b H)\
         (assert ((_ piecewise-linear-order 0) a b))",
    );
    assert_eq!(ctx.assertions.len(), 6, "5 order axioms + the use");
}

#[test]
fn same_kind_sort_index_reuses_one_predicate() {
    // Two uses of `(_ partial-order 0)` over the same sort share ONE predicate,
    // so axioms are injected exactly once: 3 axioms + 2 uses = 5 assertions, and
    // both uses name the same predicate.
    let ctx = elaborate(
        "(declare-sort H 0)(declare-const a H)(declare-const b H)(declare-const c H)\
         (assert ((_ partial-order 0) a b))\
         (assert ((_ partial-order 0) b c))",
    );
    assert_eq!(
        ctx.assertions.len(),
        5,
        "axioms injected once, then two uses"
    );
    let use1 = assertion_head(&ctx, 3).unwrap();
    let use2 = assertion_head(&ctx, 4).unwrap();
    assert_eq!(use1, use2, "same (kind, sort, index) shares one predicate");
}

#[test]
fn distinct_indices_get_distinct_predicates() {
    // `(_ partial-order 0)` and `(_ partial-order 1)` are DIFFERENT relations:
    // 3 axioms each + 2 uses = 8 assertions, with different predicate names.
    let ctx = elaborate(
        "(declare-sort H 0)(declare-const a H)(declare-const b H)\
         (assert ((_ partial-order 0) a b))\
         (assert ((_ partial-order 1) a b))",
    );
    assert_eq!(ctx.assertions.len(), 8, "two independent relations");
    let use0 = assertion_head(&ctx, 3).unwrap();
    let use1 = assertion_head(&ctx, 7).unwrap();
    assert_ne!(use0, use1, "distinct indices are distinct predicates");
}

#[test]
fn wrong_arity_is_rejected() {
    // A special relation is binary; three arguments must fail-closed.
    let commands = parse(
        "(declare-sort H 0)(declare-const a H)(declare-const b H)(declare-const c H)\
         (assert ((_ partial-order 0) a b c))",
    )
    .unwrap();
    let mut ctx = Context::new();
    let mut saw_err = false;
    for cmd in &commands {
        if ctx.process_command(cmd).is_err() {
            saw_err = true;
        }
    }
    assert!(
        saw_err,
        "a ternary special-relation application is rejected"
    );
}
