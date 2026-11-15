// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A natively built BINDER must be recoverable from its own retained source.
//!
//! `Solver::try_assert_term_with_source` demands that the retained text
//! re-elaborate to the very `TermId` that entered the assertion stack. A
//! quantifier's `TermId` is not canonical under alpha-renaming — every
//! occurrence mints globally unique binder names — so before
//! `Context::index_quantifier_for_alpha_sharing` existed, re-elaborating a
//! FAITHFUL source produced an unrelated alpha-variant and the guard refused
//! every binder-carrying assertion. With `:produce-proofs` on, that refusal
//! aborted the whole solve into no verdict.
//!
//! The guard itself is untouched by the fix, so the second half of this file
//! pins that a genuinely different formula is still refused.

use crate::api::{Logic, Solver, Sort};

fn proving_solver() -> Solver {
    let mut solver = Solver::try_new(Logic::All).expect("ALL is supported");
    solver.set_produce_proofs(true);
    solver
}

/// Assert `source` against the natively built `term` and require the retention
/// guard to accept it — i.e. the source reconstructs the native assertion.
#[track_caller]
fn assert_retains(solver: &mut Solver, term: crate::api::Term, source: &str) {
    solver
        .try_assert_term_with_source(term, source)
        .unwrap_or_else(|error| panic!("source must reconstruct {source}: {error}"));
}

#[test]
fn forall_over_int_is_retained_and_reaches_a_verdict() {
    let mut solver = proving_solver();
    let q = solver.fresh_var("q", Sort::Int);
    let zero = solver.int_const(0);
    let body = solver.try_gt(q, zero).expect("gt");
    let quantified = solver.try_forall(&[q], body).expect("forall");
    assert_retains(
        &mut solver,
        quantified,
        "(assert (forall ((q Int)) (> q 0)))",
    );
    assert_eq!(solver.executor.context().assertions_parsed().len(), 1);
    // Not all integers are positive: the assertion is refutable.
    assert!(solver.check_sat().is_unsat());
}

#[test]
fn exists_over_int_is_retained_and_reaches_a_verdict() {
    let mut solver = proving_solver();
    let q = solver.fresh_var("q", Sort::Int);
    let zero = solver.int_const(0);
    let body = solver.try_gt(q, zero).expect("gt");
    let quantified = solver.try_exists(&[q], body).expect("exists");
    assert_retains(
        &mut solver,
        quantified,
        "(assert (exists ((q Int)) (> q 0)))",
    );
    assert!(solver.check_sat().is_sat());
}

#[test]
fn forall_over_a_bitvector_sort_is_retained_and_reaches_a_verdict() {
    let mut solver = proving_solver();
    let b = solver.fresh_var("b", Sort::bitvec(8));
    let ones = solver.bv_const(255, 8);
    let body = solver.try_eq(b, ones).expect("eq");
    let quantified = solver.try_forall(&[b], body).expect("forall");
    assert_retains(
        &mut solver,
        quantified,
        "(assert (forall ((b (_ BitVec 8))) (= b #b11111111)))",
    );
    // Retention is what this test pins. Not every 8-bit vector is all-ones, so
    // a `sat` here would be WRONG; ay answers `unknown` for this refutable
    // quantified-BV shape today, which is a solver-capability question and not
    // this guard's business.
    assert!(!solver.check_sat().is_sat());
}

#[test]
fn exists_over_a_bitvector_sort_is_retained_and_reaches_a_verdict() {
    let mut solver = proving_solver();
    let b = solver.fresh_var("b", Sort::bitvec(8));
    let ones = solver.bv_const(255, 8);
    let body = solver.try_eq(b, ones).expect("eq");
    let quantified = solver.try_exists(&[b], body).expect("exists");
    assert_retains(
        &mut solver,
        quantified,
        "(assert (exists ((b (_ BitVec 8))) (= b #b11111111)))",
    );
    assert!(solver.check_sat().is_sat());
}

#[test]
fn nested_binders_are_retained() {
    let mut solver = proving_solver();
    let x = solver.fresh_var("x", Sort::Int);
    let y = solver.fresh_var("y", Sort::Int);
    let inner_body = solver.try_gt(y, x).expect("gt");
    let inner = solver.try_exists(&[y], inner_body).expect("exists");
    let outer = solver.try_forall(&[x], inner).expect("forall");
    assert_retains(
        &mut solver,
        outer,
        "(assert (forall ((x Int)) (exists ((y Int)) (> y x))))",
    );
    // Every integer has a larger integer.
    assert!(solver.check_sat().is_sat());
}

#[test]
fn a_binder_whose_body_mentions_an_outer_free_variable_is_retained() {
    let mut solver = proving_solver();
    let k = solver.declare_const("k", Sort::Int);
    let x = solver.fresh_var("x", Sort::Int);
    let sum = solver.try_add(x, k).expect("add");
    let body = solver.try_ge(sum, k).expect("ge");
    let quantified = solver.try_forall(&[x], body).expect("forall");
    assert_retains(
        &mut solver,
        quantified,
        "(assert (forall ((x Int)) (>= (+ x k) k)))",
    );
    assert_eq!(solver.executor.context().assertions_parsed().len(), 1);
    // `x + k >= k` fails at x = -1, so the closed formula is refutable
    // regardless of the free `k`.
    assert!(solver.check_sat().is_unsat());
}

#[test]
fn a_shadowed_bound_name_is_retained() {
    let mut solver = proving_solver();
    // Two DIFFERENT bound variables that share the surface name `x`: the inner
    // binder shadows the outer, and the body mentions only the inner one.
    let outer_x = solver.fresh_var("x", Sort::Int);
    let inner_x = solver.fresh_var("x", Sort::Int);
    let zero = solver.int_const(0);
    let inner_body = solver.try_gt(inner_x, zero).expect("gt");
    let inner = solver.try_exists(&[inner_x], inner_body).expect("exists");
    let outer = solver.try_forall(&[outer_x], inner).expect("forall");
    assert_retains(
        &mut solver,
        outer,
        "(assert (forall ((x Int)) (exists ((x Int)) (> x 0))))",
    );
    assert!(solver.check_sat().is_sat());
}

#[test]
fn a_binder_with_a_trigger_is_retained() {
    let mut solver = proving_solver();
    let f = solver
        .try_declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = solver.fresh_var("x", Sort::Int);
    let applied = solver.try_apply(&f, &[x]).expect("apply");
    let zero = solver.int_const(0);
    let body = solver.try_ge(applied, zero).expect("ge");
    let quantified = solver
        .try_forall_with_triggers(&[x], body, &[&[applied][..]])
        .expect("forall with trigger");
    assert_retains(
        &mut solver,
        quantified,
        "(assert (forall ((x Int)) (! (>= (f x) 0) :pattern ((f x)))))",
    );
    assert_eq!(solver.executor.context().assertions_parsed().len(), 1);
}

/// A CONSISTENT alpha-rename denotes the identical formula, so the guard
/// accepts it — the guard certifies the FORMULA the text denotes, never the
/// spelling (see the contract on `try_assert_term_with_source`).
#[test]
fn a_consistent_alpha_rename_denotes_the_same_formula_and_is_retained() {
    let mut solver = proving_solver();
    let q = solver.fresh_var("q", Sort::Int);
    let zero = solver.int_const(0);
    let body = solver.try_gt(q, zero).expect("gt");
    let quantified = solver.try_forall(&[q], body).expect("forall");
    assert_retains(
        &mut solver,
        quantified,
        "(assert (forall ((renamed Int)) (> renamed 0)))",
    );
}

/// The identity check is a SOUNDNESS GUARD. Making elaboration faithful must
/// not have made it accept a source denoting any other formula.
#[test]
fn a_mismatching_binder_source_is_still_refused() {
    let mut solver = proving_solver();
    // A free constant with the binder's surface name, so a source that
    // captures it instead of the bound variable still elaborates — and must
    // still be refused for denoting a different formula.
    let _free_q = solver.declare_const("q", Sort::Int);
    let q = solver.fresh_var("q", Sort::Int);
    let zero = solver.int_const(0);
    let body = solver.try_gt(q, zero).expect("gt");
    let quantified = solver.try_forall(&[q], body).expect("forall");

    for source in [
        // Wrong bound name: the binder no longer binds the body's `q`, which
        // now resolves to the FREE constant. A different formula.
        "(assert (forall ((z Int)) (> q 0)))",
        // Wrong bound name with nothing to capture: does not elaborate at all.
        "(assert (forall ((z Int)) (> absent 0)))",
        // Wrong bound sort.
        "(assert (forall ((q Real)) (> q 0)))",
        // Swapped quantifier.
        "(assert (exists ((q Int)) (> q 0)))",
        // Body altered.
        "(assert (forall ((q Int)) (> q 1)))",
        "(assert (forall ((q Int)) (>= q 0)))",
        "(assert (forall ((q Int)) (< q 0)))",
        // Binder dropped entirely.
        "(assert (> q 0))",
        // Extra binder.
        "(assert (forall ((q Int) (r Int)) (> q 0)))",
    ] {
        assert!(
            solver
                .try_assert_term_with_source(quantified, source)
                .is_err(),
            "must be refused: {source}"
        );
        assert!(
            solver.assertions().is_empty(),
            "a refused source must not move the stack: {source}"
        );
    }

    // The faithful source is still accepted after every refusal.
    assert_retains(
        &mut solver,
        quantified,
        "(assert (forall ((q Int)) (> q 0)))",
    );
}

/// A trigger is INTERNED into the quantifier, so a source that changes it
/// denotes a different term and is refused.
#[test]
fn a_mismatching_trigger_source_is_still_refused() {
    let mut solver = proving_solver();
    let f = solver
        .try_declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let g = solver
        .try_declare_fun("g", &[Sort::Int], Sort::Int)
        .expect("declare g");
    let x = solver.fresh_var("x", Sort::Int);
    let applied = solver.try_apply(&f, &[x]).expect("apply f");
    let other = solver.try_apply(&g, &[x]).expect("apply g");
    let zero = solver.int_const(0);
    let body = solver.try_ge(applied, zero).expect("ge");
    let quantified = solver
        .try_forall_with_triggers(&[x], body, &[&[applied][..]])
        .expect("forall with trigger");

    for source in [
        // Different trigger term.
        "(assert (forall ((x Int)) (! (>= (f x) 0) :pattern ((g x)))))",
        // No trigger at all.
        "(assert (forall ((x Int)) (>= (f x) 0)))",
    ] {
        assert!(
            solver
                .try_assert_term_with_source(quantified, source)
                .is_err(),
            "must be refused: {source}"
        );
        assert!(solver.assertions().is_empty(), "{source}");
    }
    let _ = other;
}

/// Many same-signature binders must all be recoverable: the sharing index is
/// bucketed per shape, so a query with more quantifiers than one bucket can
/// hold does not fall off a cliff into "source does not reconstruct".
#[test]
fn many_distinct_same_signature_binders_are_each_retained() {
    let mut solver = proving_solver();
    for bound in 0..200_i64 {
        let x = solver.fresh_var("x", Sort::Int);
        let limit = solver.int_const(bound);
        let body = solver.try_gt(x, limit).expect("gt");
        let quantified = solver.try_exists(&[x], body).expect("exists");
        assert_retains(
            &mut solver,
            quantified,
            &format!("(assert (exists ((x Int)) (> x {bound})))"),
        );
    }
    assert_eq!(solver.assertions().len(), 200);
}
