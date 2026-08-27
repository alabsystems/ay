// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared authenticated-source fixtures for proof-surgery tests.

use super::*;

pub(super) fn normalized_authored_or_fixture(
) -> (Executor, Vec<(TermId, FrontendTerm)>, TermId, TermId) {
    let mut executor = Executor::new();
    let commands = parse(
        "(declare-const p Bool)\n\
         (declare-const n Int)\n\
         (declare-const x Int)\n\
         (declare-const y Int)\n\
         (declare-const z Int)\n\
         (assert (=> p (=> (< 0 n) (= (+ x 0) (+ y 0)))))",
    )
    .expect("normalized authored-or fixture parses");
    executor
        .execute_all(&commands)
        .expect("normalized authored-or fixture executes");
    let canonical = executor.ctx.assertions[0];
    let parsed = executor.ctx.assertions_parsed()[0].clone();

    let TermData::App(Symbol::Named(source_name), source_disjuncts) =
        executor.ctx.terms.get(canonical).clone()
    else {
        panic!("canonical implication must be a packed or")
    };
    assert_eq!(source_name, "or");
    assert_eq!(source_disjuncts.len(), 3);
    let source_guard = source_disjuncts
        .iter()
        .copied()
        .find(|&term| {
            matches!(
                executor.ctx.terms.get(term),
                TermData::Not(atom)
                    if matches!(
                        executor.ctx.terms.get(*atom),
                        TermData::App(Symbol::Named(name), args)
                            if name == "<" && args.len() == 2
                    )
            )
        })
        .expect("canonical implication contains its negated strict guard");
    let guard = match executor.ctx.terms.get(source_guard) {
        TermData::Not(atom) => *atom,
        _ => unreachable!("source guard was matched above"),
    };
    let guard_args = match executor.ctx.terms.get(guard).clone() {
        TermData::App(_, args) => args,
        _ => unreachable!("source guard atom was matched above"),
    };
    // Mirror #7956 exactly: implication clausification dualizes the raw
    // `(not (< 0 n))` disjunct to the equivalent `(<= n 0)` literal.
    let normalized_guard = executor.ctx.terms.mk_app(
        Symbol::named("<="),
        [guard_args[1], guard_args[0]],
        Sort::Bool,
    );
    let raw_not_guard = executor.ctx.terms.mk_not_raw(guard);
    assert_ne!(
        normalized_guard, raw_not_guard,
        "fixture must exercise the checked arithmetic bridge"
    );
    let target_disjuncts: Vec<TermId> = source_disjuncts
        .iter()
        .map(|&term| {
            if term == source_guard {
                normalized_guard
            } else {
                term
            }
        })
        .collect();
    let target = executor
        .ctx
        .terms
        .mk_app(Symbol::named("or"), target_disjuncts, Sort::Bool);
    let z = executor
        .ctx
        .terms
        .lookup("z")
        .expect("declared z remains interned");
    (executor, vec![(canonical, parsed)], target, z)
}

pub(super) fn authored_array_ite_fixture() -> (Executor, Vec<(TermId, FrontendTerm)>, TermId, TermId)
{
    let mut executor = Executor::new();
    let commands = parse(
        "(declare-const a (Array Int Int))\n\
         (declare-const x Int)\n\
         (declare-const v Int)\n\
         (declare-const wrong Int)\n\
         (assert (= a (store ((as const (Array Int Int)) 0) 0 v)))\n\
         (assert (= x 0))",
    )
    .expect("authored array-ite fixture parses");
    executor
        .execute_all(&commands)
        .expect("authored array-ite fixture executes");
    let originals: Vec<(TermId, FrontendTerm)> = executor
        .ctx
        .assertions
        .iter()
        .copied()
        .zip(executor.ctx.assertions_parsed().iter().cloned())
        .collect();
    let array_equality = originals[0].0;
    let guard = originals[1].0;
    let a = executor.ctx.terms.lookup("a").expect("a is interned");
    let x = executor.ctx.terms.lookup("x").expect("x is interned");
    let v = executor.ctx.terms.lookup("v").expect("v is interned");
    let wrong = executor
        .ctx
        .terms
        .lookup("wrong")
        .expect("wrong is interned");
    let zero = executor.ctx.terms.mk_int(0.into());
    let read = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), [a, x], Sort::Int);
    let then_branch = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), [v, read], Sort::Bool);
    let else_branch = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), [zero, read], Sort::Bool);
    let ite = executor.ctx.terms.mk_ite(guard, then_branch, else_branch);
    let not_equality = executor.ctx.terms.mk_not_raw(array_equality);
    let target = executor
        .ctx
        .terms
        .mk_app(Symbol::named("or"), [not_equality, ite], Sort::Bool);
    (executor, originals, target, wrong)
}

pub(super) fn assert_native_ematching_body_preflight_rejects_excess_depth() {
    let mut terms = ay_core::TermStore::new();
    let mut body = terms.mk_bool(true);
    for _ in 0..=256 {
        body = terms.mk_app(Symbol::named("native_depth"), [body], Sort::Bool);
    }
    assert!(quant_canonical_term_work(&terms, body).is_none());
}

pub(super) fn assert_legacy_ite_scan_preflight_rejects_excess_arity() {
    let mut terms = ay_core::TermStore::new();
    let atom = terms.mk_bool(true);
    let body = terms.mk_app(
        Symbol::named("legacy_ite_wide"),
        vec![atom; 100_001],
        Sort::Bool,
    );
    assert!(quant_canonical_term_work(&terms, body).is_none());
}
