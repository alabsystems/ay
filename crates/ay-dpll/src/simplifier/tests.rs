// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the quantifier preprocessing pipeline: one test per pass
//! behaviour, the capture/occurs guards that keep each pass an equivalence,
//! the model-converter entries, and the posture gate.

use super::*;
use ay_core::term::{Symbol, TermData};
use ay_core::Sort;
use num_bigint::BigInt;
use num_rational::BigRational;

fn int(t: &mut TermStore, n: i64) -> TermId {
    t.mk_int(BigInt::from(n))
}

fn app(t: &mut TermStore, f: &str, args: Vec<TermId>, sort: Sort) -> TermId {
    t.mk_app(Symbol::named(f), args, sort)
}

fn never() -> bool {
    false
}

fn user_fns(name: &str, _arity: usize) -> bool {
    matches!(name, "f" | "g" | "p" | "q")
}

fn run(t: &mut TermStore, window: &[TermId]) -> PipelineOutcome {
    run_quantifier_pipeline(
        t,
        window,
        Posture::Raw,
        &user_fns,
        &never,
        DEFAULT_WORK_LIMIT,
        false,
    )
}

fn rewrites(outcome: &PipelineOutcome, pass: &str) -> usize {
    outcome
        .reports
        .iter()
        .find(|r| r.name == pass)
        .map_or(0, |r| r.rewrites)
}

#[test]
fn der_resolves_a_disequality_inside_a_universal() {
    // (forall x. x != a or p(x))  ==>  p(a)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let a = t.mk_var("a", Sort::Int);
    let eq = t.mk_eq(x, a);
    let neq = t.mk_not(eq);
    let px = app(&mut t, "p", vec![x], Sort::Bool);
    let body = t.mk_or(vec![neq, px]);
    let fa = t.mk_forall(vec![("x".into(), Sort::Int)], body);
    let pa = app(&mut t, "p", vec![a], Sort::Bool);
    let out = run(&mut t, &[fa]);
    assert_eq!(out.window, vec![pa]);
    assert!(rewrites(&out, "der") >= 1);
    assert!(out.converter.is_empty(), "DER is an equivalence");
}

#[test]
fn der_resolves_an_equality_inside_an_existential() {
    // (forall y. exists x. x = y and p(x)) ==> forall y. p(y): DER runs before
    // the Skolemizer, which would hide the equality behind a Skolem function.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let y = t.mk_var("y", Sort::Int);
    let eq = t.mk_eq(x, y);
    let px = app(&mut t, "p", vec![x], Sort::Bool);
    let conj = t.mk_and(vec![eq, px]);
    let ex = t.mk_exists(vec![("x".into(), Sort::Int)], conj);
    let fa = t.mk_forall(vec![("y".into(), Sort::Int)], ex);
    let py = app(&mut t, "p", vec![y], Sort::Bool);
    let expected = t.mk_forall(vec![("y".into(), Sort::Int)], py);
    // `p` is not eliminable here: `forall y. p(y)` would otherwise be a macro.
    let out = run_quantifier_pipeline(
        &mut t,
        &[fa],
        Posture::Raw,
        &|_, _| false,
        &never,
        DEFAULT_WORK_LIMIT,
        false,
    );
    assert_eq!(out.window, vec![expected]);
}

#[test]
fn der_occurs_check_blocks_self_reference() {
    // forall x. x != f(x) or p(x)  stays a universal.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let fx = app(&mut t, "f", vec![x], Sort::Int);
    let eq = t.mk_eq(x, fx);
    let neq = t.mk_not(eq);
    let px = app(&mut t, "p", vec![x], Sort::Bool);
    let body = t.mk_or(vec![neq, px]);
    let fa = t.mk_forall(vec![("x".into(), Sort::Int)], body);
    let out = run(&mut t, &[fa]);
    assert!(out
        .window
        .iter()
        .all(|&w| matches!(t.get(w), TermData::Forall(..))));
    assert_eq!(rewrites(&out, "der"), 0);
}

#[test]
fn der_substitution_renames_a_capturing_inner_binder() {
    // forall x. x != g(y) or (forall y. q(x, y))
    // ==> forall y'. q(g(y), y')   -- the free `y` of the solution survives.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let y = t.mk_var("y", Sort::Int);
    let gy = app(&mut t, "g", vec![y], Sort::Int);
    let eq = t.mk_eq(x, gy);
    let neq = t.mk_not(eq);
    let qxy = app(&mut t, "q", vec![x, y], Sort::Bool);
    let inner = t.mk_forall(vec![("y".into(), Sort::Int)], qxy);
    let body = t.mk_or(vec![neq, inner]);
    let fa = t.mk_forall(vec![("x".into(), Sort::Int)], body);
    let out = run(&mut t, &[fa]);
    assert_eq!(out.window.len(), 1);
    let free = terms::free_names(&t, out.window[0]).expect("modelled term");
    assert!(free.contains("y"), "the outer y must stay free: {free:?}");
    assert!(!free.contains("x"));
}

#[test]
fn unused_bound_variables_are_dropped() {
    // forall x y. p(x) ==> forall x. p(x);  forall z. p(a) ==> p(a)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let a = t.mk_var("a", Sort::Int);
    let px = app(&mut t, "p", vec![x], Sort::Bool);
    let pa = app(&mut t, "p", vec![a], Sort::Bool);
    let fa1 = t.mk_forall(vec![("x".into(), Sort::Int), ("y".into(), Sort::Int)], px);
    let fa2 = t.mk_forall(vec![("z".into(), Sort::Int)], pa);
    let expected1 = t.mk_forall(vec![("x".into(), Sort::Int)], px);
    let out = run_quantifier_pipeline(
        &mut t,
        &[fa1, fa2],
        Posture::Raw,
        &|_, _| false,
        &never,
        DEFAULT_WORK_LIMIT,
        false,
    );
    assert!(out.window.contains(&expected1), "{:?}", out.window);
    assert!(out.window.contains(&pa), "{:?}", out.window);
}

#[test]
fn qe_lite_solves_a_unit_coefficient_integer_literal() {
    // NUM917=1 shape: (not (forall u v. exists w. u - w = v))  ==> false
    let mut t = TermStore::new();
    let u = t.mk_var("u", Sort::Int);
    let v = t.mk_var("v", Sort::Int);
    let w = t.mk_var("w", Sort::Int);
    let diff = t.mk_sub(vec![u, w]);
    let eq = t.mk_eq(diff, v);
    let ex = t.mk_exists(vec![("w".into(), Sort::Int)], eq);
    let fa = t.mk_forall(vec![("u".into(), Sort::Int), ("v".into(), Sort::Int)], ex);
    let goal = t.mk_not(fa);
    let out = run(&mut t, &[goal]);
    assert!(out.refuted, "window: {:?}", out.window);
    assert!(rewrites(&out, "qe-lite") >= 1);
}

#[test]
fn qe_lite_substitutes_the_solution_into_the_rest_of_the_clause() {
    // forall w. not(a - w = b) or p(w)  ==>  p(a - b)
    let mut t = TermStore::new();
    let a = t.mk_var("a", Sort::Int);
    let b = t.mk_var("b", Sort::Int);
    let w = t.mk_var("w", Sort::Int);
    let diff = t.mk_sub(vec![a, w]);
    let eq = t.mk_eq(diff, b);
    let neq = t.mk_not(eq);
    let pw = app(&mut t, "p", vec![w], Sort::Bool);
    let body = t.mk_or(vec![neq, pw]);
    let fa = t.mk_forall(vec![("w".into(), Sort::Int)], body);
    let out = run(&mut t, &[fa]);
    assert_eq!(out.window.len(), 1);
    assert!(!crate::ematching::contains_quantifier(&t, out.window[0]));
    let free = terms::free_names(&t, out.window[0]).expect("modelled term");
    assert!(free.contains("a") && free.contains("b") && !free.contains("w"));
}

#[test]
fn qe_lite_refuses_a_non_unit_integer_coefficient() {
    // forall w. not(2*w = b) or p(w): w = b/2 is not an integer term.
    let mut t = TermStore::new();
    let b = t.mk_var("b", Sort::Int);
    let w = t.mk_var("w", Sort::Int);
    let two = int(&mut t, 2);
    let tw = t.mk_mul(vec![two, w]);
    let eq = t.mk_eq(tw, b);
    let neq = t.mk_not(eq);
    let pw = app(&mut t, "p", vec![w], Sort::Bool);
    let body = t.mk_or(vec![neq, pw]);
    let fa = t.mk_forall(vec![("w".into(), Sort::Int)], body);
    let out = run(&mut t, &[fa]);
    assert!(matches!(t.get(out.window[0]), TermData::Forall(..)));
    assert_eq!(rewrites(&out, "qe-lite"), 0);
}

#[test]
fn qe_lite_solves_a_real_literal_with_any_nonzero_coefficient() {
    // forall w:Real. not(2*w = b) or p(w)  ==>  p(b/2)
    let mut t = TermStore::new();
    let b = t.mk_var("b", Sort::Real);
    let w = t.mk_var("w", Sort::Real);
    let two = t.mk_rational(BigRational::from_integer(BigInt::from(2)));
    let tw = t.mk_mul(vec![two, w]);
    let eq = t.mk_eq(tw, b);
    let neq = t.mk_not(eq);
    let pw = app(&mut t, "p", vec![w], Sort::Bool);
    let body = t.mk_or(vec![neq, pw]);
    let fa = t.mk_forall(vec![("w".into(), Sort::Real)], body);
    let out = run(&mut t, &[fa]);
    assert!(!crate::ematching::contains_quantifier(&t, out.window[0]));
}

#[test]
fn skolemization_records_its_fresh_symbols() {
    // (not (forall x. p(x)))  ==>  (not p(sk)), converter: Fresh(sk)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let px = app(&mut t, "p", vec![x], Sort::Bool);
    let fa = t.mk_forall(vec![("x".into(), Sort::Int)], px);
    let goal = t.mk_not(fa);
    let out = run(&mut t, &[goal]);
    assert_eq!(out.window.len(), 1);
    assert!(!crate::ematching::contains_quantifier(&t, out.window[0]));
    let fresh: Vec<&ConverterEntry> = out
        .converter
        .entries()
        .iter()
        .filter(|e| matches!(e, ConverterEntry::Fresh { .. }))
        .collect();
    assert_eq!(fresh.len(), 1, "{:?}", out.converter);
}

#[test]
fn skolemized_goal_conflict_is_found_by_propagation() {
    // AUFNIRA nasa shape: (not (forall a b. (a = 0 and b = 0) => ((a = 3) => r)))
    // Skolemizing gives a = 0, b = 0, a = 3, not r: false.
    let mut t = TermStore::new();
    let a = t.mk_var("a", Sort::Int);
    let b = t.mk_var("b", Sort::Int);
    let r = t.mk_var("r", Sort::Bool);
    let zero = int(&mut t, 0);
    let three = int(&mut t, 3);
    let a0 = t.mk_eq(a, zero);
    let b0 = t.mk_eq(b, zero);
    let a3 = t.mk_eq(a, three);
    let premise = t.mk_and(vec![a0, b0]);
    let inner = t.mk_implies(a3, r);
    let imp = t.mk_implies(premise, inner);
    let fa = t.mk_forall(vec![("a".into(), Sort::Int), ("b".into(), Sort::Int)], imp);
    let goal = t.mk_not(fa);
    let out = run(&mut t, &[goal]);
    assert!(out.refuted, "window: {:?}", out.window);
}

#[test]
fn a_satisfiable_instance_is_not_refuted() {
    // forall x. x != a or p(x);  not p(b)   (sat: a != b)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let a = t.mk_var("a", Sort::Int);
    let b = t.mk_var("b", Sort::Int);
    let eq = t.mk_eq(x, a);
    let neq = t.mk_not(eq);
    let px = app(&mut t, "p", vec![x], Sort::Bool);
    let body = t.mk_or(vec![neq, px]);
    let fa = t.mk_forall(vec![("x".into(), Sort::Int)], body);
    let pb = app(&mut t, "p", vec![b], Sort::Bool);
    let npb = t.mk_not(pb);
    let out = run(&mut t, &[fa, npb]);
    assert!(!out.refuted);
    // ... while the same axiom refutes `not p(a)`.
    let pa = app(&mut t, "p", vec![a], Sort::Bool);
    let npa = t.mk_not(pa);
    let out = run(&mut t, &[fa, npa]);
    assert!(out.refuted);
}

#[test]
fn macro_finder_eliminates_a_definition_and_records_it() {
    // forall x. f(x) = x + 1;  f(c) <= c   ==> false, converter: f := x + 1
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let c = t.mk_var("c", Sort::Int);
    let one = int(&mut t, 1);
    let fx = app(&mut t, "f", vec![x], Sort::Int);
    let xp1 = t.mk_add(vec![x, one]);
    let def_eq = t.mk_eq(fx, xp1);
    let def = t.mk_forall(vec![("x".into(), Sort::Int)], def_eq);
    let fc = app(&mut t, "f", vec![c], Sort::Int);
    let use_ = t.mk_le(fc, c);
    let out = run(&mut t, &[def, use_]);
    assert!(rewrites(&out, "macro-finder") >= 1, "{:?}", out.reports);
    let (params, body) = out.converter.definition("f").expect("f was eliminated");
    assert_eq!(params.len(), 1);
    assert_eq!(body, xp1);
    assert!(out
        .window
        .iter()
        .all(|&w| !terms::mentions_head(&t, w, "f")));
}

#[test]
fn macro_finder_refuses_an_interpreted_or_recursive_head() {
    // forall x. f(x) = f(x) + 1 is not a macro (head occurs in the body);
    // forall x. h(x) = x is not one either (the oracle does not own `h`).
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let one = int(&mut t, 1);
    let fx = app(&mut t, "f", vec![x], Sort::Int);
    let fx1 = t.mk_add(vec![fx, one]);
    let rec = t.mk_eq(fx, fx1);
    let rec_def = t.mk_forall(vec![("x".into(), Sort::Int)], rec);
    let hx = app(&mut t, "h", vec![x], Sort::Int);
    let heq = t.mk_eq(hx, x);
    let h_def = t.mk_forall(vec![("x".into(), Sort::Int)], heq);
    let out = run(&mut t, &[rec_def, h_def]);
    assert!(out.converter.definition("f").is_none());
    assert!(out.converter.definition("h").is_none());
}

#[test]
fn macro_finder_refuses_a_body_whose_free_symbol_a_binder_would_capture() {
    // forall x. f(x) = x + k   and   forall k. p(f(k)): expanding f under the
    // binder named k would capture the free constant k.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let k = t.mk_var("k", Sort::Int);
    let fx = app(&mut t, "f", vec![x], Sort::Int);
    let xk = t.mk_add(vec![x, k]);
    let def_eq = t.mk_eq(fx, xk);
    let def = t.mk_forall(vec![("x".into(), Sort::Int)], def_eq);
    let fk = app(&mut t, "f", vec![k], Sort::Int);
    let pfk = app(&mut t, "p", vec![fk], Sort::Bool);
    let other = t.mk_forall(vec![("k".into(), Sort::Int)], pfk);
    let out = run(&mut t, &[def, other]);
    assert!(out.converter.definition("f").is_none());
}

#[test]
fn later_macros_are_expanded_inside_earlier_converter_bodies() {
    // forall x. f(x) = g(x) + 1;  forall y. g(y) = 2*y;  f(c) = 5
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let y = t.mk_var("y", Sort::Int);
    let c = t.mk_var("c", Sort::Int);
    let one = int(&mut t, 1);
    let two = int(&mut t, 2);
    let five = int(&mut t, 5);
    let fx = app(&mut t, "f", vec![x], Sort::Int);
    let gx = app(&mut t, "g", vec![x], Sort::Int);
    let gx1 = t.mk_add(vec![gx, one]);
    let f_eq = t.mk_eq(fx, gx1);
    let f_def = t.mk_forall(vec![("x".into(), Sort::Int)], f_eq);
    let gy = app(&mut t, "g", vec![y], Sort::Int);
    let ty = t.mk_mul(vec![two, y]);
    let g_eq = t.mk_eq(gy, ty);
    let g_def = t.mk_forall(vec![("y".into(), Sort::Int)], g_eq);
    let fc = app(&mut t, "f", vec![c], Sort::Int);
    let fc5 = t.mk_eq(fc, five);
    let out = run(&mut t, &[f_def, g_def, fc5]);
    assert!(out.converter.definition("f").is_some());
    assert!(out.converter.definition("g").is_some());
    assert!(out.converter.bodies_are_closed(&t), "{:?}", out.converter);
}

#[test]
fn the_proof_carrying_posture_skips_every_unjustified_pass() {
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let a = t.mk_var("a", Sort::Int);
    let eq = t.mk_eq(x, a);
    let neq = t.mk_not(eq);
    let px = app(&mut t, "p", vec![x], Sort::Bool);
    let body = t.mk_or(vec![neq, px]);
    let fa = t.mk_forall(vec![("x".into(), Sort::Int)], body);
    let out = run_quantifier_pipeline(
        &mut t,
        &[fa],
        Posture::ProofCarrying,
        &user_fns,
        &never,
        DEFAULT_WORK_LIMIT,
        false,
    );
    assert!(!out.changed);
    assert_eq!(out.window, vec![fa]);
    assert!(out
        .reports
        .iter()
        .all(|r| r.skipped_unjustified && r.rewrites == 0));
}

#[test]
fn an_exhausted_budget_leaves_the_window_sound() {
    // With no budget at all nothing may change.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let a = t.mk_var("a", Sort::Int);
    let eq = t.mk_eq(x, a);
    let neq = t.mk_not(eq);
    let px = app(&mut t, "p", vec![x], Sort::Bool);
    let body = t.mk_or(vec![neq, px]);
    let fa = t.mk_forall(vec![("x".into(), Sort::Int)], body);
    let out = run_quantifier_pipeline(&mut t, &[fa], Posture::Raw, &user_fns, &never, 0, false);
    assert!(out.budget_exhausted);
    assert_eq!(out.window, vec![fa]);
}

#[test]
fn macro_finder_refuses_a_quantified_body() {
    // forall x. p(x) = (forall y. q(x, y)) stays: expanding it would nest a
    // binder at every use of p.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let y = t.mk_var("y", Sort::Int);
    let c = t.mk_var("c", Sort::Int);
    let px = app(&mut t, "p", vec![x], Sort::Bool);
    let qxy = app(&mut t, "q", vec![x, y], Sort::Bool);
    let inner = t.mk_forall(vec![("y".into(), Sort::Int)], qxy);
    let def_eq = t.mk_eq(px, inner);
    let def = t.mk_forall(vec![("x".into(), Sort::Int)], def_eq);
    let pc = app(&mut t, "p", vec![c], Sort::Bool);
    let out = run(&mut t, &[def, pc]);
    assert!(
        out.converter.definition("p").is_none(),
        "{:?}",
        out.converter
    );
}
