// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The API `der` tactic runs the pipeline's DER pass ([`super::der_tactic`]).
//! These are the cases the tactic's former stand-alone implementation pinned,
//! plus the shapes it used to leave alone: a nested binder (which the
//! capture-avoiding substitution handles, as z3 5.1.0's `(apply der)` does)
//! and an existential.

use super::*;
use ay_core::term::{Symbol, TermData};
use ay_core::Sort;
use num_bigint::BigInt;

fn int(t: &mut TermStore, n: i64) -> TermId {
    t.mk_int(BigInt::from(n))
}

fn p1(t: &mut TermStore, arg: TermId) -> TermId {
    t.mk_app(Symbol::named("p"), vec![arg], Sort::Bool)
}

/// `∀x. ¬(x = value) ∨ p(x)`, the equality written `(= x value)` or
/// `(= value x)`.
fn forall_diseq_or_p(t: &mut TermStore, eq_lhs_is_var: bool, value: i64) -> TermId {
    let x = t.mk_var("x", Sort::Int);
    let v = int(t, value);
    let eq = if eq_lhs_is_var {
        t.mk_eq(x, v)
    } else {
        t.mk_eq(v, x)
    };
    let neq = t.mk_not(eq);
    let px = p1(t, x);
    let body = t.mk_or(vec![neq, px]);
    t.mk_forall(vec![("x".into(), Sort::Int)], body)
}

#[test]
fn der_tactic_eliminates_to_ground() {
    // forall x. (or (not (= x 5)) (p x))  ==>  (p 5)
    let mut t = TermStore::new();
    let fa = forall_diseq_or_p(&mut t, true, 5);
    let five = int(&mut t, 5);
    let p5 = p1(&mut t, five);
    let mut a = vec![fa];
    assert!(der_tactic(&mut t, &mut a));
    assert_eq!(a, vec![p5]);
}

#[test]
fn der_tactic_resolves_reversed_equality() {
    // forall x. (or (not (= 5 x)) (p x))  ==>  (p 5)
    let mut t = TermStore::new();
    let fa = forall_diseq_or_p(&mut t, false, 5);
    let five = int(&mut t, 5);
    let p5 = p1(&mut t, five);
    let mut a = vec![fa];
    assert!(der_tactic(&mut t, &mut a));
    assert_eq!(a, vec![p5]);
}

#[test]
fn der_tactic_occurs_check_blocks_self_reference() {
    // forall x. (or (not (= x (+ x 1))) (p x))  ==>  UNCHANGED
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let one = int(&mut t, 1);
    let xp1 = t.mk_add(vec![x, one]);
    let eq = t.mk_eq(x, xp1);
    let neq = t.mk_not(eq);
    let px = p1(&mut t, x);
    let body = t.mk_or(vec![neq, px]);
    let fa = t.mk_forall(vec![("x".into(), Sort::Int)], body);
    let mut a = vec![fa];
    assert!(!der_tactic(&mut t, &mut a), "occurs-check must block");
    assert_eq!(a, vec![fa]);
}

#[test]
fn der_tactic_implication_sugar() {
    // forall x. (=> (= x 5) (p x))  ==>  (p 5)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let five = int(&mut t, 5);
    let eq = t.mk_eq(x, five);
    let px = p1(&mut t, x);
    let body = t.mk_implies(eq, px);
    let fa = t.mk_forall(vec![("x".into(), Sort::Int)], body);
    let p5 = p1(&mut t, five);
    let mut a = vec![fa];
    assert!(der_tactic(&mut t, &mut a));
    assert_eq!(a, vec![p5]);
}

#[test]
fn der_tactic_multi_variable() {
    // forall x y. (or (not (= x y)) (p2 x y))  ==>  forall y. (p2 y y)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let y = t.mk_var("y", Sort::Int);
    let eq = t.mk_eq(x, y);
    let neq = t.mk_not(eq);
    let p2 = t.mk_app(Symbol::named("p2"), vec![x, y], Sort::Bool);
    let body = t.mk_or(vec![neq, p2]);
    let fa = t.mk_forall(vec![("x".into(), Sort::Int), ("y".into(), Sort::Int)], body);
    let mut a = vec![fa];
    assert!(der_tactic(&mut t, &mut a));
    let TermData::Forall(vars, b, _) = t.get(a[0]).clone() else {
        panic!("expected a forall, got {:?}", t.get(a[0]));
    };
    assert_eq!(vars.len(), 1, "one variable eliminated");
    let TermData::App(sym, args) = t.get(b).clone() else {
        panic!("expected p2, got {:?}", t.get(b));
    };
    assert_eq!(sym.name(), "p2");
    assert_eq!(
        args[0], args[1],
        "both arguments are the surviving variable"
    );
}

#[test]
fn der_tactic_empty_residual_collapses_to_false() {
    // forall x. (not (= x 5))  ==>  false
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let five = int(&mut t, 5);
    let eq = t.mk_eq(x, five);
    let neq = t.mk_not(eq);
    let fa = t.mk_forall(vec![("x".into(), Sort::Int)], neq);
    let f = t.mk_bool(false);
    let mut a = vec![fa];
    assert!(der_tactic(&mut t, &mut a));
    assert_eq!(a, vec![f]);
}

#[test]
fn der_tactic_substitutes_under_a_nested_binder_without_capture() {
    // forall x. (or (not (= x c)) (exists z. (< x z)))  ==>  exists z. (< c z)
    // (z3 5.1.0 `(apply der)` prints the same goal). The former tactic left
    // any assertion with a nested binder alone because its substitution was
    // not capture-avoiding; the pipeline's is.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let c = t.mk_var("c", Sort::Int);
    let z = t.mk_var("z", Sort::Int);
    let eq = t.mk_eq(x, c);
    let neq = t.mk_not(eq);
    let lt = t.mk_app(Symbol::named("<"), vec![x, z], Sort::Bool);
    let ex = t.mk_exists(vec![("z".into(), Sort::Int)], lt);
    let body = t.mk_or(vec![neq, ex]);
    let fa = t.mk_forall(vec![("x".into(), Sort::Int)], body);
    let mut a = vec![fa];
    assert!(der_tactic(&mut t, &mut a));
    let TermData::Exists(vars, inner_body, _) = t.get(a[0]).clone() else {
        panic!("expected the inner existential, got {:?}", t.get(a[0]));
    };
    assert_eq!(vars, vec![("z".to_string(), Sort::Int)]);
    let free = super::terms::free_names(&t, inner_body).expect("closed walk");
    assert!(free.contains("c") && free.contains("z"), "{free:?}");
    assert!(!free.contains("x"), "x := c reached the body: {free:?}");
}

#[test]
fn der_tactic_respects_a_shadowing_nested_binder() {
    // forall x. (or (not (= x 5)) (forall x. (p x)))  ==>  forall x. (p x)
    // The inner x is a different variable: substituting x := 5 must not reach
    // it (z3 5.1.0 prints the same goal).
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let five = int(&mut t, 5);
    let eq = t.mk_eq(x, five);
    let neq = t.mk_not(eq);
    let px = p1(&mut t, x);
    let inner = t.mk_forall(vec![("x".into(), Sort::Int)], px);
    let body = t.mk_or(vec![neq, inner]);
    let fa = t.mk_forall(vec![("x".into(), Sort::Int)], body);
    let mut a = vec![fa];
    assert!(der_tactic(&mut t, &mut a));
    let TermData::Forall(vars, inner_body, _) = t.get(a[0]).clone() else {
        panic!("expected the inner universal, got {:?}", t.get(a[0]));
    };
    assert_eq!(vars, vec![("x".to_string(), Sort::Int)]);
    assert_eq!(inner_body, px, "the shadowed x must not be substituted");
}

#[test]
fn der_tactic_eliminates_an_existential_equality() {
    // exists y. (and (= y c) (p y))  ==>  (p c)   (z3 5.1.0 `(apply der)` agrees)
    let mut t = TermStore::new();
    let y = t.mk_var("y", Sort::Int);
    let c = t.mk_var("c", Sort::Int);
    let eq = t.mk_eq(y, c);
    let py = p1(&mut t, y);
    let body = t.mk_and(vec![eq, py]);
    let ex = t.mk_exists(vec![("y".into(), Sort::Int)], body);
    let pc = p1(&mut t, c);
    let mut a = vec![ex];
    assert!(der_tactic(&mut t, &mut a));
    assert_eq!(a, vec![pc]);
}

#[test]
fn der_tactic_is_identity_without_a_quantifier() {
    let mut t = TermStore::new();
    let a0 = t.mk_var("a", Sort::Bool);
    let mut a = vec![a0];
    assert!(!der_tactic(&mut t, &mut a));
    assert_eq!(a, vec![a0]);
}
