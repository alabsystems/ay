// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for the `der` (destructive equality resolution) pass, including
//! the adversarial capture-guard cases that motivated the fail-closed design.

use super::*;
use num_bigint::BigInt;

fn int(t: &mut TermStore, n: i64) -> TermId {
    t.mk_int(BigInt::from(n))
}

fn p1(t: &mut TermStore, arg: TermId) -> TermId {
    t.mk_app(Symbol::named("p"), vec![arg], Sort::Bool)
}

#[test]
fn der_full_elimination_to_ground() {
    // forall x. (or (not (= x 5)) (p x))  ==>  (p 5)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let five = int(&mut t, 5);
    let eq = t.mk_eq(x, five);
    let neq = t.mk_not(eq);
    let px = p1(&mut t, x);
    let body = t.mk_or(vec![neq, px]);
    let fa = t.mk_forall(vec![("x".into(), Sort::Int)], body);
    let p5 = p1(&mut t, five);

    let mut a = vec![fa];
    assert!(Der::new().apply(&mut t, &mut a));
    assert_eq!(a, vec![p5]);
}

#[test]
fn der_resolves_reversed_equality() {
    // forall x. (or (not (= 5 x)) (p x))  ==>  (p 5)   (measured: z3 handles it)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let five = int(&mut t, 5);
    let eq = t.mk_eq(five, x);
    let neq = t.mk_not(eq);
    let px = p1(&mut t, x);
    let body = t.mk_or(vec![neq, px]);
    let fa = t.mk_forall(vec![("x".into(), Sort::Int)], body);
    let p5 = p1(&mut t, five);

    let mut a = vec![fa];
    assert!(Der::new().apply(&mut t, &mut a));
    assert_eq!(a, vec![p5]);
}

#[test]
fn der_occurs_check_blocks_self_reference() {
    // forall x. (or (not (= x (+ x 1))) (p x))  ==>  UNCHANGED (x occurs in RHS).
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
    assert!(!Der::new().apply(&mut t, &mut a), "occurs-check must block");
    assert_eq!(a, vec![fa]);
}

#[test]
fn der_implication_sugar() {
    // forall x. (=> (= x 5) (p x)) is stored as (or (not (= x 5)) (p x)) ==> (p 5)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let five = int(&mut t, 5);
    let eq = t.mk_eq(x, five);
    let px = p1(&mut t, x);
    let body = t.mk_implies(eq, px);
    let fa = t.mk_forall(vec![("x".into(), Sort::Int)], body);
    let p5 = p1(&mut t, five);

    let mut a = vec![fa];
    assert!(Der::new().apply(&mut t, &mut a));
    assert_eq!(a, vec![p5]);
}

#[test]
fn der_multi_variable() {
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
    assert!(Der::new().apply(&mut t, &mut a));
    // Result must be a forall over one variable with body p2(y, y).
    match t.get(a[0]).clone() {
        TermData::Forall(vars, b, _) => {
            assert_eq!(vars.len(), 1, "one variable eliminated");
            match t.get(b).clone() {
                TermData::App(s, args) => {
                    assert_eq!(s.name(), "p2");
                    assert_eq!(args[0], args[1], "both args are the surviving var");
                }
                other => panic!("expected p2 app, got {other:?}"),
            }
        }
        other => panic!("expected forall, got {other:?}"),
    }
}

#[test]
fn der_empty_residual_collapses_to_false() {
    // forall x. (not (= x 5))  ==>  false
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let five = int(&mut t, 5);
    let eq = t.mk_eq(x, five);
    let neq = t.mk_not(eq);
    let fa = t.mk_forall(vec![("x".into(), Sort::Int)], neq);
    let f = t.mk_bool(false);

    let mut a = vec![fa];
    assert!(Der::new().apply(&mut t, &mut a));
    assert_eq!(a, vec![f]);
}

#[test]
fn der_fail_closes_on_nested_exists_capture_guard() {
    // forall x. (or (not (= x c)) (exists z. (< x z)))  ==>  UNCHANGED.
    // The capture guard must fire on ANY nested binder: substituting x:=c into
    // an inner binder is not capture-avoiding in AY, so der leaves it alone
    // (the sound identity). This is the shape of the adversarial capture probe
    // (dercap1/dercap2), which z3 handles by renaming the inner binder.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let c = t.mk_var("c", Sort::Int);
    let eq = t.mk_eq(x, c);
    let neq = t.mk_not(eq);
    let z = t.mk_var("z", Sort::Int);
    let lt = t.mk_app(Symbol::named("<"), vec![x, z], Sort::Bool);
    let ex = t.mk_exists(vec![("z".into(), Sort::Int)], lt);
    let body = t.mk_or(vec![neq, ex]);
    let fa = t.mk_forall(vec![("x".into(), Sort::Int)], body);

    let mut a = vec![fa];
    assert!(
        !Der::new().apply(&mut t, &mut a),
        "nested binder must fail-close der to identity"
    );
    assert_eq!(a, vec![fa]);
}

#[test]
fn der_fail_closes_on_shadowing_nested_forall() {
    // forall x. (or (not (= x 5)) (forall x. (p x)))  ==>  UNCHANGED.
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
    assert!(!Der::new().apply(&mut t, &mut a));
    assert_eq!(a, vec![fa]);
}

#[test]
fn der_is_identity_on_non_forall() {
    let mut t = TermStore::new();
    let a0 = t.mk_var("a", Sort::Bool);
    let mut a = vec![a0];
    assert!(!Der::new().apply(&mut t, &mut a));
    assert_eq!(a, vec![a0]);
}
