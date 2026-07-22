// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for the `distribute-forall` pass.

use super::*;
use ay_core::Sort;

fn pred(t: &mut TermStore, name: &str, arg: TermId) -> TermId {
    t.mk_app(Symbol::named(name), vec![arg], Sort::Bool)
}

#[test]
fn distribute_forall_over_and_splits() {
    // forall x. (and (p x) (q x))  ==>  {forall x. p x, forall x. q x}
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let px = pred(&mut t, "p", x);
    let qx = pred(&mut t, "q", x);
    let body = t.mk_and(vec![px, qx]);
    let fa = t.mk_forall(vec![("x".into(), Sort::Int)], body);

    let mut a = vec![fa];
    assert!(DistributeForall::new().apply(&mut t, &mut a));
    assert_eq!(a.len(), 2);
    for &f in &a {
        assert!(
            matches!(t.get(f), TermData::Forall(_, _, _)),
            "each split is a forall"
        );
    }
}

#[test]
fn distribute_forall_flattens_nested_and() {
    // forall x. (and (p x) (and (q x) (r x)))  ==>  3 foralls.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let px = pred(&mut t, "p", x);
    let qx = pred(&mut t, "q", x);
    let rx = pred(&mut t, "r", x);
    let inner = t.mk_and(vec![qx, rx]);
    let body = t.mk_and(vec![px, inner]);
    let fa = t.mk_forall(vec![("x".into(), Sort::Int)], body);

    let mut a = vec![fa];
    assert!(DistributeForall::new().apply(&mut t, &mut a));
    assert_eq!(a.len(), 3);
}

#[test]
fn distribute_neg_exists_over_or() {
    // (not (exists x. (or (p x) (q x))))  ==>  {not exists p, not exists q}
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let px = pred(&mut t, "p", x);
    let qx = pred(&mut t, "q", x);
    let body = t.mk_or(vec![px, qx]);
    let ex = t.mk_exists(vec![("x".into(), Sort::Int)], body);
    let neg = t.mk_not(ex);

    let mut a = vec![neg];
    assert!(DistributeForall::new().apply(&mut t, &mut a));
    assert_eq!(a.len(), 2);
    for &f in &a {
        match t.get(f).clone() {
            TermData::Not(inner) => {
                assert!(matches!(t.get(inner), TermData::Exists(_, _, _)));
            }
            other => panic!("expected (not (exists ..)), got {other:?}"),
        }
    }
}

#[test]
fn distribute_forall_identity_on_implication_body() {
    // forall x. (=> (p x) (q x)) is (or (not p) q), NOT an `and` ==> UNCHANGED.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let px = pred(&mut t, "p", x);
    let qx = pred(&mut t, "q", x);
    let body = t.mk_implies(px, qx);
    let fa = t.mk_forall(vec![("x".into(), Sort::Int)], body);

    let mut a = vec![fa];
    assert!(!DistributeForall::new().apply(&mut t, &mut a));
    assert_eq!(a, vec![fa]);
}
