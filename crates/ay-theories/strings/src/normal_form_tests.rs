// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn empty_normal_form() {
    let nf = NormalForm::new();
    assert!(nf.is_empty());
    assert_eq!(nf.len(), 0);
    assert!(nf.rep.is_none());
    assert!(nf.deps.is_empty());
}

#[test]
fn singleton_normal_form() {
    let t = TermId::new(42);
    let nf = NormalForm::singleton(t);
    assert_eq!(nf.len(), 1);
    assert_eq!(nf.base[0], t);
    assert_eq!(nf.rep, Some(t));
    assert_eq!(nf.source, Some(t));
}

#[test]
fn empty_string_normal_form() {
    let rep = TermId::new(7);
    let nf = NormalForm::empty(rep);
    assert!(nf.is_empty());
    assert_eq!(nf.rep, Some(rep));
    assert_eq!(nf.source, Some(rep));
}

#[test]
fn add_and_merge_deps() {
    let a = TermId::new(1);
    let b = TermId::new(2);
    let c = TermId::new(3);
    let d = TermId::new(4);

    let mut nf1 = NormalForm::singleton(a);
    nf1.add_dep(a, b);
    assert_eq!(nf1.deps.len(), 1);

    let mut nf2 = NormalForm::singleton(c);
    nf2.add_dep(c, d);

    nf1.merge_deps(&nf2);
    assert_eq!(nf1.deps.len(), 2);
    assert_eq!(nf1.deps[0], ExplainEntry { lhs: a, rhs: b });
    assert_eq!(nf1.deps[1], ExplainEntry { lhs: c, rhs: d });
}
