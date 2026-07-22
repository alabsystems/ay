// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::TermStore;
use ay_core::Sort;

/// A compound Boolean argument to an uninterpreted function is replaced by a
/// fresh proxy variable, and a defining equality is appended.
#[test]
fn purifies_compound_bool_arg_of_uf() {
    let mut terms = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let conj = terms.mk_and(vec![a, b]);
    let fapp = terms.mk_app(Symbol::named("f"), [conj], u.clone());
    let t = terms.mk_var("t", u);
    let assertion = terms.mk_eq(fapp, t);

    let mut assertions = vec![assertion];
    let changed = purify_bool_args(&mut terms, &mut assertions);

    assert!(changed, "pass should fire on a compound Bool UF argument");
    assert_eq!(assertions.len(), 2, "a proxy definition should be appended");
}

/// Plain Boolean-variable arguments are left untouched (no spurious proxies).
#[test]
fn leaves_plain_bool_var_arg_untouched() {
    let mut terms = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let p = terms.mk_var("p", Sort::Bool);
    let fapp = terms.mk_app(Symbol::named("f"), [p], u.clone());
    let t = terms.mk_var("t", u);
    let assertion = terms.mk_eq(fapp, t);

    let mut assertions = vec![assertion];
    let changed = purify_bool_args(&mut terms, &mut assertions);

    assert!(!changed, "plain Bool-var arguments need no purification");
    assert_eq!(assertions.len(), 1);
}
