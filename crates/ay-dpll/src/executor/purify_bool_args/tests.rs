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
    let orphan_index = purify_bool_args(&mut terms, &mut assertions);

    assert!(
        !orphan_index.is_empty(),
        "pass should fire on a compound Bool UF argument"
    );
    // The rewritten `f(<compound>)` is indexed to `f(proxy)` — the ONLY term a
    // model will pin, since the original appears in no assertion the solver sees.
    assert_eq!(
        orphan_index.get(&fapp).copied(),
        Some(match terms.get(assertions[0]) {
            TermData::App(_, args) => args[0],
            _ => panic!("assertion should still be the equality"),
        }),
        "the rewritten UF application must be indexed to its solver-visible twin"
    );
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
    let orphan_index = purify_bool_args(&mut terms, &mut assertions);

    assert!(
        orphan_index.is_empty(),
        "plain Bool-var arguments need no purification"
    );
    assert_eq!(assertions.len(), 1);
}
