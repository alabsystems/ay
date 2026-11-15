// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `collect_quantifiers` on a shared DAG: linear, and the same output as the
//! tree walk, duplicates and order included.

use ay_core::{Sort, Symbol, TermId, TermStore};

use super::collect_quantifiers;

#[test]
fn a_shared_quantifier_free_dag_is_walked_once_and_the_output_is_unchanged() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("qa", Sort::Int);
    // 40 levels of (g t t): 2^40 paths for a tree walk, 41 distinct terms.
    let mut shared = terms.mk_app(Symbol::named("qf"), [a], Sort::Int);
    for _ in 0..40 {
        shared = terms.mk_app(Symbol::named("qg"), [shared, shared], Sort::Int);
    }
    let zero = terms.mk_int(0.into());
    let atom = terms.mk_eq(shared, zero);
    let x = terms.mk_var("qx", Sort::Int);
    let body = terms.mk_eq(x, shared);
    let forall = terms.mk_forall(vec![("qx".to_string(), Sort::Int)], body);
    // The quantifier twice, either side of the shared atom: the tree walk
    // reports it once per occurrence, in order.
    let root = terms.mk_app(
        Symbol::named("and"),
        [forall, atom, atom, forall],
        Sort::Bool,
    );

    let mut out: Vec<TermId> = Vec::new();
    collect_quantifiers(&mut terms, root, &mut out);
    assert_eq!(out, vec![forall, forall]);
}
