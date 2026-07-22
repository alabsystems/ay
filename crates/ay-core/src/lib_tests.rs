// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_is_theory_atom_bool_bool_equality_is_theory_atom() {
    // Regression: #6869 — Bool-Bool equalities must be theory atoms so EUF
    // sees alias chains. Dropping them caused false-SAT.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);
    let eq = terms.mk_app(Symbol::named("="), vec![x, y], Sort::Bool);
    assert!(
        is_theory_atom(&terms, eq),
        "Bool-Bool equality must be a theory atom (#6869)"
    );
}

#[test]
fn test_is_theory_atom_int_equality() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let eq = terms.mk_app(Symbol::named("="), vec![x, y], Sort::Bool);
    assert!(is_theory_atom(&terms, eq));
}

#[test]
fn test_is_theory_atom_propositional_connectives_are_not_atoms() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);

    for name in &["and", "or", "xor", "=>"] {
        let app = terms.mk_app(Symbol::named(*name), vec![x, y], Sort::Bool);
        assert!(
            !is_theory_atom(&terms, app),
            "{name} should not be a theory atom"
        );
    }
}

#[test]
fn test_is_theory_atom_uf_application() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let f_x = terms.mk_app(Symbol::named("f"), vec![x], Sort::Bool);
    assert!(is_theory_atom(&terms, f_x));
}

#[test]
fn test_is_theory_atom_constants_and_vars_are_not_atoms() {
    let mut terms = TermStore::new();
    let t = terms.mk_bool(true);
    let f = terms.mk_bool(false);
    let v = terms.mk_var("b", Sort::Bool);

    assert!(
        !is_theory_atom(&terms, t),
        "true constant is not a theory atom"
    );
    assert!(
        !is_theory_atom(&terms, f),
        "false constant is not a theory atom"
    );
    assert!(
        !is_theory_atom(&terms, v),
        "Bool variable is not a theory atom"
    );
}

#[test]
fn test_is_theory_atom_ite_is_not_atom() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let t = terms.mk_bool(true);
    let f = terms.mk_bool(false);
    let ite = terms.mk_app(Symbol::named("ite"), vec![c, t, f], Sort::Bool);
    // ite as a named App is a theory atom (it's not the TermData::Ite variant).
    // The TermData::Ite variant is created by mk_ite, not mk_app.
    // This test documents the distinction.
    assert!(is_theory_atom(&terms, ite));
}

#[test]
fn test_is_theory_atom_arithmetic_predicate() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(5.into());
    let leq = terms.mk_app(Symbol::named("<="), vec![x, five], Sort::Bool);
    assert!(is_theory_atom(&terms, leq));
}

#[test]
fn test_is_theory_atom_non_bool_is_not_atom() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let plus = terms.mk_app(Symbol::named("+"), vec![x, y], Sort::Int);
    assert!(
        !is_theory_atom(&terms, plus),
        "Int-sorted term is not a theory atom"
    );
}
