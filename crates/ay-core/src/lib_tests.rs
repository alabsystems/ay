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

#[test]
fn tight_bound_equalities_emit_anchor_star_per_sort() {
    // Anchor-star emission: a same-value group must produce a spanning
    // star (first same-sort term as anchor), not all pairs. Four Int
    // vars + one Real var pinned to 7 yield exactly three Int edges,
    // each touching the anchor; the Real var is never paired (cross-sort
    // guard) and forms its own singleton anchor. A second call with the
    // same propagated set emits nothing.
    let mut terms = TermStore::new();
    let mk = |terms: &mut TermStore, name: &str, sort: Sort| terms.mk_var(name, sort);
    let a = mk(&mut terms, "a", Sort::Int);
    let b = mk(&mut terms, "b", Sort::Int);
    let c = mk(&mut terms, "c", Sort::Int);
    let d = mk(&mut terms, "d", Sort::Int);
    let r = mk(&mut terms, "r", Sort::Real);
    // One pinning literal per var so reason composition is observable.
    let lit = |terms: &mut TermStore, v: TermId| {
        let seven = terms.mk_int(7.into());
        terms.mk_app(Symbol::named(">="), vec![v, seven], Sort::Bool)
    };
    let (la, lb, lc, ld, lr) = (
        lit(&mut terms, a),
        lit(&mut terms, b),
        lit(&mut terms, c),
        lit(&mut terms, d),
        lit(&mut terms, r),
    );
    let seven = num_rational::BigRational::from_integer(7.into());
    let triples = vec![
        (a, seven.clone(), vec![TheoryLit::new(la, true)]),
        (b, seven.clone(), vec![TheoryLit::new(lb, true)]),
        (r, seven.clone(), vec![TheoryLit::new(lr, true)]),
        (c, seven.clone(), vec![TheoryLit::new(lc, true)]),
        (d, seven.clone(), vec![TheoryLit::new(ld, true)]),
    ];
    let mut propagated = kani_compat::DetHashSet::default();
    let eqs = propagate_tight_bound_equalities(&terms, triples.clone(), &mut propagated);
    assert_eq!(eqs.len(), 3, "star over 4 Int vars has 3 edges: {eqs:?}");
    for eq in &eqs {
        assert!(
            eq.lhs == a || eq.rhs == a,
            "every star edge touches the anchor: {eq:?}"
        );
        assert_ne!(eq.lhs, r, "Real var must not be paired cross-sort");
        assert_ne!(eq.rhs, r, "Real var must not be paired cross-sort");
        assert!(
            eq.reason.contains(&TheoryLit::new(la, true)),
            "anchor reasons ride every edge: {eq:?}"
        );
    }
    let again = propagate_tight_bound_equalities(&terms, triples, &mut propagated);
    assert!(again.is_empty(), "dedup: second call emits nothing");
}
