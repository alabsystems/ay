// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::Symbol;

type Registry = Vec<(String, Vec<String>)>;

fn list_registries() -> (Registry, Registry) {
    (
        vec![(
            "List".to_string(),
            vec!["nil".to_string(), "cons".to_string()],
        )],
        vec![
            ("nil".to_string(), vec![]),
            ("cons".to_string(), vec!["hd".to_string(), "tl".to_string()]),
        ],
    )
}

fn eq(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![a, b], Sort::Bool)
}

fn tester(terms: &mut TermStore, ctor: &str, subject: TermId) -> TermId {
    terms.mk_app(
        Symbol::named(format!("is-{ctor}")),
        vec![subject],
        Sort::Bool,
    )
}

/// The full multi-constructor expansion for List over `x`,`y`, minus the
/// conjuncts named in `drop`.
fn multi_expansion(
    terms: &mut TermStore,
    x: TermId,
    y: TermId,
    list_sort: &Sort,
    drop: &[&str],
) -> TermId {
    let mut conjuncts = Vec::new();
    for ctor in ["nil", "cons"] {
        if drop.contains(&ctor) {
            continue;
        }
        let tx = tester(terms, ctor, x);
        let ty = tester(terms, ctor, y);
        let agreement = eq(terms, tx, ty);
        conjuncts.push(agreement);
    }
    for (sel, sort) in [("hd", Sort::Int), ("tl", list_sort.clone())] {
        if drop.contains(&sel) {
            continue;
        }
        let sx = terms.mk_app(Symbol::named(sel), vec![x], sort.clone());
        let sy = terms.mk_app(Symbol::named(sel), vec![y], sort);
        let field_eq = eq(terms, sx, sy);
        let guard_tester = tester(terms, "cons", x);
        let not_guard = terms.mk_not(guard_tester);
        let guarded = terms.mk_app(Symbol::named("or"), vec![not_guard, field_eq], Sort::Bool);
        conjuncts.push(guarded);
    }
    terms.mk_app(Symbol::named("and"), conjuncts, Sort::Bool)
}

#[test]
fn accepts_multi_constructor_expansion() {
    let (decls, selectors) = list_registries();
    let mut terms = TermStore::new();
    let list_sort = Sort::Uninterpreted("List".to_string());
    let x = terms.mk_var("x", list_sort.clone());
    let y = terms.mk_var("y", list_sort.clone());
    let rhs = multi_expansion(&mut terms, x, y, &list_sort, &[]);
    let eq_xy = eq(&mut terms, x, y);
    let bic = eq(&mut terms, eq_xy, rhs);
    assert!(recognize_datatype_value_eq_congruence(
        &terms,
        &[bic],
        &decls,
        &selectors
    ));
}

#[test]
fn rejects_subset_expansion() {
    // Dropping any tester agreement or guarded congruence yields a
    // STRONGER, unentailed biconditional; both directions must fail.
    let (decls, selectors) = list_registries();
    for missing in ["nil", "tl"] {
        let mut terms = TermStore::new();
        let list_sort = Sort::Uninterpreted("List".to_string());
        let x = terms.mk_var("x", list_sort.clone());
        let y = terms.mk_var("y", list_sort.clone());
        let rhs = multi_expansion(&mut terms, x, y, &list_sort, &[missing]);
        let eq_xy = eq(&mut terms, x, y);
        let bic = eq(&mut terms, eq_xy, rhs);
        assert!(
            !recognize_datatype_value_eq_congruence(&terms, &[bic], &decls, &selectors),
            "expansion missing `{missing}` must be rejected"
        );
    }
}

#[test]
fn accepts_single_constructor_expansion() {
    let decls = vec![("Pair".to_string(), vec!["mk".to_string()])];
    let selectors = vec![("mk".to_string(), vec!["fst".to_string(), "snd".to_string()])];
    let mut terms = TermStore::new();
    let pair_sort = Sort::Uninterpreted("Pair".to_string());
    let x = terms.mk_var("x", pair_sort.clone());
    let y = terms.mk_var("y", pair_sort);
    let mut conjuncts = Vec::new();
    for sel in ["fst", "snd"] {
        let sx = terms.mk_app(Symbol::named(sel), vec![x], Sort::Int);
        let sy = terms.mk_app(Symbol::named(sel), vec![y], Sort::Int);
        let field_eq = eq(&mut terms, sx, sy);
        conjuncts.push(field_eq);
    }
    let rhs = terms.mk_app(Symbol::named("and"), conjuncts, Sort::Bool);
    let eq_xy = eq(&mut terms, x, y);
    let bic = eq(&mut terms, eq_xy, rhs);
    assert!(recognize_datatype_value_eq_congruence(
        &terms,
        &[bic],
        &decls,
        &selectors
    ));
}

#[test]
fn rejects_foreign_selector_expansion() {
    // A selector outside `mk`'s registered list carries no congruence
    // authority even when the shape is otherwise perfect.
    let decls = vec![("Pair".to_string(), vec!["mk".to_string()])];
    let selectors = vec![("mk".to_string(), vec!["fst".to_string()])];
    let mut terms = TermStore::new();
    let pair_sort = Sort::Uninterpreted("Pair".to_string());
    let x = terms.mk_var("x", pair_sort.clone());
    let y = terms.mk_var("y", pair_sort);
    let sx = terms.mk_app(Symbol::named("other"), vec![x], Sort::Int);
    let sy = terms.mk_app(Symbol::named("other"), vec![y], Sort::Int);
    let rhs = eq(&mut terms, sx, sy);
    let eq_xy = eq(&mut terms, x, y);
    let bic = eq(&mut terms, eq_xy, rhs);
    assert!(!recognize_datatype_value_eq_congruence(
        &terms,
        &[bic],
        &decls,
        &selectors
    ));
}

#[test]
fn accepts_nullary_bridge_and_rejects_non_nullary() {
    let (decls, selectors) = list_registries();
    let mut terms = TermStore::new();
    let list_sort = Sort::Uninterpreted("List".to_string());
    let x = terms.mk_var("x", list_sort.clone());
    let nil = terms.mk_app(Symbol::named("nil"), vec![], list_sort.clone());
    let eq_x_nil = eq(&mut terms, x, nil);
    let is_nil_x = tester(&mut terms, "nil", x);
    let bridge = eq(&mut terms, eq_x_nil, is_nil_x);
    assert!(recognize_datatype_value_eq_congruence(
        &terms,
        &[bridge],
        &decls,
        &selectors
    ));

    // `(= (= x (cons 0 x)) (is-cons x))` is NOT valid — `is-cons x` does
    // not pin the fields — and the non-nullary registry entry refuses it.
    let zero = terms.mk_int(0.into());
    let cons = terms.mk_app(Symbol::named("cons"), vec![zero, x], list_sort);
    let eq_x_cons = eq(&mut terms, x, cons);
    let is_cons_x = tester(&mut terms, "cons", x);
    let bad_bridge = eq(&mut terms, eq_x_cons, is_cons_x);
    assert!(!recognize_datatype_value_eq_congruence(
        &terms,
        &[bad_bridge],
        &decls,
        &selectors
    ));
}

#[test]
fn accepts_ctor_application_equality_expansion() {
    // The (F3) form: `(= (= t (cons h r)) (and (is-cons t) (= (hd t) h)
    // (= (tl t) r)))`, with arbitrary conjunct order and either equality
    // orientation per field.
    let (decls, selectors) = list_registries();
    let mut terms = TermStore::new();
    let list_sort = Sort::Uninterpreted("List".to_string());
    let t = terms.mk_var("t", list_sort.clone());
    let h = terms.mk_var("h", Sort::Int);
    let r = terms.mk_var("r", list_sort.clone());
    let cons = terms.mk_app(Symbol::named("cons"), vec![h, r], list_sort);
    let eq_t_cons = eq(&mut terms, t, cons);
    let is_cons_t = tester(&mut terms, "cons", t);
    let hd_t = terms.mk_app(Symbol::named("hd"), vec![t], Sort::Int);
    let tl_t = terms.mk_app(
        Symbol::named("tl"),
        vec![t],
        Sort::Uninterpreted("List".to_string()),
    );
    let eq_hd = eq(&mut terms, h, hd_t);
    let eq_tl = eq(&mut terms, tl_t, r);
    let rhs = terms.mk_app(
        Symbol::named("and"),
        vec![eq_tl, is_cons_t, eq_hd],
        Sort::Bool,
    );
    let bic = eq(&mut terms, rhs, eq_t_cons);
    assert!(recognize_datatype_value_eq_congruence(
        &terms,
        &[bic],
        &decls,
        &selectors
    ));

    // Truncated: dropping a field equality is a STRONGER biconditional.
    let rhs_short = terms.mk_app(Symbol::named("and"), vec![is_cons_t, eq_hd], Sort::Bool);
    let bad = eq(&mut terms, eq_t_cons, rhs_short);
    assert!(!recognize_datatype_value_eq_congruence(
        &terms,
        &[bad],
        &decls,
        &selectors
    ));

    // Wrong argument binding: `(= (hd t) r-as-int)` for a foreign term.
    let z = terms.mk_var("z", Sort::Int);
    let eq_hd_wrong = eq(&mut terms, hd_t, z);
    let rhs_wrong = terms.mk_app(
        Symbol::named("and"),
        vec![is_cons_t, eq_hd_wrong, eq_tl],
        Sort::Bool,
    );
    let bad2 = eq(&mut terms, eq_t_cons, rhs_wrong);
    assert!(!recognize_datatype_value_eq_congruence(
        &terms,
        &[bad2],
        &decls,
        &selectors
    ));
}

#[test]
fn fails_closed_without_registry_entries() {
    let mut terms = TermStore::new();
    let sort = Sort::Uninterpreted("List".to_string());
    let x = terms.mk_var("x", sort.clone());
    let y = terms.mk_var("y", sort.clone());
    let rhs = multi_expansion(&mut terms, x, y, &sort, &[]);
    let eq_xy = eq(&mut terms, x, y);
    let bic = eq(&mut terms, eq_xy, rhs);
    assert!(!recognize_datatype_value_eq_congruence(
        &terms,
        &[bic],
        &[],
        &[]
    ));
}

/// Single-constructor `B { f1: Bool, f2: Int }` registries.
fn record_registries() -> (Registry, Registry) {
    (
        vec![("B".to_string(), vec!["B".to_string()])],
        vec![("B".to_string(), vec!["f1".to_string(), "f2".to_string()])],
    )
}

/// `(= (= x (B <f1_arg> 0)) (and (is-B x) <f1_conjunct> (= 0 (f2 x))))`,
/// with the Bool field conjunct supplied by the caller.
fn record_biconditional(
    terms: &mut TermStore,
    f1_arg: TermId,
    f1_conjunct: impl FnOnce(&mut TermStore, TermId) -> Option<TermId>,
) -> TermId {
    let record_sort = Sort::Uninterpreted("B".to_string());
    let x = terms.mk_var("x", record_sort.clone());
    let zero = terms.mk_int(0.into());
    let ctor = terms.mk_app(Symbol::named("B"), vec![f1_arg, zero], record_sort);
    let is_b = tester(terms, "B", x);
    let f2 = terms.mk_app(Symbol::named("f2"), vec![x], Sort::Int);
    let f2_eq = eq(terms, zero, f2);
    let f1 = terms.mk_app(Symbol::named("f1"), vec![x], Sort::Bool);
    let mut conjuncts = vec![is_b];
    if let Some(conjunct) = f1_conjunct(terms, f1) {
        conjuncts.push(conjunct);
    }
    conjuncts.push(f2_eq);
    let expansion = terms.mk_app(Symbol::named("and"), conjuncts, Sort::Bool);
    let eq_x_ctor = eq(terms, x, ctor);
    eq(terms, eq_x_ctor, expansion)
}

/// POSITIVE: `(= (f1 x) false)` folded to `(not (f1 x))` — the exact shape
/// of the Creusot `syntax/05_pearlite::struct_order` refutation.
#[test]
fn accepts_folded_false_bool_field() {
    let (decls, selectors) = record_registries();
    let mut terms = TermStore::new();
    let false_c = terms.mk_bool(false);
    let bic = record_biconditional(&mut terms, false_c, |terms, f1| Some(terms.mk_not(f1)));
    assert!(recognize_datatype_value_eq_congruence(
        &terms,
        &[bic],
        &decls,
        &selectors
    ));
}

/// POSITIVE: `(= (f1 x) true)` folded to the bare `(f1 x)`.
#[test]
fn accepts_folded_true_bool_field() {
    let (decls, selectors) = record_registries();
    let mut terms = TermStore::new();
    let true_c = terms.mk_bool(true);
    let bic = record_biconditional(&mut terms, true_c, |_, f1| Some(f1));
    assert!(recognize_datatype_value_eq_congruence(
        &terms,
        &[bic],
        &decls,
        &selectors
    ));
}

/// NEGATIVE: wrong polarity — the constructor carries `false` but the
/// expansion claims `(f1 x)`. Not valid; must be refused.
#[test]
fn rejects_bool_field_literal_with_wrong_polarity() {
    let (decls, selectors) = record_registries();
    let mut terms = TermStore::new();
    let false_c = terms.mk_bool(false);
    let bic = record_biconditional(&mut terms, false_c, |_, f1| Some(f1));
    assert!(!recognize_datatype_value_eq_congruence(
        &terms,
        &[bic],
        &decls,
        &selectors
    ));
}

/// NEGATIVE: a NON-CONSTANT Bool argument `p` with the bare literal `(f1 x)`.
/// `(f1 x)` is not `(= (f1 x) p)`; the folded form is licensed only for the
/// literal constants.
#[test]
fn rejects_bool_field_literal_for_non_constant_argument() {
    let (decls, selectors) = record_registries();
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let bic = record_biconditional(&mut terms, p, |_, f1| Some(f1));
    assert!(!recognize_datatype_value_eq_congruence(
        &terms,
        &[bic],
        &decls,
        &selectors
    ));
}

/// NEGATIVE: the Bool field is missing entirely — coverage must stay exact.
#[test]
fn rejects_expansion_missing_the_bool_field() {
    let (decls, selectors) = record_registries();
    let mut terms = TermStore::new();
    let false_c = terms.mk_bool(false);
    let bic = record_biconditional(&mut terms, false_c, |_, _| None);
    assert!(!recognize_datatype_value_eq_congruence(
        &terms,
        &[bic],
        &decls,
        &selectors
    ));
}
