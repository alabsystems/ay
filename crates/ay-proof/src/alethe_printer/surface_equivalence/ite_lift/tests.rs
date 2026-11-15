// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::super::*;
use num_bigint::BigInt;

fn rules(steps: &[String]) -> Vec<String> {
    steps
        .iter()
        .map(|step| {
            let rule = step
                .split(":rule ")
                .nth(1)
                .expect("every step names its rule");
            rule.split([' ', ')'])
                .next()
                .expect("rule name")
                .to_string()
        })
        .collect()
}

fn derive(terms: &TermStore, surface: &str, term: TermId) -> Option<Vec<String>> {
    let printer = AlethePrinter::new(terms);
    let canonical = printer.format_term(term);
    printer
        .printed_surface_equivalence_steps("t9.n", surface, term, &canonical)
        .map(|(steps, _)| steps)
}

/// How the update-axiom instance at index `0` is stored.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Instance {
    /// AY's own term:
    /// `(ite (= 1 0) (= val (select snew 0)) (= (select snew 0) (select s 0)))`.
    Canonical,
    /// The same formula already spelled as the authored atom's lift:
    /// `(ite (= 0 1) (= (select snew 0) val) (= (select snew 0) (select s 0)))`.
    Lifted,
    /// The branches exchanged: a DIFFERENT formula.
    Swapped,
}

fn frame_instance(terms: &mut TermStore, shape: Instance) -> TermId {
    let array = Sort::array(Sort::Int, Sort::Int);
    let s = terms.mk_var("s", array.clone());
    let snew = terms.mk_var("snew", array);
    let val = terms.mk_var("val", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let read_new = terms.mk_app(Symbol::named("select"), [snew, zero], Sort::Int);
    let read_old = terms.mk_app(Symbol::named("select"), [s, zero], Sort::Int);
    let framed = terms.mk_app(Symbol::named("="), [read_new, read_old], Sort::Bool);
    let (condition, updated) = if shape == Instance::Lifted {
        (
            terms.mk_app(Symbol::named("="), [zero, one], Sort::Bool),
            terms.mk_app(Symbol::named("="), [read_new, val], Sort::Bool),
        )
    } else {
        (
            terms.mk_app(Symbol::named("="), [one, zero], Sort::Bool),
            terms.mk_app(Symbol::named("="), [val, read_new], Sort::Bool),
        )
    };
    if shape == Instance::Swapped {
        terms.mk_ite_raw(condition, framed, updated)
    } else {
        terms.mk_ite_raw(condition, updated, framed)
    }
}

const AUTHORED_INSTANCE: &str = "(= (select snew 0) (ite (= 0 1) val (select s 0)))";

#[test]
fn authored_update_instance_derives_its_lifted_canonical_formula() {
    let mut terms = TermStore::new();
    let instance = frame_instance(&mut terms, Instance::Canonical);
    let steps = derive(&terms, AUTHORED_INSTANCE, instance)
        .expect("the authored atom is its Shannon lift up to atom orientation");
    assert_eq!(
        steps.last().map(String::as_str),
        Some(
            "(step t9.n (cl (= (= (select snew 0) (ite (= 0 1) val (select s 0))) \
             (ite (= 1 0) (= val (select snew 0)) (= (select snew 0) (select s 0))))) \
             :rule trans :premises (t9.n.sl t9.n.lc))"
        )
    );
    let used = rules(&steps);
    for rule in [
        "ite_intro",
        "eq_reflexive",
        "and",
        "ite1",
        "ite2",
        "eq_congruent_pred",
        "ite_pos1",
        "ite_pos2",
        "ite_neg1",
        "ite_neg2",
        "equiv_neg1",
        "equiv_neg2",
        "refl",
        "trans",
    ] {
        assert!(
            used.iter().any(|used| used == rule),
            "{rule} missing: {steps:#?}"
        );
    }
    // The branch clauses are read off the `ite` DEFINITION, whose printed
    // premise IS an `ite`: the shape carcara's `ite1`/`ite2` require.
    assert!(
        steps.iter().any(|step| step
            == "(step t9.n.sl.d (cl (ite (= 0 1) (= (ite (= 0 1) val (select s 0)) val) \
                (= (ite (= 0 1) val (select s 0)) (select s 0)))) :rule and :premises (t9.n.sl.k) :args (1))"),
        "{steps:#?}"
    );
    // The lifted text is one `refl` (equality orientation) from the canonical.
    assert!(
        steps.iter().any(|step| step
            == "(step t9.n.lc (cl (= (ite (= 0 1) (= (select snew 0) val) (= (select snew 0) (select s 0))) \
                (ite (= 1 0) (= val (select snew 0)) (= (select snew 0) (select s 0))))) :rule refl)"),
        "{steps:#?}"
    );
}

/// A canonical term that already prints as the lift needs no `trans` leg.
#[test]
fn a_canonical_term_spelled_as_the_lift_is_derived_directly() {
    let mut terms = TermStore::new();
    let instance = frame_instance(&mut terms, Instance::Lifted);
    let steps = derive(&terms, AUTHORED_INSTANCE, instance).expect("the lift itself");
    assert_eq!(
        steps.last().map(String::as_str),
        Some(
            "(step t9.n (cl (= (= (select snew 0) (ite (= 0 1) val (select s 0))) \
             (ite (= 0 1) (= (select snew 0) val) (= (select snew 0) (select s 0))))) \
             :rule resolution :premises (t9.n.e1 t9.n.e2))"
        )
    );
    assert!(
        !rules(&steps).iter().any(|rule| rule == "trans"),
        "{steps:#?}"
    );
}

/// Negative twins: exchanged branches, a different condition, a different
/// branch value, a negated condition and a surface with no `ite` argument are
/// different formulas (or outside the schema) and must never be claimed.
#[test]
fn inequivalent_lifts_decline() {
    let mut terms = TermStore::new();
    let swapped = frame_instance(&mut terms, Instance::Swapped);
    assert_eq!(derive(&terms, AUTHORED_INSTANCE, swapped), None);

    let mut terms = TermStore::new();
    let instance = frame_instance(&mut terms, Instance::Canonical);
    for surface in [
        "(= (select snew 0) (ite (= 0 2) val (select s 0)))",
        "(= (select snew 0) (ite (= 0 1) val (select s 1)))",
        "(= (select snew 0) (ite (not (= 0 1)) (select s 0) val))",
        "(= (select snew 0) (select s 0))",
    ] {
        assert_eq!(derive(&terms, surface, instance), None, "{surface}");
    }
}

/// Equal branch values make the two congruence atoms one atom. The canonical
/// term here IS the exact lift, so `atoms_are_distinct` is the only reason
/// this declines: a conservative scope limit that keeps every resolution to
/// the one pivot it is written for (pinned carcara's RUP fallback would still
/// accept the derivation, measured 2026-09-25; the limit is not load-bearing
/// for validity, and this test pins that it holds).
#[test]
fn coinciding_atoms_decline() {
    let mut terms = TermStore::new();
    let array = Sort::array(Sort::Int, Sort::Int);
    let snew = terms.mk_var("snew", array);
    let val = terms.mk_var("val", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let read_new = terms.mk_app(Symbol::named("select"), [snew, zero], Sort::Int);
    let condition = terms.mk_app(Symbol::named("="), [zero, one], Sort::Bool);
    let branch = terms.mk_app(Symbol::named("="), [read_new, val], Sort::Bool);
    let exact_lift = terms.mk_ite_raw(condition, branch, branch);
    assert_eq!(
        AlethePrinter::new(&terms).format_term(exact_lift),
        "(ite (= 0 1) (= (select snew 0) val) (= (select snew 0) val))"
    );
    assert_eq!(
        derive(
            &terms,
            "(= (select snew 0) (ite (= 0 1) val val))",
            exact_lift
        ),
        None
    );
}

/// A Boolean connective is not a lift head (`liftable_head`), even when the
/// canonical term is the exact lift of the surface: another conservative
/// scope limit, pinned on the one input only it refuses.
#[test]
fn a_connective_head_declines() {
    let mut terms = TermStore::new();
    let [c, p, q, r] = ["c", "p", "q", "r"].map(|name| terms.mk_var(name, Sort::Bool));
    let then_atom = terms.mk_app(Symbol::named("or"), [p, q], Sort::Bool);
    let else_atom = terms.mk_app(Symbol::named("or"), [p, r], Sort::Bool);
    let exact_lift = terms.mk_ite_raw(c, then_atom, else_atom);
    assert_eq!(
        AlethePrinter::new(&terms).format_term(exact_lift),
        "(ite c (or p q) (or p r))"
    );
    assert_eq!(derive(&terms, "(or p (ite c q r))", exact_lift), None);
}

/// Two stacked updates (`snew = s.update(1, val).update(2, w)`): the lift of
/// the authored atom meets the canonical formula only through `cong` over the
/// canonical OUTER `ite`, whose else branch is itself a lift.
#[test]
fn a_nested_lift_reaches_the_canonical_formula_through_cong_over_ite() {
    let mut terms = TermStore::new();
    let array = Sort::array(Sort::Int, Sort::Int);
    let s = terms.mk_var("s", array.clone());
    let snew = terms.mk_var("snew", array);
    let val = terms.mk_var("val", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let [zero, one, two] = [0, 1, 2].map(|value| terms.mk_int(BigInt::from(value)));
    let read_new = terms.mk_app(Symbol::named("select"), [snew, zero], Sort::Int);
    let read_old = terms.mk_app(Symbol::named("select"), [s, zero], Sort::Int);
    let at_one = terms.mk_app(Symbol::named("="), [one, zero], Sort::Bool);
    let at_two = terms.mk_app(Symbol::named("="), [two, zero], Sort::Bool);
    let first = terms.mk_app(Symbol::named("="), [val, read_new], Sort::Bool);
    let second = terms.mk_app(Symbol::named("="), [w, read_new], Sort::Bool);
    let framed = terms.mk_app(Symbol::named("="), [read_new, read_old], Sort::Bool);
    let inner = terms.mk_ite_raw(at_two, second, framed);
    let instance = terms.mk_ite_raw(at_one, first, inner);
    let steps = derive(
        &terms,
        "(= (select snew 0) (ite (= 0 1) val (ite (= 0 2) w (select s 0))))",
        instance,
    )
    .expect("the nested lift is one cong over the canonical ite away");
    assert_eq!(
        steps.last().map(String::as_str),
        Some(
            "(step t9.n (cl (= (= (select snew 0) (ite (= 0 1) val (ite (= 0 2) w (select s 0)))) \
             (ite (= 1 0) (= val (select snew 0)) (ite (= 2 0) (= w (select snew 0)) \
             (= (select snew 0) (select s 0)))))) :rule trans :premises (t9.n.sl t9.n.lc))"
        )
    );
    assert!(
        steps.iter().any(|step| step
            == "(step t9.n.lc (cl (= (ite (= 0 1) (= (select snew 0) val) \
                (= (select snew 0) (ite (= 0 2) w (select s 0)))) \
                (ite (= 1 0) (= val (select snew 0)) (ite (= 2 0) (= w (select snew 0)) \
                (= (select snew 0) (select s 0)))))) \
                :rule cong :premises (t9.n.lc.c0 t9.n.lc.c1 t9.n.lc.c2))"),
        "{steps:#?}"
    );
    // The inner lift is derived under the outer `cong`'s else-branch leg.
    assert!(
        steps
            .iter()
            .any(|step| step.starts_with("(step t9.n.lc.c2.sl.ii ")),
        "{steps:#?}"
    );
}

/// A canonical term that is not a Boolean `ite` is outside the schema even
/// when the surface carries an `ite` argument.
#[test]
fn a_non_ite_canonical_term_declines() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let equality = terms.mk_app(Symbol::named("="), [x, y], Sort::Bool);
    assert_eq!(derive(&terms, "(= x (ite (= x y) y y))", equality), None);
}
