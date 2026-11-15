// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The order-reversal congruence bridge over a premise whose printed spelling
//! commutes a multiplication, and its fail-closed twin.

use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, Sort, Symbol, TermId, TermStore};

use crate::{try_export_alethe_with_problem_scope_and_overrides, AlethePrintError};

/// The `QF_LIA` cascade shape at 5fb7fc52a (`(assert (= x1 (* 3 m1)))` with
/// `(assert (not (> x1 60000)))`, step t107): the internal congruence
/// `(= (< k x) (< k (* m 3)))` over the premise `(= x (* m 3))`, printed with
/// the comparison's authored `(> x k)`, the product's authored `(* 3 m)`, and
/// the premise under `premise_spelling`, its surface override if any.
fn export(premise_spelling: Option<&str>) -> Result<String, AlethePrintError> {
    let mut terms = TermStore::new();
    let k = terms.mk_var("k", Sort::Int);
    let x = terms.mk_var("x", Sort::Int);
    let m = terms.mk_var("m", Sort::Int);
    let three = terms.mk_int(3.into());
    let product = terms.mk_app(Symbol::named("*"), [m, three], Sort::Int);
    let premise = terms.mk_app(Symbol::named("="), [x, product], Sort::Bool);
    let lower_x = terms.mk_app(Symbol::named("<"), [k, x], Sort::Bool);
    let lower_product = terms.mk_app(Symbol::named("<"), [k, product], Sort::Bool);
    let conclusion = terms.mk_app(Symbol::named("="), [lower_x, lower_product], Sort::Bool);

    let mut proof = Proof::new();
    let assumed = proof.add_assume(premise, None);
    proof.add_rule_step(AletheRule::Cong, vec![conclusion], vec![assumed], vec![]);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(lower_x, "(> x k)".to_string());
    overrides.insert(product, "(* 3 m)".to_string());
    if let Some(spelling) = premise_spelling {
        overrides.insert(premise, spelling.to_string());
    }
    try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[premise, conclusion],
        Some(&overrides),
    )
}

const REPAIRED: &str = "(step t1.norm.s0 (cl (= (> x k) (not (<= x k)))) :rule comp_simplify)\n\
     (step t1.norm.s1 (cl (= (not (<= x k)) (< k x))) :rule comp_simplify)\n\
     (step t1.norm (cl (= (> x k) (< k x))) :rule trans :premises (t1.norm.s0 t1.norm.s1))\n\
     (step t1.cong.ac0.r (cl (= (* m 3) (* 3 m))) :rule aci_simp)\n\
     (step t1.cong.ac0 (cl (= x (* 3 m))) :rule trans :premises (t0 t1.cong.ac0.r))\n\
     (step t1.cong (cl (= (< k x) (< k (* 3 m)))) :rule cong :premises (t1.cong.ac0))\n\
     (step t1 (cl (= (> x k) (< k (* 3 m)))) :rule trans :premises (t1.norm t1.cong))";

/// The authored premise `(= x (* 3 m))` is bridged to its canonical
/// rendering `(= x (* m 3))` at the `assume`, and every later step prints
/// that. The order bridge now repairs it with the multiplication bridge's
/// checked `aci_simp` + `trans`, applies same-operator `cong`, and composes
/// it with the strict comparison reversal. Before, the premise had to print
/// exactly `(= x (* 3 m))`, the bridge declined, and the different-operator
/// guard refused the whole document.
#[test]
fn the_authored_assume_rendering_is_repaired_under_the_order_bridge() {
    let output = export(Some("(= x (* 3 m))")).expect("the bridge repairs the premise");
    assert!(
        output.contains("(step t0 (cl (= x (* m 3))) :rule resolution"),
        "{output}"
    );
    assert!(output.contains(REPAIRED), "{output}");
}

/// The same repair when the premise's own override is the canonical text.
#[test]
fn a_commuted_premise_spelling_is_repaired_under_the_order_bridge() {
    let output = export(Some("(= x (* m 3))")).expect("the bridge repairs the premise");
    assert!(output.contains(REPAIRED), "{output}");
}

/// A premise that already prints as the differing pair is cited as is, so
/// every step that rendered before renders byte-identically.
#[test]
fn a_matching_premise_spelling_is_cited_unchanged() {
    let output = export(None).expect("exact premise");
    assert!(
        output.contains(
            "(step t1.cong (cl (= (< k x) (< k (* 3 m)))) :rule cong :premises (t0))\n\
             (step t1 (cl (= (> x k) (< k (* 3 m)))) :rule trans :premises (t1.norm t1.cong))"
        ),
        "{output}"
    );
    assert!(!output.contains("t1.cong.ac0"), "{output}");
}

/// NEGATIVE TWIN: a printed premise that is not a certified re-spelling of
/// the differing pair (`(* m 4)` is no commutation of `(* 3 m)`) gets no
/// bridge; the different-operator guard still refuses the step.
#[test]
fn an_unrelated_premise_spelling_keeps_the_refusal() {
    let error = export(Some("(= x (* m 4))")).expect_err("no certified repair");
    assert!(
        matches!(
            &error,
            AlethePrintError::InvalidCongruenceStep { reason, .. }
                if reason.contains("different order operators")
        ),
        "{error:?}"
    );
}

/// A premise that is not an `assume` and prints as the differing pair in the
/// FLIPPED orientation — its override keeps the authored `(= (* 3 m) x)`
/// while `mk_eq` interned `(= x (* m 3))` — is cited as is, since `cong`
/// accepts a flipped premise: exactly the step the order bridge printed
/// before the positional repair existed. The repair alone pairs `(* 3 m)`
/// with `x`, finds no certified identity and no authored `assume` to cite,
/// and the different-operator guard refuses the whole document.
#[test]
fn a_flipped_derived_premise_is_cited_unchanged() {
    let mut terms = TermStore::new();
    let k = terms.mk_var("k", Sort::Int);
    let x = terms.mk_var("x", Sort::Int);
    let m = terms.mk_var("m", Sort::Int);
    let three = terms.mk_int(3.into());
    let product = terms.mk_app(Symbol::named("*"), [m, three], Sort::Int);
    let premise = terms.mk_app(Symbol::named("="), [x, product], Sort::Bool);
    let lower_x = terms.mk_app(Symbol::named("<"), [k, x], Sort::Bool);
    let lower_product = terms.mk_app(Symbol::named("<"), [k, product], Sort::Bool);
    let conclusion = terms.mk_app(Symbol::named("="), [lower_x, lower_product], Sort::Bool);

    let mut proof = Proof::new();
    let derived = proof.add_rule_step(AletheRule::Hole, vec![premise], vec![], vec![]);
    proof.add_rule_step(AletheRule::Cong, vec![conclusion], vec![derived], vec![]);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(lower_x, "(> x k)".to_string());
    overrides.insert(product, "(* 3 m)".to_string());
    overrides.insert(premise, "(= (* 3 m) x)".to_string());
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[conclusion],
        Some(&overrides),
    )
    .expect("a flipped printed premise is still the differing pair");
    assert!(
        output.contains(
            "(step t1.cong (cl (= (< k x) (< k (* 3 m)))) :rule cong :premises (t0))\n\
             (step t1 (cl (= (> x k) (< k (* 3 m)))) :rule trans :premises (t1.norm t1.cong))"
        ),
        "{output}"
    );
}
