// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A premise-free tautology is judged over the clause text it SHIPS.
//!
//! `(assert (>= x 3))` interns as `(<= 3 x)`; its `assume` is bridged with
//! `comp_simplify`, so the atom prints canonically downstream. A descendant
//! override still spells the `not` above it `(not (>= x 3))` inside other
//! terms, while `format_clause` prints the clause literal `(not (<= 3 x))`
//! off the atom's confined rendering. MEASURED before the judge read shipped
//! literals: it compared `equiv_neg2`'s operand against the override text,
//! answered "the default is exact", and pinned carcara 1.1.0 refused the
//! default rendering ("expected terms to be equal: '(not (>= x 3))' and
//! '(not (<= 3 x))'") in a `trust_free=yes` document.

use super::surface_order_orientation_twin;
use crate::try_export_alethe_with_problem_scope_and_overrides;
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, Sort, Symbol, TermStore};
use std::process::Command;

/// `(assume (<= 3 x))`, `equiv_neg2` over `(= (not (<= 3 x)) false)`, and the
/// assumed negation of that equality, closed by resolution. `descendant`
/// records the `not`'s own authored spelling.
fn export(descendant: bool) -> String {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(3.into());
    let atom = terms.mk_app(Symbol::named("<="), [three, x], Sort::Bool);
    let negated = terms.mk_not_raw(atom);
    let falsity = terms.mk_bool(false);
    let not_false = terms.mk_not_raw(falsity);
    let equality = terms.mk_app(Symbol::named("="), [negated, falsity], Sort::Bool);
    let refuted = terms.mk_not_raw(equality);

    let mut proof = Proof::new();
    let assumed = proof.add_assume(atom, None);
    let tautology = proof.add_rule_step(
        AletheRule::EquivNeg2,
        vec![equality, negated, falsity],
        Vec::new(),
        Vec::new(),
    );
    let stripped = proof.add_resolution(vec![equality, falsity], atom, tautology, assumed);
    let axiom = proof.add_rule_step(AletheRule::False, vec![not_false], Vec::new(), Vec::new());
    let unit = proof.add_resolution(vec![equality], falsity, stripped, axiom);
    let negation = proof.add_assume(refuted, None);
    proof.add_resolution(vec![], equality, unit, negation);

    let mut overrides = DetHashMap::default();
    overrides.insert(atom, "(>= x 3)".to_string());
    if descendant {
        overrides.insert(negated, "(not (>= x 3))".to_string());
    }
    try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[atom, refuted],
        Some(&overrides),
    )
    .expect("the refutation renders")
}

/// Pinned carcara's verdict with no allowance, or `None` when it is not on
/// PATH (the replay is then skipped, never passed).
fn carcara_verdict(case: &str, refuted: &str, proof: &str) -> Option<String> {
    let problem = format!(
        "(set-logic ALL)\n(declare-const x Int)\n(assert (>= x 3))\n\
         (assert (not (= {refuted} false)))\n(check-sat)\n"
    );
    if let Err(misjudged) = ay_core::pinned_carcara::pinned_carcara_can_judge(&problem, proof) {
        panic!("{case}: {misjudged}\n{proof}");
    }
    let probe = Command::new("carcara").arg("--version").output();
    if !probe.is_ok_and(|probe| probe.status.success()) {
        eprintln!("carcara not on PATH: the {case} replay is skipped");
        return None;
    }
    let dir =
        std::env::temp_dir().join(format!("ay-derived-literal-{}-{case}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("p.smt2"), problem).unwrap();
    std::fs::write(dir.join("p.alethe"), proof).unwrap();
    let output = Command::new("carcara")
        .args(["check", "--expand-let-bindings", "--"])
        .arg(dir.join("p.alethe"))
        .arg(dir.join("p.smt2"))
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let verdict = stdout.lines().last().unwrap_or("").trim().to_string();
    if verdict == "valid" {
        let _ = std::fs::remove_dir_all(&dir);
    }
    Some(format!(
        "{verdict}\n{}\nkept: {}",
        String::from_utf8_lossy(&output.stderr),
        dir.display()
    ))
}

/// NEGATIVE CONTROL: the replay refuses, before the checker runs (so with or
/// without carcara on PATH), a refutation of this runner's own problem that
/// rests on one false `evaluate` step (`(bvsge #xf #xe)` is true, and the
/// problem is satisfiable), for which pinned carcara 1.1.0 prints `valid`
/// (measured with this exact pair; see `ay_core::pinned_carcara`).
#[test]
#[should_panic(expected = "is not evidence")]
fn the_carcara_replay_refuses_a_document_pinned_carcara_misjudges() {
    carcara_verdict(
        "false_valid_control",
        "(bvsge #xf #xe)",
        "(assume a1 (not (= (bvsge #xf #xe) false)))\n\
         (step t1 (cl (= (bvsge #xf #xe) false)) :rule evaluate)\n\
         (step t2 (cl) :rule resolution :premises (t1 a1))\n",
    );
}

fn assert_carcara_valid(case: &str, refuted: &str, proof: &str) {
    if let Some(verdict) = carcara_verdict(case, refuted, proof) {
        assert_eq!(
            verdict.lines().next().unwrap_or(""),
            "valid",
            "{case}: {verdict}\n{proof}"
        );
    }
}

#[test]
fn a_tautology_over_a_confined_atom_is_judged_on_its_shipped_literal() {
    let proof = export(true);
    assert!(
        proof.contains("(cl (>= x 3) (not (<= 3 x))) :rule la_generic :args (1 1))"),
        "the operand and the shipped literal are two orientations of one atom:\n{proof}"
    );
    assert!(
        !proof.contains("(cl (= (not (>= x 3)) false) (not (<= 3 x)) false) :rule equiv_neg2)"),
        "{proof}"
    );
    assert_carcara_valid("descendant", "(not (>= x 3))", &proof);
}

/// Negative twin: without the descendant spelling, the operand and the
/// literal print alike and the default rendering is kept.
#[test]
fn a_tautology_without_a_descendant_spelling_keeps_the_default_rendering() {
    let proof = export(false);
    assert!(
        proof.contains("(cl (= (not (<= 3 x)) false) (not (<= 3 x)) false) :rule equiv_neg2)"),
        "{proof}"
    );
    assert!(!proof.contains(":rule la_generic"), "{proof}");
    assert_carcara_valid("canonical", "(not (<= 3 x))", &proof);
}

#[test]
fn an_order_twin_is_read_directly_or_under_one_negation_only() {
    assert_eq!(
        surface_order_orientation_twin("(>= x 3)").as_deref(),
        Some("(<= 3 x)")
    );
    assert_eq!(
        surface_order_orientation_twin("(not (>= x 3))").as_deref(),
        Some("(not (<= 3 x))")
    );
    for none in ["(not (not (>= x 3)))", "(not (= x 3))", "(= x 3)", "p"] {
        assert_eq!(surface_order_orientation_twin(none), None, "{none}");
    }
}
