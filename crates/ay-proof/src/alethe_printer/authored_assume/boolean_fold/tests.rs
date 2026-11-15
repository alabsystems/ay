// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The Boolean-fold mirror computes exactly carcara's one-step results, the
//! printer bridges a folded authored `assume` with them, and every document
//! it emits is replayed by pinned carcara when it is on PATH.

use super::mirror::*;
use super::normalize::fold_surface;
use super::*;
use crate::{
    folded_authored_assume_bridge_is_supported, try_export_alethe_with_problem_scope_and_overrides,
};
use ay_core::{Proof, Symbol, TermStore};
use num_bigint::BigInt;
use std::process::Command;

fn texts(operands: &[&str]) -> Vec<String> {
    operands
        .iter()
        .map(|operand| (*operand).to_string())
        .collect()
}

#[test]
fn and_or_simplify_mirrors_carcaras_generic_and_or_simplify() {
    let and = |operands: &[&str]| and_or_simplify(&texts(operands), true);
    let or = |operands: &[&str]| and_or_simplify(&texts(operands), false);
    assert_eq!(and(&["A", "true"]).as_deref(), Some("A"));
    assert_eq!(and(&["A", "A"]).as_deref(), Some("A"));
    assert_eq!(and(&["A"]).as_deref(), Some("A"));
    assert_eq!(and(&["true", "true"]).as_deref(), Some("true"));
    assert_eq!(and(&["A", "B", "true"]).as_deref(), Some("(and A B)"));
    assert_eq!(and(&["A", "false"]).as_deref(), Some("false"));
    assert_eq!(and(&["A", "(not (not (not A)))"]).as_deref(), Some("false"));
    assert_eq!(or(&["A", "false"]).as_deref(), Some("A"));
    assert_eq!(or(&["false", "A", "A"]).as_deref(), Some("A"));
    assert_eq!(or(&["A", "true"]).as_deref(), Some("true"));
    assert_eq!(or(&["(not A)", "A"]).as_deref(), Some("true"));
    // Repeated operands are one term to carcara's parser modulo bit-vector
    // literal spelling, and carcara keeps the first.
    assert_eq!(
        and(&["(bvult x #x03)", "(bvult x #b00000011)"]).as_deref(),
        Some("(bvult x #x03)")
    );
}

/// NEGATIVE TWIN: what carcara's rule cannot state or does not change is
/// never emitted. A single survivor that is itself a conjunction is read by
/// carcara as ITS operands (`(= (and (and p q) true) (and p q))` is refused),
/// and a unary conjunction of a conjunction is unwrapped by carcara first.
#[test]
fn and_or_simplify_declines_what_carcara_cannot_state() {
    let and = |operands: &[&str]| and_or_simplify(&texts(operands), true);
    assert_eq!(and(&["(and p q)", "true"]), None);
    assert_eq!(and(&["(and p q)"]), None);
    assert_eq!(and(&["A", "B"]), None);
    assert_eq!(and_or_simplify(&texts(&["(or p q)", "false"]), false), None);
}

#[test]
fn one_step_rules_take_carcaras_first_matching_pattern() {
    assert_eq!(not_simplify("(not A)").as_deref(), Some("A"));
    assert_eq!(not_simplify("false").as_deref(), Some("true"));
    assert_eq!(not_simplify("A"), None);
    let eq = |left: &str, right: &str| equality_simplify(left, right);
    assert_eq!(
        eq("A", "A"),
        Some((FoldRule::EqSimplify, "true".to_string()))
    );
    assert_eq!(
        eq("A", "true"),
        Some((FoldRule::EquivSimplify, "A".to_string()))
    );
    assert_eq!(
        eq("true", "A"),
        Some((FoldRule::EquivSimplify, "A".to_string()))
    );
    assert_eq!(
        eq("A", "false"),
        Some((FoldRule::EquivSimplify, "(not A)".to_string()))
    );
    // `(= (not a) (not b))` is carcara's FIRST pattern, ahead of the constants.
    assert_eq!(
        eq("(not A)", "(not true)"),
        Some((FoldRule::EquivSimplify, "(= A true)".to_string()))
    );
    assert_eq!(
        eq("A", "(not A)"),
        Some((FoldRule::EquivSimplify, "false".to_string()))
    );
    assert_eq!(eq("A", "B"), None);
    // `(ite c t t)` comes before the negated-condition swap.
    assert_eq!(ite_simplify("(not c)", "A", "A").as_deref(), Some("A"));
    assert_eq!(
        ite_simplify("(not c)", "A", "B").as_deref(),
        Some("(ite c B A)")
    );
    assert_eq!(ite_simplify("true", "A", "B").as_deref(), Some("A"));
    assert_eq!(
        ite_simplify("c", "false", "true").as_deref(),
        Some("(not c)")
    );
    assert_eq!(ite_simplify("c", "(ite c A B)", "C"), None);
    assert_eq!(implies_simplify("true", "A").as_deref(), Some("A"));
    assert_eq!(implies_simplify("A", "false").as_deref(), Some("(not A)"));
    assert_eq!(
        implies_simplify("(not A)", "(not B)").as_deref(),
        Some("(=> B A)")
    );
}

#[test]
fn a_nested_fold_chains_cong_and_trans_bottom_up() {
    let mut nodes = 0;
    let (folded, steps, structural) =
        fold_surface("(not (and (not A) (= x x)))", "t0.n", 0, &mut nodes).expect("folds");
    assert_eq!(folded, "A");
    assert!(structural);
    assert_eq!(
        steps,
        vec![
            "(step t0.n.a0.a1 (cl (= (= x x) true)) :rule eq_simplify)",
            "(step t0.n.a0.g (cl (= (and (not A) (= x x)) (and (not A) true))) :rule cong :premises (t0.n.a0.a1))",
            "(step t0.n.a0.s (cl (= (and (not A) true) (not A))) :rule and_simplify)",
            "(step t0.n.a0 (cl (= (and (not A) (= x x)) (not A))) :rule trans :premises (t0.n.a0.g t0.n.a0.s))",
            "(step t0.n.g (cl (= (not (and (not A) (= x x))) (not (not A)))) :rule cong :premises (t0.n.a0))",
            "(step t0.n.s (cl (= (not (not A)) A)) :rule not_simplify)",
            "(step t0.n (cl (= (not (and (not A) (= x x))) A)) :rule trans :premises (t0.n.g t0.n.s))",
        ]
    );
}

/// NEGATIVE TWIN: a pure connective re-spelling is no fold, and a surface
/// with an annotation is never read through.
#[test]
fn respelling_alone_is_not_a_fold() {
    let mut nodes = 0;
    let (folded, _, structural) =
        fold_surface("(distinct a b)", "t0", 0, &mut nodes).expect("re-spells");
    assert_eq!(folded, "(not (= a b))");
    assert!(!structural);
    assert!(fold_surface("(xor p q)", "t0", 0, &mut nodes).is_none());
    assert!(fold_reads_opaque_syntax("(or (! p :named n) false)"));
}

// ---------------------------------------------------------------------------
// Printer: the whole bridge, replayed by pinned carcara.
// ---------------------------------------------------------------------------

/// `(< x 3)` over Int, built raw, and its negation.
fn comparison(terms: &mut TermStore) -> (TermId, TermId) {
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let root = terms.mk_app(Symbol::named("<"), [x, three], Sort::Bool);
    (root, terms.mk_not_raw(root))
}

/// `assume root` spelled `surface`, `assume (not root)`, `(cl)`.
fn export(terms: &TermStore, root: TermId, negated: TermId, surface: &str) -> String {
    let mut proof = Proof::new();
    let positive = proof.add_assume(root, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(vec![], root, positive, negative);
    let mut overrides = HashMap::default();
    overrides.insert(root, surface.to_string());
    try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        terms,
        &[root, negated],
        Some(&overrides),
    )
    .expect("folded authored assume exports")
}

/// Pinned carcara's verdict line with no allowance, or `None` when it is not
/// on PATH (the replay is then skipped, never passed). Under `CI` a missing
/// carcara fails the test, as `require_carcara_or_skip` does in
/// `group_proofs`.
fn carcara_verdict(case: &str, problem: &str, proof: &str) -> Option<String> {
    let probe = Command::new("carcara").arg("--version").output();
    if !probe.is_ok_and(|probe| probe.status.success()) {
        assert!(
            std::env::var_os("CI").is_none(),
            "carcara not on PATH: the {case} replay is mandatory in CI"
        );
        eprintln!("carcara not on PATH: the {case} replay is skipped");
        return None;
    }
    let dir = std::env::temp_dir().join(format!("ay-boolean-fold-{}-{case}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("p.smt2"), problem).unwrap();
    std::fs::write(dir.join("p.alethe"), proof).unwrap();
    let output = Command::new("carcara")
        .arg("check")
        .arg("--expand-let-bindings")
        .arg("--")
        .arg(dir.join("p.alethe"))
        .arg(dir.join("p.smt2"))
        .output()
        .unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    Some(
        String::from_utf8_lossy(&output.stdout)
            .lines()
            .last()
            .unwrap_or("")
            .trim()
            .to_string(),
    )
}

#[test]
fn folded_authored_assumes_are_bridged_with_checked_simplification_steps() {
    for (case, surface, rule) in [
        ("or_false", "(or (< x 3) false)", ":rule or_simplify"),
        ("eq_true", "(= (< x 3) true)", ":rule equiv_simplify"),
        ("xor_false", "(xor (< x 3) false)", ":rule connective_def"),
        (
            "distinct_false",
            "(distinct (< x 3) false)",
            ":rule distinct_elim",
        ),
        ("ite_same", "(ite r (< x 3) (< x 3))", ":rule ite_simplify"),
        (
            "not_and_not",
            "(not (and (not (< x 3)) (= x x)))",
            ":rule not_simplify",
        ),
        ("imp_true", "(=> true (< x 3))", ":rule implies_simplify"),
    ] {
        let mut terms = TermStore::new();
        let (root, negated) = comparison(&mut terms);
        // `r` is only named by the authored `ite` spelling.
        let _ = terms.mk_var("r", Sort::Bool);
        assert!(
            folded_authored_assume_bridge_is_supported(&terms, root, surface),
            "{case}: the producer preflight admits the fold"
        );
        let proof = export(&terms, root, negated, surface);
        assert!(
            proof.starts_with(&format!("(assume t0.a {surface})")),
            "{case}:\n{proof}"
        );
        assert!(proof.contains(rule), "{case}:\n{proof}");
        assert!(
            proof.contains("(step t0 (cl (< x 3)) :rule resolution"),
            "{case}:\n{proof}"
        );
        assert!(!proof.contains(":rule hole"), "{case}:\n{proof}");
        let problem = format!(
            "(set-logic QF_LIA)\n(declare-const x Int)\n(declare-const r Bool)\n\
             (assert {surface})\n(assert (not (< x 3)))\n(check-sat)\n"
        );
        if let Some(verdict) = carcara_verdict(case, &problem, &proof) {
            assert_eq!(verdict, "valid", "{case}:\n{proof}");
        }
    }
}

/// NEGATIVE TWIN: a spelling that does not fold onto the canonical term is
/// never bridged. `(or (< x 4) false)` folds to `(< x 4)`, which no checked
/// step turns into `(< x 3)`; `(and (and (< x 3) (< x 4)) true)` would need
/// the `and_simplify` result carcara cannot state. The producer preflight
/// refuses both, so the restoring pass never installs them.
#[test]
fn a_spelling_that_does_not_fold_onto_the_canonical_term_is_refused() {
    let mut terms = TermStore::new();
    let (root, _) = comparison(&mut terms);
    for surface in [
        "(or (< x 4) false)",
        "(= (< x 3) false)",
        "(xor (< x 3) true)",
        "(or (! (< x 3) :named n) false)",
    ] {
        assert!(
            !folded_authored_assume_bridge_is_supported(&terms, root, surface),
            "{surface} must not be admitted"
        );
    }
    let x = terms.mk_var("x", Sort::Int);
    let four = terms.mk_int(BigInt::from(4));
    let other = terms.mk_app(Symbol::named("<"), [x, four], Sort::Bool);
    let conjunction = terms.mk_app(Symbol::named("and"), [root, other], Sort::Bool);
    assert!(!folded_authored_assume_bridge_is_supported(
        &terms,
        conjunction,
        "(and (and (< x 3) (< x 4)) true)"
    ));
}
