// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{
    nullary_definition_assume_bridge_is_supported, try_export_alethe_with_authored_surfaces,
    AletheAuthoredSurfaces,
};
use ay_core::{Symbol, TermStore};
use std::process::Command;

/// `(= v0 <value>)` over a one-bit `v0`, built raw so the canonical text is
/// exactly `(= v0 <value>)`, plus its negation.
fn one_bit_contradiction(terms: &mut TermStore, value: TermId) -> (TermId, TermId) {
    let v0 = terms.mk_var("v0", Sort::bitvec(1));
    let root = terms.mk_app(Symbol::named("="), [v0, value], Sort::Bool);
    let negated = terms.mk_not_raw(root);
    (root, negated)
}

/// `assume root` (spelled `surface`), `assume (not root)`, `(cl)`.
fn export(
    terms: &TermStore,
    root: TermId,
    negated: TermId,
    surface: &str,
    definitions: Option<&HashMap<String, String>>,
) -> Result<String, AlethePrintError> {
    let mut proof = Proof::new();
    let positive = proof.add_assume(root, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(vec![], root, positive, negative);
    let mut overrides = HashMap::default();
    overrides.insert(root, surface.to_string());
    try_export_alethe_with_authored_surfaces(
        &proof,
        terms,
        &[root, negated],
        Some(&overrides),
        AletheAuthoredSurfaces {
            negation_shell_assumes: None,
            nullary_definitions: definitions,
        },
        None,
    )
}

fn table(entries: &[(&str, &str)]) -> HashMap<String, String> {
    entries
        .iter()
        .map(|(name, body)| ((*name).to_string(), (*body).to_string()))
        .collect()
}

/// Pinned carcara's first verdict line with no allowance, or `None` when it
/// is not on PATH (the replay is then skipped, never passed).
fn carcara_verdict(case: &str, problem: &str, proof: &str) -> Option<String> {
    if let Err(misjudged) = ay_core::pinned_carcara::pinned_carcara_can_judge(problem, proof) {
        panic!("{case}: {misjudged}\n{proof}");
    }
    let probe = Command::new("carcara").arg("--version").output();
    if !probe.is_ok_and(|probe| probe.status.success()) {
        eprintln!("carcara not on PATH: the {case} replay is skipped");
        return None;
    }
    let dir = std::env::temp_dir().join(format!(
        "ay-nullary-definition-{}-{case}",
        std::process::id()
    ));
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
    let stdout = String::from_utf8_lossy(&output.stdout);
    let verdict = stdout.lines().last().unwrap_or("").trim().to_string();
    let stderr = String::from_utf8_lossy(&output.stderr);
    if verdict == "valid" {
        let _ = std::fs::remove_dir_all(&dir);
    }
    Some(format!("{verdict}\n{stderr}\nkept: {}", dir.display()))
}

/// NEGATIVE CONTROL: the replay refuses, before the checker runs (so with or
/// without carcara on PATH), the pair pinned carcara prints `valid` for only
/// through its `evaluate` defect (`ay_core::pinned_carcara`).
#[test]
#[should_panic(expected = "is not evidence")]
fn the_carcara_replay_refuses_a_document_pinned_carcara_misjudges() {
    carcara_verdict(
        "false_valid_control",
        ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROBLEM,
        ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROOF,
    );
}

fn assert_carcara_valid(case: &str, problem: &str, proof: &str) {
    if let Some(verdict) = carcara_verdict(case, problem, proof) {
        assert_eq!(
            verdict.lines().next().unwrap_or(""),
            "valid",
            "{case}: {verdict}\n{proof}"
        );
    }
}

#[test]
fn authored_macro_assume_is_bridged_through_the_definition_premise() {
    let mut terms = TermStore::new();
    let one = terms.mk_bitvec(1.into(), 1);
    let (root, negated) = one_bit_contradiction(&mut terms, one);
    let definitions = table(&[("one", "#b1")]);
    assert!(nullary_definition_assume_bridge_is_supported(
        &terms,
        root,
        "(= v0 one)",
        &definitions
    ));
    let proof = export(&terms, root, negated, "(= v0 one)", Some(&definitions))
        .expect("the definition premise bridges the authored spelling");
    assert!(proof.contains("(assume t0.a (= v0 one))"), "{proof}");
    assert!(proof.contains("(assume t0.n.c1 (= one #b1))"), "{proof}");
    assert!(
        proof.contains("(step t0 (cl (= v0 #b1)) :rule resolution"),
        "{proof}"
    );
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "{proof}"
    );
    assert_carcara_valid(
        "flat",
        "(set-logic ALL)\n(declare-const v0 (_ BitVec 1))\n\
         (define-fun one () (_ BitVec 1) #b1)\n(assert (= v0 one))\n\
         (assert (not (= v0 #b1)))\n(check-sat)\n",
        &proof,
    );
}

#[test]
fn a_macro_body_naming_another_macro_is_bridged_with_trans() {
    let mut terms = TermStore::new();
    let zero = terms.mk_bitvec(0.into(), 1);
    let flipped = terms.mk_app(Symbol::named("bvnot"), [zero], Sort::bitvec(1));
    let (root, negated) = one_bit_contradiction(&mut terms, flipped);
    let definitions = table(&[("zero", "#b0"), ("flip", "(bvnot zero)")]);
    let proof = export(&terms, root, negated, "(= v0 flip)", Some(&definitions))
        .expect("nested definitions bridge recursively");
    assert!(
        proof.contains("(assume t0.n.c1.d (= flip (bvnot zero)))"),
        "{proof}"
    );
    assert!(
        proof.contains("(assume t0.n.c1.b.c0 (= zero #b0))"),
        "{proof}"
    );
    assert!(proof.contains(":rule trans"), "{proof}");
    assert_carcara_valid(
        "nested",
        "(set-logic ALL)\n(declare-const v0 (_ BitVec 1))\n\
         (define-fun zero () (_ BitVec 1) #b0)\n(define-fun flip () (_ BitVec 1) (bvnot zero))\n\
         (assert (= v0 flip))\n(assert (not (= v0 (bvnot #b0))))\n(check-sat)\n",
        &proof,
    );
}

/// Negative twin: a body that is not the canonical text is never assumed as
/// the leaf's equality, and without a table nothing changes at all.
#[test]
fn a_mismatched_or_missing_definition_never_assumes_a_premise() {
    let mut terms = TermStore::new();
    let one = terms.mk_bitvec(1.into(), 1);
    let (root, negated) = one_bit_contradiction(&mut terms, one);
    let wrong = table(&[("one", "#b0")]);
    assert!(!nullary_definition_assume_bridge_is_supported(
        &terms,
        root,
        "(= v0 one)",
        &wrong
    ));
    assert!(!nullary_definition_assume_bridge_is_supported(
        &terms,
        root,
        "(= v0 one)",
        &HashMap::default()
    ));
    // Whatever the ordinary path renders (or refuses) without a table is
    // exactly what a non-matching table renders: no premise is invented.
    let mismatched = format!(
        "{:?}",
        export(&terms, root, negated, "(= v0 one)", Some(&wrong))
    );
    let without = format!("{:?}", export(&terms, root, negated, "(= v0 one)", None));
    assert_eq!(mismatched, without);
    assert!(!mismatched.contains("(= one #b"), "{mismatched}");
}

/// `(not (= v0 #b1))` built raw, its raw negation, and the one-row refutation
/// over them, for a Bool macro `lo` whose body is `(= v0 #b1)`.
fn negated_macro_refutation(terms: &mut TermStore) -> (TermId, TermId, Proof) {
    let one = terms.mk_bitvec(1.into(), 1);
    let (inner, _) = one_bit_contradiction(terms, one);
    let root = terms.mk_not_raw(inner);
    let negated = terms.mk_not_raw(root);
    let mut proof = Proof::new();
    let positive = proof.add_assume(root, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(vec![], root, positive, negative);
    (root, negated, proof)
}

/// `(assert (not lo))` over `(define-fun lo () Bool (= v0 #b1))`: the
/// canonical root is a `not`, which is a term constructor rather than a
/// symbol application, and the definition schema bridges it with `cong` over
/// the definition leaf. Before that arm the bridge declined and the query
/// published the expanded `(assume t0 (not ..))` pinned carcara refuses.
#[test]
fn a_negated_macro_assume_is_bridged_by_cong_under_not() {
    let mut terms = TermStore::new();
    let (root, negated, _) = negated_macro_refutation(&mut terms);
    let definitions = table(&[("lo", "(= v0 #b1)")]);
    assert!(nullary_definition_assume_bridge_is_supported(
        &terms,
        root,
        "(not lo)",
        &definitions
    ));
    let proof = export(&terms, root, negated, "(not lo)", Some(&definitions))
        .expect("the definition premise bridges the negated macro");
    assert!(proof.contains("(assume t0.a (not lo))"), "{proof}");
    assert!(
        proof.contains("(assume t0.n.c0 (= lo (= v0 #b1)))"),
        "{proof}"
    );
    assert!(
        proof.contains("(step t0.n (cl (= (not lo) (not (= v0 #b1)))) :rule cong"),
        "{proof}"
    );
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "{proof}"
    );
    assert_carcara_valid(
        "negated",
        "(set-logic ALL)\n(declare-const v0 (_ BitVec 1))\n\
         (define-fun lo () Bool (= v0 #b1))\n(assert (not lo))\n\
         (assert (not (not (= v0 #b1))))\n(check-sat)\n",
        &proof,
    );
}

/// Negative twins of the `not` arm: without a table the ordinary schema never
/// treats `not` as a congruence head, and a body that is not the term never
/// becomes a leaf.
#[test]
fn a_negated_macro_without_its_definition_is_never_bridged() {
    let mut terms = TermStore::new();
    let (root, negated, _) = negated_macro_refutation(&mut terms);
    let wrong = table(&[("lo", "(= v0 #b0)")]);
    assert!(!nullary_definition_assume_bridge_is_supported(
        &terms, root, "(not lo)", &wrong
    ));
    let without = format!("{:?}", export(&terms, root, negated, "(not lo)", None));
    assert!(!without.contains(":rule cong"), "{without}");
    assert!(!without.contains("(= lo "), "{without}");
    let mismatched = format!(
        "{:?}",
        export(&terms, root, negated, "(not lo)", Some(&wrong))
    );
    assert_eq!(mismatched, without);
}

/// The wire channel a publication screen judges is the exporter's: a macro
/// spelling the planner confines through the table leaves the channel, and
/// without the table it stays, as if it rode the whole document.
#[test]
fn the_wire_channel_confines_a_macro_spelling_only_with_its_table() {
    let mut terms = TermStore::new();
    let (root, _, proof) = negated_macro_refutation(&mut terms);
    let mut overrides = HashMap::default();
    overrides.insert(root, "(not lo)".to_string());
    let definitions = table(&[("lo", "(= v0 #b1)")]);
    let planned = crate::effective_wire_term_overrides_for_authored_proof(
        &proof,
        &terms,
        Some(&overrides),
        AletheAuthoredSurfaces {
            negation_shell_assumes: None,
            nullary_definitions: Some(&definitions),
        },
    )
    .expect("plans");
    assert!(
        planned.as_ref().is_some_and(|map| !map.contains_key(&root)),
        "{planned:?}"
    );
    let unplanned =
        crate::effective_wire_term_overrides_for_proof(&proof, &terms, Some(&overrides))
            .expect("plans");
    assert_eq!(
        unplanned
            .as_ref()
            .and_then(|map| map.get(&root))
            .map(String::as_str),
        Some("(not lo)")
    );
}

/// `(assert (not (not lo)))` over `(define-fun lo () Bool (= v0 #b1))`:
/// `mk_not` drops the double negation, so the canonical root is `lo`'s body
/// and no `not` head is left for `cong`. `not_simplify` strips the authored
/// shells and the definition premise bridges `lo`.
#[test]
fn a_double_negated_macro_assume_is_stripped_with_not_simplify() {
    let mut terms = TermStore::new();
    let one = terms.mk_bitvec(1.into(), 1);
    let (root, negated) = one_bit_contradiction(&mut terms, one);
    let definitions = table(&[("lo", "(= v0 #b1)")]);
    assert!(nullary_definition_assume_bridge_is_supported(
        &terms,
        root,
        "(not (not lo))",
        &definitions
    ));
    let proof = export(&terms, root, negated, "(not (not lo))", Some(&definitions))
        .expect("not_simplify and the definition premise bridge the double negation");
    assert!(proof.contains("(assume t0.a (not (not lo)))"), "{proof}");
    assert!(
        proof.contains("(step t0.n.nn (cl (= (not (not lo)) lo)) :rule not_simplify)"),
        "{proof}"
    );
    assert!(
        proof.contains("(assume t0.n.nb (= lo (= v0 #b1)))"),
        "{proof}"
    );
    assert!(
        proof.contains(
            "(step t0.n (cl (= (not (not lo)) (= v0 #b1))) :rule trans :premises (t0.n.nn t0.n.nb))"
        ),
        "{proof}"
    );
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "{proof}"
    );
    assert_carcara_valid(
        "double_negated",
        "(set-logic ALL)\n(declare-const v0 (_ BitVec 1))\n\
         (define-fun lo () Bool (= v0 #b1))\n(assert (not (not lo)))\n\
         (assert (not (= v0 #b1)))\n(check-sat)\n",
        &proof,
    );
}

/// Negative twins of the double-negation strip: an odd number of `not`s is a
/// different assertion and is never bridged, and neither a missing nor a
/// mismatched definition turns the strip into a premise.
#[test]
fn an_odd_negation_or_a_missing_definition_is_never_stripped() {
    let mut terms = TermStore::new();
    let one = terms.mk_bitvec(1.into(), 1);
    let (root, negated) = one_bit_contradiction(&mut terms, one);
    let definitions = table(&[("lo", "(= v0 #b1)")]);
    for odd in ["(not lo)", "(not (not (not lo)))"] {
        assert!(
            !nullary_definition_assume_bridge_is_supported(&terms, root, odd, &definitions),
            "{odd}"
        );
    }
    let wrong = table(&[("lo", "(= v0 #b0)")]);
    assert!(!nullary_definition_assume_bridge_is_supported(
        &terms,
        root,
        "(not (not lo))",
        &wrong
    ));
    let without = format!(
        "{:?}",
        export(&terms, root, negated, "(not (not lo))", None)
    );
    assert!(!without.contains(":rule not_simplify"), "{without}");
    assert!(!without.contains("(= lo "), "{without}");
    let mismatched = format!(
        "{:?}",
        export(&terms, root, negated, "(not (not lo))", Some(&wrong))
    );
    assert_eq!(mismatched, without);
}

// EXPLICIT: this file is itself loaded through a `#[path]`, so a bare
// `mod leaf_tests;` (or `mod ite_tests;`) would not resolve here.
#[path = "ite_tests.rs"]
mod ite_tests;
#[path = "leaf_tests.rs"]
mod leaf_tests;
#[path = "shared_body_tests.rs"]
mod shared_body_tests;
#[path = "swapped_tests.rs"]
mod swapped_tests;
