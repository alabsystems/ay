// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An `assume` leaf must print an assertion the PROBLEM states.
//!
//! `TermStore::mk_not` eliminates a double negation at term construction, so
//! `(assert (not (not phi)))` leaves the store holding only `phi`: no `TermId`
//! for the authored formula exists anywhere, and every term-keyed provenance
//! check therefore certifies AY's own rewriting as a premise of the query.
//! Measured on
//! `benchmarks/smtlib-all/QF_ABV/non-incremental__QF_ABV__egt__egt-6069.smt2`
//! at build 9538: `unproved_steps=0 foreign_assumes=no trust_free=yes
//! ay_self_checkable=yes` beside
//! `[ERROR] checking failed on step 't0' with rule 'assume'`.
//!
//! These tests pin the two halves of the repair: the emitted shape, and the
//! fail-closed behaviour when the promised authored text is not derivable from
//! the printed term.

use super::*;
use crate::try_export_alethe_with_authored_assume_shells;
use ay_core::AletheRule;

/// `assume phi` + `assume (not phi)` + a resolution to the empty clause, with
/// `phi` authored as `(not (not phi))`.
fn double_negated_leaf_proof() -> (TermStore, Proof, TermId, TermId) {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not(p);
    let mut proof = Proof::new();
    let positive = proof.add_assume(p, None);
    let negative = proof.add_assume(not_p, None);
    proof.add_resolution(vec![], p, positive, negative);
    (terms, proof, p, not_p)
}

#[test]
fn double_negation_elimination_is_invisible_to_the_term_store() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not(p);
    let not_not_p = terms.mk_not(not_p);
    assert_eq!(
        not_not_p, p,
        "the authored `(not (not p))` has no TermId of its own — which is why a \
         term-keyed foreign-assume check cannot see this defect at all"
    );
}

#[test]
fn authored_negation_shells_are_printed_at_the_leaf_and_derived() {
    let (terms, proof, p, not_p) = double_negated_leaf_proof();
    let mut shells = HashMap::default();
    shells.insert(p, "(not (not p))".to_string());
    let text = try_export_alethe_with_authored_assume_shells(
        &proof,
        &terms,
        &[p, not_p],
        None,
        Some(&shells),
        None,
    )
    .expect("the authored double negation must export");

    // The leaf carries the PROBLEM's spelling, under a side id.
    assert!(
        text.contains("(assume t0.a (not (not p)))"),
        "the assume must print what the problem asserts, got:\n{text}"
    );
    // `not_not` is `(cl (not (not (not psi))) psi)`.
    assert!(
        text.contains("(step t0.n1 (cl (not (not (not p))) p) :rule not_not)"),
        "the shells must be discharged by the stock rule, got:\n{text}"
    );
    // The ORIGINAL id still concludes the canonical unit every consumer cites.
    assert!(
        text.contains("(step t0 (cl p) :rule resolution :premises (t0.a t0.n1))"),
        "the original id must conclude the canonical unit, got:\n{text}"
    );
    assert!(
        !text.contains("(assume t0 p)"),
        "the rewritten leaf must not survive anywhere, got:\n{text}"
    );
}

#[test]
fn two_authored_shell_pairs_peel_one_pair_per_step() {
    let (terms, proof, p, not_p) = double_negated_leaf_proof();
    let mut shells = HashMap::default();
    shells.insert(p, "(not (not (not (not p))))".to_string());
    let text = try_export_alethe_with_authored_assume_shells(
        &proof,
        &terms,
        &[p, not_p],
        None,
        Some(&shells),
        None,
    )
    .expect("two authored shell pairs must export");
    assert!(
        text.contains("(assume t0.a (not (not (not (not p)))))"),
        "{text}"
    );
    assert!(
        text.contains(
            "(step t0.n2 (cl (not (not (not (not (not p))))) (not (not p))) :rule not_not)"
        ),
        "{text}"
    );
    assert!(
        text.contains("(step t0.r2 (cl (not (not p))) :rule resolution :premises (t0.a t0.n2))"),
        "{text}"
    );
    assert!(
        text.contains("(step t0.n1 (cl (not (not (not p))) p) :rule not_not)"),
        "{text}"
    );
    assert!(
        text.contains("(step t0 (cl p) :rule resolution :premises (t0.r2 t0.n1))"),
        "{text}"
    );
}

/// THE MUTATION DIFFERENTIAL. A promised authored spelling that is not the
/// printed term under negation shells must DECLINE the whole export, never
/// print the rewritten leaf and never print an underived one.
#[test]
fn an_authored_spelling_the_printer_cannot_derive_declines_the_export() {
    let (terms, proof, p, not_p) = double_negated_leaf_proof();
    for wrong in [
        // A different atom under the shells: `p` is not what is asserted.
        "(not (not q))",
        // An odd shell count: this is `(not p)`, a different formula.
        "(not (not (not p)))",
        // Not a shell shape at all.
        "(or p p)",
    ] {
        let mut shells = HashMap::default();
        shells.insert(p, wrong.to_string());
        let error = try_export_alethe_with_authored_assume_shells(
            &proof,
            &terms,
            &[p, not_p],
            None,
            Some(&shells),
            None,
        )
        .expect_err("a spelling the printer cannot derive must decline");
        assert!(
            matches!(
                error,
                AlethePrintError::InvalidSurfaceStep { ref reason, .. }
                    if reason.contains("negation shells")
            ),
            "expected a typed decline for {wrong}, got: {error}"
        );
    }
}

#[test]
fn no_shell_map_prints_exactly_what_it_printed_before() {
    let (terms, proof, p, not_p) = double_negated_leaf_proof();
    let with_none = try_export_alethe_with_authored_assume_shells(
        &proof,
        &terms,
        &[p, not_p],
        None,
        None,
        None,
    )
    .expect("the unmapped export must be unchanged");
    let empty = HashMap::default();
    let with_empty = try_export_alethe_with_authored_assume_shells(
        &proof,
        &terms,
        &[p, not_p],
        None,
        Some(&empty),
        None,
    )
    .expect("an empty shell map must be inert");
    assert_eq!(with_none, with_empty);
    assert!(with_none.contains("(assume t0 p)"), "{with_none}");
}

#[test]
fn shell_admission_is_purely_textual_and_bounded() {
    use crate::negation_shell_assume_surface_pairs as pairs;
    assert_eq!(pairs("(not (not p))", "p"), Some(1));
    assert_eq!(pairs("(not (not (not (not p))))", "p"), Some(2));
    // An assume already spelled as the problem writes it needs no bridge.
    assert_eq!(pairs("p", "p"), None);
    // One shell is a DIFFERENT formula, not a shell pair over `p`.
    assert_eq!(pairs("(not p)", "p"), None);
    // The peel is anchored at both ends: a suffix that is not the closing pair
    // must not be accepted.
    assert_eq!(pairs("(not (not p) q)", "p"), None);
    let huge = "x".repeat(authored_assume::MAX_EQUIVALENCE_BYTES + 1);
    assert_eq!(
        pairs(&format!("(not (not {huge}))"), &huge),
        None,
        "an unbounded spelling must decline rather than peel"
    );
}

#[test]
fn a_rule_step_never_consults_the_shell_map() {
    // The map is an ASSUME-leaf channel. A step mentioning the same term must
    // keep the canonical rendering, or the document contradicts itself.
    let (terms, proof, p, not_p) = double_negated_leaf_proof();
    let mut shells = HashMap::default();
    shells.insert(p, "(not (not p))".to_string());
    let text = try_export_alethe_with_authored_assume_shells(
        &proof,
        &terms,
        &[p, not_p],
        None,
        Some(&shells),
        None,
    )
    .expect("export");
    let resolution = text
        .lines()
        .find(|line| line.contains(":rule resolution") && line.contains("(cl)"))
        .unwrap_or_default();
    assert!(
        !resolution.contains("(not (not p))"),
        "the terminal resolution must cite the canonical unit, got: {resolution}"
    );
    let _ = AletheRule::Resolution;
}
