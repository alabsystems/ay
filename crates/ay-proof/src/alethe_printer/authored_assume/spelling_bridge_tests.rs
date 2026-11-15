// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The authored-assume bridges behind three refused publications
//! (`ay.proof.artifact-refused`): a Boolean fold onto the document's own
//! rendering (`boolean_fold::render_folded_document_equivalence`) and the
//! ancestor guard over printed terms only (`printed_terms`) here; the printed
//! equivalence re-planned against the commit's view in `post_commit_tests.rs`
//! and the operand-swapped comparison schema in
//! `comparison_reversal_tests.rs`, which share the helpers below.
//! Every document is replayed by pinned carcara when it is on PATH, and every
//! acceptance has a negative twin the printer must keep refusing.

use super::*;
use crate::try_export_alethe_with_problem_scope_and_overrides;
use ay_core::{AletheRule, Symbol, TermStore};
use num_bigint::BigInt;
use std::process::Command;

/// Pinned carcara's verdict line with no allowance, or `None` when it is not
/// on PATH (the replay is then skipped, never passed). Under `CI` a missing
/// carcara fails the test.
pub(super) fn carcara_verdict(case: &str, problem: &str, proof: &str) -> Option<String> {
    let probe = Command::new("carcara").arg("--version").output();
    if !probe.is_ok_and(|probe| probe.status.success()) {
        assert!(
            std::env::var_os("CI").is_none(),
            "carcara not on PATH: the {case} replay is mandatory in CI"
        );
        eprintln!("carcara not on PATH: the {case} replay is skipped");
        return None;
    }
    let dir =
        std::env::temp_dir().join(format!("ay-spelling-bridge-{}-{case}", std::process::id()));
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

pub(super) fn overrides(entries: &[(TermId, &str)]) -> HashMap<TermId, String> {
    entries
        .iter()
        .map(|(term, text)| (*term, (*text).to_string()))
        .collect()
}

pub(super) fn assert_valid(case: &str, problem: &str, proof: &str) {
    assert!(!proof.contains(":rule hole"), "{case}:\n{proof}");
    if let Some(verdict) = carcara_verdict(case, problem, proof) {
        assert_eq!(verdict, "valid", "{case}:\n{proof}");
    }
}

// ---------------------------------------------------------------------------
// The Boolean fold onto the document's rendering.

#[test]
fn a_fold_lands_on_the_documents_rendering_byte_for_byte_or_up_to_alpha() {
    let (exact, nodes) = boolean_fold::render_folded_document_equivalence(
        "t0",
        "(= (bvult b #x03) false)",
        "(not (bvult b #x03))",
    );
    assert!(nodes > 0);
    assert_eq!(
        exact.as_deref(),
        Some(
            "(assume t0.a (= (bvult b #x03) false))\n\
             (step t0.n (cl (= (= (bvult b #x03) false) (not (bvult b #x03)))) :rule equiv_simplify)\n\
             (step t0.e (cl (not (= (= (bvult b #x03) false) (not (bvult b #x03)))) (not (= (bvult b #x03) false)) (not (bvult b #x03))) :rule equiv_pos2)\n\
             (step t0 (cl (not (bvult b #x03))) :rule resolution :premises (t0.e t0.n t0.a))"
        )
    );
    let (alpha, _) = boolean_fold::render_folded_document_equivalence(
        "t1",
        "(or (= (* 3 m) x) false)",
        "(= x (* 3 m))",
    );
    let alpha = alpha.expect("an equality fold up to operand order is one refl");
    assert!(
        alpha.contains("(step t1.r (cl (= (= (* 3 m) x) (= x (* 3 m)))) :rule refl)"),
        "{alpha}"
    );
    assert!(
        alpha.ends_with("(step t1 (cl (= x (* 3 m))) :rule resolution :premises (t1.e t1.t t1.a))"),
        "{alpha}"
    );
}

/// NEGATIVE TWIN: the fold concludes nothing but its own result. A fold onto
/// the other polarity, onto another term, a mere connective re-spelling, and
/// a fold through a `let` are all declined.
#[test]
fn a_fold_that_does_not_reach_the_rendering_is_declined() {
    for (surface, rendering) in [
        ("(= (bvult b #x03) false)", "(bvult b #x03)"),
        ("(or (< x 4) false)", "(< x 3)"),
        ("(or (= a b) false)", "(= a c)"),
        ("(distinct a b)", "(not (= a b))"),
        ("(or (let ((q x)) (< q 3)) false)", "(< x 3)"),
        ("(< x 3)", "(< x 3)"),
    ] {
        assert_eq!(
            boolean_fold::render_folded_document_equivalence("t0", surface, rendering).0,
            None,
            "{surface} over {rendering}"
        );
    }
}

/// `(assume t0 neg)`, `(assume t1 atom)`, `(cl)`.
fn refutation(atom: TermId, negated: TermId) -> Proof {
    let mut proof = Proof::new();
    let negative = proof.add_assume(negated, None);
    let positive = proof.add_assume(atom, None);
    proof.add_resolution(vec![], atom, positive, negative);
    proof
}

#[test]
fn a_negative_fold_over_a_respelled_operand_is_bridged_onto_the_documents_rendering() {
    let mut terms = TermStore::new();
    let b = terms.mk_var("b", Sort::bitvec(8));
    let three = terms.mk_bitvec(BigInt::from(3), 8);
    let atom = terms.mk_app(Symbol::named("bvult"), [b, three], Sort::Bool);
    let negated = terms.mk_not_raw(atom);
    let proof = refutation(atom, negated);
    let table = overrides(&[
        (atom, "(bvult b #x03)"),
        (negated, "(= (bvult b #x03) false)"),
    ]);
    let document = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[negated, atom],
        Some(&table),
    )
    .expect("the negative fold is bridged onto the document's rendering");
    assert!(
        document.starts_with("(assume t0.a (= (bvult b #x03) false))\n"),
        "{document}"
    );
    assert!(
        document.contains("(step t0 (cl (not (bvult b #x03))) :rule resolution"),
        "{document}"
    );
    assert!(
        document.contains("(assume t1 (bvult b #x03))"),
        "{document}"
    );
    let problem = "(set-logic QF_BV)\n(declare-const b (_ BitVec 8))\n\
                   (assert (= (bvult b #x03) false))\n(assert (bvult b #x03))\n(check-sat)\n";
    assert_valid("negative_fold_bv", problem, &document);
}

#[test]
fn an_equality_fold_reaches_the_documents_rendering_up_to_operand_order() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let m = terms.mk_var("m", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let product = terms.mk_app(Symbol::named("*"), [m, three], Sort::Int);
    let atom = terms.mk_app(Symbol::named("="), [x, product], Sort::Bool);
    let negated = terms.mk_not_raw(atom);
    let mut proof = Proof::new();
    let positive = proof.add_assume(atom, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(vec![], atom, positive, negative);
    let table = overrides(&[(product, "(* 3 m)"), (atom, "(or (= (* 3 m) x) false)")]);
    let document = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[atom, negated],
        Some(&table),
    )
    .expect("the fold is bridged onto the document's rendering");
    assert!(
        document.contains("(step t0 (cl (= x (* 3 m))) :rule resolution"),
        "{document}"
    );
    assert!(document.contains(":rule refl"), "{document}");
    let problem = "(set-logic QF_LIA)\n(declare-const x Int)\n(declare-const m Int)\n\
                   (assert (or (= (* 3 m) x) false))\n(assert (not (= x (* 3 m))))\n(check-sat)\n";
    assert_valid("equality_fold_alpha", problem, &document);
}

// ---------------------------------------------------------------------------
// The ancestor guard reads printed overridden terms only.

#[test]
fn an_overridden_ancestor_the_proof_never_mentions_withholds_no_bridge() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let equality = terms.mk_app(Symbol::named("="), [x, y], Sort::Bool);
    let ancestor = terms.mk_not_raw(equality);
    let table = overrides(&[
        (equality, "(not (distinct x y))"),
        (ancestor, "(distinct x y)"),
    ]);
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&table));
    let mut proof = Proof::new();
    proof.add_assume(equality, None);
    let roots = printed_terms::printed_proof_roots(&proof).expect("known step shapes");
    let printed = printer
        .printed_terms_below(&roots)
        .expect("a quantifier-free proof is read completely");
    assert!(printed.contains(&equality) && printed.contains(&x));
    assert!(!printed.contains(&ancestor));
    let guarded = printer
        .strict_descendants_of_printed_overridden_terms(&roots)
        .expect("bounded");
    assert!(!guarded.contains(&equality), "{guarded:?}");
    let everything = printer
        .strict_descendants_of_overridden_terms()
        .expect("bounded");
    assert!(everything.contains(&equality), "{everything:?}");
}

/// `(assert (not (distinct x y)))` feeding a `cong`: the front end also
/// spells `(distinct x y)` onto the internal `(not (= x y))`, which the
/// refutation never mentions. Bridged, the `cong` reads the printed equality.
#[test]
fn an_unprinted_ancestor_override_lets_a_negated_distinct_feed_cong() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let equality = terms.mk_app(Symbol::named("="), [x, y], Sort::Bool);
    let ancestor = terms.mk_not_raw(equality);
    let p_x = terms.mk_app(Symbol::named("P"), [x], Sort::Bool);
    let p_y = terms.mk_app(Symbol::named("P"), [y], Sort::Bool);
    let not_p_x = terms.mk_not_raw(p_x);
    let not_p_y = terms.mk_not_raw(p_y);
    let lifted = terms.mk_app(Symbol::named("="), [p_x, p_y], Sort::Bool);
    let not_lifted = terms.mk_not_raw(lifted);
    let mut proof = Proof::new();
    let assumed = proof.add_assume(equality, None);
    let holds = proof.add_assume(p_x, None);
    let fails = proof.add_assume(not_p_y, None);
    let congruence = proof.add_rule_step(AletheRule::Cong, vec![lifted], vec![assumed], vec![]);
    let transfer = proof.add_rule_step(
        AletheRule::EquivPos2,
        vec![not_lifted, not_p_x, p_y],
        vec![],
        vec![],
    );
    let implication = proof.add_resolution(vec![not_p_x, p_y], lifted, congruence, transfer);
    let consequence = proof.add_resolution(vec![p_y], p_x, holds, implication);
    proof.add_resolution(vec![], p_y, consequence, fails);
    let table = overrides(&[
        (equality, "(not (distinct x y))"),
        (ancestor, "(distinct x y)"),
    ]);
    let document = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[equality, p_x, not_p_y],
        Some(&table),
    )
    .expect("the negated distinct is bridged before the cong reads it");
    assert!(
        document.starts_with("(assume t0.a (not (distinct x y)))\n"),
        "{document}"
    );
    assert!(
        document.contains("(step t0 (cl (= x y)) :rule resolution"),
        "{document}"
    );
    let problem = "(set-logic QF_UFLIA)\n(declare-const x Int)\n(declare-const y Int)\n\
                   (declare-fun P (Int) Bool)\n(assert (not (distinct x y)))\n(assert (P x))\n\
                   (assert (not (P y)))\n(check-sat)\n";
    assert_valid("negated_distinct_cong", problem, &document);
}

/// NEGATIVE TWIN: once the proof prints the overridden ancestor, the guard
/// holds; a binder keeps it over every override.
#[test]
fn a_printed_overridden_ancestor_still_withholds_the_bridge() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let equality = terms.mk_app(Symbol::named("="), [x, y], Sort::Bool);
    let ancestor = terms.mk_not_raw(equality);
    let table = overrides(&[
        (equality, "(not (distinct x y))"),
        (ancestor, "(distinct x y)"),
    ]);
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&table));
    let mut proof = Proof::new();
    let positive = proof.add_assume(equality, None);
    let negative = proof.add_assume(ancestor, None);
    proof.add_resolution(vec![], equality, positive, negative);
    let roots = printed_terms::printed_proof_roots(&proof).expect("known step shapes");
    let guarded = printer
        .strict_descendants_of_printed_overridden_terms(&roots)
        .expect("bounded");
    assert!(guarded.contains(&equality), "{guarded:?}");

    let body = terms.mk_app(Symbol::named("<"), [x, y], Sort::Bool);
    let quantified = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&table));
    let mut proof = Proof::new();
    proof.add_assume(quantified, None);
    let roots = printed_terms::printed_proof_roots(&proof).expect("known step shapes");
    assert_eq!(printer.printed_terms_below(&roots), None);
    // Unread completely, every override guards its descendants again.
    let guarded = printer
        .strict_descendants_of_printed_overridden_terms(&roots)
        .expect("bounded");
    assert!(guarded.contains(&equality), "{guarded:?}");
}

/// NEGATIVE TWIN: a Skolem witness prints its `choice` body without that body
/// being a child, and a subproof that binds variables prints its steps under
/// binders, so a proof with either is not read completely and every override
/// guards its descendants. The variables an `NraSos` certificate's basis
/// prints are roots of the walk.
#[test]
fn a_skolem_witness_or_a_binding_subproof_keeps_the_guard_and_an_sos_basis_is_printed() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let equality = terms.mk_app(Symbol::named("="), [x, y], Sort::Bool);
    let ancestor = terms.mk_not_raw(equality);
    let witness = terms.mk_var("sk", Sort::Int);
    terms.mark_skolem_symbol("sk");
    terms.register_skolem_choice(
        witness,
        ay_core::SkolemChoice {
            binder: "x".to_string(),
            sort: Sort::Int,
            body: ancestor,
        },
    );
    let pinned = terms.mk_app(Symbol::named("="), [witness, y], Sort::Bool);
    let table = overrides(&[
        (equality, "(not (distinct x y))"),
        (ancestor, "(distinct x y)"),
    ]);
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&table));
    let mut proof = Proof::new();
    proof.add_assume(pinned, None);
    let roots = printed_terms::printed_proof_roots(&proof).expect("known step shapes");
    assert_eq!(printer.printed_terms_below(&roots), None);
    let guarded = printer
        .strict_descendants_of_printed_overridden_terms(&roots)
        .expect("bounded");
    assert!(guarded.contains(&equality), "{guarded:?}");

    let mut proof = Proof::new();
    let end = proof.add_assume(equality, None);
    proof.add_step(ProofStep::Anchor {
        end_step: end,
        variables: vec![("x".to_string(), Sort::Int)],
    });
    assert_eq!(printed_terms::printed_proof_roots(&proof), None);

    let zero = ay_core::NraSosRational {
        numerator: BigInt::from(0),
        denominator: BigInt::from(1),
    };
    let mut proof = Proof::new();
    proof.add_step(ProofStep::NraSos {
        clause: vec![],
        certificate: ay_core::NraSosCertificate {
            basis: vec![vec![], vec![y]],
            gram: vec![vec![zero.clone(); 2]; 2],
            terms: vec![],
            rhs: zero,
        },
    });
    let roots = printed_terms::printed_proof_roots(&proof).expect("known step shapes");
    assert_eq!(roots, [y]);
}
