// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression: an authored conjunction that elaboration FOLDS away must still
//! export a certificate an independent checker accepts — and when it cannot,
//! the document must say so with a countable `hole` rather than claim a
//! derivation it does not contain.
//!
//! ## What was published before this lane existed
//!
//! `(assert (and (not p) (= x1 x1)))` + `(assert p)` in QF_DT. The reflexive
//! equality simplifies to `true` and is dropped, so the assertion interns as
//! the bare `(not p)`. The root surface override still printed the authored
//! conjunction — correctly, since carcara matches every `assume` against the
//! problem file — but the override is keyed by the FOLDED `TermId` and is
//! consulted at every print site, so the resolution that consumed the assume
//! printed with no eliminable pivot:
//!
//! ```text
//! (assume t0 (and (not p) (= x1 x1)))
//! (assume t1 p)
//! (step t2 (cl) :rule resolution :premises (t1 t0))
//! ```
//!
//! AY answered `unsat` and stamped the artifact
//! `trust_free=yes ay_self_checkable=yes`; carcara 1.1.0 answered **invalid** —
//! "pivot was not eliminated". The stamp is the thing downstream consumers are
//! told to trust, so an artifact an independent checker rejects while AY calls
//! it trust-free is the worst of the three failure modes.
//!
//! Measured across QF_DT / QF_UF / QF_LIA / QF_AX, every foldable authored
//! conjunct shape reproduced it: reflexive equality, literal `true`, duplicate
//! conjuncts, folded-conjunct-first, nested conjunctions, and several folds at
//! once — 24 instances, all `invalid`, all stamped trust-free.

use super::{
    extract_assume_terms, require_carcara_or_skip, run_carcara_trust_free,
    solve_unsat_and_get_proof,
};
use ntest::timeout;

/// The two-assertion refutation, in one logic, with `FOLDABLE` substituted for
/// a conjunct that elaboration removes.
fn fold_problem(logic: &str, declarations: &str, conjunction: &str) -> String {
    format!(
        "(set-logic {logic})\n\
         {declarations}\
         (declare-fun p () Bool)\n\
         (declare-fun q () Bool)\n\
         (assert {conjunction})\n\
         (assert p)\n\
         (check-sat)\n"
    )
}

/// Every foldable authored conjunct shape, in four logics, must export a
/// certificate carcara accepts as **valid** with no trust and no hole.
#[test]
#[timeout(300_000)]
fn folded_authored_conjunctions_export_externally_valid_certificates() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let logics = [
        (
            "QF_DT",
            "(declare-datatypes ((nat 0)) (((succ (pred nat)) (zero))))\n\
             (declare-fun x () nat)\n",
        ),
        ("QF_UF", "(declare-sort U 0)\n(declare-fun x () U)\n"),
        ("QF_LIA", "(declare-fun x () Int)\n"),
        ("QF_AX", "(declare-fun x () (Array Int Int))\n"),
    ];
    // Each conjunction is unsatisfiable together with `(assert p)` and each
    // one elaborates to the bare `(not p)`.
    let shapes = [
        ("refl", "(and (not p) (= x x))"),
        ("true_conjunct", "(and (not p) true)"),
        ("duplicate", "(and (not p) (not p))"),
        ("folded_first", "(and (= x x) (not p))"),
        ("nested", "(and (and (not p) (= x x)) true)"),
        ("multiple", "(and (not p) (= x x) true (= x x))"),
        // Controls: nothing folds. These were already valid and must stay so.
        ("control_survives", "(and (not p) q)"),
        ("control_reordered", "(and q (not p))"),
    ];

    for (logic, declarations) in logics {
        for (shape, conjunction) in shapes {
            let label = format!("folded_and_{}_{shape}", logic.to_lowercase());
            let problem = fold_problem(logic, declarations, conjunction);
            let proof = solve_unsat_and_get_proof(&problem, &label);
            assert!(
                !proof.contains(":rule hole") && !proof.contains(":rule trust"),
                "{label}: a foldable conjunct must not cost an unproved step:\n{proof}"
            );
            assert!(
                run_carcara_trust_free(&carcara, &label, &problem, &proof),
                "{label}: carcara must accept the certificate as valid:\n\
                 problem:\n{problem}\nproof:\n{proof}"
            );
        }
    }
}

/// The fold target is a BARE ATOM: `(and p (= x x))` interns as `p` itself.
///
/// `override_would_hijack_atom` refuses whole-assertion spellings on atomic
/// canonicals because, keyed by `TermId`, they re-spell every occurrence of
/// that atom — so this assertion had NO surface override at all and the export
/// published `(assume t0 p)`, which is no assertion of the problem. carcara:
/// "could not match term to any of the original problem premises", while AY
/// stamped `trust_free=yes ay_self_checkable=yes`.
///
/// The refusal is exempted for exactly this shape because the printer's
/// folded-conjunction plan confines the spelling to the `assume`. Kept as its
/// own test because it also pins the ORDERING hazard that broke the first
/// attempt: the second assertion descends to its own `p` operand and its
/// identity spelling must not clobber the conjunction recorded for the same
/// `TermId`.
#[test]
#[timeout(300_000)]
fn folded_conjunction_onto_a_bare_atom_exports_an_externally_valid_certificate() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let logics = [
        (
            "QF_DT",
            "(declare-datatypes ((nat 0)) (((succ (pred nat)) (zero))))\n\
             (declare-fun x () nat)\n",
        ),
        ("QF_UF", "(declare-sort U 0)\n(declare-fun x () U)\n"),
        ("QF_LIA", "(declare-fun x () Int)\n"),
        ("QF_AX", "(declare-fun x () (Array Int Int))\n"),
    ];
    for (logic, declarations) in logics {
        let label = format!("folded_and_atom_{}", logic.to_lowercase());
        let problem = format!(
            "(set-logic {logic})\n\
             {declarations}\
             (declare-fun p () Bool)\n\
             (assert (and p (= x x)))\n\
             (assert (not p))\n\
             (check-sat)\n"
        );
        let proof = solve_unsat_and_get_proof(&problem, &label);
        assert!(
            proof.contains("(and p (= x x))"),
            "{label}: the assume must be the authored conjunction, not the \
             folded atom:\n{proof}"
        );
        assert!(
            !proof.contains(":rule hole") && !proof.contains(":rule trust"),
            "{label}: no unproved step is owed here:\n{proof}"
        );
        assert!(
            run_carcara_trust_free(&carcara, &label, &problem, &proof),
            "{label}: carcara must accept the certificate as valid:\n\
             problem:\n{problem}\nproof:\n{proof}"
        );
    }
}

/// The atom-identity spelling must not displace a recorded conjunction, and
/// must not disturb an ordinary atom either: an assertion that is just `p`
/// still prints as `p` everywhere.
#[test]
#[timeout(120_000)]
fn atom_identity_spelling_neither_clobbers_nor_perturbs() {
    let problem = "(set-logic QF_UF)\n\
                   (declare-fun p () Bool)\n\
                   (declare-fun q () Bool)\n\
                   (assert (or p q))\n\
                   (assert (not p))\n\
                   (assert (not q))\n\
                   (check-sat)\n";
    let proof = solve_unsat_and_get_proof(problem, "atom_identity_untouched");
    let mut assumes = extract_assume_terms(&proof);
    assumes.sort();
    assert_eq!(
        assumes,
        vec![
            "(not p)".to_string(),
            "(not q)".to_string(),
            "(or p q)".to_string()
        ],
        "plain atomic assertions keep printing as themselves:\n{proof}"
    );
}

/// The `assume` still has to be the problem's own assertion — that is the
/// whole reason the authored spelling is preserved at all. This is the half of
/// the invariant that does not need an external checker.
#[test]
#[timeout(120_000)]
fn folded_authored_conjunction_assume_is_the_problem_assertion() {
    let problem = fold_problem(
        "QF_UF",
        "(declare-sort U 0)\n(declare-fun x () U)\n",
        "(and (not p) (= x x))",
    );
    let proof = solve_unsat_and_get_proof(&problem, "folded_and_assume_identity");
    assert_eq!(
        extract_assume_terms(&proof),
        vec!["(and (not p) (= x x))".to_string(), "p".to_string()],
        "the folded conjunction must still be assumed exactly as authored:\n{proof}"
    );
    assert!(
        proof.contains(":rule and_pos"),
        "the folded conjunction must be projected onto its surviving conjunct \
         with the same and_pos step the non-folding path emits:\n{proof}"
    );
}

/// NEGATIVE CONTROL for the external check above.
///
/// A checker that accepts everything proves nothing, so break the artifact on
/// purpose — delete the `and_pos` projection and rewire the resolution to the
/// raw `assume`, which is exactly the document main published — and require
/// carcara to reject THAT. Without this, `run_carcara_trust_free` returning
/// `true` is not evidence.
#[test]
#[timeout(120_000)]
fn carcara_rejects_the_unbridged_folded_conjunction_document() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let problem = fold_problem(
        "QF_UF",
        "(declare-sort U 0)\n(declare-fun x () U)\n",
        "(and (not p) (= x x))",
    );
    let forged = "(assume t0 (and (not p) (= x x)))\n\
                  (assume t1 p)\n\
                  (step t2 (cl) :rule resolution :premises (t1 t0))\n";
    assert!(
        !run_carcara_trust_free(&carcara, "folded_and_negative_control", &problem, forged),
        "the negative control must be REJECTED; a checker that accepts the \
         unbridged document is not verifying anything"
    );
}

/// When the surviving conjunct is itself RE-SPELLED by canonicalization —
/// `(and (=> p q) (= x x))` folds to `(or (not p) q)`, which is no printed
/// conjunct of the authored `and` — no `and_pos` index exists. The document
/// must then carry exactly one visible, countable `hole` for that single
/// equivalence and stay *holey*, never claim a resolution it cannot make.
#[test]
#[timeout(120_000)]
fn unbridgeable_fold_costs_one_visible_hole_not_a_false_claim() {
    let problem = "(set-logic QF_UF)\n\
                   (declare-sort U 0)\n\
                   (declare-fun x () U)\n\
                   (declare-fun p () Bool)\n\
                   (declare-fun q () Bool)\n\
                   (assert (and (=> p q) (= x x)))\n\
                   (assert (and p (not q)))\n\
                   (check-sat)\n";
    let proof = solve_unsat_and_get_proof(problem, "folded_and_respelled_conjunct");
    assert_eq!(
        extract_assume_terms(&proof),
        vec![
            "(and (=> p q) (= x x))".to_string(),
            "(and p (not q))".to_string()
        ],
        "both assumes must remain the problem's own assertions:\n{proof}"
    );
    assert_eq!(
        proof.matches(":rule hole").count(),
        1,
        "exactly one hole, for the fold equivalence itself:\n{proof}"
    );
    assert!(
        !proof.contains(":rule trust"),
        "an unbridgeable fold is a hole, never a trust step:\n{proof}"
    );
}
