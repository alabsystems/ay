// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The eighth false green's two siblings over the printer's Skolem channel
//! (2026-09-13), end to end against the pinned external checker.
//!
//! One mechanism, two rules. `register_substituted_surface_overrides`
//! carries the AUTHORED spelling of a Skolemized body across `binder :=
//! choice` into the printer's own `skolem_overrides` channel, which every
//! print site consults before the producer's table. Two consumers were blind
//! to that channel on main:
//!
//! * `la_generic`: the producer-table promotions judged the CANONICAL clause
//!   while the literal shipped in its authored spelling, so an operand the
//!   store had simplified at construction (`(ite (= z z) z 0)` for `z`,
//!   `(select (store A z z) z)` for `z`) reached the wire as an atom the
//!   checker cannot cancel — `final disequality is not contradictory` under
//!   a green flag. Now every `la_generic` is judged over the bytes it ships
//!   and declines to the honest `hole`; an operand the checker CAN read
//!   (`(+ z 0)`) keeps its valid document.
//! * `sko_ex`: a positive authored `exists` whose binder elaboration renamed
//!   and whose body it canonicalized printed the authored quantifier beside
//!   an anchor over the internal binder and the canonical body
//!   (`BindingIsNotInContext`), and the `forall_inst` at its witness printed
//!   the canonical instance under the authored quantifier. Now the anchor
//!   binds the printed binder over the printed body, the collector descends
//!   the `exists` body so its atoms carry their authored spellings, and the
//!   final-proof pass spells the instance the rebuild lanes had purged. The
//!   derivation exists, so the document is VALID, not a hole.

use super::{
    refuse_pinned_carcara_misjudgments, require_carcara_or_skip, solve_unsat_and_get_proof,
};
use ntest::timeout;
use std::path::Path;

/// Sibling 1, pure UFLIA: the instance operand `(ite (= z z) z 0)` is `z` to
/// the store but ships in its authored spelling.
const LA_GENERIC_OVER_SIMPLIFIED_ITE: &str = r#"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-const a0 Int)
(assert (> (f a0) a0))
(assert (forall ((y Int)) (! (<= (f y) (g y)) :pattern ((f y)))))
(assert (forall ((w Int)) (! (> (f w) w) :pattern ((g w)))))
(assert (not (forall ((z Int)) (or (< z 0) (>= (g z) (ite (= z z) z 0))))))
(check-sat)
"#;

/// Sibling 1 in AUFLIA: `(select (store A z z) z)` is `z` to the store.
const LA_GENERIC_OVER_SIMPLIFIED_SELECT_STORE: &str = r#"
(set-logic AUFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-const a0 Int)
(declare-const A (Array Int Int))
(assert (> (f a0) a0))
(assert (forall ((y Int)) (! (<= (f y) (g y)) :pattern ((f y)))))
(assert (forall ((w Int)) (! (> (f w) w) :pattern ((g w)))))
(assert (not (forall ((z Int)) (or (< z 0) (>= (g z) (select (store A z z) z))))))
(check-sat)
"#;

/// The same shape over an operand the checker's linear reader CAN fold:
/// `(+ z 0)` is `z` to the store and `z + 0` to carcara. Evidence that must
/// survive the judgement.
const LA_GENERIC_OVER_PLUS_ZERO: &str = r#"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-const a0 Int)
(assert (> (f a0) a0))
(assert (forall ((y Int)) (! (<= (f y) (g y)) :pattern ((f y)))))
(assert (forall ((w Int)) (! (> (f w) w) :pattern ((g w)))))
(assert (not (forall ((z Int)) (or (< z 0) (>= (g z) (+ z 0))))))
(check-sat)
"#;

/// Sibling 2: a positive authored `exists` with a renamed binder and a
/// canonicalized body.
const SKO_EX_RENAMED_BINDER: &str = r#"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-const a0 Int)
(assert (> (f a0) a0))
(assert (forall ((y Int)) (! (<= (f y) (g y)) :pattern ((f y)))))
(assert (forall ((w Int)) (! (> (f w) w) :pattern ((g w)))))
(assert (exists ((z Int)) (and (>= z 0) (< (g z) z))))
(check-sat)
"#;

/// Sibling 2 over an uninterpreted sort.
const SKO_EX_UF_SORT: &str = r#"
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun g (U) U)
(declare-fun P (U) Bool)
(declare-const a0 U)
(assert (P (f a0)))
(assert (forall ((y U)) (! (=> (P (f y)) (P (g y))) :pattern ((f y)))))
(assert (forall ((w U)) (! (P w) :pattern ((g w)))))
(assert (exists ((z U)) (and (P (g z)) (not (P z)))))
(check-sat)
"#;

/// Sibling 2 with a De Morgan body: the authored `(not (or ..))` is an `and`
/// to the store, so the authored instance spelling cannot be projected by
/// `and_pos` without a bridge AY does not derive. The floor is the honest
/// hole the base already printed — never a refused export, never `invalid`.
const SKO_EX_DE_MORGAN_BODY: &str = r#"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-const a0 Int)
(assert (> (f a0) a0))
(assert (forall ((y Int)) (! (<= (f y) (g y)) :pattern ((f y)))))
(assert (forall ((w Int)) (! (> (f w) w) :pattern ((g w)))))
(assert (exists ((z Int)) (not (or (< z 0) (>= (g z) z)))))
(check-sat)
"#;

/// The eighth shape itself, the control: a negated universal, valid on the
/// eighth fix and still valid here.
const EIGHTH_SHAPE_CONTROL: &str = r#"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-const a0 Int)
(assert (> (f a0) a0))
(assert (forall ((y Int)) (! (<= (f y) (g y)) :pattern ((f y)))))
(assert (forall ((w Int)) (! (> (f w) w) :pattern ((g w)))))
(assert (not (forall ((z Int)) (or (< z 0) (>= (g z) z)))))
(check-sat)
"#;

/// The pinned checker's one-word verdict on `proof` for `problem`, the way
/// the campaign's gate reads it: `valid`, `holey` or `invalid`. A pair whose
/// verdict is not evidence (`ay_core::pinned_carcara`) fails the test first.
fn carcara_verdict(carcara: &Path, problem: &str, proof: &str) -> String {
    refuse_pinned_carcara_misjudgments("skolem channel", problem, proof);
    let directory = tempfile::tempdir().expect("temporary checker directory");
    let problem_path = directory.path().join("problem.smt2");
    let proof_path = directory.path().join("proof.alethe");
    std::fs::write(&problem_path, problem).expect("write problem");
    std::fs::write(&proof_path, proof).expect("write proof");
    let output = std::process::Command::new(carcara)
        .arg("check")
        .arg("--allow-int-real-subtyping")
        .arg("--")
        .arg(&proof_path)
        .arg(&problem_path)
        .output()
        .expect("run the pinned checker");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let verdict = stdout.lines().last().unwrap_or("").trim().to_string();
    assert!(
        matches!(verdict.as_str(), "valid" | "holey" | "invalid"),
        "the checker printed no verdict: stdout={stdout} stderr={stderr}"
    );
    if verdict != "valid" {
        eprintln!("carcara {verdict}: {}", stderr.trim());
    }
    verdict
}

/// NEGATIVE CONTROL: the pair pinned carcara prints `valid` for only through
/// its `evaluate` defect is refused before the checker runs, so none of this
/// file's `valid`/`holey`/not-`invalid` assertions can pass on it.
#[test]
#[should_panic(expected = "is not evidence")]
fn the_skolem_channel_runner_refuses_a_document_pinned_carcara_misjudges() {
    carcara_verdict(
        Path::new("carcara"),
        ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROBLEM,
        ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROOF,
    );
}

fn rule_count(proof: &str, rule: &str) -> usize {
    proof.matches(&format!(":rule {rule}")).count()
}

#[test]
#[timeout(120_000)]
fn skolem_channel_la_generic_over_a_simplified_ite_operand_is_holed_not_claimed() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let proof = solve_unsat_and_get_proof(LA_GENERIC_OVER_SIMPLIFIED_ITE, "sks_la_generic_ite");
    // The authored operand reaches the wire (one spelling per witness); the
    // `la_generic` that would claim rows over it is the honest hole.
    assert!(
        proof.contains("(ite (= (choice"),
        "the instance ships in its authored spelling:\n{proof}"
    );
    let verdict = carcara_verdict(&carcara, LA_GENERIC_OVER_SIMPLIFIED_ITE, &proof);
    assert_ne!(
        verdict, "invalid",
        "no step may claim a rule the shipped text does not instantiate:\n{proof}"
    );
    assert_eq!(
        (
            verdict.as_str(),
            rule_count(&proof, ay_core::UNPROVED_STEP_RULE) > 0
        ),
        ("holey", true),
        "the Skolem-channel la_generic must decline to the honest hole:\n{proof}"
    );
}

#[test]
#[timeout(120_000)]
fn skolem_channel_la_generic_over_a_simplified_select_store_is_holed_not_claimed() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let proof = solve_unsat_and_get_proof(
        LA_GENERIC_OVER_SIMPLIFIED_SELECT_STORE,
        "sks_la_generic_select_store",
    );
    assert!(
        proof.contains("(select (store A (choice"),
        "the instance ships in its authored spelling:\n{proof}"
    );
    let verdict = carcara_verdict(&carcara, LA_GENERIC_OVER_SIMPLIFIED_SELECT_STORE, &proof);
    assert_eq!(
        (
            verdict.as_str(),
            rule_count(&proof, ay_core::UNPROVED_STEP_RULE) > 0
        ),
        ("holey", true),
        "the Skolem-channel la_generic must decline to the honest hole:\n{proof}"
    );
}

#[test]
#[timeout(120_000)]
fn skolem_channel_la_generic_over_plus_zero_keeps_its_valid_document() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let proof = solve_unsat_and_get_proof(LA_GENERIC_OVER_PLUS_ZERO, "sks_la_generic_plus_zero");
    assert!(
        proof.contains("(+ (choice") && rule_count(&proof, "la_generic") >= 2,
        "the authored `(+ z 0)` operand ships and its la_generic steps are kept:\n{proof}"
    );
    assert_eq!(
        rule_count(&proof, ay_core::UNPROVED_STEP_RULE),
        0,
        "no evidence may be destroyed by the printed judgement:\n{proof}"
    );
    assert_eq!(
        carcara_verdict(&carcara, LA_GENERIC_OVER_PLUS_ZERO, &proof),
        "valid",
        "{proof}"
    );
}

#[test]
#[timeout(120_000)]
fn sko_ex_with_a_renamed_binder_ships_a_valid_document() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let proof = solve_unsat_and_get_proof(SKO_EX_RENAMED_BINDER, "sks_sko_ex_renamed_binder");
    // The anchor binds the PRINTED binder over the PRINTED body, and the
    // instance at the witness is spelled under the authored quantifier.
    assert!(
        proof.contains("(anchor :step")
            && proof.contains("(:= (z Int) (choice ((z Int)) (and (>= z 0) (< (g z) z))))"),
        "the anchor must bind the authored binder to a choice over the authored body:\n{proof}"
    );
    assert_eq!(rule_count(&proof, "sko_ex"), 1, "{proof}");
    assert!(
        proof.contains("(> (f (choice ((z Int)) (and (>= z 0) (< (g z) z)))) (choice ((z Int)) (and (>= z 0) (< (g z) z))))"),
        "the forall_inst instance must be the authored body under `w := choice`:\n{proof}"
    );
    assert_eq!(
        rule_count(&proof, ay_core::UNPROVED_STEP_RULE),
        0,
        "the derivation exists and must print without a hole:\n{proof}"
    );
    assert_eq!(
        carcara_verdict(&carcara, SKO_EX_RENAMED_BINDER, &proof),
        "valid",
        "{proof}"
    );
}

#[test]
#[timeout(120_000)]
fn sko_ex_over_an_uninterpreted_sort_ships_a_valid_document() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let proof = solve_unsat_and_get_proof(SKO_EX_UF_SORT, "sks_sko_ex_uf");
    assert_eq!(rule_count(&proof, "sko_ex"), 1, "{proof}");
    assert_eq!(
        rule_count(&proof, ay_core::UNPROVED_STEP_RULE),
        0,
        "{proof}"
    );
    assert_eq!(
        carcara_verdict(&carcara, SKO_EX_UF_SORT, &proof),
        "valid",
        "{proof}"
    );
}

#[test]
#[timeout(120_000)]
fn sko_ex_with_a_de_morgan_body_declines_honestly_and_never_refuses_the_export() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    // `solve_unsat_and_get_proof` asserts the export is a document, not an
    // `(error ..)`: a refused export here would widen the `--proof FILE`
    // no-verdict decline (#8821) to a shape the base already printed.
    let proof = solve_unsat_and_get_proof(SKO_EX_DE_MORGAN_BODY, "sks_sko_ex_de_morgan");
    let verdict = carcara_verdict(&carcara, SKO_EX_DE_MORGAN_BODY, &proof);
    assert_ne!(verdict, "invalid", "{proof}");
}

#[test]
#[timeout(120_000)]
fn the_eighth_shape_control_stays_valid() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let proof = solve_unsat_and_get_proof(EIGHTH_SHAPE_CONTROL, "sks_eighth_control");
    assert_eq!(
        rule_count(&proof, ay_core::UNPROVED_STEP_RULE),
        0,
        "{proof}"
    );
    assert_eq!(
        carcara_verdict(&carcara, EIGHTH_SHAPE_CONTROL, &proof),
        "valid",
        "{proof}"
    );
}

// ---------------------------------------------------------------------------
// 2026-09-16: two refutations of the siblings above, and the false green an
// adversarial verifier found beside them.
// ---------------------------------------------------------------------------

/// REFUTATION 1. The authored `exists` body the store De Morgan'd AND
/// FLATTENED: `(and A (not (or B C)))` is the three-conjunct
/// `(and A (not B) (not C))` internally, so the head-only guard passed it and
/// `and_pos :args (2)` had no conjunct 2 to project. The export was refused —
/// no document at all in the default posture, `unsat` moved to `unknown`
/// under `--strict-proofs`, exit 1 with no verdict under `--proof FILE` —
/// where the base ships a two-hole document and exits 0 in all three.
const SKO_EX_FLATTENED_AND_BODY: &str = r#"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-const a0 Int)
(assert (> (f a0) a0))
(assert (forall ((y Int)) (! (<= (f y) (g y)) :pattern ((f y)))))
(assert (forall ((w Int)) (! (> (f w) w) :pattern ((g w)))))
(assert (exists ((z Int)) (and (>= z 0) (not (or (< z 0) (>= (g z) z))))))
(check-sat)
"#;

/// The same shape in AUFLIA, with the diverging conjunct carrying an array
/// operand the store simplifies (`(select (store A z z) z)` is `z`).
const SKO_EX_ARRAY_OPERAND_BODY: &str = r#"
(set-logic AUFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-const a0 Int)
(declare-const A (Array Int Int))
(assert (> (f a0) a0))
(assert (forall ((y Int)) (! (<= (f y) (g y)) :pattern ((f y)))))
(assert (forall ((w Int)) (! (> (f w) w) :pattern ((g w)))))
(assert (exists ((z Int)) (and (>= z 0) (< (g (select (store A z z) z)) z))))
(check-sat)
"#;

/// REFUTATION 2a. A legal quoted function symbol that SPELLS the rule. Not a
/// rule: an operand. The line-scanning reader refused the whole export of a
/// document the pinned checker calls `valid`.
const QUOTED_SYMBOL_SPELLING_THE_RULE: &str = r#"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun |g :rule la_generic :args (1 1)| (Int) Int)
(declare-const a0 Int)
(assert (> (f a0) a0))
(assert (forall ((y Int)) (! (<= (f y) (|g :rule la_generic :args (1 1)| y)) :pattern ((f y)))))
(assert (forall ((w Int)) (! (> (f w) w) :pattern ((|g :rule la_generic :args (1 1)| w)))))
(assert (not (forall ((z Int)) (or (< z 0) (>= (|g :rule la_generic :args (1 1)| z) (+ z 0))))))
(check-sat)
"#;

/// REFUTATION 2b. A QF_SLIA string literal that spells the rule.
const STRING_LITERAL_SPELLING_THE_RULE: &str = r#"
(set-logic QF_SLIA)
(declare-const s String)
(assert (= s " :rule la_generic :args (1 1)"))
(assert (distinct s " :rule la_generic :args (1 1)"))
(check-sat)
"#;

/// REFUTATION 2c. The same for `poly_simp`, with an unbalanced parenthesis
/// inside the literal so the line also fails to parse as a command.
const STRING_LITERAL_SPELLING_POLY_SIMP: &str = r#"
(set-logic QF_SLIA)
(declare-const s String)
(assert (= s "x :rule poly_simp)"))
(assert (distinct s "x :rule poly_simp)"))
(check-sat)
"#;

/// THE TENTH FALSE GREEN, and NOT the Skolem channel: `or` claimed over a
/// printed IMPLICATION. Elaboration represents the authored `(=> A B)` as the
/// internal `(or (not A) B)`, the `assume` has to print the problem's own
/// text, and the `or` decomposition of the `forall_inst` unit clause then
/// claims a rule the printed premise does not instantiate.
const OR_OVER_A_PRINTED_IMPLICATION: &str = r#"
(set-logic UFLIA)
(declare-fun P (Int) Bool)
(declare-fun g (Int) Int)
(assert (forall ((y Int)) (! (=> (>= y 0) (P (g y))) :pattern ((P (g y))))))
(assert (not (forall ((z Int)) (or (< z 0) (P (g (ite (= z z) z 0)))))))
(check-sat)
"#;

/// Its control, with the simplification removed: equally green and equally
/// refused while the instance kept its authored implication document-wide,
/// which is the evidence the shape is the implication and not the Skolem
/// channel. Since the printed-equivalence schema relates an operand-swapped
/// comparison (`surface_equivalence/comparison.rs`), the confined instance
/// derives the canonical disjunction from the authored
/// `(=> (>= (choice ..) 0) ..)`, so the `or` decomposition reads a printed
/// `or` and the control is pinned `valid`; the `ite` fixture above still
/// declines to the hole.
const OR_OVER_A_PRINTED_IMPLICATION_CONTROL: &str = r#"
(set-logic UFLIA)
(declare-fun P (Int) Bool)
(declare-fun g (Int) Int)
(assert (forall ((y Int)) (! (=> (>= y 0) (P (g y))) :pattern ((P (g y))))))
(assert (not (forall ((z Int)) (or (< z 0) (P (g z))))))
(check-sat)
"#;

#[test]
#[timeout(120_000)]
fn sko_ex_with_a_flattened_and_body_publishes_a_document_and_never_refuses_the_export() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    // `solve_unsat_and_get_proof` asserts an actual document came back.
    let proof = solve_unsat_and_get_proof(SKO_EX_FLATTENED_AND_BODY, "sks_sko_ex_flattened");
    assert!(
        proof.contains(":rule and_pos"),
        "the projection must still be derived over the store's own spelling:\n{proof}"
    );
    assert_ne!(
        carcara_verdict(&carcara, SKO_EX_FLATTENED_AND_BODY, &proof),
        "invalid",
        "{proof}"
    );
}

#[test]
#[timeout(120_000)]
fn sko_ex_with_an_array_operand_body_publishes_a_document() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let proof = solve_unsat_and_get_proof(SKO_EX_ARRAY_OPERAND_BODY, "sks_sko_ex_array_operand");
    assert_ne!(
        carcara_verdict(&carcara, SKO_EX_ARRAY_OPERAND_BODY, &proof),
        "invalid",
        "{proof}"
    );
}

#[test]
#[timeout(120_000)]
fn a_quoted_symbol_spelling_the_rule_keeps_its_valid_document() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let proof = solve_unsat_and_get_proof(QUOTED_SYMBOL_SPELLING_THE_RULE, "sks_quoted_rule");
    assert_eq!(
        rule_count(&proof, ay_core::UNPROVED_STEP_RULE),
        0,
        "a symbol is not a rule; no evidence may be lost to one:\n{proof}"
    );
    assert_eq!(
        carcara_verdict(&carcara, QUOTED_SYMBOL_SPELLING_THE_RULE, &proof),
        "valid",
        "{proof}"
    );
}

#[test]
#[timeout(120_000)]
fn a_string_literal_spelling_the_rule_keeps_its_valid_document() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    for (problem, name) in [
        (STRING_LITERAL_SPELLING_THE_RULE, "sks_string_la_generic"),
        (STRING_LITERAL_SPELLING_POLY_SIMP, "sks_string_poly_simp"),
    ] {
        let proof = solve_unsat_and_get_proof(problem, name);
        assert_eq!(
            rule_count(&proof, ay_core::UNPROVED_STEP_RULE),
            0,
            "a string literal is not a rule:\n{proof}"
        );
        assert_eq!(
            carcara_verdict(&carcara, problem, &proof),
            "valid",
            "{proof}"
        );
    }
}

#[test]
#[timeout(120_000)]
fn or_claimed_over_a_printed_implication_is_derived_or_declines_to_the_honest_hole() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    for (problem, name, derived) in [
        (OR_OVER_A_PRINTED_IMPLICATION, "sks_or_over_implies", false),
        (
            OR_OVER_A_PRINTED_IMPLICATION_CONTROL,
            "sks_or_over_implies_control",
            true,
        ),
    ] {
        let proof = solve_unsat_and_get_proof(problem, name);
        assert!(
            proof.contains("(=> (>= (choice"),
            "the instance must still ship the authored implication:\n{proof}"
        );
        let holes = rule_count(&proof, ay_core::UNPROVED_STEP_RULE);
        if derived {
            assert_eq!(
                holes, 0,
                "the confined instance derives the canonical disjunction:\n{proof}"
            );
        } else {
            assert!(
                holes > 0,
                "the `or` over an implication must decline to a hole:\n{proof}"
            );
        }
        assert_eq!(
            carcara_verdict(&carcara, problem, &proof),
            if derived { "valid" } else { "holey" },
            "{proof}"
        );
    }
}

// ---------------------------------------------------------------------------
// 2026-09-16, pass three: the structure verifier's two findings.
// ---------------------------------------------------------------------------

/// FINDING 1. The tenth shape with the function symbol `|g\nh|` — a newline
/// inside a quoted symbol, legal SMT-LIB 2.6. The ledger the `or` and
/// `resolution` judgements read was filled by a LINE scan, so a command
/// spanning lines recorded nothing and both judgements took their "premise
/// not recorded → unchanged" path: `unproved_steps=0 ay_self_checkable=yes`,
/// pinned carcara `invalid` at the `or` over the printed implication, in
/// every document-emitting posture (build 9706). The controls pin the
/// discriminator: a TAB or CR in the symbol is holed, a newline in a symbol
/// outside the `or` premise's clause is holed, a newline with no violation
/// is valid.
const OR_OVER_A_PRINTED_IMPLICATION_WITH_A_NEWLINE_SYMBOL: &str = r#"
(set-logic UFLIA)
(declare-fun P (Int) Bool)
(declare-fun |g
h| (Int) Int)
(assert (forall ((y Int)) (! (=> (>= y 0) (P (|g
h| y))) :pattern ((P (|g
h| y))))))
(assert (not (forall ((z Int)) (or (< z 0) (P (|g
h| (ite (= z z) z 0)))))))
(check-sat)
"#;

/// FINDING 2. A positive `exists` whose authored body is `(not (or A B))`
/// where the store folds `A` to `false` and collapses `(or false B)` to `B`:
/// the skeleton guard matched the store ATOM `B` at depth 1 with the printed
/// `(or A B)`, the authored body was carried, and the mixed identities died
/// in `judge_printed_resolution` at `t16` — no document in the default
/// posture, `unsat` moved to `unknown` under `--strict-proofs`, exit 1 with
/// no verdict under `--proof FILE`, where the base publishes a two-hole
/// document at exit 0 in every posture.
const NOT_OR_ROOT_WITH_A_FOLDED_DISJUNCT: &str = r#"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-const a0 Int)
(assert (> (f a0) a0))
(assert (forall ((y Int)) (! (<= (f y) (g y)) :pattern ((f y)))))
(assert (forall ((w Int)) (! (> (f w) w) :pattern ((g w)))))
(assert (exists ((z Int)) (not (or (< 0 (- 0 1)) (>= (g z) z)))))
(check-sat)
"#;

/// The same over a constant comparison the store folds (`(< 1 0)`).
const NOT_OR_ROOT_WITH_A_FALSE_DISJUNCT: &str = r#"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-const a0 Int)
(assert (> (f a0) a0))
(assert (forall ((y Int)) (! (<= (f y) (g y)) :pattern ((f y)))))
(assert (forall ((w Int)) (! (> (f w) w) :pattern ((g w)))))
(assert (exists ((z Int)) (not (or (< 1 0) (>= (g z) z)))))
(check-sat)
"#;

#[test]
#[timeout(120_000)]
fn an_or_premise_spanning_lines_is_judged_and_declines_to_the_honest_hole() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let proof = solve_unsat_and_get_proof(
        OR_OVER_A_PRINTED_IMPLICATION_WITH_A_NEWLINE_SYMBOL,
        "sks_or_over_implies_newline",
    );
    assert!(
        proof.contains("(=> (>= (choice") && proof.contains("|g\nh|"),
        "the instance ships the authored implication and the symbol keeps its newline:\n{proof}"
    );
    assert!(
        rule_count(&proof, ay_core::UNPROVED_STEP_RULE) > 0,
        "the `or` over an implication must decline to a hole whatever lines its premise spans:\n{proof}"
    );
    assert_eq!(
        carcara_verdict(
            &carcara,
            OR_OVER_A_PRINTED_IMPLICATION_WITH_A_NEWLINE_SYMBOL,
            &proof
        ),
        "holey",
        "{proof}"
    );
}

#[test]
#[timeout(120_000)]
fn an_exists_whose_disjunct_the_store_folded_publishes_a_document() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    for (problem, name) in [
        (NOT_OR_ROOT_WITH_A_FOLDED_DISJUNCT, "sks_not_or_root_folded"),
        (NOT_OR_ROOT_WITH_A_FALSE_DISJUNCT, "sks_not_or_root_false"),
    ] {
        // `solve_unsat_and_get_proof` asserts an actual document came back:
        // a refused export here is the #8821 widening the base never had.
        let proof = solve_unsat_and_get_proof(problem, name);
        assert!(
            !proof.contains("(choice ((z Int)) (not (or"),
            "the authored body must not be carried where the store folded it:\n{proof}"
        );
        assert_ne!(
            carcara_verdict(&carcara, problem, &proof),
            "invalid",
            "{proof}"
        );
    }
}
