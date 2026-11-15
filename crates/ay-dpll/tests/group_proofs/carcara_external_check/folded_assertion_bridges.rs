// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authored assertions that elaboration FOLDS, and their SAT twins.
//!
//! `(assert (or (< x 3) false))` interns as the bare `(< x 3)`, and so do
//! `(and (< x 3) (= x x))`, `(= (< x 3) true)`, `(xor (< x 3) false)`,
//! `(distinct (< x 3) false)`, `(ite r (< x 3) (< x 3))` and
//! `(not (and (not (< x 3)) (= x x)))`. At `2c356fd15` each of these, with
//! `(assert (>= x 5))`, published `(assume t0 (< x 3))` under
//! `foreign_assumes=yes`; pinned carcara 1.1.0 answered `invalid` ("could not
//! match term to any of the original problem premises") and `--strict-proofs`
//! answered `unknown`. The document now assumes the authored assertion
//! verbatim and derives the folded term with carcara's own simplification
//! rules (`alethe_printer/authored_assume/boolean_fold.rs`) or the
//! folded-conjunction projection (`alethe_printer/folded_assume.rs`).
//!
//! Three siblings the same sweep measured ride along:
//! * `(assert (or (and p q) false))` + `(assert (not p))` published an
//!   `or_pos` whose disjuncts were out of the root's order under
//!   `trust_free=yes` (carcara: "expected terms to be equal: '(and p q)' and
//!   'false'");
//! * `(assert (and (< (+ x y) 3) true))` holed its Farkas lemma because the
//!   folded-conjunction plan left the authored conjunction in the wire-rule
//!   view;
//! * `(assert (not (= (< x 3) false)))` reaches the native SOS lane, whose
//!   lone-generator restatement was a one-premise `resolution` (carcara:
//!   "expected at least 2 premises, got 1"; closed by `reordering` since
//!   `05da30b49`).
//!
//! Every bridged UNSAT document must be literally `valid` with no allowance.
//! Where the fold would confine a root beside another override re-spelling a
//! term inside or around it, the root stays where the base left it, and the
//! base's document (`valid`, or one disclosed `hole`) is pinned instead.

use super::{
    carcara_verdict_without_allowances, parse, require_carcara_or_skip, solve_unsat_and_get_proof,
    CarcaraVerdict, Executor,
};
use ntest::timeout;

fn problem(logic: &str, declarations: &str, assertions: &[&str]) -> String {
    let mut text = format!("(set-logic {logic})\n{declarations}\n");
    for assertion in assertions {
        text.push_str(&format!("(assert {assertion})\n"));
    }
    text.push_str("(check-sat)\n");
    text
}

fn assumed_terms(proof: &str) -> Vec<&str> {
    proof
        .lines()
        .filter_map(|line| line.strip_prefix("(assume "))
        .filter_map(|rest| rest.split_once(' '))
        .filter_map(|(_, term)| term.trim_end().strip_suffix(')'))
        .collect()
}

const LIA: &str = "(declare-const x Int)\n(declare-const y Int)\n(declare-const r Bool)";

/// Solve, require a hole-free document whose first `assume` is the authored
/// folded assertion, and require pinned carcara to answer `valid`.
fn assert_bridged(label: &str, problem: &str, authored: &str) {
    let proof = solve_unsat_and_get_proof(problem, label);
    for forbidden in [":rule hole", ":rule trust"] {
        assert!(!proof.contains(forbidden), "{label}: {forbidden}:\n{proof}");
    }
    assert!(
        assumed_terms(&proof).contains(&authored),
        "{label}: the authored assertion {authored} must be assumed verbatim:\n{proof}"
    );
    if let Some(carcara) = require_carcara_or_skip() {
        assert_eq!(
            carcara_verdict_without_allowances(&carcara, label, problem, &proof),
            CarcaraVerdict::Valid,
            "{label}: pinned carcara must re-derive every step:\n{proof}"
        );
    }
}

fn assert_sat(label: &str, problem: &str) {
    let script = format!("(set-option :produce-proofs true)\n{problem}\n");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&parse(&script).expect("parse"))
        .expect("execute");
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("sat"),
        "{label}: the satisfiable twin must stay SAT, got {outputs:?}"
    );
}

#[test]
#[timeout(240_000)]
fn folded_authored_assertions_are_assumed_verbatim_and_bridged() {
    for (label, folded) in [
        ("folded_and_reflexive", "(and (< x 3) (= x x))"),
        ("folded_or_false", "(or (< x 3) false)"),
        ("folded_and_true", "(and (< x 3) true)"),
        ("folded_and_duplicate", "(and (< x 3) (< x 3))"),
        ("folded_eq_true", "(= (< x 3) true)"),
        ("folded_xor_false", "(xor (< x 3) false)"),
        ("folded_distinct_false", "(distinct (< x 3) false)"),
        ("folded_not_and_not", "(not (and (not (< x 3)) (= x x)))"),
        ("folded_ite_same", "(ite r (< x 3) (< x 3))"),
        ("folded_nested", "(or (= (and (< x 3) true) true) false)"),
        ("folded_reversed_comparison", "(or (> 3 x) false)"),
    ] {
        assert_bridged(
            label,
            &problem("QF_LIA", LIA, &[folded, "(>= x 5)"]),
            folded,
        );
        assert_sat(
            &format!("{label}_sat"),
            &problem("QF_LIA", LIA, &[folded, "(>= x 1)"]),
        );
    }
}

/// The fold onto a NEGATED term, a later row that re-spells the folded root
/// (`(not (< x 3))` once overwrote the root's authored spelling), and the
/// lone-generator SOS route.
#[test]
#[timeout(240_000)]
fn folded_negations_and_respelled_roots_are_bridged() {
    assert_bridged(
        "folded_eq_false",
        &problem("QF_LIA", LIA, &["(= (< x 3) false)", "(< x 3)"]),
        "(= (< x 3) false)",
    );
    assert_bridged(
        "folded_root_respelled_by_a_later_row",
        &problem("QF_LIA", LIA, &["(or (< x 3) false)", "(not (< x 3))"]),
        "(or (< x 3) false)",
    );
    assert_bridged(
        "folded_not_eq_false_sos_lane",
        &problem("QF_LIA", LIA, &["(not (= (< x 3) false))", "(>= x 5)"]),
        "(not (= (< x 3) false))",
    );
}

/// The same bridge over the other theories the sweep covered: a Boolean
/// variable root (the atom guard once cost it its whole proof: `unknown`
/// under `:produce-proofs`), an equality AY stores with its operands swapped
/// (`refl` modulo equality order), bit-vectors, and a Real decimal the
/// canonical term spells `(/ 5.0 2.0)` (one unit `la_generic` implication).
#[test]
#[timeout(240_000)]
fn folded_assertions_over_other_theories_are_bridged() {
    assert_bridged(
        "folded_bool_variable",
        &problem(
            "QF_UF",
            "(declare-const p Bool)",
            &["(or p false)", "(not p)"],
        ),
        "(or p false)",
    );
    assert_bridged(
        "folded_uf_swapped_equality",
        &problem(
            "QF_UF",
            "(declare-sort U 0)\n(declare-const a U)\n(declare-const c U)\n(declare-fun f (U) U)",
            &["(or (= (f a) c) false)", "(not (= (f a) c))"],
        ),
        "(or (= (f a) c) false)",
    );
    assert_bridged(
        "folded_uf_swapped_equality_conjunct",
        &problem(
            "QF_UF",
            "(declare-sort U 0)\n(declare-const a U)\n(declare-const c U)\n(declare-fun f (U) U)",
            &["(and (= (f a) c) true)", "(not (= (f a) c))"],
        ),
        "(and (= (f a) c) true)",
    );
    assert_bridged(
        "folded_bv_xor",
        &problem(
            "QF_BV",
            "(declare-const b (_ BitVec 8))",
            &["(xor (bvult b #x03) false)", "(bvuge b #x05)"],
        ),
        "(xor (bvult b #b00000011) false)",
    );
    assert_bridged(
        "folded_real_decimal",
        &problem(
            "QF_LRA",
            "(declare-const y Real)",
            &["(or (< y 2.5) false)", "(>= y 3.0)"],
        ),
        "(or (< y 2.5) false)",
    );
    assert_bridged(
        "folded_real_decimal_conjunct",
        &problem(
            "QF_LRA",
            "(declare-const y Real)",
            &["(and (< y 2.5) true)", "(>= y 3.0)"],
        ),
        "(and (< y 2.5) true)",
    );
}

/// `(assert (or (and p q) false))` + `(assert (not p))`: the `and_pos` over
/// the folded disjunction is re-slotted through `or_pos`, whose disjuncts
/// must follow the ROOT's printed order.
#[test]
#[timeout(120_000)]
fn folded_disjunction_or_pos_keeps_the_roots_disjunct_order() {
    let declarations = "(declare-const p Bool)\n(declare-const q Bool)";
    assert_bridged(
        "folded_or_and_false_first",
        &problem("QF_UF", declarations, &["(or (and p q) false)", "(not p)"]),
        "(or (and p q) false)",
    );
    assert_bridged(
        "folded_or_false_and",
        &problem("QF_UF", declarations, &["(or false (and p q))", "(not p)"]),
        "(or false (and p q))",
    );
}

/// `(assert (and (< (+ x y) 3) true))`: the Farkas lemma over the folded
/// root must be judged over the canonical text the document prints.
#[test]
#[timeout(120_000)]
fn folded_conjunction_theory_lemma_is_judged_over_the_printed_text() {
    assert_bridged(
        "folded_and_true_farkas",
        &problem(
            "QF_LIA",
            LIA,
            &["(and (< (+ x y) 3) true)", "(and (>= x 2) (>= y 2))"],
        ),
        "(and (< (+ x y) 3) true)",
    );
}

/// NEGATIVE TWIN: a fold no checked step reaches keeps an honest, countable
/// `hole` and the authored `assume`; it is never published as verified. The
/// nested decimal fold `(and (or (< y 2.5) false) (= y y))` would need the
/// fold AND the arithmetic implication under the conjunction projection.
#[test]
#[timeout(120_000)]
fn an_unbridged_fold_stays_one_visible_hole() {
    let label = "folded_unbridged_nested_decimal";
    let problem = problem(
        "QF_LRA",
        "(declare-const y Real)",
        &["(and (or (< y 2.5) false) (= y y))", "(>= y 3.0)"],
    );
    let proof = solve_unsat_and_get_proof(&problem, label);
    assert!(
        assumed_terms(&proof).contains(&"(and (or (< y 2.5) false) (= y y))"),
        "{label}: the authored assertion stays the assume:\n{proof}"
    );
    assert_eq!(proof.matches(":rule hole").count(), 1, "{label}:\n{proof}");
    assert!(!proof.contains(":rule trust"), "{label}:\n{proof}");
    if let Some(carcara) = require_carcara_or_skip() {
        assert_eq!(
            carcara_verdict_without_allowances(&carcara, label, &problem, &proof),
            CarcaraVerdict::Holey,
            "{label}:\n{proof}"
        );
    }
}

const LIA_BOOL: &str = "(declare-const x Int)\n(declare-const y Int)\n(declare-const p Bool)\n\
                        (declare-const q Bool)\n(declare-const r Bool)";

/// Every `assume` of `proof` is one of `assertions` as written.
fn assert_every_assume_is_authored(label: &str, proof: &str, assertions: &[&str]) {
    for assumed in assumed_terms(proof) {
        assert!(
            assertions.contains(&assumed),
            "{label}: `{assumed}` is not an assertion of the problem:\n{proof}"
        );
    }
}

/// NO-REGRESSION: a fold that would confine its root beside another override
/// re-spelling a term inside or around it (`boolean_fold/document_spelling.rs`)
/// leaves the root where the base left it, and the base's document stays
/// literally `valid`. With the fold confining these roots, the first five lost
/// their answer under `:produce-proofs` or their checked document (the root
/// printed `(and p (< x 3))` while its `and_pos` conjunct printed the
/// descendant's `(not (not (< x 3)))`), and the last lost it to the
/// implication's planned rendering, which read the first row's spelling on
/// the folded root.
#[test]
#[timeout(240_000)]
fn folds_beside_respelled_terms_keep_the_base_document() {
    for (label, assertions) in [
        (
            "respelled_descendant_under_and",
            &["(and p (not (not (< x 3))))", "(>= x 5)"][..],
        ),
        (
            "respelled_descendant_under_or",
            &["(or r (not (not (< x 3))))", "(>= x 5)", "(not r)"],
        ),
        (
            "respelled_descendant_under_eq",
            &["(= p (not (not (< x 3))))", "p", "(>= x 5)"],
        ),
        (
            "respelled_descendants_under_and",
            &[
                "(and (not (not (< x 3))) (not (not (< y 3))))",
                "(>= (+ x y) 9)",
            ],
        ),
        (
            "respelled_reversed_descendant_under_and",
            &["(and p (not (not (> 3 x))))", "(>= x 5)"],
        ),
        (
            "respelled_ancestor_of_the_folded_root",
            &[
                "(= (< x 3) true)",
                "(=> (= (< x 3) true) (>= (+ y 1) 7))",
                "(< y 6)",
                "(or (< x 3) (> y 100))",
            ],
        ),
    ] {
        let problem = problem("QF_LIA", LIA_BOOL, assertions);
        let proof = solve_unsat_and_get_proof(&problem, label);
        for forbidden in [":rule hole", ":rule trust"] {
            assert!(!proof.contains(forbidden), "{label}: {forbidden}:\n{proof}");
        }
        assert_every_assume_is_authored(label, &proof, assertions);
        if let Some(carcara) = require_carcara_or_skip() {
            assert_eq!(
                carcara_verdict_without_allowances(&carcara, label, &problem, &proof),
                CarcaraVerdict::Valid,
                "{label}:\n{proof}"
            );
        }
    }
}

/// NO-REGRESSION: a fold under a compound root whose descendant carries the
/// row's own spelling keeps the base's UNSAT answer and its honest document:
/// no `trust`, every `assume` authored, and carcara never `invalid` (the base
/// published one disclosed `hole` for each). With the fold confining these
/// roots, each lost its publication under `:produce-proofs`.
#[test]
#[timeout(240_000)]
fn folds_under_respelled_compound_roots_keep_their_answer() {
    for (label, folded) in [
        (
            "or_duplicate_under_and",
            "(and p (or false (< x 3) (< x 3)))",
        ),
        ("eq_true_under_and", "(and p (= (< x 3) true))"),
        ("xor_false_under_and", "(and p (xor (< x 3) false))"),
        ("ite_same_under_and", "(and p (ite q (< x 3) (< x 3)))"),
    ] {
        let assertions = [folded, "(>= x 5)"];
        let problem = problem("QF_LIA", LIA_BOOL, &assertions);
        let proof = solve_unsat_and_get_proof(&problem, label);
        assert!(!proof.starts_with("(error"), "{label}:\n{proof}");
        assert!(!proof.contains(":rule trust"), "{label}:\n{proof}");
        assert_every_assume_is_authored(label, &proof, &assertions);
        if let Some(carcara) = require_carcara_or_skip() {
            assert_ne!(
                carcara_verdict_without_allowances(&carcara, label, &problem, &proof),
                CarcaraVerdict::Invalid,
                "{label}:\n{proof}"
            );
        }
    }
}

/// A folded row whose root already carries a DIFFERENT spelling an earlier
/// pass left there (another row's descendant: AY stores `(= c (f a))`, so
/// `(not (= (f a) c))` spells it `(= (f a) c)`) replaces that entry, because
/// the printer confines the row's own spelling to its `assume`. Before, the
/// disagreement declined the whole map and `:produce-proofs` answered
/// `unknown`.
#[test]
#[timeout(120_000)]
fn a_confined_fold_replaces_a_disagreeing_earlier_spelling() {
    assert_bridged(
        "folded_eq_true_over_a_respelled_root",
        &problem(
            "QF_UF",
            "(declare-sort U 0)\n(declare-const a U)\n(declare-const c U)\n(declare-fun f (U) U)",
            &["(= (= (f a) c) true)", "(not (= (f a) c))"],
        ),
        "(= (= (f a) c) true)",
    );
    assert_bridged(
        "folded_eq_false_over_a_respelled_select",
        &problem(
            "QF_AX",
            "(declare-sort I 0)\n(declare-sort E 0)\n(declare-const m (Array I E))\n\
             (declare-const i I)\n(declare-const v E)",
            &[
                "(= (not (= (select m i) v)) false)",
                "(not (= (select m i) v))",
            ],
        ),
        "(= (not (= (select m i) v)) false)",
    );
}
