// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bool nullary `define-fun`s used as whole assertions, and their SAT twins.
//!
//! `(assert lo)` over `(define-fun lo () Bool (bvult x #x3))` elaborates to
//! the root `(bvult x #x3)`. At `32eace1dc` every document below either
//! published the EXPANDED body as its `assume`, which is no premise of the
//! problem (pinned carcara 1.1.0: "could not match term to any of the original
//! problem premises"), or, for the descendant shape, a `trust_free=yes`
//! document carcara refused at an `equiv_neg2` over `(not m)` and
//! `(not (< x 3))`. Carcara, run without `--apply-function-defs`, holds
//! `(= lo body)` as a premise, and every document now bridges the authored
//! assertion through it.
//!
//! Three shapes reached the same foreign `assume` by other routes: a double
//! negation `mk_not` dropped (`(not (not lo))`, stripped with `not_simplify`),
//! a final-boundary bit-blast candidate that purged a source row's macro
//! spelling (`(not lo)` over an 8-bit `bvslt`), and a raw root whose
//! comparison raw interning canonicalized (`(and lo r)` over `(>= x 3)`).
//!
//! Every UNSAT document must be literally `valid` with no allowance.

use super::{
    carcara_verdict_without_allowances, parse, require_carcara_or_skip, solve_unsat_and_get_proof,
    CarcaraVerdict, Executor,
};
use ntest::timeout;

fn problem(declarations: &str, assertions: &[&str]) -> String {
    let mut text = format!("(set-logic ALL)\n{declarations}\n");
    for assertion in assertions {
        text.push_str(&format!("(assert {assertion})\n"));
    }
    text.push_str("(check-sat)\n");
    text
}

const BV_LO: &str = "(declare-const x (_ BitVec 4))\n(define-fun lo () Bool (bvult x #x3))";
const INT_LO: &str = "(declare-const x Int)\n(define-fun lo () Bool (< x 3))";
const NESTED_LO: &str = "(declare-const x (_ BitVec 4))\n\
    (define-fun three () (_ BitVec 4) #x3)\n(define-fun lo () Bool (bvult x three))";
const MACRO_OF_MACRO: &str = "(declare-const x (_ BitVec 4))\n\
    (define-fun lo () Bool (bvult x #x3))\n(define-fun lo2 () Bool lo)";
const DESCENDANT: &str =
    "(declare-const x Int)\n(declare-const r Bool)\n(define-fun m () Bool (< x 3))";
const BOOLREF_LO: &str =
    "(declare-const x Int)\n(define-fun lo0 () Bool (< x 3))\n(define-fun lo () Bool lo0)";
const BVS_LO: &str = "(declare-const x (_ BitVec 8))\n(define-fun lo () Bool (bvslt x #x00))";
const GEQ_LO: &str =
    "(declare-const x Int)\n(declare-const r Bool)\n(define-fun lo () Bool (>= x 3))";

fn assumed_terms(proof: &str) -> Vec<&str> {
    proof
        .lines()
        .filter_map(|line| line.strip_prefix("(assume "))
        .filter_map(|rest| rest.split_once(' '))
        .filter_map(|(_, term)| term.trim_end().strip_suffix(')'))
        .collect()
}

/// Solve, require a hole-free document pinned carcara checks `valid`, and
/// require exactly the authored row and the definition premises among its
/// `assume`s, never the expanded body.
fn assert_bridged(label: &str, problem: &str, authored: &str, premises: &[&str], expanded: &str) {
    let proof = solve_unsat_and_get_proof(problem, label);
    for forbidden in [":rule hole", ":rule trust"] {
        assert!(!proof.contains(forbidden), "{label}: {forbidden}:\n{proof}");
    }
    let assumed = assumed_terms(&proof);
    assert!(assumed.contains(&authored), "{label}: {authored}:\n{proof}");
    for premise in premises {
        assert!(assumed.contains(premise), "{label}: {premise}:\n{proof}");
    }
    assert!(
        !assumed.contains(&expanded),
        "{label}: the expanded body is no premise of the problem:\n{proof}"
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
#[timeout(120_000)]
fn a_bool_macro_whole_assertion_is_bridged_through_its_definition() {
    let bv_premise = "(= lo (bvult x #x3))";
    assert_bridged(
        "nullary_macro_bv_whole",
        &problem(BV_LO, &["lo", "(bvuge x #x5)"]),
        "lo",
        &[bv_premise],
        "(bvult x #b0011)",
    );
    assert_bridged(
        "nullary_macro_int_whole",
        &problem(INT_LO, &["lo", "(>= x 5)"]),
        "lo",
        &["(= lo (< x 3))"],
        "(< x 3)",
    );
    assert_bridged(
        "nullary_macro_nested_whole",
        &problem(NESTED_LO, &["lo", "(bvuge x #x5)"]),
        "lo",
        &["(= lo (bvult x three))", "(= three #x3)"],
        "(bvult x #b0011)",
    );
    assert_bridged(
        "nullary_macro_macro_of_macro",
        &problem(MACRO_OF_MACRO, &["lo2", "(bvuge x #x5)"]),
        "lo2",
        &["(= lo2 lo)", bv_premise],
        "(bvult x #b0011)",
    );
    assert_sat(
        "nullary_macro_bv_whole_sat",
        &problem(BV_LO, &["lo", "(bvuge x #x1)"]),
    );
    assert_sat(
        "nullary_macro_int_whole_sat",
        &problem(INT_LO, &["lo", "(>= x 1)"]),
    );
}

#[test]
#[timeout(120_000)]
fn a_negated_bool_macro_is_bridged_through_its_definition() {
    assert_bridged(
        "nullary_macro_bv_not",
        &problem(BV_LO, &["(not lo)", "(bvult x #x2)"]),
        "(not lo)",
        &["(= lo (bvult x #x3))"],
        "(not (bvult x #b0011))",
    );
    assert_sat(
        "nullary_macro_bv_not_sat",
        &problem(BV_LO, &["(not lo)", "(bvuge x #x5)"]),
    );
}

#[test]
#[timeout(120_000)]
fn a_macro_named_descendant_never_rides_the_document() {
    assert_bridged(
        "nullary_macro_descendant",
        &problem(DESCENDANT, &["m", "(or r (not m))", "(not r)"]),
        "(or r (not m))",
        &["m", "(= m (< x 3))"],
        "(or r (not (< x 3)))",
    );
    assert_sat(
        "nullary_macro_descendant_sat",
        &problem(DESCENDANT, &["m", "(or r (not m))"]),
    );
}

#[test]
#[timeout(120_000)]
fn a_double_negated_bool_macro_is_stripped_and_bridged() {
    assert_bridged(
        "nullary_macro_int_not_not",
        &problem(INT_LO, &["(not (not lo))", "(>= x 5)"]),
        "(not (not lo))",
        &["(= lo (< x 3))"],
        "(< x 3)",
    );
    assert_bridged(
        "nullary_macro_boolref_not_not",
        &problem(BOOLREF_LO, &["(not (not lo))", "(>= x 5)"]),
        "(not (not lo))",
        &["(= lo lo0)", "(= lo0 (< x 3))"],
        "(< x 3)",
    );
    assert_sat(
        "nullary_macro_int_not_not_sat",
        &problem(INT_LO, &["(not (not lo))", "(>= x 1)"]),
    );
}

#[test]
#[timeout(120_000)]
fn a_final_boundary_candidate_keeps_a_macro_row_spelling() {
    assert_bridged(
        "nullary_macro_bvs_not",
        &problem(BVS_LO, &["(not lo)", "(bvslt x #xf0)"]),
        "(not lo)",
        &["(= lo (bvslt x #x00))"],
        "(not (bvslt x #b00000000))",
    );
    assert_sat(
        "nullary_macro_bvs_not_sat",
        &problem(BVS_LO, &["(not lo)", "(bvsge x #x05)"]),
    );
}

#[test]
#[timeout(120_000)]
fn a_canonicalized_raw_root_is_bridged_through_its_macro_row() {
    assert_bridged(
        "nullary_macro_geq_and",
        &problem(GEQ_LO, &["(and lo r)", "(< x 1)"]),
        "(and lo r)",
        &["(= lo (>= x 3))"],
        "(and (<= 3 x) r)",
    );
    assert_sat(
        "nullary_macro_geq_and_sat",
        &problem(GEQ_LO, &["(and lo r)", "(> x 5)"]),
    );
}

/// A macro row FOLLOWED by a row that negates the expanded body. The ordinary
/// collector descends the later `(not body)` onto the macro row's own root
/// and overwrites its spelling with `body`. MEASURED with the bare-symbol
/// bridge alone: `lo` then `(not (bvult x #x3))` answered `unknown` under
/// `:produce-proofs` (the restoration met the descendant spelling on the
/// root and declined the whole reconstruction), the Int twin published a
/// holey document, and `(not (not lo))` then `(not (< x 3))` still
/// published `(assume t0 (< x 3))`, which pinned carcara 1.1.0 refused. The
/// reversed row order was already valid.
#[test]
#[timeout(120_000)]
fn a_macro_row_keeps_its_spelling_over_a_later_negated_body() {
    assert_bridged(
        "nullary_macro_bv_whole_then_negated_body",
        &problem(BV_LO, &["lo", "(not (bvult x #x3))"]),
        "lo",
        &["(= lo (bvult x #x3))"],
        "(bvult x #b0011)",
    );
    assert_bridged(
        "nullary_macro_int_whole_then_negated_body",
        &problem(INT_LO, &["lo", "(not (< x 3))"]),
        "lo",
        &["(= lo (< x 3))"],
        "(< x 3)",
    );
    assert_bridged(
        "nullary_macro_int_not_not_then_negated_body",
        &problem(INT_LO, &["(not (not lo))", "(not (< x 3))"]),
        "(not (not lo))",
        &["(= lo (< x 3))"],
        "(< x 3)",
    );
    assert_sat(
        "nullary_macro_bv_whole_then_negated_body_sat",
        &problem(BV_LO, &["lo", "(not (bvult x #x2))"]),
    );
    assert_sat(
        "nullary_macro_int_not_not_then_negated_body_sat",
        &problem(INT_LO, &["(not (not lo))", "(not (< x 1))"]),
    );
}

/// A negated macro whose body is itself a negation, and an equality body
/// authored in the orientation the term store does not keep. `mk_not` drops
/// the double negation the unfolding exposes and the store orients `(= 3 x)`
/// as `(= x 3)`, so neither root keeps a head `cong` can follow. MEASURED
/// with the bare-symbol and double-negation bridges alone: each query
/// published the canonical `(assume t0 (< x 3))` or `(assume t0 (= x 3))`
/// under `foreign_assumes=yes`, and pinned carcara 1.1.0 refused it ("could
/// not match term to any of the original problem premises").
#[test]
#[timeout(120_000)]
fn a_negation_bodied_macro_under_not_and_a_flipped_equality_are_bridged() {
    const INT_NLO: &str = "(declare-const x Int)\n(define-fun nlo () Bool (not (< x 3)))";
    const INT_HI: &str = "(declare-const x Int)\n(define-fun lo () Bool (< x 3))\n\
        (define-fun hi () Bool (not lo))";
    const INT_TOP: &str = "(declare-const x Int)\n(define-fun lo () Bool (< x 3))\n\
        (define-fun hi () Bool (not lo))\n(define-fun top () Bool (not hi))";
    const INT_EQ: &str = "(declare-const x Int)\n(define-fun lo () Bool (= 3 x))";
    assert_bridged(
        "nullary_macro_int_negated_negation_body",
        &problem(INT_NLO, &["(not nlo)", "(>= x 5)"]),
        "(not nlo)",
        &["(= nlo (not (< x 3)))"],
        "(< x 3)",
    );
    assert_bridged(
        "nullary_macro_int_negated_macro_of_macro",
        &problem(INT_HI, &["(not hi)", "(>= x 5)"]),
        "(not hi)",
        &["(= hi (not lo))", "(= lo (< x 3))"],
        "(< x 3)",
    );
    assert_bridged(
        "nullary_macro_int_macro_of_negated_macro",
        &problem(INT_TOP, &["top", "(>= x 5)"]),
        "top",
        &["(= top (not hi))", "(= hi (not lo))", "(= lo (< x 3))"],
        "(< x 3)",
    );
    assert_bridged(
        "nullary_macro_int_flipped_equality",
        &problem(INT_EQ, &["lo", "(= x 4)"]),
        "lo",
        &["(= lo (= 3 x))"],
        "(= x 3)",
    );
    assert_sat(
        "nullary_macro_int_negated_negation_body_sat",
        &problem(INT_NLO, &["(not nlo)", "(< x 1)"]),
    );
    assert_sat(
        "nullary_macro_int_negated_macro_of_macro_sat",
        &problem(INT_HI, &["(not hi)", "(< x 1)"]),
    );
    assert_sat(
        "nullary_macro_int_macro_of_negated_macro_sat",
        &problem(INT_TOP, &["top", "(< x 1)"]),
    );
    assert_sat(
        "nullary_macro_int_flipped_equality_sat",
        &problem(INT_EQ, &["lo", "(< x 4)"]),
    );
}

/// A raw root among more macro rows than any probe budget: `(and m_i (> x_i
/// (- 5)))` interns `m_i`'s `(> x_i i)` as `(< i x_i)`, so no expansion spells
/// the root and the pass looks the row up by its raw re-intern. MEASURED
/// under the 64-probe search this lookup replaced: valid through 64 rows, and
/// from 65 rows upward the query published `(assume t1 (and (< 0 x0) (> x0
/// (- 5))))`, which pinned carcara 1.1.0 refused ("could not match term to
/// any of the original problem premises").
#[test]
#[timeout(300_000)]
fn a_raw_macro_root_among_many_macro_rows_is_still_bridged() {
    let rows = 70;
    let mut declarations = String::new();
    let mut assertions = Vec::new();
    for i in 0..rows {
        declarations.push_str(&format!(
            "(declare-const x{i} Int)\n(define-fun m{i} () Bool (> x{i} {i}))\n"
        ));
        assertions.push(format!("(and m{i} (> x{i} (- 5)))"));
    }
    let mut unsat: Vec<&str> = assertions.iter().map(String::as_str).collect();
    unsat.push("(< x0 0)");
    assert_bridged(
        "nullary_macro_seventy_rows",
        &problem(&declarations, &unsat),
        "(and m0 (> x0 (- 5)))",
        &["(= m0 (> x0 0))"],
        "(and (< 0 x0) (> x0 (- 5)))",
    );
    unsat.pop();
    unsat.push("(> x0 0)");
    assert_sat(
        "nullary_macro_seventy_rows_sat",
        &problem(&declarations, &unsat),
    );
}

/// Require `unsat` and NO Alethe document: the proof export refuses.
fn assert_document_withheld(label: &str, problem: &str) {
    let script = format!("(set-option :produce-proofs true)\n{problem}(get-proof)\n");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&parse(&script).expect("parse"))
        .expect("execute");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{label}: the verdict is the native proof's, got {outputs:?}"
    );
    let document = outputs.last().map(String::as_str).unwrap_or("");
    assert!(
        document.starts_with("(error ") && !document.contains("(assume "),
        "{label}: a macro row no stock rule bridges must withhold the document:\n{document}"
    );
}

/// A macro row the printer can neither confine by head nor bridge through its
/// definition premise. MEASURED before the refusal: a `let` body (`m`) and a
/// store/select body (`lo`) each published the EXPANDED body as the `assume`
/// (`(< (+ x 1) 0)`, `(= v w)`) under `foreign_assumes=yes`, and pinned
/// carcara 1.1.0 refused it ("could not match term to any of the original
/// problem premises"). The document is now withheld and the verdict kept;
/// the SAT twins stay SAT.
#[test]
#[timeout(120_000)]
fn an_unbridgeable_macro_row_withholds_the_document() {
    const LET_M: &str = "(declare-const x Int)\n(define-fun m () Bool (let ((y (+ x 1))) (< y 0)))";
    const ARRAY_LO: &str = "(declare-const a (Array Int Int))\n(declare-const v Int)\n\
        (declare-const w Int)\n(define-fun lo () Bool (= (select (store a 0 v) 0) w))";
    assert_document_withheld("nullary_macro_let_body", &problem(LET_M, &["m", "(> x 5)"]));
    assert_document_withheld(
        "nullary_macro_array_body",
        &problem(ARRAY_LO, &["lo", "(not (= v w))"]),
    );
    assert_sat(
        "nullary_macro_let_body_sat",
        &problem(LET_M, &["m", "(< x (- 5))"]),
    );
    assert_sat(
        "nullary_macro_array_body_sat",
        &problem(ARRAY_LO, &["lo", "(= v 1)"]),
    );
}
