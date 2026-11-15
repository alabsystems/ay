// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authored spellings whose `unsat` the printer used to publish without a
//! document (`ay.proof.artifact-refused`; `--strict-proofs` answered
//! `unknown`), and their SAT twins.
//!
//! MEASURED at `e9ba9acac` with `ay --proof`:
//! * a NEGATIVE fold over an operand that keeps its own authored spelling,
//!   `(= (bvult b #x03) false)` + `(bvult b #x03)` and its `xor`, `or`,
//!   `distinct`, `ite` and `=>` siblings over bit-vector, UF, array and
//!   arithmetic atoms: "the printed premises do not eliminate the printed
//!   resolution pivot" (36 files of the folded-assertion sweep);
//! * `(not (distinct x y))` or `(not (not (= x y)))` feeding a `cong`:
//!   "surface congruence premise is not a printed equality";
//! * `(=> (>= y 0) (<= x 3))` beside `(assert (>= y 0))`: "planned authored
//!   assume equivalence no longer has a checked derivation".
//!
//! Each document now assumes the authored assertion verbatim and derives the
//! printed term with stock rules (`alethe_printer/authored_assume/`
//! `boolean_fold.rs`, `printed_terms.rs`, `post_commit.rs`, and
//! `surface_equivalence/comparison.rs`); pinned carcara must answer `valid`
//! with no allowance. A negated CHAINED comparison stays an honest refusal:
//! pinned carcara has no rule that expands one.

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

/// Solve, require a hole-free document that assumes `authored` verbatim and
/// nothing the input does not assert, and require pinned carcara to answer
/// `valid`.
fn assert_bridged(label: &str, problem: &str, assertions: &[&str], authored: &str) {
    let proof = solve_unsat_and_get_proof(problem, label);
    for forbidden in [":rule hole", ":rule trust"] {
        assert!(!proof.contains(forbidden), "{label}: {forbidden}:\n{proof}");
    }
    let assumed = assumed_terms(&proof);
    assert!(
        assumed.contains(&authored),
        "{label}: the authored assertion {authored} must be assumed verbatim:\n{proof}"
    );
    for term in assumed {
        assert!(
            assertions.contains(&term),
            "{label}: `{term}` is assumed but not asserted:\n{proof}"
        );
    }
    if let Some(carcara) = require_carcara_or_skip() {
        assert_eq!(
            carcara_verdict_without_allowances(&carcara, label, problem, &proof),
            CarcaraVerdict::Valid,
            "{label}: pinned carcara must re-derive every step:\n{proof}"
        );
    }
}

fn last_output(problem: &str, get_proof: bool) -> (Vec<String>, String) {
    let script = format!(
        "(set-option :produce-proofs true)\n{problem}\n{}",
        if get_proof { "(get-proof)\n" } else { "" }
    );
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&parse(&script).expect("parse"))
        .expect("execute");
    let last = outputs.last().cloned().unwrap_or_default();
    (outputs, last)
}

fn assert_sat(label: &str, problem: &str) {
    let (outputs, last) = last_output(problem, false);
    assert_eq!(
        last, "sat",
        "{label}: the satisfiable twin must stay SAT, got {outputs:?}"
    );
}

/// One UNSAT case: its assertions, the authored assertion the document must
/// assume verbatim, and the assertions whose conjunction is SAT.
struct Case {
    label: &'static str,
    logic: &'static str,
    declarations: &'static str,
    assertions: &'static [&'static str],
    authored: &'static str,
    sat_twin: &'static [&'static str],
}

fn check(case: &Case) {
    assert_bridged(
        case.label,
        &problem(case.logic, case.declarations, case.assertions),
        case.assertions,
        case.authored,
    );
    assert_sat(
        &format!("{}_sat", case.label),
        &problem(case.logic, case.declarations, case.sat_twin),
    );
}

const BV: &str = "(declare-const b (_ BitVec 8))";
const UF: &str = "(declare-sort U 0)\n(declare-const a U)\n(declare-const c U)\n\
                  (declare-fun f (U) U)";
const AX: &str = "(declare-sort I 0)\n(declare-sort E 0)\n(declare-const m (Array I E))\n\
                  (declare-const i I)\n(declare-const v E)";
const LIA: &str = "(declare-const x Int)\n(declare-const y Int)\n(declare-const m Int)";
const LRA: &str = "(declare-const x Real)\n(declare-const y Real)";

#[test]
#[timeout(240_000)]
fn a_negative_fold_over_a_respelled_operand_is_bridged_onto_the_documents_rendering() {
    for case in [
        Case {
            label: "negative_fold_bv_eq_false",
            logic: "QF_BV",
            declarations: BV,
            assertions: &["(= (bvult b #x03) false)", "(bvult b #x03)"],
            authored: "(= (bvult b #x03) false)",
            sat_twin: &["(= (bvult b #x03) false)"],
        },
        Case {
            label: "negative_fold_bv_xor_true",
            logic: "QF_BV",
            declarations: BV,
            assertions: &["(xor (bvslt b #x03) true)", "(bvslt b #x03)"],
            authored: "(xor (bvslt b #x03) true)",
            sat_twin: &["(xor (bvslt b #x03) true)"],
        },
        Case {
            label: "negative_fold_uf_eq_false",
            logic: "QF_UF",
            declarations: UF,
            assertions: &["(= (= (f a) c) false)", "(= (f a) c)"],
            authored: "(= (= (f a) c) false)",
            sat_twin: &["(= (= (f a) c) false)"],
        },
        Case {
            label: "negative_fold_ax_distinct_true",
            logic: "QF_AX",
            declarations: AX,
            assertions: &["(distinct (= (select m i) v) true)", "(= (select m i) v)"],
            authored: "(distinct (= (select m i) v) true)",
            sat_twin: &["(distinct (= (select m i) v) true)"],
        },
        Case {
            label: "negative_fold_lia_implies_false",
            logic: "QF_LIA",
            declarations: LIA,
            assertions: &["(=> (> x 3) false)", "(> x 3)"],
            authored: "(=> (> x 3) false)",
            sat_twin: &["(=> (> x 3) false)"],
        },
        Case {
            label: "negative_fold_lra_ite",
            logic: "QF_LRA",
            declarations: LRA,
            assertions: &["(ite (< y 2.5) false true)", "(< y 2.5)"],
            authored: "(ite (< y 2.5) false true)",
            sat_twin: &["(ite (< y 2.5) false true)"],
        },
        Case {
            label: "fold_up_to_equality_order",
            logic: "QF_LIA",
            declarations: LIA,
            assertions: &["(or (= (* 3 m) x) false)", "(>= x 1)", "(<= (* 3 m) 0)"],
            authored: "(or (= (* 3 m) x) false)",
            sat_twin: &["(or (= (* 3 m) x) false)", "(>= x 1)"],
        },
    ] {
        check(&case);
    }
}

#[test]
#[timeout(240_000)]
fn a_negated_distinct_or_double_negation_feeds_cong_as_a_printed_equality() {
    for case in [
        Case {
            label: "negated_distinct_cong",
            logic: "QF_LIA",
            declarations: LIA,
            assertions: &["(not (distinct x y))", "(> x (+ y 2))"],
            authored: "(not (distinct x y))",
            sat_twin: &["(not (distinct x y))", "(>= x y)"],
        },
        Case {
            label: "negated_distinct_swapped_cong",
            logic: "QF_LIA",
            declarations: LIA,
            assertions: &["(not (distinct y x))", "(> x (+ y 2))"],
            authored: "(not (distinct y x))",
            sat_twin: &["(not (distinct y x))", "(>= x y)"],
        },
        Case {
            label: "double_negation_cong",
            logic: "QF_LIA",
            declarations: LIA,
            assertions: &["(not (not (= x y)))", "(> x (+ y 2))"],
            authored: "(not (not (= x y)))",
            sat_twin: &["(not (not (= x y)))", "(>= x y)"],
        },
    ] {
        check(&case);
    }
}

#[test]
#[timeout(240_000)]
fn an_implication_beside_its_confined_antecedent_keeps_its_bridge() {
    for case in [
        Case {
            label: "implication_beside_antecedent_lia",
            logic: "QF_LIA",
            declarations: LIA,
            assertions: &["(=> (>= y 0) (<= x 3))", "(> x 5)", "(>= y 0)"],
            authored: "(=> (>= y 0) (<= x 3))",
            sat_twin: &["(=> (>= y 0) (<= x 3))", "(>= y 0)"],
        },
        Case {
            label: "implication_beside_antecedent_lra",
            logic: "QF_LRA",
            declarations: LRA,
            assertions: &["(=> (>= y 0.0) (<= x 2.0))", "(>= y 0.0)", "(> x 2.0)"],
            authored: "(=> (>= y 0.0) (<= x 2.0))",
            sat_twin: &["(=> (>= y 0.0) (<= x 2.0))", "(>= y 0.0)"],
        },
    ] {
        check(&case);
    }
}

/// NEGATIVE TWIN: a negated chained comparison has no pinned-carcara rule, so
/// the publication stays refused, loudly, and never prints a `hole` for it.
#[test]
#[timeout(120_000)]
fn a_negated_chained_comparison_stays_an_honest_refusal() {
    let problem = problem("QF_LIA", LIA, &["(not (> x 60000 0))", "(> x 60000)"]);
    let (outputs, last) = last_output(&problem, true);
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{outputs:?}"
    );
    assert!(last.contains("UNVERIFIABLE PROOF"), "{last}");
    assert!(!last.contains(":rule hole"), "{last}");
}
