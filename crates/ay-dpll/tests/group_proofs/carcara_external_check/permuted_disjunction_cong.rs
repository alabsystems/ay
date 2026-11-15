// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An authored disjunction the term store keeps in another operand order,
//! rewritten to `false` by `cong`, with and without a nullary macro.
//!
//! `(assert (< x 3))`, `(assert (or (not (< x 3)) r))`, `(assert (not r))`:
//! the `or` interns as `(or r (not (< x 3)))` and its root override restores
//! the authored order, so the printed `cong` conclusion lists its operands
//! in a different order than the internal premises. MEASURED at `938ec0327`:
//! the step shipped `:premises (t5 t9)` in stored order under the authored
//! conclusion, and pinned carcara 1.1.0 refused the `trust_free=yes`
//! document ("premise '(= r false)' doesn't justify conclusion arguments
//! '(not (< x 3))' and 'false'"). With `(>= x 3)` the atom's authored
//! spelling is confined to its `assume` while the `not` above it keeps a
//! descendant override, and the `equiv_neg2` step read `(= (not (>= x 3))
//! false)` beside the literal `(not (<= 3 x))` ("expected terms to be equal:
//! '(not (>= x 3))' and '(not (<= 3 x))'"), again `trust_free=yes`.
//!
//! The macro twins `(define-fun lo () Bool (< x 3))` reach the same two
//! steps: `(assert lo)` already at `938ec0327`, and `(assert (not (not lo)))`
//! once the definition premise bridged its root (it was refused before).
//! Every UNSAT document must be literally `valid`; every SAT twin stays SAT.

use super::{
    carcara_verdict_without_allowances, parse, require_carcara_or_skip, solve_unsat_and_get_proof,
    CarcaraVerdict, Executor,
};
use ntest::timeout;

const DECLARATIONS: &str = "(declare-const x Int)\n(declare-const r Bool)\n";

fn problem(definition: &str, first: &str, disjunction: &str, last: &str) -> String {
    format!(
        "(set-logic ALL)\n{DECLARATIONS}{definition}\n(assert {first})\n(assert {disjunction})\n{last}(check-sat)\n"
    )
}

/// `step id` -> its printed clause, for every `step` line of `proof`.
fn step_clauses(proof: &str) -> Vec<(&str, &str)> {
    proof
        .lines()
        .filter_map(|line| line.strip_prefix("(step "))
        .filter_map(|rest| rest.split_once(' '))
        .filter_map(|(id, rest)| Some((id, rest.split(" :rule ").next()?)))
        .collect()
}

/// Every `cong` step whose conclusion rewrites `disjunction` cites, FIRST,
/// the premise that rewrites its first printed operand `first_operand`.
fn assert_cong_premises_in_printed_order(
    label: &str,
    proof: &str,
    disjunction: &str,
    first_operand: &str,
) {
    let clauses = step_clauses(proof);
    let mut seen = false;
    for line in proof.lines().filter(|line| line.contains(" :rule cong ")) {
        if !line.contains(&format!("(cl (= {disjunction} ")) {
            continue;
        }
        seen = true;
        let premises = line
            .split(":premises (")
            .nth(1)
            .and_then(|rest| rest.split(')').next())
            .unwrap_or("");
        let first = premises.split_whitespace().next().unwrap_or("");
        let clause = clauses
            .iter()
            .find(|(id, _)| *id == first)
            .map_or("", |(_, clause)| *clause);
        assert!(
            clause.starts_with(&format!("(cl (= {first_operand} ")),
            "{label}: the first `cong` premise must rewrite `{first_operand}`, got `{clause}`:\n{proof}"
        );
    }
    assert!(seen, "{label}: no `cong` over `{disjunction}`:\n{proof}");
}

fn assert_valid(label: &str, problem: &str) -> String {
    let proof = solve_unsat_and_get_proof(problem, label);
    for forbidden in [":rule hole", ":rule trust"] {
        assert!(!proof.contains(forbidden), "{label}: {forbidden}:\n{proof}");
    }
    if let Some(carcara) = require_carcara_or_skip() {
        assert_eq!(
            carcara_verdict_without_allowances(&carcara, label, problem, &proof),
            CarcaraVerdict::Valid,
            "{label}: pinned carcara must re-derive every step:\n{proof}"
        );
    }
    proof
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
fn a_permuted_disjunction_ships_its_cong_premises_in_printed_order() {
    let disjunction = "(or (not (< x 3)) r)";
    let macro_lo = "(define-fun lo () Bool (< x 3))";
    for (label, definition, first) in [
        ("permuted_or_cong_plain", "", "(< x 3)"),
        ("permuted_or_cong_double_negated", "", "(not (not (< x 3)))"),
        ("permuted_or_cong_macro", macro_lo, "lo"),
        (
            "permuted_or_cong_macro_double_negated",
            macro_lo,
            "(not (not lo))",
        ),
    ] {
        let proof = assert_valid(
            label,
            &problem(definition, first, disjunction, "(assert (not r))\n"),
        );
        assert_cong_premises_in_printed_order(label, &proof, disjunction, "(not (< x 3))");
        assert_sat(
            &format!("{label}_sat"),
            &problem(definition, first, disjunction, ""),
        );
    }
}

#[test]
#[timeout(120_000)]
fn a_negated_comparison_descendant_is_bridged_to_its_confined_atom() {
    let disjunction = "(or (not (>= x 3)) r)";
    let macro_lo = "(define-fun lo () Bool (>= x 3))";
    for (label, definition, first) in [
        ("negated_comparison_descendant_plain", "", "(>= x 3)"),
        ("negated_comparison_descendant_macro", macro_lo, "lo"),
        (
            "negated_comparison_descendant_macro_double_negated",
            macro_lo,
            "(not (not lo))",
        ),
    ] {
        assert_valid(
            label,
            &problem(definition, first, disjunction, "(assert (not r))\n"),
        );
        assert_sat(
            &format!("{label}_sat"),
            &problem(definition, first, disjunction, ""),
        );
    }
}
