// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A premise-free `equiv_*` step whose source PRINTS as a chainable `=`.
//!
//! `(assert (= p q q))` elaborates to `(and (= p q) (= q q))`, which the term
//! store folds to the binary `(= p q)`; the authored-surface override keeps
//! printing it as `(= p q q)` so the `assume` matches the problem. AY's strict
//! checker validated `equiv_pos2` over the binary store term, the printer's
//! surface judge instantiated the two-operand template over the first two of
//! three printed operands, and the document shipped (938ec0327) as
//! `unproved_steps=0 trust_free=yes ay_self_checkable=yes` with
//!
//! ```text
//! (step t3 (cl (not (= p q q)) (not p) q) :rule equiv_pos2)
//! ```
//!
//! which carcara 1.1.0 refuses: "term '(not (= p q q))' is of the wrong form,
//! expected '(not (= phi_1 phi_2))'". The same false green shipped for a
//! reversed chain (`equiv_pos1`), a chain nested in an authored `or`, and a
//! chain over a negated operand. The step is now derived through `nary_elim`
//! and a binary `equiv_*` instance over one chain link.

use super::{require_carcara_or_skip, run_carcara_trust_free, solve_unsat_and_get_proof};
use ntest::timeout;

fn problem(asserts: &[&str]) -> String {
    let mut text = String::from(
        "(set-logic QF_UF)\n(declare-fun p () Bool)\n(declare-fun q () Bool)\n(declare-fun r () Bool)\n",
    );
    for assertion in asserts {
        text.push_str(&format!("(assert {assertion})\n"));
    }
    text.push_str("(check-sat)\n");
    text
}

/// Operand count of every `equiv_pos*`/`equiv_neg*` step's source `=`: the
/// first clause literal, under its `not` for the `pos` rules.
fn equiv_source_arities(proof: &str) -> Vec<(usize, String)> {
    let mut arities = Vec::new();
    for line in proof.lines().map(str::trim) {
        let Some(rule) = ["equiv_pos1", "equiv_pos2", "equiv_neg1", "equiv_neg2"]
            .into_iter()
            .find(|rule| line.ends_with(&format!(":rule {rule})")))
        else {
            continue;
        };
        let clause = line.split_once("(cl ").map_or("", |(_, rest)| rest);
        let first = first_term(clause);
        let source = if rule.starts_with("equiv_pos") {
            first
                .strip_prefix("(not ")
                .and_then(|t| t.strip_suffix(')'))
                .unwrap_or("")
        } else {
            first
        };
        let operands = source
            .strip_prefix("(= ")
            .and_then(|t| t.strip_suffix(')'))
            .map_or(0, count_terms);
        arities.push((operands, line.to_string()));
    }
    arities
}

/// The first balanced term of `text`.
fn first_term(text: &str) -> &str {
    let mut depth = 0usize;
    for (index, byte) in text.bytes().enumerate() {
        match byte {
            b'(' => depth += 1,
            b')' if depth == 0 => return &text[..index],
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return &text[..=index];
                }
            }
            b' ' if depth == 0 => return &text[..index],
            _ => {}
        }
    }
    text
}

fn count_terms(mut text: &str) -> usize {
    let mut count = 0;
    while !text.trim_start().is_empty() {
        text = text.trim_start();
        let term = first_term(text);
        text = &text[term.len()..];
        count += 1;
    }
    count
}

#[test]
fn equiv_source_arity_reader_counts_printed_operands() {
    let arities = equiv_source_arities(
        "(step t3 (cl (not (= p q q)) (not p) q) :rule equiv_pos2)\n\
         (step t4 (cl (= (f a) b) (not (f a)) (not b)) :rule equiv_neg1)",
    );
    let counts: Vec<usize> = arities.iter().map(|(count, _)| *count).collect();
    assert_eq!(counts, vec![3, 2]);
}

#[test]
#[timeout(60_000)]
fn chainable_equality_equiv_steps_are_derived_not_mislabelled() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let mut cases: Vec<Vec<&str>> = Vec::new();
    for chain in ["(= p q q)", "(= p p q)", "(= p q p q)", "(= p q q q)"] {
        cases.push(vec![chain, "p", "(not q)"]);
        cases.push(vec![chain, "(not p)", "q"]);
    }
    // Each measured `invalid` on 938ec0327: a chain whose only matching link
    // is REVERSED (`equiv_pos1`), a chain nested in an authored `or`, and a
    // chain over a negated operand (the link instance states `(not (not p))`).
    cases.push(vec!["(= q p p)", "p", "(not q)"]);
    cases.push(vec!["(or (= p q q) r)", "(not r)", "p", "(not q)"]);
    cases.push(vec!["(= (not p) q q)", "(not p)", "(not q)"]);
    for (index, asserts) in cases.iter().enumerate() {
        let label = format!("chainable_equality_{index}");
        let text = problem(asserts);
        let proof = solve_unsat_and_get_proof(&text, &label);
        for (operands, line) in equiv_source_arities(&proof) {
            assert_eq!(
                operands, 2,
                "{label}: an equiv_* step names a {operands}-operand source:\n{line}\n\n{proof}"
            );
        }
        assert!(
            proof.contains(":rule nary_elim)"),
            "{label}: the chain must be expanded by a checked nary_elim:\n{proof}"
        );
        assert!(
            run_carcara_trust_free(&carcara, &label, &text, &proof),
            "{label}: the chainable-equality derivation must replay without trust:\n{proof}"
        );
    }
}
