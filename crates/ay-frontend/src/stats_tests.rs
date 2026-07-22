// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::parse;

use super::collect_formula_stats;

#[test]
fn test_collect_formula_stats_counts_terms_sorts_and_theories() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (and (> x 0) (= y (+ x 1))))
        (check-sat)
    "#;
    let commands = parse(input).expect("parse");
    let stats = collect_formula_stats(&commands);

    assert_eq!(stats.commands, 5);
    assert_eq!(
        stats.sort_distribution.get("Int").copied(),
        Some(2),
        "two declared Int constants"
    );
    assert!(
        stats.terms >= 8,
        "expected nested AST terms to be counted, got {}",
        stats.terms
    );
    assert_eq!(
        stats.theory_usage.get("arith").copied(),
        Some(2),
        ">, + should contribute arithmetic operator usage"
    );
    assert_eq!(
        stats.theory_usage.get("bool").copied(),
        Some(2),
        "and, = should contribute boolean/core operator usage"
    );
}

#[test]
fn test_formula_stats_display_is_smt2_style() {
    let input = r#"
        (set-logic QF_UF)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (assert (= (f x) x))
        (check-sat)
    "#;
    let commands = parse(input).expect("parse");
    let stats = collect_formula_stats(&commands);
    let rendered = format!("{stats}");

    assert!(rendered.contains("(:formula-statistics"));
    assert!(rendered.contains(":commands 5"));
    assert!(rendered.contains(":sort.Int"));
    assert!(rendered.contains(":theory.uf_or_other"));
}
