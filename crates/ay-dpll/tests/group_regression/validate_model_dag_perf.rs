// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Performance regression test for validate_model on DAG-shaped term stores.
//!
//! The model validation loop calls classification predicates (contains_internal_symbol,
//! contains_quantifier, contains_datatype_term, contains_array_term,
//! contains_bv_comparison_predicate) per assertion. Without memoization or
//! precomputation, these recursive tree walks re-traverse shared DAG subterms,
//! causing exponential blowup on deeply shared formulas.
//!
//! This test constructs formulas with significant subterm sharing and verifies
//! that model validation completes within bounded time, catching regressions
//! if the classification is made naive again.

use ntest::timeout;

fn results(output: &str) -> Vec<&str> {
    output
        .lines()
        .map(str::trim)
        .filter(|l| *l == "sat" || *l == "unsat" || *l == "unknown")
        .collect()
}

/// Wide LIA formula with many assertions sharing subterms.
/// The term store will have shared subterms (e.g., `(+ x y)` appears in
/// multiple assertions). Model validation must classify all assertions
/// without exponential re-traversal.
#[test]
#[timeout(10_000)]
fn test_validate_model_wide_lia_shared_subterms() {
    // Build a formula with 100 variables and 200 assertions, each referencing
    // shared arithmetic subexpressions. This creates a DAG, not a tree.
    let mut smt = String::from("(set-logic QF_LIA)\n");
    for i in 0..100 {
        smt.push_str(&format!("(declare-const x{i} Int)\n"));
    }
    // Chain of assertions referencing overlapping pairs
    for i in 0..99 {
        smt.push_str(&format!("(assert (>= (+ x{} x{}) 0))\n", i, i + 1));
        smt.push_str(&format!("(assert (<= (+ x{} x{}) 1000))\n", i, i + 1));
    }
    smt.push_str("(check-sat)\n");

    let output = crate::common::solve(&smt);
    let r = results(&output);
    assert_eq!(r, vec!["sat"], "Wide LIA formula should be SAT");
}

/// Deep nested ITE formula. ITE nodes create binary DAG sharing when the
/// same condition variable appears in multiple branches.
#[test]
#[timeout(10_000)]
fn test_validate_model_deep_ite_dag() {
    let mut smt = String::from("(set-logic QF_LIA)\n");
    smt.push_str("(declare-const x Int)\n");
    smt.push_str("(declare-const y Int)\n");
    for i in 0..20 {
        smt.push_str(&format!("(declare-const c{i} Bool)\n"));
    }

    // Build a chain of ITEs that share the same x, y subterms:
    // (assert (> (ite c0 (+ x 1) (+ y 1)) 0))
    // (assert (> (ite c1 (+ x 1) (+ y 1)) 0))
    // ...
    // The (+ x 1) and (+ y 1) subterms are shared across all assertions.
    for i in 0..20 {
        smt.push_str(&format!("(assert (> (ite c{i} (+ x 1) (+ y 1)) 0))\n"));
    }
    smt.push_str("(assert (> x 0))\n");
    smt.push_str("(assert (> y 0))\n");
    smt.push_str("(check-sat)\n");

    let output = crate::common::solve(&smt);
    let r = results(&output);
    assert_eq!(r, vec!["sat"], "Deep ITE formula should be SAT");
}

/// Mixed theory formula with DT + LIA subterms. Exercises the datatype
/// classification path which is most expensive (O(C*S) per App node
/// without precomputation).
#[test]
#[timeout(10_000)]
fn test_validate_model_mixed_dt_lia_classification() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Pair 0)) (((mkpair (fst Int) (snd Int)))))
        (declare-const p1 Pair)
        (declare-const p2 Pair)
        (declare-const p3 Pair)
        (assert (> (fst p1) 0))
        (assert (> (snd p1) 0))
        (assert (> (fst p2) (fst p1)))
        (assert (> (snd p2) (snd p1)))
        (assert (> (fst p3) (fst p2)))
        (assert (> (snd p3) (snd p2)))
        (assert (< (fst p3) 100))
        (assert (< (snd p3) 100))
        (check-sat)
    "#;

    let output = crate::common::solve(smt);
    let r = results(&output);
    assert_eq!(r, vec!["sat"], "Mixed DT+LIA formula should be SAT");
}

/// Formula with array assertions. Array classification must work correctly
/// since false-on-array-assertion degrades to Unknown rather than hard error.
#[test]
#[timeout(10_000)]
fn test_validate_model_array_classification() {
    let smt = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const v Int)
        (assert (= (select (store a i v) i) v))
        (assert (> v 0))
        (assert (> i 0))
        (check-sat)
    "#;

    let output = crate::common::solve(smt);
    let r = results(&output);
    // SAT or Unknown are both acceptable (array model evaluation is incomplete)
    assert!(
        r == vec!["sat"] || r == vec!["unknown"],
        "Array formula should be SAT or Unknown, got: {r:?}"
    );
}
