// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! UFBV congruence regression tests for complex BV expression arguments (#5475).
//!
//! These tests verify that materialize_uf_arg_bv_terms correctly bitblasts
//! complex BV sub-expressions inside UF application arguments before congruence
//! axiom generation. Without materialization, get_term_bits returns None for
//! these terms and the congruence axiom is silently skipped.

use ntest::timeout;

fn results(output: &str) -> Vec<&str> {
    output
        .lines()
        .map(str::trim)
        .filter(|l| *l == "sat" || *l == "unsat" || *l == "unknown")
        .collect()
}

/// Complex BV expression args: f(bvadd(x, 1)) vs f(bvadd(y, 1)) with x=y.
#[test]
#[timeout(10_000)]
fn test_ufbv_complex_bv_arg_bvadd_unsat_5475() {
    let smt = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (assert (= x y))
        (assert (distinct (f (bvadd x #x01)) (f (bvadd y #x01))))
        (check-sat)
    "#;
    // x=y -> bvadd(x,1)=bvadd(y,1) -> f(bvadd(x,1))=f(bvadd(y,1)) -> unsat
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

/// Complex multi-argument BV expressions: f(bvadd(a, 1), bvor(b, c)) with
/// both argument positions using BV operations.
#[test]
#[timeout(10_000)]
fn test_ufbv_complex_multi_bv_arg_unsat_5475() {
    let smt = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-fun a () (_ BitVec 8))
        (declare-fun b () (_ BitVec 8))
        (declare-fun c () (_ BitVec 8))
        (declare-fun d () (_ BitVec 8))
        (assert (= a c))
        (assert (= b d))
        (assert (distinct (f (bvadd a #x01) (bvor b #x0F))
                          (f (bvadd c #x01) (bvor d #x0F))))
        (check-sat)
    "#;
    // a=c, b=d -> both arg pairs equal -> f results equal -> unsat
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

/// Nested BV operations in UF args: f(bvadd(bvshl(x, 2), 1)).
#[test]
#[timeout(10_000)]
fn test_ufbv_nested_bv_ops_arg_unsat_5475() {
    let smt = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (assert (= x y))
        (assert (distinct (f (bvadd (bvshl x #x02) #x01))
                          (f (bvadd (bvshl y #x02) #x01))))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}
