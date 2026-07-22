// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Tests for multi-argument function congruence (#6154) and
//! UF distinguishability regression (#6146).
//!
//! The EUF solver had zero multi-argument congruence tests — exactly the
//! pattern that #6146 (verification-consumer UF distinguishability regression) bugs.
//! These tests verify:
//!
//! 1. Multi-arg congruence: f(a1,a2) = f(b1,b2) when a1=b1, a2=b2
//! 2. Partial mismatch: f(a,b) != f(a,c) when b != c (SAT)
//! 3. Distinguishability: different UFs with same args can differ (SAT)
//! 4. verification-consumer regression patterns from #6146

use ntest::timeout;

// --- Multi-argument congruence: UNSAT cases ---

/// Basic 2-arg congruence: f(a,b) = f(c,d) when a=c, b=d.
/// Asserting f(a,b) != f(c,d) with a=c, b=d is UNSAT by congruence.
#[test]
#[timeout(10_000)]
fn test_2arg_congruence_unsat_6154() {
    let smt = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U U) U)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
(assert (= a c))
(assert (= b d))
(assert (not (= (f a b) (f c d))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "f(a,b) = f(c,d) by congruence when a=c, b=d"
    );
}

/// 3-arg congruence: g(a,b,c) = g(d,e,f) when a=d, b=e, c=f.
#[test]
#[timeout(10_000)]
fn test_3arg_congruence_unsat_6154() {
    let smt = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun g (U U U) U)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
(declare-const e U)
(declare-const ff U)
(assert (= a d))
(assert (= b e))
(assert (= c ff))
(assert (not (= (g a b c) (g d e ff))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "g(a,b,c) = g(d,e,f) by congruence when all args equal"
    );
}

/// Transitive 2-arg congruence: f(a,b) = f(c,d) via a=x=c, b=y=d.
#[test]
#[timeout(10_000)]
fn test_2arg_transitive_congruence_unsat_6154() {
    let smt = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U U) U)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
(declare-const x U)
(declare-const y U)
(assert (= a x))
(assert (= x c))
(assert (= b y))
(assert (= y d))
(assert (not (= (f a b) (f c d))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Transitive congruence through intermediate equalities"
    );
}

// --- Partial mismatch: SAT cases ---

/// Partial arg equality: f(a,b) != f(a,c) when b and c are unconstrained.
/// SAT because b and c can differ, so f can return different values.
#[test]
#[timeout(10_000)]
fn test_2arg_partial_mismatch_sat_6154() {
    let smt = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U U) U)
(declare-const a U)
(declare-const b U)
(declare-const c U)
; Only first arg shared, second arg unconstrained
(assert (not (= (f a b) (f a c))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "f(a,b) != f(a,c) is SAT when b,c unconstrained"
    );
}

/// 3-arg with one arg different: g(a,b,c) != g(a,b,d) when c != d.
#[test]
#[timeout(10_000)]
fn test_3arg_one_arg_different_sat_6154() {
    let smt = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun g (U U U) U)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
(assert (distinct c d))
(assert (not (= (g a b c) (g a b d))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "g(a,b,c) != g(a,b,d) is SAT when c != d"
    );
}

// --- UF distinguishability: SAT cases (verification-consumer #6146 regression patterns) ---

/// verification-consumer pattern: two distinct UFs with same args can return different values.
/// __quantifier_consumer_bit_and(x,255) != __quantifier_consumer_bit_or(x,255) should be SAT.
#[test]
#[timeout(10_000)]
fn test_distinct_ufs_same_args_sat_6146() {
    let smt = r#"
(set-logic QF_AUFLIA)
(declare-fun __quantifier_consumer_bit_and (Int Int) Int)
(declare-fun __quantifier_consumer_bit_or (Int Int) Int)
(declare-const x Int)
(assert (not (= (__quantifier_consumer_bit_and x 255) (__quantifier_consumer_bit_or x 255))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "Distinct UFs with same args CAN differ (verification-consumer #6146)"
    );
}

/// verification-consumer pattern: f(x,y) != f(a,b) with all args unconstrained.
/// SAT because args can be different, and f can return different values.
#[test]
#[timeout(10_000)]
fn test_multiarg_uf_unconstrained_sat_6146() {
    let smt = r#"
(set-logic QF_AUFLIA)
(declare-fun logic_max (Int Int) Int)
(declare-const x Int)
(declare-const y Int)
(declare-const a Int)
(declare-const b Int)
(assert (not (= (logic_max x y) (logic_max a b))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "f(x,y) != f(a,b) SAT when args unconstrained (verification-consumer #6146)"
    );
}

/// verification-consumer pattern: same UF, different argument values should be distinguishable.
/// f(1,2) != f(3,4) should be SAT.
#[test]
#[timeout(10_000)]
fn test_multiarg_uf_different_consts_sat_6146() {
    let smt = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int Int) Int)
(assert (not (= (f 1 2) (f 3 4))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "f(1,2) != f(3,4) SAT — different args allow different results"
    );
}

/// verification-consumer pattern: f(x,y) != f(y,x) with no constraint making x=y.
/// Swapped arguments should be distinguishable.
#[test]
#[timeout(10_000)]
fn test_multiarg_uf_swapped_args_sat_6146() {
    let smt = r#"
(set-logic QF_AUFLIA)
(declare-fun f (Int Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (distinct x y))
(assert (not (= (f x y) (f y x))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "f(x,y) != f(y,x) SAT when x != y");
}

/// verification-consumer pattern: bounded args with UF disequality.
/// f(x,y) != f(a,b) with bounds should still be SAT.
#[test]
#[timeout(10_000)]
fn test_multiarg_uf_bounded_args_sat_6146() {
    let smt = r#"
(set-logic QF_AUFLIA)
(declare-fun f (Int Int) Int)
(declare-const x Int)
(declare-const y Int)
(declare-const a Int)
(declare-const b Int)
(assert (>= x 0))
(assert (>= y 0))
(assert (>= a 0))
(assert (>= b 0))
(assert (not (= (f x y) (f a b))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "f(x,y) != f(a,b) SAT with bounds (verification-consumer #6146)"
    );
}

// --- Mixed congruence + disequality ---

/// Congruence forces equality, then disequality with a third application.
/// f(a,b) = f(c,d) by congruence (a=c, b=d), then f(a,b) != f(e,g) is SAT.
#[test]
#[timeout(10_000)]
fn test_2arg_congruence_then_disequality_sat_6154() {
    let smt = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U U) U)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
(declare-const e U)
(declare-const g U)
(assert (= a c))
(assert (= b d))
; f(a,b) = f(c,d) by congruence — this is fine
(assert (= (f a b) (f c d)))
; f(a,b) != f(e,g) — SAT because e,g are unconstrained
(assert (not (= (f a b) (f e g))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "Congruent pair + disequality with third app is SAT"
    );
}

/// All args congruent but asserting disequality: UNSAT.
/// f(a,b) = f(c,d) by congruence, then f(c,d) != f(a,b) is UNSAT.
#[test]
#[timeout(10_000)]
fn test_2arg_congruence_self_disequality_unsat_6154() {
    let smt = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U U) U)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
(assert (= a c))
(assert (= b d))
(assert (not (= (f a b) (f c d))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Congruent pair disequality is UNSAT"
    );
}

// --- UFLRA and UFLIA variants ---

/// UFLRA: multi-arg UF with Real args, disequality should be SAT.
#[test]
#[timeout(10_000)]
fn test_uflra_multiarg_disequality_sat_6146() {
    let smt = r#"
(set-logic QF_UFLRA)
(declare-fun h (Real Real) Real)
(declare-const x Real)
(declare-const y Real)
(assert (= x 1.0))
(assert (= y 2.0))
(assert (not (= (h x y) (h y x))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "h(1.0,2.0) != h(2.0,1.0) is SAT");
}

/// UFLIA: multi-arg congruence with equal Int args — UNSAT.
#[test]
#[timeout(10_000)]
fn test_uflia_multiarg_congruence_unsat_6146() {
    let smt = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (= x 1))
(assert (= y 2))
(assert (not (= (f x y) (f 1 2))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "f(x,y) = f(1,2) when x=1, y=2 by congruence"
    );
}

/// AUFLIA: multi-arg UF disequality with array context (verification-consumer pattern).
#[test]
#[timeout(10_000)]
fn test_auflia_multiarg_uf_disequality_sat_6146() {
    let smt = r#"
(set-logic QF_AUFLIA)
(declare-fun unwrap (Int) Int)
(declare-fun unwrap_err (Int) Int)
(declare-const val Int)
; unwrap and unwrap_err are different UFs — can return different values
(assert (not (= (unwrap val) (unwrap_err val))))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "unwrap(val) != unwrap_err(val) SAT (verification-consumer #6146)"
    );
}
