// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Smoke tests for each theory solver entry point: SAT, UNSAT, and model.
//!
//! Each theory solver (propositional, EUF, LRA, LIA, BV) gets at least one
//! SAT test, one UNSAT test, and one model extraction test. These ensure the
//! solve_* entry points are wired correctly and produce consistent results.
//!
//! Part of #2812

use ay_frontend::sexp::{parse_sexp, SExpr};
use ntest::timeout;

fn results(output: &str) -> Vec<&str> {
    output
        .lines()
        .map(str::trim)
        .filter(|l| *l == "sat" || *l == "unsat" || *l == "unknown")
        .collect()
}

fn get_value_binding(output: &str, name: &str) -> Option<SExpr> {
    let value_line = output
        .lines()
        .map(str::trim)
        .find(|line| line.starts_with("(("))?;
    let parsed = parse_sexp(value_line).ok()?;
    let SExpr::List(ref bindings) = parsed else {
        return None;
    };

    for binding in bindings {
        let SExpr::List(ref items) = binding else {
            continue;
        };
        if items.len() != 2 {
            continue;
        }
        if items[0].as_symbol() == Some(name) {
            return Some(items[1].clone());
        }
    }
    None
}

fn sexpr_to_i64(expr: &SExpr) -> Option<i64> {
    match expr {
        SExpr::Numeral(n) => n.parse().ok(),
        SExpr::List(items) if items.len() == 2 && items[0].is_symbol("-") => {
            let abs = sexpr_to_i64(&items[1])?;
            Some(-abs)
        }
        _ => None,
    }
}

fn sexpr_to_f64(expr: &SExpr) -> Option<f64> {
    match expr {
        SExpr::Numeral(n) => n.parse().ok(),
        SExpr::Decimal(d) => d.parse().ok(),
        SExpr::List(items) if items.len() == 2 && items[0].is_symbol("-") => {
            let abs = sexpr_to_f64(&items[1])?;
            Some(-abs)
        }
        SExpr::List(items) if items.len() == 3 && items[0].is_symbol("/") => {
            let num = sexpr_to_f64(&items[1])?;
            let den = sexpr_to_f64(&items[2])?;
            if den == 0.0 {
                None
            } else {
                Some(num / den)
            }
        }
        _ => None,
    }
}

fn sexpr_to_bv_u64(expr: &SExpr) -> Option<u64> {
    match expr {
        SExpr::Hexadecimal(h) => u64::from_str_radix(h.trim_start_matches("#x"), 16).ok(),
        SExpr::Binary(b) => u64::from_str_radix(b.trim_start_matches("#b"), 2).ok(),
        _ => None,
    }
}

// ---- Propositional (QF_UF with only Bool) ----

#[test]
#[timeout(10_000)]
fn test_propositional_sat() {
    let smt = r#"
        (set-logic QF_UF)
        (declare-const p Bool)
        (declare-const q Bool)
        (assert (or p q))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}

#[test]
#[timeout(10_000)]
fn test_propositional_unsat() {
    let smt = r#"
        (set-logic QF_UF)
        (declare-const p Bool)
        (assert p)
        (assert (not p))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

// ---- EUF (QF_UF) ----

#[test]
#[timeout(10_000)]
fn test_euf_sat() {
    let smt = r#"
        (set-logic QF_UF)
        (declare-sort S 0)
        (declare-fun f (S) S)
        (declare-const a S)
        (declare-const b S)
        (assert (= (f a) (f b)))
        (assert (not (= a b)))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}

#[test]
#[timeout(10_000)]
fn test_euf_unsat_congruence() {
    let smt = r#"
        (set-logic QF_UF)
        (declare-sort S 0)
        (declare-fun f (S) S)
        (declare-const a S)
        (declare-const b S)
        (assert (= a b))
        (assert (not (= (f a) (f b))))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

#[test]
#[timeout(10_000)]
fn test_euf_unsat_transitivity() {
    let smt = r#"
        (set-logic QF_UF)
        (declare-sort S 0)
        (declare-const a S)
        (declare-const b S)
        (declare-const c S)
        (assert (= a b))
        (assert (= b c))
        (assert (not (= a c)))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

// ---- LRA (QF_LRA) ----

#[test]
#[timeout(10_000)]
fn test_lra_sat() {
    let smt = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (>= x 0.0))
        (assert (<= x 10.0))
        (assert (= y (* 2.0 x)))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}

#[test]
#[timeout(10_000)]
fn test_lra_unsat() {
    let smt = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (> x 5.0))
        (assert (< x 3.0))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

#[test]
#[timeout(10_000)]
fn test_lra_model_extraction() {
    let smt = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (= x 3.5))
        (check-sat)
        (get-value (x))
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat"], "Expected sat, got: {output}");
    let x_binding = get_value_binding(&output, "x").expect("missing get-value binding for x");
    let x_value = sexpr_to_f64(&x_binding).expect("x binding is not a numeric expression");
    assert!(
        (x_value - 3.5).abs() <= f64::EPSILON,
        "Expected x = 3.5, got binding: {x_binding}"
    );
}

// ---- LIA (QF_LIA) ----

#[test]
#[timeout(10_000)]
fn test_lia_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (assert (<= x 10))
        (assert (= y (* 2 x)))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}

#[test]
#[timeout(10_000)]
fn test_lia_unsat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (> x 5))
        (assert (< x 3))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

#[test]
#[timeout(10_000)]
fn test_lia_unsat_no_integer_solution() {
    // 2x = 3 has no integer solution
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= (* 2 x) 3))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

#[test]
#[timeout(10_000)]
fn test_lia_model_extraction() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= x 42))
        (check-sat)
        (get-value (x))
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat"], "Expected sat, got: {output}");
    let x_binding = get_value_binding(&output, "x").expect("missing get-value binding for x");
    assert_eq!(
        sexpr_to_i64(&x_binding),
        Some(42),
        "Expected x = 42, got binding: {x_binding}"
    );
}

// ---- BV (QF_BV) ----

#[test]
#[timeout(10_000)]
fn test_bv_sat() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= (bvadd x y) #xFF))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}

#[test]
#[timeout(10_000)]
fn test_bv_unsat() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x0A))
        (assert (= x #xFF))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

#[test]
#[timeout(10_000)]
fn test_bv_unsat_overflow() {
    // x + 1 = x for 8-bit only when overflow wraps, but bvadd wraps mod 256
    // so x + 1 = x is always UNSAT
    let smt = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= (bvadd x #x01) x))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

#[test]
#[timeout(10_000)]
fn test_bv_model_extraction() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x2A))
        (check-sat)
        (get-value (x))
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat"], "Expected sat, got: {output}");
    let x_binding = get_value_binding(&output, "x").expect("missing get-value binding for x");
    assert_eq!(
        sexpr_to_bv_u64(&x_binding),
        Some(0x2A),
        "Expected x = #x2A, got binding: {x_binding}"
    );
}

// Regression: model minimizer used stale BV model cache for extract
// terms, allowing minimizer to set x=0 even when (extract 0 0 x)=1
// was required. The extract evaluator must recompute from the parent
// variable, not use the cached bitblast-time value (#5098, #5121).
#[test]
#[timeout(10_000)]
fn test_bv_extract_model_minimization_5098() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (assert (= (_ bv1 1) ((_ extract 0 0) x)))
        (assert (= (_ bv0 1) ((_ extract 1 1) x)))
        (check-sat)
        (get-value (x))
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat"], "Expected sat, got: {output}");
    let x_val = get_value_binding(&output, "x").expect("missing x binding");
    let x = sexpr_to_bv_u64(&x_val).expect("cannot parse x value");
    // Bit 0 must be 1, bit 1 must be 0
    assert_eq!(x & 1, 1, "bit 0 of x must be 1, got x={x:#x}");
    assert_eq!((x >> 1) & 1, 0, "bit 1 of x must be 0, got x={x:#x}");
}

// Regression: model minimizer used stale BV model cache for repeat
// terms. (_ repeat 2) on a 4-bit value produces an 8-bit value by
// concatenating the argument with itself. The evaluator must recompute
// from the parent variable, not use the cached bitblast-time value (#5098).
#[test]
#[timeout(10_000)]
fn test_bv_repeat_model_minimization_5098() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 4))
        (assert (= ((_ repeat 2) x) #xAA))
        (check-sat)
        (get-value (x))
    "#;
    // (_ repeat 2) x = x concat x. #xAA = 0b10101010 = 0xA concat 0xA.
    // So x must be 0xA (= 0b1010 = 10).
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat"], "Expected sat, got: {output}");
    let x_val = get_value_binding(&output, "x").expect("missing x binding");
    let x = sexpr_to_bv_u64(&x_val).expect("cannot parse x value");
    assert_eq!(
        x, 0xA,
        "x must be 0xA for (repeat 2) x = #xAA, got x={x:#x}"
    );
}

// Proof coverage: concat model correctness after minimization.
// The minimizer tries x=0 and y=0; concat must recompute from
// updated variable values, not use stale bitblast-time cache.
#[test]
#[timeout(10_000)]
fn test_bv_concat_model_minimization() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (assert (= (concat x y) #xAB42))
        (check-sat)
        (get-value (x y))
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat"], "Expected sat, got: {output}");
    let x_val = get_value_binding(&output, "x").expect("missing x binding");
    let y_val = get_value_binding(&output, "y").expect("missing y binding");
    let x = sexpr_to_bv_u64(&x_val).expect("cannot parse x value");
    let y = sexpr_to_bv_u64(&y_val).expect("cannot parse y value");
    // concat(x, y) = #xAB42 means x = #xAB, y = #x42
    assert_eq!(
        x, 0xAB,
        "x must be 0xAB for concat(x,y)=#xAB42, got x={x:#x}"
    );
    assert_eq!(
        y, 0x42,
        "y must be 0x42 for concat(x,y)=#xAB42, got y={y:#x}"
    );
}

// Proof coverage: zero_extend model correctness after minimization.
// zero_extend(4, x) where x is 4-bit should pad high bits with 0.
#[test]
#[timeout(10_000)]
fn test_bv_zero_extend_model_minimization() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 4))
        (assert (= ((_ zero_extend 4) x) #xA5))
        (check-sat)
    "#;
    // zero_extend(4, x) = 0000 ++ x. For result #xA5 = 0b10100101,
    // high 4 bits must be 0000, but #xA5 high nibble = 0b1010 ≠ 0.
    // This is UNSAT.
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

// Proof coverage: sign_extend model with specific bit constraint.
#[test]
#[timeout(10_000)]
fn test_bv_sign_extend_model_minimization() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 4))
        (assert (= ((_ sign_extend 4) x) #xF5))
        (check-sat)
        (get-value (x))
    "#;
    // sign_extend(4, x) = #xF5 = 0b11110101.
    // Low 4 bits = 0101 = 5, sign bit (bit 3) = 0, extended = 00000101 = #x05 ≠ #xF5.
    // Actually: low 4 bits = 0101, bit 3 = 0 → extension = 0000, result = 00000101.
    // That ≠ #xF5, so we need bit 3 = 1: low 4 = 0101 has bit 3 = 0.
    // For #xF5 = 11110101: low 4 = 0101, extension = 1111 → bit 3 of x must be 1.
    // But 0101 has bit 3 = 0. UNSAT.
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

// Proof coverage: multiple extract constraints from one variable.
// The minimizer tries to shrink x; each extract must hold post-minimization.
#[test]
#[timeout(10_000)]
fn test_bv_multi_extract_model_minimization() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 32))
        (assert (= ((_ extract 7 0) x) #x42))
        (assert (= ((_ extract 15 8) x) #xAB))
        (assert (= ((_ extract 23 16) x) #xCD))
        (assert (= ((_ extract 31 24) x) #xEF))
        (check-sat)
        (get-value (x))
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat"], "Expected sat, got: {output}");
    let x_val = get_value_binding(&output, "x").expect("missing x binding");
    let x = sexpr_to_bv_u64(&x_val).expect("cannot parse x value");
    assert_eq!(
        x, 0xEFCDAB42,
        "x must be 0xEFCDAB42 for four extract constraints, got x={x:#x}"
    );
}

// ---- BV n-ary left-associative ops (#5445) ----

#[test]
#[timeout(10_000)]
fn test_bv_nary_bvadd_3args() {
    // (bvadd #x01 #x02 #x03) = #x06 per left-associative desugaring
    let smt = r#"
        (set-logic QF_BV)
        (assert (not (= (bvadd #x01 #x02 #x03) #x06)))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

#[test]
#[timeout(10_000)]
fn test_bv_nary_bvadd_4args() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= (bvadd #x01 #x02 #x03 #x04) x))
        (check-sat)
        (get-value (x))
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat"], "Expected sat, got: {output}");
    let x_val = get_value_binding(&output, "x").expect("missing x binding");
    let x = sexpr_to_bv_u64(&x_val).expect("cannot parse x value");
    assert_eq!(x, 0x0A, "1+2+3+4 = 10 = 0x0A, got x={x:#x}");
}

#[test]
#[timeout(10_000)]
fn test_bv_nary_bvmul_3args() {
    // (bvmul #x02 #x03 #x04) = #x18 (2*3*4 = 24 = 0x18)
    let smt = r#"
        (set-logic QF_BV)
        (assert (not (= (bvmul #x02 #x03 #x04) #x18)))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

#[test]
#[timeout(10_000)]
fn test_bv_nary_bvand_3args() {
    // (bvand #xFF #x0F #x03) = #x03
    let smt = r#"
        (set-logic QF_BV)
        (assert (not (= (bvand #xFF #x0F #x03) #x03)))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

#[test]
#[timeout(10_000)]
fn test_bv_nary_bvor_3args() {
    // (bvor #x01 #x02 #x04) = #x07
    let smt = r#"
        (set-logic QF_BV)
        (assert (not (= (bvor #x01 #x02 #x04) #x07)))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

#[test]
#[timeout(10_000)]
fn test_bv_nary_bvxor_3args() {
    // (bvxor #xFF #x0F #xF0) = #xFF ^ #x0F = #xF0, then #xF0 ^ #xF0 = #x00
    let smt = r#"
        (set-logic QF_BV)
        (assert (not (= (bvxor #xFF #x0F #xF0) #x00)))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

#[test]
#[timeout(10_000)]
fn test_bv_nary_concat_3args() {
    // (concat #x01 #x02 #x03) = #x010203 (left-associative)
    let smt = r#"
        (set-logic QF_BV)
        (assert (not (= (concat #x01 #x02 #x03) #x010203)))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

#[test]
#[timeout(10_000)]
fn test_bv_nary_concat_4args() {
    // (concat #xAA #xBB #xCC #xDD) = #xAABBCCDD
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 32))
        (assert (= x (concat #xAA #xBB #xCC #xDD)))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}

#[test]
#[timeout(10_000)]
fn test_bool_nary_xor_3args() {
    // (xor true true false) = (xor (xor true true) false) = (xor false false) = false
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun a () Bool)
        (declare-fun b () Bool)
        (declare-fun c () Bool)
        (assert a)
        (assert b)
        (assert (not c))
        (assert (xor a b c))
        (check-sat)
    "#;
    // xor(true, true, false) = xor(xor(true,true), false) = xor(false, false) = false
    // Asserting it's true contradicts => unsat
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

// ---- Reset test ----

#[test]
#[timeout(10_000)]
fn test_reset_clears_incremental_state() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= x 5))
        (push 1)
        (assert (= x 10))
        (check-sat)
        (pop 1)
        (check-sat)
        (reset)
        (set-logic QF_LIA)
        (declare-const y Int)
        (assert (= y 7))
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    // First check-sat: x=5 AND x=10 => UNSAT
    // Second check-sat: x=5 => SAT
    // After reset, third: y=7 => SAT
    assert_eq!(results(&output), vec!["unsat", "sat", "sat"]);
}

// ---- Empty assertion set ----

#[test]
#[timeout(10_000)]
fn test_empty_assertions_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}

// ---- Combined theory smoke ----

#[test]
#[timeout(10_000)]
fn test_euf_lia_combined_sat() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= (f x) 5))
        (assert (= (f y) 5))
        (assert (> x 0))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}

#[test]
#[timeout(10_000)]
fn test_euf_lia_combined_unsat() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (assert (= x 3))
        (assert (= (f x) 10))
        (assert (not (= (f 3) 10)))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

#[test]
#[timeout(10_000)]
fn test_euf_lra_combined_sat() {
    let smt = r#"
        (set-logic QF_UFLRA)
        (declare-fun g (Real) Real)
        (declare-const x Real)
        (assert (= (g x) 2.5))
        (assert (> x 0.0))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}

#[test]
#[timeout(10_000)]
fn test_array_euf_sat() {
    let smt = r#"
        (set-logic QF_AX)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (assert (= (select (store a i 42) i) 42))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}

#[test]
#[timeout(10_000)]
fn test_array_euf_unsat() {
    let smt = r#"
        (set-logic QF_AX)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (assert (not (= (select (store a i 42) i) 42)))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

/// Regression test for #4830: Dioph expand_single_substitution silently
/// dropped unexpandable fresh variables, making composed substitutions
/// tighter than the original and causing false UNSAT.
///
/// This system has 5 bounded integer vars with 2 equality constraints.
/// Solution: (1, 1, 0, 0, 3). The Dioph solver introduces fresh vars
/// during coefficient reduction; these must not be silently dropped.
#[test]
#[timeout(10_000)]
fn test_lia_dioph_fresh_var_expansion_false_unsat_4830() {
    let smt = r#"
        (set-logic QF_LIA)
        (set-info :status sat)
        (declare-fun x0 () Int)
        (declare-fun x1 () Int)
        (declare-fun x2 () Int)
        (declare-fun x3 () Int)
        (declare-fun x4 () Int)
        (assert (>= x0 0))
        (assert (<= x0 255))
        (assert (>= x1 0))
        (assert (<= x1 255))
        (assert (>= x2 0))
        (assert (<= x2 255))
        (assert (>= x3 0))
        (assert (<= x3 255))
        (assert (>= x4 0))
        (assert (<= x4 255))
        (assert (= (+ (* 3 x0) (* 7 x1) (* (- 2) x2)) 10))
        (assert (= (+ (* 5 x1) (* (- 3) x3) (* 4 x4)) 17))
        (assert (>= (+ x0 x1 x2 x3 x4) 5))
        (assert (<= (+ x0 x1 x2 x3 x4) 20))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}

// ---- Non-BV-return UF distinct congruence (audit fix) ----

/// When a UF returns a non-BV sort and the formula uses `distinct` (not `=`),
/// the congruence axiom must still enforce: x=y → ¬(distinct f(x) f(y)).
/// Regression test for missing distinct handling in generate_non_bv_euf_congruence.
#[test]
#[timeout(10_000)]
fn test_ufbv_non_bv_return_distinct_congruence() {
    let smt = r#"
        (set-logic QF_UFBV)
        (declare-sort U 0)
        (declare-fun f ((_ BitVec 8)) U)
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (assert (= x y))
        (assert (distinct (f x) (f y)))
        (check-sat)
    "#;
    // x=y → f(x)=f(y) → ¬(distinct f(x) f(y)) → unsat
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

// ---- DT+BV congruence: UFs with DT-sorted arguments in BV solver ----

/// f(DT) -> BV: when c1=c2, f(c1) must equal f(c2).
/// Regression: DT args have no BV bits, so both generate_euf_bv_axioms_debug
/// (requires BV args) and generate_non_bv_euf_congruence (skipped BV-return
/// pairs) missed this case entirely. Part of #5433.
#[test]
#[timeout(10_000)]
fn test_dt_bv_congruence_uf_with_dt_arg() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Color ((Red) (Blue) (Green)))
        (declare-fun f (Color) (_ BitVec 8))
        (declare-fun c1 () Color)
        (declare-fun c2 () Color)
        (assert (= c1 c2))
        (assert (distinct (f c1) (f c2)))
        (check-sat)
    "#;
    // c1=c2 -> f(c1)=f(c2) -> unsat
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

/// f(DT, BV) -> BV: mixed DT and BV arguments.
/// When c1=c2, f(c1, v) must equal f(c2, v) regardless of v being BV-sorted.
/// Part of #5433.
#[test]
#[timeout(10_000)]
fn test_dt_bv_congruence_mixed_args() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Color ((Red) (Blue) (Green)))
        (declare-fun f (Color (_ BitVec 8)) (_ BitVec 8))
        (declare-fun c1 () Color)
        (declare-fun c2 () Color)
        (declare-fun v () (_ BitVec 8))
        (assert (= c1 c2))
        (assert (distinct (f c1 v) (f c2 v)))
        (check-sat)
    "#;
    // c1=c2 -> f(c1,v)=f(c2,v) -> unsat
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

/// DT tester congruence: is-Some(x) should match is-Some(y) when x=y.
/// Part of #5433.
#[test]
#[timeout(10_000)]
fn test_dt_tester_congruence() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Opt ((Some (val (_ BitVec 8))) (None)))
        (declare-fun x () Opt)
        (declare-fun y () Opt)
        (assert (= x y))
        (assert ((_ is Some) x))
        (assert (not ((_ is Some) y)))
        (check-sat)
    "#;
    // x=y and is-Some(x) and not(is-Some(y)) -> unsat
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

// ---- QF_UFBV coverage tests (Part of #5434) ----

/// Nested BV predicates in Boolean structure under QF_UFBV.
/// Exercises predicate linking: the SAT solver must see BV predicates
/// (bvult, bvugt) that appear under Boolean connectives.
#[test]
#[timeout(10_000)]
fn test_ufbv_nested_bv_predicate_sat_5434() {
    let smt = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (assert (or (bvult x y) (bvugt x y)))
        (assert (= (f x) #x42))
        (check-sat)
    "#;
    // x != y (from disjunction) and f(x) = 0x42: satisfiable.
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}

/// UF with BV-sorted return type: basic SAT + get-value.
/// Exercises model extraction for uninterpreted functions returning BV.
#[test]
#[timeout(10_000)]
fn test_ufbv_bv_return_sat_5434() {
    let smt = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-fun x () (_ BitVec 8))
        (assert (= (f x) #xFF))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}

/// Multi-argument UF congruence: f(a, b1) = f(c, b2) when a=c, b1=b2.
/// Exercises congruence axiom with multiple BV-sorted arguments and
/// explicit equalities on all argument pairs.
#[test]
#[timeout(10_000)]
fn test_ufbv_multi_arg_congruence_unsat_5434() {
    let smt = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-fun a () (_ BitVec 8))
        (declare-fun b1 () (_ BitVec 8))
        (declare-fun c () (_ BitVec 8))
        (declare-fun b2 () (_ BitVec 8))
        (assert (= a c))
        (assert (= b1 b2))
        (assert (not (= (f a b1) (f c b2))))
        (check-sat)
    "#;
    // a=c, b1=b2 -> f(a,b1) = f(c,b2) -> unsat
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

// ---- QF_ABV: Array + BitVector smoke tests (#5466) ----

/// ABV SAT: select from stored array element returns the stored value.
#[test]
#[timeout(10_000)]
fn test_abv_sat_store_select_5466() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const idx (_ BitVec 8))
        (declare-const val (_ BitVec 8))
        (assert (= idx #x03))
        (assert (= val #xAB))
        (assert (= (select (store a idx val) idx) val))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}

/// ABV UNSAT: contradictory store/select — store #xFF at idx, then require
/// select at same idx returns #x00.
#[test]
#[timeout(10_000)]
fn test_abv_unsat_contradictory_store_select_5466() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const idx (_ BitVec 8))
        (assert (= (select (store a idx #xFF) idx) #x00))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

/// ABV model extraction: get-value for BV terms after array constraints.
#[test]
#[timeout(10_000)]
fn test_abv_model_get_value_bv_5466() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const x (_ BitVec 8))
        (assert (= x #x42))
        (assert (= (select a x) #x10))
        (check-sat)
        (get-value (x))
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat"]);
    let val = get_value_binding(&output, "x").expect("missing x binding");
    let x = sexpr_to_bv_u64(&val).expect("cannot parse x value");
    assert_eq!(x, 0x42, "x must be #x42, got {x:#x}");
}

/// ABV model extraction: get-value for array select expression.
#[test]
#[timeout(10_000)]
fn test_abv_model_get_value_array_select_5466() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const idx (_ BitVec 8))
        (declare-const result (_ BitVec 8))
        (assert (= idx #x05))
        (assert (= (select a idx) #xBE))
        (assert (= result (select a idx)))
        (check-sat)
        (get-value (idx result))
    "#;
    let output = crate::common::solve(smt);
    let sat_results = results(&output);
    assert!(
        matches!(sat_results.as_slice(), ["sat"] | ["unknown"]),
        "ABV array-select model query must not be unsat; got {output}"
    );
    if sat_results.as_slice() == ["unknown"] {
        return;
    }
    let idx_val = get_value_binding(&output, "idx").expect("missing idx");
    let idx = sexpr_to_bv_u64(&idx_val).expect("parse idx");
    assert_eq!(idx, 0x05, "idx must be #x05, got {idx:#x}");
    let res_val = get_value_binding(&output, "result").expect("missing result");
    let result = sexpr_to_bv_u64(&res_val).expect("parse result");
    assert_eq!(
        result, 0xBE,
        "result = select(a,idx) must be #xBE, got {result:#x}"
    );
}

// ---- QF_AUFBV: Array + UF + BitVector smoke tests (#5466) ----

/// AUFBV SAT: array + UF + BV combination, all satisfiable.
#[test]
#[timeout(10_000)]
fn test_aufbv_sat_array_uf_bv_5466() {
    let smt = r#"
        (set-logic QF_AUFBV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (assert (= x #x10))
        (assert (= (f x) #x20))
        (assert (= (select a (f x)) #xFF))
        (check-sat)
    "#;
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}

/// AUFBV UNSAT: UF congruence over array arguments.
/// x=y → f(x)=f(y) → select(a, f(x)) = select(a, f(y)).
#[test]
#[timeout(10_000)]
fn test_aufbv_unsat_uf_congruence_array_5466() {
    let smt = r#"
        (set-logic QF_AUFBV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= x y))
        (assert (distinct (select a (f x)) (select a (f y))))
        (check-sat)
    "#;
    // x=y → f(x)=f(y) → select(a, f(x))=select(a, f(y)) → unsat
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

/// AUFBV model extraction: get-value for BV and UF terms.
#[test]
#[timeout(10_000)]
fn test_aufbv_model_get_value_5466() {
    let smt = r#"
        (set-logic QF_AUFBV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (assert (= x #xFF))
        (assert (= (f x) #x01))
        (assert (= (select a x) #xAA))
        (check-sat)
        (get-value (x))
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat"]);
    let val = get_value_binding(&output, "x").expect("missing x binding");
    let x = sexpr_to_bv_u64(&val).expect("cannot parse x value");
    assert_eq!(x, 0xFF, "x must be #xFF, got {x:#x}");
}

/// AUFBV non-BV-return UF: regression for #5459.
/// p: BV→Bool. x=y → p(x)↔p(y). Assert p(x) ∧ ¬p(y) is UNSAT.
#[test]
#[timeout(10_000)]
fn test_aufbv_non_bv_return_uf_congruence_5466() {
    let smt = r#"
        (set-logic QF_AUFBV)
        (declare-fun p ((_ BitVec 8)) Bool)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= x y))
        (assert (p x))
        (assert (not (p y)))
        (check-sat)
    "#;
    // x=y → p(x)↔p(y) → unsat
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

/// ABV model: BV variable equated to array select must return the
/// constrained value, not zero (#5478). The BV minimizer was zeroing
/// variables because the SAT-level fallback in evaluate_term can't detect
/// that the proposed value violates array-level constraints.
#[test]
#[timeout(10_000)]
fn test_abv_minimizer_respects_array_select_5478() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun x () (_ BitVec 8))
        (assert (= (select a #x05) #xFF))
        (assert (= x (select a #x05)))
        (check-sat)
        (get-value (x))
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat"], "Expected sat, got: {output}");
    let x_val = get_value_binding(&output, "x").expect("missing x binding");
    let x = sexpr_to_bv_u64(&x_val).expect("cannot parse x value");
    assert_eq!(x, 0xFF, "x must be 0xFF from select(a, 0x05), got x={x:#x}");
}

/// UFBV model congruence: f(x) and f(y) must have the same value when x=y (#5461).
///
/// The term f(y) only appears in get-value, not in assertions, so the BV model
/// has no direct entry for it. The model extraction must find the congruent
/// application f(x) and return its value.
#[test]
#[timeout(10_000)]
fn test_ufbv_congruence_sat_model_consistency_5461() {
    let smt = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (assert (= x y))
        (assert (= (f x) #x42))
        (check-sat)
        (get-value ((f x) (f y)))
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat"], "Expected sat, got: {output}");
    // Parse get-value output: (((f x) #x42) ((f y) #x42))
    let value_line = output
        .lines()
        .map(str::trim)
        .find(|line| line.starts_with("(("))
        .expect("missing get-value output");
    let parsed = parse_sexp(value_line).expect("parse get-value");
    let SExpr::List(ref bindings) = parsed else {
        panic!("expected list, got: {parsed:?}");
    };
    assert_eq!(bindings.len(), 2, "expected 2 bindings, got: {value_line}");
    // Both bindings should have the same BV value (#x42 = 66).
    let fx_val =
        sexpr_to_bv_u64(&bindings[0].as_list().unwrap()[1]).expect("cannot parse (f x) value");
    let fy_val =
        sexpr_to_bv_u64(&bindings[1].as_list().unwrap()[1]).expect("cannot parse (f y) value");
    assert_eq!(fx_val, 0x42, "f(x) should be #x42 (66), got {fx_val:#x}");
    assert_eq!(
        fy_val, fx_val,
        "congruence violation: x=y but f(x)={fx_val:#x} != f(y)={fy_val:#x}"
    );
}

/// Multi-argument UFBV congruence: g(x1,x2) and g(y1,y2) must agree when
/// x1=y1 and x2=y2. Exercises the multi-arg path in find_congruent_bv_app.
#[test]
#[timeout(10_000)]
fn test_ufbv_multi_arg_congruence_model_5461() {
    let smt = r#"
        (set-logic QF_UFBV)
        (declare-fun g ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-fun x1 () (_ BitVec 8))
        (declare-fun x2 () (_ BitVec 8))
        (declare-fun y1 () (_ BitVec 8))
        (declare-fun y2 () (_ BitVec 8))
        (assert (= x1 y1))
        (assert (= x2 y2))
        (assert (= (g x1 x2) #xAB))
        (check-sat)
        (get-value ((g x1 x2) (g y1 y2)))
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat"], "Expected sat, got: {output}");
    let value_line = output
        .lines()
        .map(str::trim)
        .find(|line| line.starts_with("(("))
        .expect("missing get-value output");
    let parsed = parse_sexp(value_line).expect("parse get-value");
    let SExpr::List(ref bindings) = parsed else {
        panic!("expected list, got: {parsed:?}");
    };
    assert_eq!(bindings.len(), 2, "expected 2 bindings, got: {value_line}");
    let gx_val = sexpr_to_bv_u64(&bindings[0].as_list().unwrap()[1]).expect("parse g(x1,x2)");
    let gy_val = sexpr_to_bv_u64(&bindings[1].as_list().unwrap()[1]).expect("parse g(y1,y2)");
    assert_eq!(gx_val, 0xAB, "g(x1,x2) should be #xAB, got {gx_val:#x}");
    assert_eq!(
        gy_val, gx_val,
        "congruence: g(x1,x2)={gx_val:#x} != g(y1,y2)={gy_val:#x}"
    );
}

// ---- DT+BV UF congruence: ArgDiffResult::Unencodable tests (#5473) ----

/// Mixed DT+BV UF args: when DT args differ, f(Red, bv) and f(Green, bv)
/// should NOT be forced equal (Red != Green is unencodable in BV bits).
/// This exercises the ArgDiffResult::Unencodable path in
/// generate_non_bv_euf_congruence.
#[test]
#[timeout(10_000)]
fn test_dt_bv_congruence_unencodable_different_dt_args_sat_5473() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Color 0)) (((Red) (Green) (Blue))))
        (declare-fun f (Color (_ BitVec 8)) (_ BitVec 8))
        (declare-const bv1 (_ BitVec 8))
        (assert (distinct (f Red bv1) (f Green bv1)))
        (check-sat)
    "#;
    // Red != Green, so f(Red, bv1) != f(Green, bv1) is satisfiable.
    // Without the Unencodable fix, this would be false UNSAT.
    assert_eq!(results(&crate::common::solve(smt)), vec!["sat"]);
}

/// Same DT+BV UF args: when DT args are equal (same constructor),
/// f(Red, x) = f(Red, y) when x=y (standard congruence).
#[test]
#[timeout(10_000)]
fn test_dt_bv_congruence_same_dt_args_unsat_5473() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Color 0)) (((Red) (Green) (Blue))))
        (declare-fun f (Color (_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= x y))
        (assert (distinct (f Red x) (f Red y)))
        (check-sat)
    "#;
    // x=y and same DT arg (Red) -> f(Red,x) = f(Red,y) -> unsat
    assert_eq!(results(&crate::common::solve(smt)), vec!["unsat"]);
}

// ---- #5475 Gap B: Complex BV expression arguments in UF congruence ----

/// Complex BV expression args: f(bvadd(x, 1)) vs f(bvadd(y, 1)) with x=y.
/// The bvadd sub-expressions must be materialized (bitblasted) before
/// congruence axiom generation, otherwise get_term_bits returns None
/// and the congruence axiom is silently skipped.
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
