// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// =========================================================================
// QF_BV Division tests
// =========================================================================

#[test]
fn test_executor_qf_bv_udiv_sat() {
    // x / 3 = 2 means x can be 6, 7, or 8
    // With additional constraint x = 7
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const q (_ BitVec 8))
        (assert (= q (bvudiv x #x03)))
        (assert (= q #x02))
        (assert (= x #x07))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_bv_udiv_unsat() {
    // x / 3 = 2 and x / 3 = 3 is unsatisfiable
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= (bvudiv x #x03) #x02))
        (assert (= (bvudiv x #x03) #x03))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_bv_urem_sat() {
    // x % 3 = 1 should be satisfiable (e.g., x = 1, 4, 7, ...)
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= (bvurem x #x03) #x01))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_bv_urem_constraint_sat() {
    // x % 4 = 3 and x < 16 should be satisfiable (x = 3, 7, 11, 15)
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= (bvurem x #x04) #x03))
        (assert (bvult x #x10))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_bv_div_by_zero() {
    // Division by zero: x / 0 = 0xFF (all ones for 8-bit)
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x05))
        (assert (= (bvudiv x #x00) #xff))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_bv_rem_by_zero() {
    // Remainder by zero: x % 0 = x
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x07))
        (assert (= (bvurem x #x00) x))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_bv_sdiv_positive() {
    // Signed division: 7 / 2 = 3
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x07))
        (assert (= (bvsdiv x #x02) #x03))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_bv_srem_positive() {
    // Signed remainder: 7 % 3 = 1
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x07))
        (assert (= (bvsrem x #x03) #x01))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_bv_div_quotient_remainder() {
    // Quotient-remainder relationship: a = q * b + r
    // For a = 10, b = 3: q = 3, r = 1
    let input = r#"
        (set-logic QF_BV)
        (declare-const a (_ BitVec 8))
        (declare-const b (_ BitVec 8))
        (declare-const q (_ BitVec 8))
        (declare-const r (_ BitVec 8))
        (assert (= a #x0a))
        (assert (= b #x03))
        (assert (= q (bvudiv a b)))
        (assert (= r (bvurem a b)))
        (assert (= a (bvadd (bvmul q b) r)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_bv_div_no_wraparound_unsat() {
    // Regression: prevent overflow-based "solutions" to udiv/urem.
    // In 4-bit unsigned, 1 / 15 = 0 and 1 % 15 = 1, so the asserted values are UNSAT.
    let input = r#"
        (set-logic QF_BV)
        (declare-const a (_ BitVec 4))
        (declare-const b (_ BitVec 4))
        (assert (= a #b0001))
        (assert (= b #b1111))
        (assert (= (bvudiv a b) #b1111))
        (assert (= (bvurem a b) #b0000))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

// Repro for the aterm base64::encode false-overflow bug.
//
// bv64 `len` with (bvule len isize::MAX); bv64 `fc = (bvudiv len 3)`.
// Asking whether `fc` can reach usize::MAX (the witness the verifier checks for
// `fc + 1` overflow). Correct answer: UNSAT, because
// fc = len/3 <= isize::MAX/3 = 0x2AAA_AAAA_AAAA_AAAA << usize::MAX.
//
// The observed bug: ay-dpll's bound propagation only asserts the trivial type
// bound (fc <= usize::MAX) and never derives fc <= isize::MAX/3 from the udiv
// relation, so it returns a spurious model with fc = 0xFFFFFFFFFFFFFFFF (SAT).
#[test]
fn test_executor_qf_bv_udiv_overflow_witness_unsat() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const len (_ BitVec 64))
        (declare-const fc (_ BitVec 64))
        ; len <= isize::MAX
        (assert (bvule len #x7FFFFFFFFFFFFFFF))
        ; fc = len / 3  (full_chunks)
        (assert (= fc (bvudiv len #x0000000000000003)))
        ; overflow witness: fc reaches usize::MAX
        (assert (= fc #xFFFFFFFFFFFFFFFF))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs,
        vec!["unsat"],
        "fc = len/3 <= isize::MAX/3 cannot reach usize::MAX"
    );
}

// Same property framed as bvadd overflow of fc + 1, via the no-overflow
// predicate bvuaddo. With len <= isize::MAX and fc = len/3, fc + 1 cannot
// overflow, so asserting overflow must be UNSAT.
#[test]
fn test_executor_qf_bv_udiv_addo_unsat() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const len (_ BitVec 64))
        (declare-const fc (_ BitVec 64))
        (assert (bvule len #x7FFFFFFFFFFFFFFF))
        (assert (= fc (bvudiv len #x0000000000000003)))
        ; fc + 1 wraps to 0  <=>  fc = usize::MAX (overflow witness)
        (assert (= (bvadd fc #x0000000000000001) #x0000000000000000))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"], "fc + 1 cannot overflow usize");
}

// Mul framing: fc*3 <= len instead of fc = len/3. With len <= isize::MAX,
// fc = usize::MAX would need usize::MAX*3 <= len, impossible. UNSAT.
#[test]
fn test_executor_qf_bv_udiv_mul_framing_unsat() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const len (_ BitVec 64))
        (declare-const fc (_ BitVec 64))
        (assert (bvule len #x7FFFFFFFFFFFFFFF))
        ; fc * 3 does not overflow, and fc * 3 <= len  (the udiv lower bound)
        (assert (not (bvumulo fc #x0000000000000003)))
        (assert (bvule (bvmul fc #x0000000000000003) len))
        (assert (= fc #xFFFFFFFFFFFFFFFF))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs,
        vec!["unsat"],
        "fc*3 <= len forbids fc = usize::MAX"
    );
}
