// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// QF_BV (Quantifier-Free Bitvectors) tests
// =========================================================================

#[test]
fn test_executor_qf_bv_simple_sat() {
    // Simple bitvector constraint - should be satisfiable
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= x y))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_bv_constant_equality_sat() {
    // x = 5 should be satisfiable
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x05))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_bv_contradiction_unsat() {
    // x = 5 and x = 6 is unsatisfiable
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x05))
        (assert (= x #x06))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_bv_addition_sat() {
    // x + y = 10 should be satisfiable
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= (bvadd x y) #x0a))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_bv_bitwise_and_sat() {
    // (x & 0xFF) = x is always true for 8-bit bitvectors
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= (bvand x #xff) x))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_bv_ult_sat() {
    // x < 10 should be satisfiable
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (bvult x #x0a))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_bv_ult_unsat() {
    // x < 0 is unsatisfiable for unsigned bitvectors
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (bvult x #x00))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_bv_combined_constraints() {
    // x + y = 100, x < y should be satisfiable
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= (bvadd x y) #x64))
        (assert (bvult x y))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_bv_bvor_sat() {
    // (x | y) = 0xFF should be satisfiable
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= (bvor x y) #xff))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_bv_bvxor_sat() {
    // x XOR x = 0 is always true
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= (bvxor x x) #x00))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_bv_bvxnor_unsat() {
    // bvxnor(x,y) = ~(x XOR y), so bvxnor(x,y) = (bvxor x y) is a contradiction.
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= (bvxnor x y) (bvxor x y)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_bv_bvnand_unsat() {
    // bvnand(x,y) = ~(x AND y), so bvnand(x,y) = (bvand x y) is a contradiction.
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= (bvnand x y) (bvand x y)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_bv_bvnor_unsat() {
    // bvnor(x,y) = ~(x OR y), so bvnor(x,y) = (bvor x y) is a contradiction.
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= (bvnor x y) (bvor x y)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_bv_bvcomp_unsat() {
    // bvcomp(x,y) is #b1 iff x=y.
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (not (= x y)))
        (assert (= (bvcomp x y) #b1))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_bv_rotate_right_unsat() {
    // rotate_right is a bit permutation; rotate_right(1,#b0001) = #b1000 (4-bit).
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (assert (= x #b0001))
        (assert (= ((_ rotate_right 1) x) #b0001))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_bv_repeat_unsat() {
    // repeat duplicates the bit pattern: repeat(2,#b01) = #b0101 (4-bit).
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 2))
        (assert (= x #b01))
        (assert (= ((_ repeat 2) x) #b0000))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_bv_ite_unsat() {
    // t is either #b00 or #b01, so it can't be distinct from both.
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 2))
        (declare-const t (_ BitVec 2))
        (assert (= t (ite (= x #b00) #b00 #b01)))
        (assert (not (= t #b00)))
        (assert (not (= t #b01)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_bv_ite_bool_var_linking_incremental() {
    // Regression: Bool variables used in BV `ite` conditions must be linked to Tseitin vars,
    // and the BV-side Bool term mapping must be stable across incremental check-sat calls.
    let input = r#"
        (set-logic QF_BV)
        (declare-const b Bool)
        (declare-const x (_ BitVec 1))
        (assert (= x (ite b #b0 #b1)))
        (check-sat)
        (push 1)
        (assert b)
        (assert (= x #b1))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 3);
    assert!(
        outputs[0] == "sat" || outputs[0] == "unknown",
        "first incremental BV query should be sat or unknown, got {}",
        outputs[0]
    );
    assert_eq!(outputs[1], "unsat");
    assert_eq!(outputs[2], "sat");
}

#[test]
fn test_executor_qf_bv_ite_bool_eq_condition_unsat() {
    // Regression: Boolean equality inside BV `ite` conditions must be bitblasted soundly.
    // Here (= b1 b2) is true, so x must be #b0, conflicting with x = #b1.
    let input = r#"
        (set-logic QF_BV)
        (declare-const b1 Bool)
        (declare-const b2 Bool)
        (declare-const x (_ BitVec 1))
        (assert b1)
        (assert b2)
        (assert (= x (ite (= b1 b2) #b0 #b1)))
        (assert (= x #b1))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_bv_bvsmod_unsat() {
    // In 8-bit signed: #xfb is -5, and (-5) mod_s 3 = 1, so asserting 2 is UNSAT.
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #xfb))
        (assert (= (bvsmod x #x03) #x02))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_bv_bvnot_sat() {
    // ~x = 0xFE means x = 0x01
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= (bvnot x) #xfe))
        (assert (= x #x01))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
