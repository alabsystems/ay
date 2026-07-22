// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness regression test for QF_SLIA bridge contradictory value propagation.
//!
//! When arithmetic expressions contain ITE terms whose branches reference
//! unconstrained theory variables (e.g., str.to_code), the Nelson-Oppen
//! interface bridge can evaluate the expression to different values across
//! iterations as the LIA model changes. Without the contradictory-value
//! guard, the bridge propagates both `expr=0` and `expr=10` to EUF,
//! which derives `0=10` → false-UNSAT.
//!
//! Root cause: model-dependent bridge equalities become stale when back-
//! propagated equalities change the LIA model between N-O iterations.
//! Fix: InterfaceBridge.propagated_term_values tracks the const_term last
//! propagated for each arith_term and skips contradictory re-propagation.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// Minimal reproduction: ITE-wrapped str.to_code in arithmetic.
/// The ITE conditions `(= (str.len s) 1)` are trivially true from the
/// asserted length constraints, so the bridge takes the then-branch and
/// evaluates `str.to_code(s)`. In iteration 0, LIA assigns str.to_code(s)=0
/// (unconstrained), making the sum=0. After propagation, LIA adjusts and
/// the sum becomes 10 in iteration 1. Without the fix, both values are
/// propagated to EUF → false-UNSAT.
const SLIA_ITE_STR_TO_CODE_MINIMAL: &str = r#"
(set-logic QF_SLIA)
(set-info :status sat)

(declare-const s1 String)
(declare-const s2 String)
(assert (= 1 (str.len s1)))
(assert (= 1 (str.len s2)))

(declare-const result Int)
(assert (= result (+ (* 256 (ite (= (str.len s1) 1) (str.to_code s1) 256))
                     (ite (= (str.len s2) 1) (str.to_code s2) 256))))
(assert (>= result 10))

(check-sat)
"#;

#[test]
#[timeout(15_000)]
fn test_slia_ite_str_to_code_not_false_unsat() {
    let commands = parse(SLIA_ITE_STR_TO_CODE_MINIMAL).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(
        outputs,
        vec!["unsat"],
        "QF_SLIA ITE+str.to_code formula is SAT (:status sat, Z3 confirms). \
         AY must not return unsat. Bug: bridge contradictory value propagation."
    );
}

/// 4-byte variant: four str.to_code variables in a big-endian sum with
/// additional string constraints. Exercises the bridge with more interface
/// terms and inter-theory interactions.
const SLIA_4BYTE_STR_TO_CODE: &str = r#"
(set-logic QF_SLIA)
(set-info :status sat)

(declare-const size1 String)
(declare-const size2 String)
(declare-const size3 String)
(declare-const size4 String)
(assert (= 1 (str.len size1)))
(assert (= 1 (str.len size2)))
(assert (= 1 (str.len size3)))
(assert (= 1 (str.len size4)))

(declare-const p2_size Int)
(assert (= p2_size
  (+ (+ (+ (* 16777216 (ite (= (str.len size1) 1) (str.to_code size1) 256))
           (*    65536 (ite (= (str.len size2) 1) (str.to_code size2) 256)))
           (*      256 (ite (= (str.len size3) 1) (str.to_code size3) 256)))
           (ite (= (str.len size4) 1) (str.to_code size4) 256))))
(assert (>= p2_size 10))
(assert (<= p2_size 100))

(check-sat)
"#;

#[test]
#[timeout(15_000)]
fn test_slia_4byte_str_to_code_not_false_unsat() {
    let commands = parse(SLIA_4BYTE_STR_TO_CODE).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(
        outputs,
        vec!["unsat"],
        "QF_SLIA 4-byte str.to_code formula is SAT (:status sat, Z3 confirms). \
         AY must not return unsat. Bug: bridge contradictory value propagation."
    );
}

/// Combined variant with string constraints (str.contains negation) and
/// both size and offset 4-byte sums. This is closer to the original
/// issue2429-code.smt2 benchmark.
const SLIA_COMBINED_STR_CONTAINS: &str = r#"
(set-logic QF_SLIA)
(set-info :status sat)

(declare-const p1 String)
(declare-const p2 String)
(declare-const size1 String)
(declare-const off1 String)
(assert (= 1 (str.len size1)))
(assert (= 1 (str.len off1)))

(declare-const before_p3 String)
(assert (= before_p3 (str.++ p1 p2)))
(assert (not (str.contains before_p3 "ABCD")))

(declare-const p2_size Int)
(declare-const p2_off Int)
(assert (= p2_size (ite (= (str.len size1) 1) (str.to_code size1) 256)))
(assert (= p2_off (ite (= (str.len off1) 1) (str.to_code off1) 256)))
(assert (<= (+ p2_size p2_off) (str.len before_p3)))
(assert (>= p2_size 10))

(check-sat)
"#;

#[test]
#[timeout(15_000)]
fn test_slia_combined_str_contains_not_false_unsat() {
    let commands = parse(SLIA_COMBINED_STR_CONTAINS).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(
        outputs,
        vec!["unsat"],
        "QF_SLIA combined str.contains formula is SAT (:status sat, Z3 confirms). \
         AY must not return unsat. Bug: bridge contradictory value propagation."
    );
}
