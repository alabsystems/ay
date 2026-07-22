// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for UF+LIA congruence gap (#3581).
//!
//! When UF and LIA interact, ay must chain function equalities with arithmetic.
//! For example:
//!   f(0) = 0
//!   f(1) = f(0) + 1
//!   NOT(f(1) = 1)
//!
//! This is UNSAT: substituting f(0)=0 into f(1)=f(0)+1 gives f(1)=1.
//! Z3 solves this instantly. AY was failing because the Nelson-Oppen
//! equality propagation between EUF and LIA did not chain through
//! arithmetic expressions containing UF subterms.

use ntest::timeout;

/// Core reproducer: f(0) = 0, f(1) = f(0) + 1, f(1) != 1 → UNSAT
#[test]
#[timeout(10_000)]
fn test_uf_lia_congruence_chain_basic_3581() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (assert (= (f 0) 0))
        (assert (= (f 1) (+ (f 0) 1)))
        (assert (not (= (f 1) 1)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Three-step chain: f(0) = 0, f(1) = f(0) + 1, f(2) = f(1) + 1, f(2) != 2
#[test]
#[timeout(10_000)]
fn test_uf_lia_congruence_chain_three_steps_3581() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (assert (= (f 0) 0))
        (assert (= (f 1) (+ (f 0) 1)))
        (assert (= (f 2) (+ (f 1) 1)))
        (assert (not (= (f 2) 2)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Two functions: f(0)=0, g(0)=f(0)+1, g(0)!=1 → UNSAT
#[test]
#[timeout(10_000)]
fn test_uf_lia_two_functions_chain_3581() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (assert (= (f 0) 0))
        (assert (= (g 0) (+ (f 0) 1)))
        (assert (not (= (g 0) 1)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// SAT case: f(0)=0, f(1)=f(0)+1, f(1)=1 is satisfiable
#[test]
#[timeout(10_000)]
fn test_uf_lia_congruence_chain_sat_3581() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (assert (= (f 0) 0))
        (assert (= (f 1) (+ (f 0) 1)))
        (assert (= (f 1) 1))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "sat");
}

/// Multiplication chain: f(0)=5, g(x)=2*f(0), g(x)!=10 → UNSAT
#[test]
#[timeout(10_000)]
fn test_uf_lia_multiply_chain_3581() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (declare-const x Int)
        (assert (= (f 0) 5))
        (assert (= (g x) (* 2 (f 0))))
        (assert (not (= (g x) 10)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Indirect chain where the derived value (7) does not appear as a literal
/// constant in the formula. f(0)=3, f(1)=f(0)+4, f(1)!=7 → UNSAT
/// The constant 7 never appears in the formula — only 3 and 4 do.
/// The N-O bridge must evaluate f(0)+4 = 3+4 = 7 and propagate f(1)=7,
/// which requires the bridge to synthesize the constant 7.
#[test]
#[timeout(10_000)]
fn test_uf_lia_derived_constant_not_in_formula_3581() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (assert (= (f 0) 3))
        (assert (= (f 1) (+ (f 0) 4)))
        (assert (not (= (f 1) 7)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Chain where the negated equality target is not a constant but a variable
/// expression: f(0)=x, f(1)=f(0)+1, f(1)!=x+1 → UNSAT
#[test]
#[timeout(10_000)]
fn test_uf_lia_chain_with_variable_target_3581() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (assert (= (f 0) x))
        (assert (= (f 1) (+ (f 0) 1)))
        (assert (not (= (f 1) (+ x 1))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Two-function chain requiring cross-UF propagation:
/// f(0) = 0, g(0) = f(0), h(0) = g(0) + 1, h(0) != 1 → UNSAT
#[test]
#[timeout(10_000)]
fn test_uf_lia_cross_function_chain_3581() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (declare-fun h (Int) Int)
        (assert (= (f 0) 0))
        (assert (= (g 0) (f 0)))
        (assert (= (h 0) (+ (g 0) 1)))
        (assert (not (= (h 0) 1)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Pure LIA chain that happens to use UF notation (should still be UNSAT):
/// f(x) = x + 1, f(x) != x + 1 → UNSAT (trivially)
#[test]
#[timeout(10_000)]
fn test_uf_lia_tautological_unsat_3581() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (assert (= (f x) (+ x 1)))
        (assert (not (= (f x) (+ x 1))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Same as basic but with auto-detected logic (no set-logic).
/// Verifies the logic auto-detection routes to the correct combined solver.
#[test]
#[timeout(10_000)]
fn test_uf_lia_congruence_chain_auto_logic_3581() {
    let smt = r#"
        (declare-fun f (Int) Int)
        (assert (= (f 0) 0))
        (assert (= (f 1) (+ (f 0) 1)))
        (assert (not (= (f 1) 1)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Chain with negation and subtraction: f(0)=10, f(1)=f(0)-3, f(1)!=7 → UNSAT
#[test]
#[timeout(10_000)]
fn test_uf_lia_subtraction_chain_3581() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (assert (= (f 0) 10))
        (assert (= (f 1) (- (f 0) 3)))
        (assert (not (= (f 1) 7)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Complex arithmetic in the chain: f(0)=2, g(0)=f(0)*3+1, g(0)!=7 → UNSAT
#[test]
#[timeout(10_000)]
fn test_uf_lia_complex_arith_chain_3581() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (assert (= (f 0) 2))
        (assert (= (g 0) (+ (* 3 (f 0)) 1)))
        (assert (not (= (g 0) 7)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Incremental context with push/pop to test state management
#[test]
#[timeout(10_000)]
fn test_uf_lia_congruence_chain_incremental_3581() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (assert (= (f 0) 0))
        (assert (= (f 1) (+ (f 0) 1)))
        (push 1)
        (assert (not (= (f 1) 1)))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= (f 1) 1))
        (check-sat)
        (pop 1)
    "#;
    let output = crate::common::solve(smt);
    let lines: Vec<&str> = output
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .collect();
    assert_eq!(lines, vec!["unsat", "sat"]);
}

/// Deeper chain: f(0)=0, f(n+1)=f(n)+1, f(5)!=5 → UNSAT
/// Tests that the Nelson-Oppen loop handles 5 chained equalities.
#[test]
#[timeout(10_000)]
fn test_uf_lia_deep_chain_3581() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (assert (= (f 0) 0))
        (assert (= (f 1) (+ (f 0) 1)))
        (assert (= (f 2) (+ (f 1) 1)))
        (assert (= (f 3) (+ (f 2) 1)))
        (assert (= (f 4) (+ (f 3) 1)))
        (assert (= (f 5) (+ (f 4) 1)))
        (assert (not (= (f 5) 5)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Pattern from verification-consumer VCs: pre/post condition with UF
/// inv(0) = base, inv(1) = inv(0) - step, inv(2) = inv(1) - step
/// base=100, step=10 → inv(0)=100, inv(1)=90, inv(2)=80
/// NOT(inv(2) = 80) → UNSAT
///
/// This requires chaining UF equalities through arithmetic with
/// intermediate variables (base, step) that are bound by separate equalities.
#[test]
#[timeout(10_000)]
fn test_uf_lia_verification_consumer_vc_pattern_3581() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun inv (Int) Int)
        (declare-const base Int)
        (declare-const step Int)
        (assert (= base 100))
        (assert (= step 10))
        (assert (= (inv 0) base))
        (assert (= (inv 1) (- (inv 0) step)))
        (assert (= (inv 2) (- (inv 1) step)))
        (assert (not (= (inv 2) 80)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Minimal reproducer: f(0)=x, f(1)=f(0)-x, f(1)!=0 → UNSAT
/// f(0)=x, f(1)=f(0)-x = x-x = 0, so f(1)=0
#[test]
#[timeout(10_000)]
fn test_uf_lia_variable_arith_chain_3581() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (assert (= (f 0) x))
        (assert (= (f 1) (- (f 0) x)))
        (assert (not (= (f 1) 0)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}
