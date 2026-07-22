// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for LIA unknown-recovery chain (#4785).
//!
//! These test problems that previously returned `unknown` because the LRA
//! simplex cycling/iteration-limit path had no integer-closing fallback.
//! The recovery chain (GCD tableau test, HNF cuts, small Gomory cuts)
//! should now catch these before giving up.

use ntest::timeout;

/// GCD-based infeasibility: 4x + 6y = 7 has no integer solution since gcd(4,6)=2
/// doesn't divide 7. This exercises the gcd_test_tableau() recovery path.
#[test]
#[timeout(10_000)]
fn test_gcd_recovery_from_lra_relaxation() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= (+ (* 4 x) (* 6 y)) 7))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Modular ring constraint: x ≡ 0 (mod 256) with 0 < x < 256 is unsat.
/// Expressed as: x = 256*k, 1 <= x, x <= 255.
/// The only multiple of 256 in [1,255] doesn't exist.
#[test]
#[timeout(10_000)]
fn test_ring_modular_infeasible() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const k Int)
        (assert (= x (* 256 k)))
        (assert (>= x 1))
        (assert (<= x 255))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Two equations with large coefficients that create a tight integer gap.
/// 17x + 23y = 100, 31x - 13y = 50. This system has a unique rational
/// solution that is non-integer, so LIA must detect infeasibility through
/// cuts or GCD analysis.
#[test]
#[timeout(30_000)]
fn test_tight_coefficient_system_unsat() {
    // 17x + 23y = 100  =>  x = (100 - 23y)/17
    // 31x - 13y = 50
    // Substituting: 31*(100 - 23y)/17 - 13y = 50
    // 3100 - 713y - 221y = 850
    // -934y = -2250
    // y = 2250/934 = 1125/467 (non-integer)
    // So x = (100 - 23*1125/467)/17 = non-integer
    // The system is infeasible in integers.
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= (+ (* 17 x) (* 23 y)) 100))
        (assert (= (- (* 31 x) (* 13 y)) 50))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Satisfiable ring problem: x = 16k, 0 <= x <= 256. k=1 gives x=16.
/// Ensures the recovery chain doesn't break SAT results.
#[test]
#[timeout(10_000)]
fn test_ring_modular_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const k Int)
        (assert (= x (* 16 k)))
        (assert (>= x 1))
        (assert (<= x 256))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "sat");
}

/// HNF-cut recovery: system with 3 equalities over 4 vars, bounded.
/// 2x + 3y = 12, 4x + z = 20, 0 <= x <= 10, 0 <= y <= 10, 0 <= z <= 20, 0 <= w <= 5.
/// Additional: w = x + y - 5.
/// The system constrains x to integer values where 2x+3y=12, 4x+z=20.
/// From eq1: y = (12-2x)/3, integer iff x ≡ 0 (mod 3).
/// From eq2: z = 20-4x.
/// x=0: y=4, z=20, w=-1 (invalid: w>=0)
/// x=3: y=2, z=8, w=0 (valid!)
/// x=6: y=0, z=-4 (invalid: z>=0)
/// So unique solution x=3, y=2, z=8, w=0.
#[test]
#[timeout(10_000)]
fn test_bounded_equality_system_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const z Int)
        (declare-const w Int)
        (assert (= (+ (* 2 x) (* 3 y)) 12))
        (assert (= (+ (* 4 x) z) 20))
        (assert (= w (- (+ x y) 5)))
        (assert (>= x 0)) (assert (<= x 10))
        (assert (>= y 0)) (assert (<= y 10))
        (assert (>= z 0)) (assert (<= z 20))
        (assert (>= w 0)) (assert (<= w 5))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "sat");
}

/// Regression: this SAT formula must never produce false UNSAT.
///
/// Z3 model: c=3, a=-5, b=11, d=-17 (verified manually).
/// AY previously oscillated on this formula (splits on vars 2 and 4 alternately).
/// The oscillation recovery fallback should help, but there is a deeper
/// Gomory cut soundness issue: the cuts generated from the equality-substituted
/// tableau can be too tight, cutting off feasible integer points.
///
/// Tracked: Gomory cut false-UNSAT on equality-dense formulas.
/// Accept `sat` or `unknown`; reject `unsat`.
#[test]
#[timeout(30_000)]
fn test_oscillation_fallback_must_not_be_unsat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (declare-const d Int)
        (assert (>= (* 2 c) 5))
        (assert (>= (+ (* (- 2) d) (* 4 c) (* (- 2) a)) 1))
        (assert (= (+ d (* (- 1) b) (* (- 4) a)) (- 8)))
        (assert (<= (+ (* 4 b) (* 3 d)) (- 4)))
        (assert (<= (+ (* (- 3) b) (* (- 4) c) (* 3 d)) (- 3)))
        (assert (= b (+ (* 4 c) (- 1))))
        (check-sat)
    "#;
    let result = crate::common::solve(smt).trim().to_string();
    assert_ne!(
        result, "unsat",
        "Z3 returns sat (c=3, a=-5, b=11, d=-17); AY must not claim unsat"
    );
}
