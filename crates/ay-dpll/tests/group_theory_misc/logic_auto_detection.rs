// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for logic auto-detection (#1071)
//!
//! When `set-logic` is not specified, AY should auto-detect the logic from
//! formula features and route to the correct solver.

use ntest::timeout;

/// Parse and solve an SMT2 formula, returning the result string.
/// Test that bitvector formulas are solved correctly without set-logic.
///
/// Regression test for #1071: ay returns incorrect SAT when set-logic is omitted.
/// Before the fix, this would route to QF_UF solver and return sat with invalid model.
#[test]
#[timeout(60_000)]
fn test_bv_without_set_logic() {
    // Simple bitvector formula that should be unsat:
    // a + 1 = a is never true for bitvectors (due to overflow semantics)
    let smt = r#"
        (declare-fun a () (_ BitVec 32))
        (assert (= (bvadd a (_ bv1 32)) a))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "BV formula without set-logic should be unsat"
    );
}

/// Test that bitvector+array formulas are solved correctly without set-logic.
#[test]
#[timeout(60_000)]
fn test_abv_without_set_logic() {
    let smt = r#"
        (declare-fun arr () (Array (_ BitVec 32) (_ BitVec 32)))
        (declare-fun a () (_ BitVec 32))
        (assert (= (select arr a) (_ bv1 32)))
        (assert (= (select arr a) (_ bv2 32)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "ABV formula without set-logic should be unsat"
    );
}

/// Test that AUFBV formulas are solved correctly without set-logic.
#[test]
#[timeout(60_000)]
fn test_aufbv_without_set_logic() {
    let smt = r#"
        (declare-fun arr () (Array (_ BitVec 32) (_ BitVec 32)))
        (declare-fun f ((_ BitVec 32)) (_ BitVec 32))
        (declare-fun a () (_ BitVec 32))
        (assert (= (select arr (f a)) (_ bv1 32)))
        (assert (= (select arr (f a)) (_ bv2 32)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "AUFBV formula without set-logic should be unsat"
    );
}

/// Test that LIA formulas are solved correctly without set-logic.
#[test]
#[timeout(60_000)]
fn test_lia_without_set_logic() {
    let smt = r#"
        (declare-fun x () Int)
        (assert (> x 0))
        (assert (< x 0))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "LIA formula without set-logic should be unsat"
    );
}

/// Test that LRA formulas are solved correctly without set-logic.
#[test]
#[timeout(60_000)]
fn test_lra_without_set_logic() {
    let smt = r#"
        (declare-fun x () Real)
        (assert (> x 0.5))
        (assert (< x 0.5))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "LRA formula without set-logic should be unsat"
    );
}

/// Test that UFLIA formulas are solved correctly without set-logic.
#[test]
#[timeout(60_000)]
fn test_uflia_without_set_logic() {
    let smt = r#"
        (declare-fun f (Int) Int)
        (declare-fun x () Int)
        (assert (= (f x) 5))
        (assert (= (f x) 10))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "UFLIA formula without set-logic should be unsat"
    );
}

/// Test that pure UF formulas are solved correctly without set-logic.
#[test]
#[timeout(60_000)]
fn test_uf_without_set_logic() {
    let smt = r#"
        (declare-sort S 0)
        (declare-fun a () S)
        (declare-fun b () S)
        (declare-fun f (S) S)
        (assert (= (f a) (f b)))
        (assert (distinct a b))
        (assert (distinct (f a) (f b)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "UF formula without set-logic should be unsat"
    );
}

/// Test that propositional formulas work without set-logic.
#[test]
#[timeout(60_000)]
fn test_propositional_without_set_logic() {
    let smt = r#"
        (declare-fun p () Bool)
        (assert p)
        (assert (not p))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Propositional formula without set-logic should be unsat"
    );
}

/// Test that propositional `check-sat-assuming` narrows correctly without set-logic.
#[test]
#[timeout(60_000)]
fn test_propositional_check_sat_assuming_without_set_logic() {
    let smt = r#"
        (declare-fun p () Bool)
        (assert p)
        (check-sat-assuming ((not p)))
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Propositional check-sat-assuming without set-logic should be unsat"
    );
}

/// Test that SAT formulas return sat correctly.
#[test]
#[timeout(60_000)]
fn test_sat_bv_without_set_logic() {
    let smt = r#"
        (declare-fun a () (_ BitVec 32))
        (assert (bvugt a (_ bv0 32)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(result.trim(), "sat", "SAT BV formula should return sat");
}

/// Test that non-linear Int formulas route to NIA (#1551).
///
/// This is the concrete soundness risk from #1551: `(* x x) = 2` over Int
/// should be unsat (no integer squares to 2), not treated as a linear variable.
#[test]
#[timeout(60_000)]
fn test_nonlinear_int_routes_to_nia() {
    // (= (* x x) 2) is unsat over integers - no integer squares to 2
    let smt = r#"
        (declare-fun x () Int)
        (assert (= (* x x) 2))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    // Should return "unsat" or "unknown" (if NIA incomplete), but NOT "sat"
    assert!(
        result.trim() == "unsat" || result.trim() == "unknown",
        "Non-linear Int formula (* x x) = 2 should be unsat or unknown, got: {}",
        result.trim()
    );
}

/// Test that linear Int still routes to LIA.
#[test]
#[timeout(60_000)]
fn test_linear_int_routes_to_lia() {
    // Linear formula: 2*x = 4 is sat (x=2)
    let smt = r#"
        (declare-fun x () Int)
        (assert (= (* 2 x) 4))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "Linear Int formula should route to LIA and be sat"
    );
}

/// Test non-linear Real detection.
#[test]
#[timeout(60_000)]
fn test_nonlinear_real_routes_to_nra() {
    // x^2 = -1 is unsat over reals
    let smt = r#"
        (declare-fun x () Real)
        (assert (= (* x x) (- 1.0)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    // Should return "unsat" or "unknown", but NOT "sat"
    assert!(
        result.trim() == "unsat" || result.trim() == "unknown",
        "Non-linear Real formula (* x x) = -1 should be unsat or unknown, got: {}",
        result.trim()
    );
}

/// Test that division by a variable is detected as non-linear (#1551 follow-up).
#[test]
#[timeout(60_000)]
fn test_div_by_variable_routes_to_nia() {
    // Division by a variable is non-linear
    let smt = r#"
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (> y 0))
        (assert (= (div x y) 2))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    // Should return "sat" or "unknown" (NIA is incomplete), but NOT error
    assert!(
        result.trim() == "sat" || result.trim() == "unknown",
        "Division by variable should route to NIA, got: {}",
        result.trim()
    );
}

/// Test that division by a constant stays linear.
#[test]
#[timeout(60_000)]
fn test_div_by_constant_stays_lia() {
    // Division by a constant is linear (routes to LIA, not NIA)
    // Note: AY's LIA solver may not fully support div, returning "unknown"
    let smt = r#"
        (declare-fun x () Int)
        (assert (= (div x 3) 2))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    // Formula is SAT (x = 6 is a witness). Division by constant is linear,
    // so this routes to LIA. AY may return unknown (incompleteness) but
    // must never return false-UNSAT.
    assert!(
        result.trim() == "sat" || result.trim() == "unknown",
        "Division by constant formula is SAT (x=6), got {got:?} (false-UNSAT regression)",
        got = result.trim()
    );
}

/// Test that quantified NIA can be solved or returns unknown.
/// The formula `forall y: x*y > 0` is UNSAT (y=0 is a counterexample).
/// With the NIA split-loop pipeline (#7920), the solver can now handle
/// NeedSplit from the underlying LIA branch-and-bound, enabling solutions.
#[test]
#[timeout(60_000)]
fn test_quantified_nia_solves_or_unknown() {
    let smt = r#"
        (set-logic NIA)
        (declare-fun x () Int)
        (assert (forall ((y Int)) (> (* x y) 0)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    // Formula is UNSAT (y=0 gives x*0=0, not >0). Solver may also return unknown.
    assert!(
        result.trim() == "unsat" || result.trim() == "unknown",
        "Quantified NIA formula is UNSAT, got: {}",
        result.trim()
    );
}

/// Test that quantified NRA is either solved or returns unknown.
/// See #1580 for tracking this feature gap.
#[test]
#[timeout(60_000)]
fn test_quantified_nra_returns_unknown() {
    let smt = r#"
        (set-logic NRA)
        (declare-fun x () Real)
        (assert (forall ((y Real)) (> (* x y) 0.0)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert!(
        matches!(result.trim(), "unsat" | "unknown"),
        "Quantified NRA formula is UNSAT, got: {}",
        result.trim()
    );
}

/// Test that QF_LRA with nonlinear terms auto-upgrades to QF_NRA (#4125, #5605).
///
/// Consumers like optimization_consumer declare QF_LRA but use `(* x y)` (real multiplication).
/// The executor should detect `has_nonlinear_real` via StaticFeatures and upgrade
/// to QF_NRA so the NRA solver handles it instead of returning "unknown".
#[test]
#[timeout(60_000)]
fn test_qf_lra_with_nonlinear_upgrades_to_nra() {
    // Declare QF_LRA but use nonlinear real multiplication.
    // x^2 = -1 is unsat over reals (no real number squared is negative).
    let smt = r#"
        (set-logic QF_LRA)
        (declare-fun x () Real)
        (assert (= (* x x) (- 1.0)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert!(
        matches!(result.trim(), "unsat" | "unknown"),
        "QF_LRA with nonlinear terms must not return sat, got: {}",
        result.trim()
    );
}

/// Test that QF_LRA without nonlinear terms stays as LRA.
#[test]
#[timeout(60_000)]
fn test_qf_lra_linear_stays_lra() {
    // Pure linear real arithmetic — should NOT upgrade to NRA.
    let smt = r#"
        (set-logic QF_LRA)
        (declare-fun x () Real)
        (declare-fun y () Real)
        (assert (> (+ x y) 1.0))
        (assert (< x 0.5))
        (assert (< y 0.5))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    // x + y > 1 but x < 0.5 and y < 0.5, so x + y < 1.0 → unsat
    assert_eq!(
        result.trim(),
        "unsat",
        "Linear QF_LRA should stay as LRA and return unsat, got: {}",
        result.trim()
    );
}

/// Datatypes + NONLINEAR integer arithmetic must reach the DT+NIA lane.
///
/// Content detection routes datatype+Int content to the internal `_DT_AUFLIA`
/// category; `with_nonlinear` then used to collapse it to `Other`, and check-sat
/// answered `Err(UnsupportedLogic)` — the CLI's opaque
/// `(incomplete decision-execution-error)`. The Barrett `rec-fun-ijcar2016`
/// family (SMT-LIB divisions AUFBVDTNIA/AUFBVDTLIA) hits exactly this path,
/// because `AUFBVDTNIA` is an accepted-but-unmapped token that routes through
/// content detection. The same file with a declared `AUFDTNIA` already solved.
/// (#dt-nia-content-route)
const DT_NONLINEAR_INT_UNSAT_BODY: &str = r#"
    (declare-datatypes ((Lst 0)) (((Cons (hd Int) (tl Lst)) (Nil))))
    (declare-fun l () Lst)
    (declare-fun n () Int)
    (declare-fun m () Int)
    (assert ((_ is Cons) l))
    (assert (= (hd l) (* n m)))
    (assert (> (hd l) 5))
    (assert (< (* n m) 3))
    (check-sat)
"#;

#[test]
#[timeout(60_000)]
fn dt_nonlinear_int_without_set_logic_reaches_a_lane() {
    let result = crate::common::solve(DT_NONLINEAR_INT_UNSAT_BODY);
    assert_eq!(
        result.trim(),
        "unsat",
        "DT + nonlinear Int must route to the DT+NIA lane, got: {}",
        result.trim()
    );
}

#[test]
#[timeout(60_000)]
fn dt_nonlinear_int_under_unmapped_aufbvdtnia_reaches_a_lane() {
    let smt = format!("(set-logic AUFBVDTNIA){DT_NONLINEAR_INT_UNSAT_BODY}");
    let result = crate::common::solve(&smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "an accepted-but-unmapped AUFBVDTNIA routes through content detection \
         and must reach the same lane, got: {}",
        result.trim()
    );
}

#[test]
#[timeout(60_000)]
fn dt_nonlinear_int_under_all_reaches_a_lane() {
    let smt = format!("(set-logic ALL){DT_NONLINEAR_INT_UNSAT_BODY}");
    let result = crate::common::solve(&smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "(set-logic ALL) must not report `unsupported logic: ALL` on content \
         that has a lane, got: {}",
        result.trim()
    );
}

/// The declared arm this mirrors keeps working.
#[test]
#[timeout(60_000)]
fn dt_nonlinear_int_under_declared_aufdtnia_reaches_a_lane() {
    let smt = format!("(set-logic AUFDTNIA){DT_NONLINEAR_INT_UNSAT_BODY}");
    let result = crate::common::solve(&smt);
    assert_eq!(result.trim(), "unsat");
}

/// Array-bearing DT + nonlinear Int stays fail-closed: the `Ufdtnia` lane
/// composes DT axioms over `solve_uf_nia`, which has no array theory, so
/// `select`/`store` would be uninterpreted and a `sat` could violate
/// read-over-write. It must NOT publish a verdict.
#[test]
#[timeout(60_000)]
fn array_bearing_dt_nonlinear_int_stays_fail_closed() {
    let smt = r#"
        (declare-datatypes ((Lst 0)) (((Cons (hd Int) (tl Lst)) (Nil))))
        (declare-fun l () Lst)
        (declare-fun a () (Array Int Int))
        (declare-fun n () Int)
        (declare-fun m () Int)
        (assert ((_ is Cons) l))
        (assert (= (hd l) (select (store a 0 (* n m)) 0)))
        (assert (> (hd l) 5))
        (assert (< (* n m) 3))
        (check-sat)
    "#;
    let commands = ay_frontend::parse(smt).expect("parse");
    let mut exec = ay_dpll::Executor::new();
    match exec.execute_all(&commands) {
        // Fail-closed: either a hard `UnsupportedLogic` refusal (today) or a
        // sound `unknown`. A definitive verdict from a lane with no array
        // theory is what this test forbids.
        Ok(lines) => assert!(
            lines
                .iter()
                .all(|l| l.trim() != "sat" && l.trim() != "unsat"),
            "array-bearing DT+NIA must not publish a verdict from an \
             array-blind lane, got: {lines:?}"
        ),
        Err(_) => {}
    }
}

/// DT + FP has no sound combined solver (#8728) and must keep its QUIET
/// `unknown` — the `Other` fallback is narrowed by the DT+NIA arm above, not
/// deleted.
#[test]
#[timeout(60_000)]
fn dt_plus_fp_keeps_its_quiet_unknown() {
    let smt = r#"
        (declare-datatypes ((Box 0)) (((Mk (getFlt (_ FloatingPoint 8 24))))))
        (declare-fun b () Box)
        (declare-fun x () (_ FloatingPoint 8 24))
        (assert (distinct (Mk ((_ to_fp 8 24) RNE 1.0)) (Mk x)))
        (assert (fp.isNaN x))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unknown",
        "DT + FP must stay a sound fail-closed unknown, got: {}",
        result.trim()
    );
}
