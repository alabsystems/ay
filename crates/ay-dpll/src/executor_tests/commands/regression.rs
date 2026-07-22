// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ========== Recursive Function Definition Tests ==========

#[test]
fn test_define_fun_rec_parses() {
    // Test that define-fun-rec is parsed and handled without error
    let input = r#"
        (set-logic QF_LIA)
        (define-fun-rec fact ((n Int)) Int (ite (= n 0) 1 (* n (fact (- n 1)))))
        (declare-const x Int)
        (assert (= x 5))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "sat");
}

#[test]
fn test_define_fun_rec_no_params() {
    // Test recursive function with no parameters (constant recursive definition)
    let input = r#"
        (set-logic QF_LIA)
        (define-fun-rec const_val () Int 42)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "sat");
}

#[test]
fn test_define_funs_rec_parses() {
    // Test that define-funs-rec is parsed and handled without error
    let input = r#"
        (set-logic QF_LIA)
        (define-funs-rec
            ((is_even ((n Int)) Bool) (is_odd ((n Int)) Bool))
            ((ite (= n 0) true (is_odd (- n 1)))
             (ite (= n 0) false (is_even (- n 1)))))
        (declare-const x Int)
        (assert (= x 4))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "sat");
}

#[test]
fn test_define_funs_rec_multiple_params() {
    // Test mutually recursive functions with multiple parameters
    let input = r#"
        (set-logic QF_LIA)
        (define-funs-rec
            ((f1 ((a Int) (b Int)) Int) (f2 ((x Int) (y Int)) Int))
            ((+ a (f2 b a)) (- x (f1 y x))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "sat");
}

// ========== #6077 Dispatch Soundness Tests ==========

/// #6077 Bug 1: check_sat_assuming under QF_LIA with nonlinear integer terms
/// must not produce false SAT. The LIA solver cannot handle nonlinear terms
/// correctly — it treats (* x y) as a fresh variable. The fix upgrades to NIA.
///
/// Formula: x > 0, y > 0, x * y < 0 (contradictory for positive integers).
/// Under QF_LIA without NIA upgrade: SAT (spurious — treats x*y as fresh var).
/// Under QF_NIA: UNSAT (correct — detects nonlinear constraint).
#[test]
fn test_check_sat_assuming_qf_lia_nonlinear_upgrade_6077() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (> x 0))
        (assert (> y 0))
        (check-sat-assuming ((< (* x y) 0)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // With nonlinear upgrade, must NOT return sat (x>0, y>0 → x*y>0, not <0).
    // Acceptable: unsat or unknown.
    assert!(
        outputs[0] == "unknown" || outputs[0] == "unsat",
        "QF_LIA with nonlinear assumptions must not return false SAT (#6077 Bug 1) — got: {}",
        outputs[0]
    );
}

/// #6077 Bug 3: UF + Int + Real formula via auto-detection must not drop Int.
///
/// Formula uses UF (f), Int (x), and Real (r) simultaneously. The UNSAT
/// depends on integer reasoning: x = 5 makes f(x) = f(5) which contradicts
/// (not (f 5)). Under QF_UFLRA (pre-fix): Int constraints dropped, so x = 5
/// is ignored and the formula becomes satisfiable (false SAT).
/// Under QF_AUFLIRA (post-fix): both Int and Real handled correctly.
///
/// NOTE (P1:49 audit): Previous version used `f(x) AND NOT f(x)` which is a
/// trivial UF contradiction (UNSAT regardless of arithmetic routing). This
/// version requires integer equality reasoning: x must be determined as 5 to
/// trigger the UF conflict between f(x) and NOT f(5).
#[test]
fn test_auto_detect_uf_int_real_not_false_sat_6077() {
    // Auto-detection: don't set logic, let the solver infer it.
    let input = r#"
        (declare-fun f (Int) Bool)
        (declare-const x Int)
        (declare-const r Real)
        (assert (f x))
        (assert (= x 5))
        (assert (> r 0.0))
        (assert (not (f 5)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // f(x) with x=5 gives f(5), which contradicts (not (f 5)).
    // This requires both UF (congruence closure) and Int (x=5) to solve.
    // Auto-detection must route to a logic handling both sorts.
    assert!(
        outputs[0] == "unknown" || outputs[0] == "unsat",
        "UF+Int+Real formula where UNSAT depends on Int reasoning must not return false SAT (#6077 Bug 3) — got: {}",
        outputs[0]
    );
}

/// #6077: check_sat_internal (regular check-sat) must detect nonlinear terms
/// under QF_UFLIA and return Unknown instead of routing to the linear solver.
///
/// Formula: x > 0, y > 0, x * y < 0 — contradictory for positive integers.
/// Without the guard, the linear solver treats (* x y) as a fresh variable
/// and produces false SAT (caught by model validation as an error).
/// With the guard, the solver detects nonlinear Int and returns "unknown".
#[test]
fn test_check_sat_qf_uflia_nonlinear_must_not_return_sat_6077() {
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (> x 0))
        (assert (> y 0))
        (assert (< (* x y) 0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert!(
        outputs[0] == "unknown" || outputs[0] == "unsat",
        "QF_UFLIA with nonlinear check-sat must not return false SAT (#6077) — got: {}",
        outputs[0]
    );
}

/// #6077: check_sat_internal must detect nonlinear terms under QF_UFLRA.
#[test]
fn test_check_sat_qf_uflra_nonlinear_must_not_return_sat_6077() {
    let input = r#"
        (set-logic QF_UFLRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (> x 0.0))
        (assert (> y 0.0))
        (assert (< (* x y) 0.0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert!(
        outputs[0] == "unknown" || outputs[0] == "unsat",
        "QF_UFLRA with nonlinear check-sat must not return false SAT (#6077) — got: {}",
        outputs[0]
    );
}

/// #6077: check_sat_internal must detect nonlinear terms under QF_AUFLIA.
#[test]
fn test_check_sat_qf_auflia_nonlinear_must_not_return_sat_6077() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (> x 0))
        (assert (> y 0))
        (assert (< (* x y) 0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert!(
        outputs[0] == "unknown" || outputs[0] == "unsat",
        "QF_AUFLIA with nonlinear check-sat must not return false SAT (#6077) — got: {}",
        outputs[0]
    );
}

/// #6077: check_sat_internal must detect nonlinear terms under QF_AUFLRA.
#[test]
fn test_check_sat_qf_auflra_nonlinear_must_not_return_sat_6077() {
    let input = r#"
        (set-logic QF_AUFLRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (> x 0.0))
        (assert (> y 0.0))
        (assert (< (* x y) 0.0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert!(
        outputs[0] == "unknown" || outputs[0] == "unsat",
        "QF_AUFLRA with nonlinear check-sat must not return false SAT (#6077) — got: {}",
        outputs[0]
    );
}

/// #6077: Quantified UFLIA with nonlinear int must not return false SAT.
///
/// The quantified path (check_sat_internal, LogicCategory::Uflia) must detect
/// nonlinear terms and return Unknown. Without the guard, the linear solver
/// ignores the nonlinear multiplication and may produce false SAT.
#[test]
fn test_check_sat_uflia_nonlinear_must_not_return_sat_6077() {
    let input = r#"
        (set-logic UFLIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-fun f (Int) Int)
        (assert (forall ((z Int)) (! (>= (f z) 0) :pattern ((f z)))))
        (assert (> x 0))
        (assert (> y 0))
        (assert (< (* x y) 0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert!(
        outputs[0] == "unknown" || outputs[0] == "unsat",
        "UFLIA with nonlinear check-sat must not return false SAT (#6077) — got: {}",
        outputs[0]
    );
}

/// #6077: Quantified UFLRA with nonlinear real must not return false SAT.
#[test]
fn test_check_sat_uflra_nonlinear_must_not_return_sat_6077() {
    let input = r#"
        (set-logic UFLRA)
        (declare-const x Real)
        (declare-const y Real)
        (declare-fun f (Real) Real)
        (assert (forall ((z Real)) (! (>= (f z) 0.0) :pattern ((f z)))))
        (assert (> x 0.0))
        (assert (> y 0.0))
        (assert (< (* x y) 0.0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert!(
        outputs[0] == "unknown" || outputs[0] == "unsat",
        "UFLRA with nonlinear check-sat must not return false SAT (#6077) — got: {}",
        outputs[0]
    );
}

/// #6077: Quantified AUFLIA with nonlinear int must not return false SAT.
#[test]
fn test_check_sat_auflia_nonlinear_must_not_return_sat_6077() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-fun f (Int) Int)
        (declare-sort A 0)
        (declare-fun arr () (Array Int A))
        (assert (forall ((z Int)) (! (>= (f z) 0) :pattern ((f z)))))
        (assert (> x 0))
        (assert (> y 0))
        (assert (< (* x y) 0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert!(
        outputs[0] == "unknown" || outputs[0] == "unsat",
        "AUFLIA with nonlinear check-sat must not return false SAT (#6077) — got: {}",
        outputs[0]
    );
}

/// #6077: Quantified AUFLRA with nonlinear real must not return false SAT.
#[test]
fn test_check_sat_auflra_nonlinear_must_not_return_sat_6077() {
    let input = r#"
        (set-logic AUFLRA)
        (declare-const x Real)
        (declare-const y Real)
        (declare-fun f (Real) Real)
        (declare-sort A 0)
        (declare-fun arr () (Array Int A))
        (assert (forall ((z Real)) (! (>= (f z) 0.0) :pattern ((f z)))))
        (assert (> x 0.0))
        (assert (> y 0.0))
        (assert (< (* x y) 0.0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert!(
        outputs[0] == "unknown" || outputs[0] == "unsat",
        "AUFLRA with nonlinear check-sat must not return false SAT (#6077) — got: {}",
        outputs[0]
    );
}

// ========== check_sat_assuming nonlinear guard tests (#6077 audit) ==========

/// #6077 audit: check_sat_assuming under QF_LRA with nonlinear real must not
/// return false SAT. The guard at executor.rs:778 upgrades to NRA solver.
///
/// Formula: x > 0, y > 0, assumption x*y < 0 — contradictory.
/// Without guard: LRA treats (* x y) as fresh variable → false SAT.
/// With guard: NRA solver correctly determines UNSAT.
#[test]
fn test_check_sat_assuming_qf_lra_nonlinear_must_not_return_sat_6077() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (> x 0.0))
        (assert (> y 0.0))
        (check-sat-assuming ((< (* x y) 0.0)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert!(
        outputs[0] == "unknown" || outputs[0] == "unsat",
        "QF_LRA check-sat-assuming with nonlinear must not return false SAT — got: {}",
        outputs[0]
    );
}

/// #6077 audit: check_sat_assuming under QF_UFLIA with nonlinear int must not
/// return false SAT. The guard at executor.rs:848 returns Unknown.
#[test]
fn test_check_sat_assuming_qf_uflia_nonlinear_must_not_return_sat_6077() {
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (> x 0))
        (assert (> y 0))
        (check-sat-assuming ((< (* x y) 0)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert!(
        outputs[0] == "unknown" || outputs[0] == "unsat",
        "QF_UFLIA check-sat-assuming with nonlinear must not return false SAT — got: {}",
        outputs[0]
    );
}

/// #6077 audit: check_sat_assuming under QF_UFLRA with nonlinear real must not
/// return false SAT. The guard at executor.rs:879 returns Unknown.
#[test]
fn test_check_sat_assuming_qf_uflra_nonlinear_must_not_return_sat_6077() {
    let input = r#"
        (set-logic QF_UFLRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (> x 0.0))
        (assert (> y 0.0))
        (check-sat-assuming ((< (* x y) 0.0)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert!(
        outputs[0] == "unknown" || outputs[0] == "unsat",
        "QF_UFLRA check-sat-assuming with nonlinear must not return false SAT — got: {}",
        outputs[0]
    );
}

/// #6077 audit: check_sat_assuming under QF_AUFLIA with nonlinear int must not
/// return false SAT. The guard at executor.rs:895 returns Unknown.
#[test]
fn test_check_sat_assuming_qf_auflia_nonlinear_must_not_return_sat_6077() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (> x 0))
        (assert (> y 0))
        (check-sat-assuming ((< (* x y) 0)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert!(
        outputs[0] == "unknown" || outputs[0] == "unsat",
        "QF_AUFLIA check-sat-assuming with nonlinear must not return false SAT — got: {}",
        outputs[0]
    );
}

/// #6077 audit: check_sat_assuming under QF_AUFLRA with nonlinear real must not
/// return false SAT. The guard at executor.rs:907 returns Unknown.
#[test]
fn test_check_sat_assuming_qf_auflra_nonlinear_must_not_return_sat_6077() {
    let input = r#"
        (set-logic QF_AUFLRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (> x 0.0))
        (assert (> y 0.0))
        (check-sat-assuming ((< (* x y) 0.0)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert!(
        outputs[0] == "unknown" || outputs[0] == "unsat",
        "QF_AUFLRA check-sat-assuming with nonlinear must not return false SAT — got: {}",
        outputs[0]
    );
}

/// #6077 audit: check_sat_internal under QF_LIA with nonlinear int must upgrade
/// to NIA solver. The guard at executor.rs:1590 upgrades to solve_nia().
///
/// This covers the check_sat path; the check_sat_assuming path (line 799) is
/// covered by test_check_sat_assuming_qf_lia_nonlinear_upgrade_6077.
#[test]
fn test_check_sat_qf_lia_nonlinear_must_not_return_sat_6077() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (> x 0))
        (assert (> y 0))
        (assert (< (* x y) 0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert!(
        outputs[0] == "unknown" || outputs[0] == "unsat",
        "QF_LIA with nonlinear check-sat must not return false SAT (#6077) — got: {}",
        outputs[0]
    );
}

// ========== LIRA/AUFLIRA nonlinear guard tests (#6085) ==========

/// #6085: check_sat_internal (regular check-sat) must detect nonlinear terms
/// under QF_LIRA and return Unknown instead of routing to the linear solver.
///
/// LIRA is mixed int+real, so we check has_nonlinear_int || has_nonlinear_real.
/// Formula: x > 0, x * x < 0 — contradictory (x² ≥ 0 always).
#[test]
fn test_check_sat_qf_lira_nonlinear_must_not_return_sat_6085() {
    let input = r#"
        (set-logic QF_LIRA)
        (declare-const x Int)
        (declare-const y Real)
        (assert (> x 0))
        (assert (> y 0.5))
        (assert (< (to_real (* x x)) 0.0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert!(
        outputs[0] == "unknown" || outputs[0] == "unsat",
        "QF_LIRA with nonlinear check-sat must not return false SAT (#6085) — got: {}",
        outputs[0]
    );
}

/// #6085: check_sat_internal must detect nonlinear terms under QF_AUFLIRA.
#[test]
fn test_check_sat_qf_auflira_nonlinear_must_not_return_sat_6085() {
    let input = r#"
        (set-logic QF_AUFLIRA)
        (declare-const x Int)
        (declare-const y Real)
        (declare-fun arr () (Array Int Real))
        (assert (> x 0))
        (assert (> y 0.5))
        (assert (< (to_real (* x x)) 0.0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert!(
        outputs[0] == "unknown" || outputs[0] == "unsat",
        "QF_AUFLIRA with nonlinear check-sat must not return false SAT (#6085) — got: {}",
        outputs[0]
    );
}

// ── Centralized nonlinear upgrade tests (#6086) ─────────────────────────

/// #6086: Centralized pre-dispatch nonlinear upgrade for quantified UFLIA.
/// Formula: x > 0, y > 0, x*y < 0 under UFLIA (quantified + UF + LIA).
/// Must not return false SAT — with_nonlinear upgrades Uflia→Ufnia.
#[test]
fn test_centralized_nonlinear_upgrade_uflia_6086() {
    let input = r#"
        (set-logic UFLIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (> x 0))
        (assert (> y 0))
        (assert (< (* x y) 0))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert!(
        outputs[0] == "unknown" || outputs[0] == "unsat",
        "UFLIA with nonlinear int must not return false SAT (#6086) — got: {}",
        outputs[0]
    );
}

/// #6086: Centralized pre-dispatch nonlinear upgrade for quantified UFLRA.
/// Formula: x > 0.0, y > 0.0, x*y < 0.0 under UFLRA.
/// Must not return false SAT — with_nonlinear upgrades Uflra→Ufnra.
#[test]
fn test_centralized_nonlinear_upgrade_uflra_6086() {
    let input = r#"
        (set-logic UFLRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (> x 0.0))
        (assert (> y 0.0))
        (assert (< (* x y) 0.0))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert!(
        outputs[0] == "unknown" || outputs[0] == "unsat",
        "UFLRA with nonlinear real must not return false SAT (#6086) — got: {}",
        outputs[0]
    );
}

/// #6086: Centralized pre-dispatch nonlinear upgrade for quantified AUFLIA.
/// with_nonlinear upgrades Auflia→Ufnia.
#[test]
fn test_centralized_nonlinear_upgrade_auflia_6086() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (> x 0))
        (assert (> y 0))
        (assert (< (* x y) 0))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert!(
        outputs[0] == "unknown" || outputs[0] == "unsat",
        "AUFLIA with nonlinear int must not return false SAT (#6086) — got: {}",
        outputs[0]
    );
}

/// #6086: Centralized pre-dispatch nonlinear upgrade for quantified LIA.
/// with_nonlinear upgrades Lia→Nia.
#[test]
fn test_centralized_nonlinear_upgrade_quantified_lia_6086() {
    let input = r#"
        (set-logic LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (> x 0))
        (assert (> y 0))
        (assert (< (* x y) 0))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert!(
        outputs[0] == "unknown" || outputs[0] == "unsat",
        "LIA with nonlinear int must not return false SAT (#6086) — got: {}",
        outputs[0]
    );
}

/// #6086: Centralized pre-dispatch nonlinear upgrade for quantified LIRA.
/// with_nonlinear upgrades Lira→Nira.
#[test]
fn test_centralized_nonlinear_upgrade_quantified_lira_6086() {
    let input = r#"
        (set-logic LIRA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (> x 0))
        (assert (> y 0))
        (assert (< (* x y) 0))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert!(
        outputs[0] == "unknown" || outputs[0] == "unsat",
        "LIRA with nonlinear int must not return false SAT (#6086) — got: {}",
        outputs[0]
    );
}

// ========== QF_UF EUF guard regression tests (#6498) ==========

#[test]
fn test_qf_uf_sat_not_degraded_to_unknown_6498() {
    // Pure QF_UF query: uninterpreted function, equality check.
    // Must return sat, not unknown — the EUF theory solver provides
    // independent verification of congruence closure consistency.
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun f (U) U)
        (declare-const a U)
        (declare-const b U)
        (assert (= (f a) b))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs[0], "sat",
        "QF_UF with EUF model must not degrade to unknown (#6498) — got: {}",
        outputs[0]
    );
}

#[test]
fn test_qf_uf_uninterpreted_fn_unconstrained_6498() {
    // Unconstrained UF function returning Bool — should be sat
    // (any interpretation of g works).
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun g (U) Bool)
        (declare-const x U)
        (assert (g x))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs[0], "sat",
        "Unconstrained UF function must return sat (#6498) — got: {}",
        outputs[0]
    );
}

#[test]
fn test_qf_uf_equality_coercion_6498() {
    // Equality between different UF applications — must return sat, not unknown.
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun f (U) U)
        (declare-fun g (U) U)
        (declare-const a U)
        (assert (= (f a) (g a)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs[0], "sat",
        "UF equality between different functions must return sat (#6498) — got: {}",
        outputs[0]
    );
}

// ========== Simplify Command Tests ==========
