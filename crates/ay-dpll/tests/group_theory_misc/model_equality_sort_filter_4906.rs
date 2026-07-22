// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #4906: discover_model_equality must filter non-arithmetic terms.
//!
//! W4:1961 (29570455a) introduced `discover_model_equality` which panicked on
//! QF_AUFLIA problems when Array-sorted variables in `interface_arith_terms`
//! were paired with Int-sorted variables, creating `(= Int Array)` equalities
//! that panic in `mk_eq`.
//!
//! W4:1962 (e386ec20d) fixed the sort filter in `is_arith_evaluable` for `Var`.
//! W4:1966 (a848f3a84) extended model equality to Real-sorted terms (#4906).
//! These tests ensure the fix works end-to-end on real QF_AUFLIA/QF_AUFLIRA formulas.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// QF_AUFLIA: Store permutation with extra store — must be SAT.
/// Previously panicked with: `BUG: mk_eq expects same sort, got Int = Array(...)`
#[test]
#[timeout(30_000)]
fn test_auflia_model_equality_no_sort_panic_4906() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-fun base () (Array Int Int))
        (declare-fun v1 () Int)
        (declare-fun v2 () Int)
        (declare-fun v3 () Int)

        (declare-fun a1 () (Array Int Int))
        (declare-fun a2 () (Array Int Int))
        (declare-fun b1 () (Array Int Int))
        (declare-fun b2 () (Array Int Int))
        (declare-fun b3 () (Array Int Int))

        (assert (= a1 (store base 1 v1)))
        (assert (= a2 (store a1 2 v2)))
        (assert (= b1 (store base 2 v2)))
        (assert (= b2 (store b1 1 v1)))
        (assert (= b3 (store b2 3 v3)))
        (assert (not (= a2 b3)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execution should not panic on sort mismatch");

    assert_eq!(
        outputs[0], "sat",
        "Regression #4906: store permutation with extra store must be sat (got {})",
        outputs[0]
    );
}

/// Same as above but with symbolic (non-constant) indices.
#[test]
#[timeout(30_000)]
fn test_auflia_model_equality_symbolic_indices_no_sort_panic_4906() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-fun base () (Array Int Int))
        (declare-fun i1 () Int)
        (declare-fun i2 () Int)
        (declare-fun i3 () Int)
        (declare-fun v1 () Int)
        (declare-fun v2 () Int)
        (declare-fun v3 () Int)

        (declare-fun a1 () (Array Int Int))
        (declare-fun a2 () (Array Int Int))
        (declare-fun b1 () (Array Int Int))
        (declare-fun b2 () (Array Int Int))
        (declare-fun b3 () (Array Int Int))

        (assert (distinct i1 i2))
        (assert (distinct i1 i3))
        (assert (distinct i2 i3))
        (assert (= a1 (store base i1 v1)))
        (assert (= a2 (store a1 i2 v2)))
        (assert (= b1 (store base i2 v2)))
        (assert (= b2 (store b1 i1 v1)))
        (assert (= b3 (store b2 i3 v3)))
        (assert (not (= a2 b3)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execution should not panic on sort mismatch");

    assert_eq!(
        outputs[0], "sat",
        "Regression #4906: symbolic indices store permutation must be sat (got {})",
        outputs[0]
    );
}

/// Simple AUFLIA with UF and arrays — tests that model equality discovery
/// operates only on Int-sorted interface terms, not Array-sorted ones.
#[test]
#[timeout(30_000)]
fn test_auflia_uf_array_mix_no_sort_panic_4906() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-fun arr () (Array Int Int))
        (declare-fun x () Int)
        (declare-fun y () Int)

        (assert (= (select arr x) 1))
        (assert (= (select arr y) 1))
        (assert (distinct x y))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execution should not panic");

    assert_eq!(
        outputs[0], "sat",
        "distinct indices with same value in array should be sat (got {})",
        outputs[0]
    );
}

/// QF_UFLRA: Real-sorted terms must be handled by model equality discovery
/// without panicking. W4:1966 (a848f3a84) extended is_arith_evaluable and
/// register_interface_pair to accept Sort::Real alongside Sort::Int.
/// This test ensures Real-sorted UF terms go through model equality correctly.
#[test]
#[timeout(30_000)]
fn test_lra_model_equality_real_sort_no_panic_4906() {
    let input = r#"
        (set-logic QF_UFLRA)
        (declare-fun f (Real) Real)
        (declare-fun x () Real)
        (declare-fun y () Real)

        (assert (= (f x) 1.0))
        (assert (= (f y) 1.0))
        (assert (distinct x y))
        (assert (> x 0.0))
        (assert (> y 0.0))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execution should not panic on Real-sorted model equality");

    assert_eq!(
        outputs[0], "sat",
        "Regression #4906: Real-sorted UF with same value should be sat (got {})",
        outputs[0]
    );
}

/// QF_AUFLIRA: Mixed Int/Real terms in the same formula. Model equality
/// must handle both sorts without creating cross-sort equalities.
#[test]
#[timeout(30_000)]
fn test_lira_model_equality_mixed_sorts_no_panic_4906() {
    let input = r#"
        (set-logic QF_AUFLIRA)
        (declare-fun f (Int) Int)
        (declare-fun g (Real) Real)
        (declare-fun n () Int)
        (declare-fun m () Int)
        (declare-fun x () Real)
        (declare-fun y () Real)

        (assert (= (f n) 5))
        (assert (= (f m) 5))
        (assert (distinct n m))
        (assert (= (g x) 2.5))
        (assert (= (g y) 2.5))
        (assert (distinct x y))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execution should not panic on mixed Int/Real model equality");

    assert!(
        matches!(outputs[0].as_str(), "sat" | "unknown"),
        "Regression #4906: mixed Int/Real UF model equality must not be unsat, got {}",
        outputs[0]
    );
}

/// QF_AUFLIRA: Arrays with Real values and UF functions returning Real.
/// Tests that Array(Int,Real) terms are excluded from model equality
/// (only Int and Real scalars should participate).
#[test]
#[timeout(30_000)]
fn test_auflira_real_array_excluded_from_model_equality_4906() {
    let input = r#"
        (set-logic QF_AUFLIRA)
        (declare-fun arr () (Array Int Real))
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun r () Real)

        (assert (= x 0))
        (assert (= y 1))
        (assert (= (select arr x) 3.14))
        (assert (= (select arr y) 3.14))
        (assert (distinct x y))
        (assert (= r (+ (select arr x) (select arr y))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execution should not panic on AUFLIRA model equality");

    assert!(
        matches!(outputs[0].as_str(), "sat" | "unknown"),
        "Regression #4906: AUFLIRA with Real array values must not be unsat, got {}",
        outputs[0]
    );
}

/// QF_UFLRA: UNSAT formula that requires model-based theory combination (Nelson-Oppen)
/// on Real-sorted terms to discover the contradiction.
///
/// The formula says: f(x) != f(y), but the LRA constraints force x = y.
/// Without model equality propagating x = y from LRA to EUF, the EUF solver
/// cannot discover that f(x) = f(y) (by congruence, since x = y).
///
/// If Real-sort model equality is broken (is_arith_evaluable returns false for Real),
/// the solver would return "sat" or "unknown" instead of "unsat".
///
/// This is a hard-path test: model equality MUST activate and propagate the
/// Real-sorted equality for the solver to prove UNSAT.
#[test]
#[timeout(30_000)]
fn test_uflra_model_equality_real_required_for_unsat_4906() {
    let input = r#"
        (set-logic QF_UFLRA)
        (declare-fun f (Real) Real)
        (declare-fun x () Real)
        (declare-fun y () Real)

        ; LRA forces x = y: both are pinned to 3.5
        (assert (>= x 3.5))
        (assert (<= x 3.5))
        (assert (>= y 3.5))
        (assert (<= y 3.5))

        ; EUF says f(x) != f(y) — contradicts x = y via congruence
        (assert (distinct (f x) (f y)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execution should not panic");

    assert_eq!(
        outputs[0], "unsat",
        "#4906 hard-path: Real-sorted model equality required to propagate x=y to EUF"
    );
}

/// QF_UFLRA: UNSAT formula with 3 Real variables and 2 UF functions.
///
/// LRA forces x=y via pinning both to the same interval, but also requires
/// reasoning about a third variable z with a different UF application.
/// Specifically: x >= 1.0, x <= 1.0, y >= 1.0, y <= 1.0 forces x = y = 1.0.
/// Then f(x) != f(y) is a contradiction via congruence.
/// The extra g(z) term ensures the solver must correctly filter which
/// Real-sorted terms participate in model equality (z is independent).
#[test]
#[timeout(30_000)]
fn test_uflra_model_equality_real_multi_uf_unsat_4906() {
    let input = r#"
        (set-logic QF_UFLRA)
        (declare-fun f (Real) Real)
        (declare-fun g (Real) Real)
        (declare-fun x () Real)
        (declare-fun y () Real)
        (declare-fun z () Real)

        ; LRA forces x = y = 1.0
        (assert (>= x 1.0))
        (assert (<= x 1.0))
        (assert (>= y 1.0))
        (assert (<= y 1.0))

        ; z is independent but constrained
        (assert (> z 0.0))
        (assert (= (g z) 42.0))

        ; EUF says f(x) != f(y) — contradicts x = y via congruence
        (assert (distinct (f x) (f y)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execution should not panic");

    assert_eq!(
        outputs[0], "unsat",
        "#4906 hard-path: Real model equality with multiple UF functions"
    );
}
