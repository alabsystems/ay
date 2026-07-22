// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Non-convex UFLIA/AUFLIA correctness tests (#4906).
//!
//! These problems involve non-convex theory combinations where the solver
//! must correctly handle disjunctive constraints + UF congruence. On these
//! specific instances, CDCL case splitting on the disjunctions provides
//! enough information for EUF congruence to derive the result — so these
//! tests validate the overall UFLIA/AUFLIA pipeline correctness, not
//! specifically the `discover_model_equality` phase-hint mechanism.
//!
//! True model-equality-requiring problems need LIA to fix variable values
//! via bounds (not disjunctions), where the equality is implicit in the
//! model but not expressible as a CDCL clause. Such tests are harder to
//! construct because the interface bridge's `evaluate_and_propagate` also
//! handles constant-matching cases.
//!
//! Reference: Z3 smt_context.cpp:4576-4632 (assume_eq + try_true_first).

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// Non-convex UNSAT: f(x) != f(y), x in {0,1}, y in {0,1}, f(0)=f(1).
///
/// CDCL case-splits on the disjunctions, binding x and y to constants.
/// EUF congruence then derives f(x)=f(0) or f(x)=f(1), and the
/// asserted f(0)=f(1) forces f(x)=f(y) in all branches.
#[test]
#[timeout(30_000)]
fn test_uflia_nonconvex_function_collapse_unsat_4906() {
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun x () Int)
        (declare-fun y () Int)

        ; x and y are in {0, 1}
        (assert (or (= x 0) (= x 1)))
        (assert (or (= y 0) (= y 1)))

        ; f(0) = f(1) — collapses f on the relevant domain
        (assert (= (f 0) (f 1)))

        ; But f(x) != f(y) — contradicts the collapse
        (assert (not (= (f x) (f y))))

        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // The only valid answers are "unsat" or "unknown" (if the solver gives up).
    // "sat" would be a soundness bug.
    assert_ne!(
        outputs[0], "sat",
        "BUG: non-convex UFLIA problem must not return sat — f(0)=f(1) forces f(x)=f(y) for x,y in {{0,1}}"
    );
}

/// Simpler non-convex example: x in {0,1}, y in {0,1}, f(x) = 5, f(y) = 5,
/// but x != y and f is injective on {0,1} (f(0) != f(1)).
///
/// This is UNSAT: f(x)=5, f(y)=5 implies f(x)=f(y), but f(0)!=f(1) and
/// x,y in {0,1} with x!=y means {x,y}={0,1}, so f(0)=f(1). Contradiction.
#[test]
#[timeout(30_000)]
fn test_uflia_nonconvex_injective_contradiction_unsat_4906() {
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun x () Int)
        (declare-fun y () Int)

        (assert (or (= x 0) (= x 1)))
        (assert (or (= y 0) (= y 1)))
        (assert (not (= x y)))

        ; f(x) and f(y) both equal 5
        (assert (= (f x) 5))
        (assert (= (f y) 5))

        ; But f is injective on {0,1}
        (assert (not (= (f 0) (f 1))))

        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_ne!(
        outputs[0], "sat",
        "BUG: injective f with equal values on domain {{0,1}} must not return sat"
    );
}

/// Non-convex SAT case: x in {0,1,2}, y in {0,1,2}, f(x)!=f(y), f is
/// injective. This is SAT when x != y (e.g., x=0, y=1).
#[test]
#[timeout(30_000)]
fn test_uflia_nonconvex_injective_sat_4906() {
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun x () Int)
        (declare-fun y () Int)

        (assert (>= x 0))
        (assert (<= x 2))
        (assert (>= y 0))
        (assert (<= y 2))
        (assert (not (= x y)))

        ; f is injective on {0,1,2}
        (assert (not (= (f 0) (f 1))))
        (assert (not (= (f 0) (f 2))))
        (assert (not (= (f 1) (f 2))))

        ; f(x) != f(y)
        (assert (not (= (f x) (f y))))

        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs[0], "sat",
        "Injective f with distinct x,y in {{0,1,2}} and f(x)!=f(y) should be sat"
    );
}

/// Non-convex AUFLIA: array-index model equality. Two array accesses at
/// indices that must be equal by LIA, with a UF constraint that connects them.
#[test]
#[timeout(30_000)]
fn test_auflia_nonconvex_index_equality_unsat_4906() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-fun arr () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun j () Int)

        ; i and j are both in {0, 1}
        (assert (or (= i 0) (= i 1)))
        (assert (or (= j 0) (= j 1)))

        ; arr[0] = arr[1] (same value at both indices)
        (assert (= (select arr 0) (select arr 1)))

        ; But arr[i] != arr[j]
        (assert (not (= (select arr i) (select arr j))))

        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_ne!(
        outputs[0], "sat",
        "BUG: arr[0]=arr[1] with i,j in {{0,1}} means arr[i]=arr[j]"
    );
}
