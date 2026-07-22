// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for lazy, demand-driven DT case-splitting (iterative
//! deepening final-check).
//!
//! Before this fix, the eager DT axiom pass unrolled recursive selector
//! structure only to a hardcoded depth (`MAX_RECURSIVE_DT_DEPTH = 3`). Any
//! obligation whose (UN)SAT proof needed a constructor case-split deeper than 3
//! returned `unknown` (sound but incomplete), and adversarial shapes could even
//! be reported with a spurious `sat`. The lazy final-check in `solve_dt`
//! re-solves at a strictly larger depth on `unknown`, materializing the next
//! frontier of `sel_i(...)` subterms + their entailed (C)/(D) tautologies, until
//! a definitive verdict is reached. These tests pin the depth>3 behaviour that
//! the old depth-3 path got wrong.

use ntest::timeout;

/// SAT: `n` is forced distinct from `zero, succ(zero), ..., succ^4(zero)`.
///
/// A satisfying model exists (e.g. `n = succ^5(zero)`), but finding it requires
/// case-splitting the recursive `Nat` structure to depth 5 — one deeper than the
/// old depth-3 eager cap. The old path returned `unknown`; the lazy
/// final-check now reports the correct `sat`.
#[test]
#[timeout(60_000)]
fn test_qf_dt_deep_sat_exclude_shallow_values() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Nat ((zero) (succ (pred Nat))))
        (declare-fun n () Nat)
        (assert (not (= n zero)))
        (assert (not (= n (succ zero))))
        (assert (not (= n (succ (succ zero)))))
        (assert (not (= n (succ (succ (succ zero))))))
        (assert (not (= n (succ (succ (succ (succ zero)))))))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "n distinct from 0..4 is satisfiable (n = 5); requires depth-5 case split"
    );
}

/// SAT at depth 8: pushes the deepening loop well past the old cap.
#[test]
#[timeout(60_000)]
fn test_qf_dt_deep_sat_depth_eight() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Nat ((zero) (succ (pred Nat))))
        (declare-fun n () Nat)
        (assert (not (= n zero)))
        (assert (not (= n (succ zero))))
        (assert (not (= n (succ (succ zero)))))
        (assert (not (= n (succ (succ (succ zero))))))
        (assert (not (= n (succ (succ (succ (succ zero)))))))
        (assert (not (= n (succ (succ (succ (succ (succ zero))))))))
        (assert (not (= n (succ (succ (succ (succ (succ (succ zero)))))))))
        (assert (not (= n (succ (succ (succ (succ (succ (succ (succ zero))))))))))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "n distinct from 0..7 is satisfiable (n = 8); requires depth-8 case split"
    );
}

/// UNSAT at depth 5: `n` is pinned to `succ^5(zero)` by a tester chain, then
/// asserted unequal to that concrete value. The contradiction needs the
/// constructor (C) axiom to reconstruct the structure five levels deep — past
/// the old depth-3 cap.
#[test]
#[timeout(60_000)]
fn test_qf_dt_deep_unsat_tester_chain_depth_five() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Nat ((zero) (succ (pred Nat))))
        (declare-fun n () Nat)
        (assert (is-succ n))
        (assert (is-succ (pred n)))
        (assert (is-succ (pred (pred n))))
        (assert (is-succ (pred (pred (pred n)))))
        (assert (is-succ (pred (pred (pred (pred n))))))
        (assert (is-zero (pred (pred (pred (pred (pred n)))))))
        (assert (not (= n (succ (succ (succ (succ (succ zero))))))))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "tester chain pins n = succ^5(zero); asserting n != that value is unsat"
    );
}

/// UNSAT pigeonhole at depth 4: five `Nat` variables each bounded to one of the
/// four values `{0,1,2,3}` (via a depth-4 `is-zero` disjunction over the pred
/// chain) and required pairwise distinct. Five values cannot fit four slots, so
/// it is unsat — but only a solver that case-splits the bounded structure to
/// depth 4 sees it.
#[test]
#[timeout(120_000)]
fn test_qf_dt_deep_unsat_bounded_pigeonhole() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Nat ((zero) (succ (pred Nat))))
        (declare-fun a () Nat)
        (declare-fun b () Nat)
        (declare-fun c () Nat)
        (declare-fun d () Nat)
        (declare-fun e () Nat)
        (assert (or (is-zero a) (is-zero (pred a)) (is-zero (pred (pred a))) (is-zero (pred (pred (pred a))))))
        (assert (or (is-zero b) (is-zero (pred b)) (is-zero (pred (pred b))) (is-zero (pred (pred (pred b))))))
        (assert (or (is-zero c) (is-zero (pred c)) (is-zero (pred (pred c))) (is-zero (pred (pred (pred c))))))
        (assert (or (is-zero d) (is-zero (pred d)) (is-zero (pred (pred d))) (is-zero (pred (pred (pred d))))))
        (assert (or (is-zero e) (is-zero (pred e)) (is-zero (pred (pred e))) (is-zero (pred (pred (pred e))))))
        (assert (distinct a b c d e))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "5 nats bounded to 4 values cannot be pairwise distinct (pigeonhole)"
    );
}

/// Termination guard: an unconstrained recursive `Nat` with only `is-succ n`
/// must terminate at the structural fixpoint with `sat` (model `n = succ(zero)`),
/// never loop forever on the genuinely-infinite recursive shape.
#[test]
#[timeout(30_000)]
fn test_qf_dt_unconstrained_recursive_terminates_sat() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Nat ((zero) (succ (pred Nat))))
        (declare-fun n () Nat)
        (assert (is-succ n))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "is-succ(n) is satisfiable (n = succ(zero)); deepening must terminate"
    );
}
