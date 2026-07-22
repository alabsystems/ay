// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression test for issue #3041: AUFLIA solver non-determinism.
//!
//! The AUFLIA solver returned Unsat for a satisfiable formula ~60% of the time
//! due to non-deterministic HashMap iteration order in hashbrown (random seeds
//! per process). The fix sorts collected vectors from HashMap/HashSet iterations
//! in EUF's rebuild_closure(), check(), explain(), and Nelson-Oppen interface
//! term evaluation.

use ntest::timeout;

/// #3041: AUFLIA formula with quantifier instantiation must produce deterministic results.
///
/// This formula uses forall quantifiers with explicit :pattern triggers that have
/// matching ground terms (f(a), f(b)), ensuring E-matching instantiation occurs.
/// Before the fix, hashbrown's random hash seeds caused non-deterministic iteration
/// of EUF's `assigns` HashMap in `rebuild_closure()`, leading to different union-find
/// representative assignments, different congruence closure results, and spurious
/// UNSAT conclusions.
#[test]
#[timeout(60000)]
fn test_auflia_determinism_unsat_3041() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (declare-const b Int)

        ; f(x) = x + 1 for all x (with trigger pattern)
        (assert (forall ((x Int)) (! (= (f x) (+ x 1)) :pattern ((f x)))))

        ; a and b are distinct
        (assert (not (= a b)))

        ; a = 5, so f(a) = 6
        (assert (= a 5))
        ; b = 6, so f(b) = 7
        (assert (= b 6))

        ; f(a) = b (6 = 6, true)
        (assert (= (f a) b))

        ; f(b) != f(a) + 1 (7 != 7, false — this is unsat)
        (assert (not (= (f b) (+ (f a) 1))))

        (check-sat)
    "#;

    // Run 10 times to catch non-determinism.
    // Before the fix, different hash seeds in each run could cause
    // different results from the same formula.
    for i in 0..10 {
        let outputs = crate::common::solve_vec(smt);
        assert_eq!(
            outputs,
            vec!["unsat"],
            "Run {i}: expected unsat but got {outputs:?}"
        );
    }
}

/// #3041: EUF congruence closure must be deterministic with multiple equalities.
///
/// This tests the QF_UFLIA path (no quantifiers, same EUF+LIA theory combination)
/// with multiple equality assertions that exercise the congruence closure. The
/// non-deterministic iteration of `assigns` in `rebuild_closure()` caused different
/// union orders and different congruence discoveries.
#[test]
#[timeout(60000)]
fn test_euf_lia_congruence_determinism_3041() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)

        ; a = b, so by congruence f(a) = f(b) and g(a) = g(b)
        (assert (= a b))

        ; f(a) = c + 1
        (assert (= (f a) (+ c 1)))

        ; f(b) != c + 1 (contradicts f(a) = f(b) from congruence and f(a) = c + 1)
        (assert (not (= (f b) (+ c 1))))

        (check-sat)
    "#;

    for i in 0..10 {
        let outputs = crate::common::solve_vec(smt);
        assert_eq!(
            outputs,
            vec!["unsat"],
            "Run {i}: expected unsat but got {outputs:?}"
        );
    }
}

/// #3041: Nelson-Oppen interface terms must be processed deterministically.
///
/// This tests the congruence closure in the Nelson-Oppen loop with multiple
/// UF+LIA equalities. The non-deterministic iteration of `assigns` HashMap
/// caused different union orders and different congruence discoveries.
#[test]
#[timeout(60000)]
fn test_nelson_oppen_interface_determinism_3041() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)

        ; a = b = c (transitive equality chain)
        (assert (= a b))
        (assert (= b c))

        ; f(a) = g(b) (connects f and g through a = b)
        (assert (= (f a) (g b)))

        ; f(c) != g(a) — but c = b = a, so f(c) = f(a) = g(b) = g(a)
        (assert (not (= (f c) (g a))))

        (check-sat)
    "#;

    for i in 0..10 {
        let outputs = crate::common::solve_vec(smt);
        assert_eq!(
            outputs,
            vec!["unsat"],
            "Run {i}: expected unsat but got {outputs:?}"
        );
    }
}
