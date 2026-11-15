// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Verdict-level spec for the exact-quotient lemmas asserted next to a
//! symbolic-divisor `div`/`mod` (#nia-symbolic-division-exact, Verus fix queue
//! row D2). Ground truth for each fixture was checked with z3 4.12.5.

/// Refutable only through the quotient or remainder the operands' syntax fixes.
/// Each is UNSAT (z3 4.12.5).
const REFUTABLE: &[(&str, &str)] = &[
    (
        "div d d is 1",
        "(declare-const d Int)
         (assert (not (= d 0)))
         (assert (not (= (div d d) 1)))
         (check-sat)",
    ),
    (
        "mod d d is 0",
        "(declare-const d Int)
         (assert (not (= d 0)))
         (assert (not (= (mod d d) 0)))
         (check-sat)",
    ),
    (
        "mod of a multiple is 0",
        "(declare-const x Int) (declare-const y Int)
         (assert (> y 0))
         (assert (not (= (mod (* x y) y) 0)))
         (check-sat)",
    ),
    (
        "div of a constant multiple is the constant",
        "(declare-const y Int)
         (assert (< y 0))
         (assert (not (= (div (* 3 y) y) 3)))
         (check-sat)",
    ),
    (
        "div of zero is zero",
        "(declare-const y Int)
         (assert (not (= y 0)))
         (assert (not (= (div 0 y) 0)))
         (check-sat)",
    ),
    (
        "div d d through a quantified definition (Verus EucDiv)",
        "(declare-fun EucDiv (Int Int) Int)
         (assert (forall ((x Int) (y Int)) (! (= (EucDiv x y) (div x y)) :pattern ((EucDiv x y)))))
         (declare-const d Int)
         (assert (not (= d 0)))
         (assert (not (= (EucDiv d d) 1)))
         (check-sat)",
    ),
];

/// The same shapes where the divisor may be zero, and shapes the lemmas must
/// not touch. Each is SAT, so an `unsat` means a lemma fired where it does not
/// hold. z3 4.12.5 answers `sat` on all but the quantified one, where it times
/// out; that one has the model `d = 0`, `EucDiv(0, 0) = (div 0 0) = 0`.
const SATISFIABLE: &[(&str, &str)] = &[
    (
        "div d d with d possibly 0",
        "(declare-const d Int)
         (assert (not (= (div d d) 1)))
         (check-sat)",
    ),
    (
        "mod of a multiple with a possibly zero divisor",
        "(declare-const x Int) (declare-const y Int)
         (assert (not (= (mod (* x y) y) 0)))
         (check-sat)",
    ),
    (
        "div of zero with a possibly zero divisor",
        "(declare-const y Int)
         (assert (not (= (div 0 y) 0)))
         (check-sat)",
    ),
    (
        "div d d through a quantified definition with d possibly 0",
        "(declare-fun EucDiv (Int Int) Int)
         (assert (forall ((x Int) (y Int)) (! (= (EucDiv x y) (div x y)) :pattern ((EucDiv x y)))))
         (declare-const d Int)
         (assert (not (= (EucDiv d d) 1)))
         (check-sat)",
    ),
    (
        "div of a non-multiple",
        "(declare-const x Int) (declare-const y Int)
         (assert (> y 1)) (assert (= x (+ y 1)))
         (assert (= (mod x y) 1))
         (check-sat)",
    ),
];

#[test]
fn exact_quotient_lemmas_refute_quotient_facts() {
    for (name, smt) in REFUTABLE {
        let results = crate::common::solve_vec(smt);
        assert!(
            results.iter().any(|r| r == "unsat"),
            "{name}: the operands fix the quotient and remainder whenever the \
             divisor is nonzero; got {results:?}"
        );
    }
}

#[test]
fn exact_quotient_lemmas_never_refute_a_satisfiable_query() {
    for (name, smt) in SATISFIABLE {
        let results = crate::common::solve_vec(smt);
        assert!(
            !results.iter().any(|r| r == "unsat"),
            "WRONG ANSWER ({name}): this query is SATISFIABLE; got {results:?}"
        );
    }
}
