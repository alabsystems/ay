// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for #7979: post-CEGQI E-matching pass.
//!
//! Enumerative instantiation of triggerless quantifiers can introduce new ground
//! terms that trigger patterns in other quantifiers. Without a post-CEGQI
//! E-matching round, the triggered quantifier never sees the ground term and
//! the solver returns Unknown on a formula that is UNSAT.

use ntest::timeout;

/// Core #7979 pattern: triggerless quantifier produces ground term for triggered quantifier.
///
/// Chain:
///   1. `forall y. y > 5 => f(y) > 0` (triggerless, enumerative picks y=6)
///   2. `forall x. f(x) > 0 => g(x) = 1` (triggered on f(x))
///   3. `not(g(6) = 1)` (ground negation)
///
/// The ground term `6` from assertion `not(g(6) = 1)` seeds enumerative
/// instantiation of quantifier 1, producing `f(6) > 0`. The post-CEGQI
/// E-matching pass sees `f(6)` and instantiates quantifier 2 at x=6,
/// yielding `f(6) > 0 => g(6) = 1`. Combined with `f(6) > 0` and
/// `not(g(6) = 1)`, the solver derives UNSAT.
#[test]
#[timeout(60000)]
fn test_triggerless_produces_ground_for_triggered_unsat_7979() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (assert (forall ((x Int))
            (! (=> (> (f x) 0) (= (g x) 1))
               :pattern ((f x)))))
        (assert (forall ((y Int))
            (=> (> y 5) (> (f y) 0))))
        (assert (not (= (g 6) 1)))
        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "#7979: triggerless→triggered chain must derive UNSAT"
    );
}

/// Variant: triggerless enumerative instantiation feeds multi-round E-matching.
///
/// The triggerless quantifier 2 produces `P(a)` via enumerative instantiation
/// (a is the only ground term of sort S). Post-CEGQI E-matching then matches
/// quantifier 1's trigger `(P x)` against `P(a)`, producing `Q(f(a))`.
/// Combined with `not(Q(f(a)))`, this is UNSAT.
#[test]
#[timeout(60000)]
fn test_triggerless_enum_feeds_triggered_ematching_7979() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-sort S 0)
        (declare-fun P (S) Bool)
        (declare-fun Q (S) Bool)
        (declare-fun f (S) S)
        (declare-const a S)
        (assert (forall ((x S))
            (! (=> (P x) (Q (f x)))
               :pattern ((P x)))))
        (assert (forall ((y S)) (P y)))
        (assert (not (Q (f a))))
        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "#7979: triggerless enum + triggered E-matching chain must derive UNSAT"
    );
}

/// Variant: verification-consumer-style NonZero + wrapping arithmetic pattern.
///
/// A triggerless type invariant axiom produces `is_u32(x)` for ground `x`.
/// A triggered wrapping_add axiom uses `is_u32(a)` to derive the add result.
/// The negated postcondition contradicts the derived value.
#[test]
#[timeout(60000)]
fn test_nonzero_wrapping_pattern_7979() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun is_u32 (Int) Bool)
        (declare-fun wrapping_add (Int Int) Int)

        ; Triggerless type invariant: all declared Int constants satisfy is_u32
        (declare-const a Int)
        (declare-const b Int)
        (assert (forall ((x Int))
            (=> (and (>= x 0) (<= x 4294967295))
                (is_u32 x))))
        (assert (>= a 0))
        (assert (<= a 4294967295))
        (assert (>= b 0))
        (assert (<= b 4294967295))

        ; Triggered wrapping_add axiom: is_u32(a) AND is_u32(b) => wrapping_add(a,b) in range
        (assert (forall ((x Int) (y Int))
            (! (=> (and (is_u32 x) (is_u32 y)
                        (>= (+ x y) 0) (<= (+ x y) 4294967295))
                   (= (wrapping_add x y) (+ x y)))
               :pattern ((wrapping_add x y)))))

        ; Concrete values
        (assert (= a 100))
        (assert (= b 200))

        ; Should derive wrapping_add(a, b) = 300
        (assert (not (= (wrapping_add a b) 300)))
        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "#7979: NonZero/wrapping pattern must derive UNSAT"
    );
}

/// SAT case: post-CEGQI E-matching must not introduce false conflicts.
///
/// The triggerless quantifier produces ground instances but the formula
/// is satisfiable. The post-CEGQI pass must not over-instantiate.
///
/// Note: With quantifiers present, the solver may return Unknown because
/// model validation cannot verify universally quantified assertions.
/// The key invariant is that UNSAT is never returned for satisfiable formulas.
/// Both SAT and Unknown are acceptable here. (#7979)
#[test]
#[timeout(60000)]
fn test_post_cegqi_ematching_preserves_sat_7979() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (assert (forall ((x Int))
            (! (=> (> (f x) 0) (> (g x) 0))
               :pattern ((f x)))))
        (assert (forall ((y Int))
            (=> (> y 5) (> (f y) 0))))
        ; g(6) > 0 is consistent with the axioms (not negated)
        (assert (> (g 6) 0))
        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_ne!(
        outputs,
        vec!["unsat"],
        "#7979: SAT formula must never return UNSAT after post-CEGQI E-matching"
    );
}
