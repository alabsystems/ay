// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #7979: E-matching convergence on AUFLIA formulas.
//!
//! Two SAT-level behavioral changes (#7633: shrink_enabled=false in theory mode,
//! #7649: has_been_incremental=true disabling inprocessing) altered the CDCL
//! search trajectory, breaking E-matching convergence on AUFLIA formulas that
//! verification-consumer depends on (patterns from #7883-#7887).
//!
//! Fix: re-enable vivification in theory mode (safe: clause strengthening only,
//! no variable elimination or binary implication generation).
//!
//! These patterns exercise ground-pool E-matching, wrapping arithmetic,
//! loop-preservation invariants, array axiom instantiation, and nested
//! quantifier skolemization — all common in verification-consumer's verification conditions.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn expect_unsat(input: &str, label: &str) {
    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let last = outputs.last().expect("at least one output");
    assert_eq!(last.trim(), "unsat", "{label}: expected UNSAT");
}

/// Pattern 1: Ground-pool E-matching.
/// The universal `(=> (= x (some_uf)) (inv x))` with pattern `(inv x)` must
/// be instantiated with x := 42 (from the ground assertion `(= 42 (some_uf))`
/// and the negated goal `(not (inv 42))`). After instantiation, the formula
/// is propositionally unsatisfiable.
#[test]
#[timeout(30_000)]
fn test_ematching_ground_pool_7979() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-fun inv (Int) Bool)
        (declare-fun some_uf () Int)
        (assert (forall ((x Int)) (! (=> (= x (some_uf)) (inv x)) :pattern ((inv x)))))
        (assert (= 42 (some_uf)))
        (assert (not (inv 42)))
        (check-sat)
        "#,
        "ground-pool E-matching",
    );
}

/// Pattern 2: Wrapping arithmetic via universally quantified function.
/// `wrapping_add(a, b) = (a + b) mod 256` for all a, b.
/// With x=200, y=100: wrapping_add(200, 100) = 300 mod 256 = 44.
/// Asserting not(wrapping_add(200,100) = 44) should be UNSAT.
#[test]
#[timeout(30_000)]
fn test_ematching_wrapping_arithmetic_7979() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-fun wrapping_add (Int Int) Int)
        (assert (forall ((a Int) (b Int)) (! (= (wrapping_add a b) (mod (+ a b) 256)) :pattern ((wrapping_add a b)))))
        (declare-const x Int)
        (declare-const y Int)
        (assert (= x 200))
        (assert (= y 100))
        (assert (not (= (wrapping_add x y) 44)))
        (check-sat)
        "#,
        "wrapping arithmetic E-matching",
    );
}

/// Pattern 3: Loop preservation invariant.
/// `invariant(n) <=> (n >= 0)` for all n.
/// Pre: invariant(x_pre). Post: x_post = x_pre + 1. Goal: invariant(x_post).
/// Since x_pre >= 0 implies x_pre + 1 >= 0, this is UNSAT.
#[test]
#[timeout(30_000)]
fn test_ematching_loop_preservation_7979() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-const x_pre Int)
        (declare-const x_post Int)
        (declare-fun invariant (Int) Bool)
        (assert (forall ((n Int)) (! (= (invariant n) (>= n 0)) :pattern ((invariant n)))))
        (assert (invariant x_pre))
        (assert (= x_post (+ x_pre 1)))
        (assert (not (invariant x_post)))
        (check-sat)
        "#,
        "loop preservation E-matching",
    );
}

/// Pattern 4: Simple E-matching chain instantiation.
/// Universal: P(x) => P(f(x)) for all x.
/// Ground: P(a) is true.
/// Goal: not(P(f(a))) should be UNSAT after instantiating x := a.
#[test]
#[timeout(30_000)]
fn test_ematching_simple_chain_7979() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-sort S 0)
        (declare-fun P (S) Bool)
        (declare-fun f (S) S)
        (declare-const a S)
        (assert (forall ((x S)) (! (=> (P x) (P (f x))) :pattern ((P x)))))
        (assert (P a))
        (assert (not (P (f a))))
        (check-sat)
        "#,
        "simple E-matching chain",
    );
}

/// Pattern 5: Array store/select axiom with quantified invariant.
/// Heap invariant: all cells at indices in [0, len) are non-negative.
/// Store a non-negative value, verify invariant preserved.
#[test]
#[timeout(30_000)]
fn test_ematching_array_invariant_7979() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-const heap (Array Int Int))
        (declare-const heap2 (Array Int Int))
        (declare-fun valid (Int) Bool)
        (assert (forall ((i Int)) (! (=> (valid i) (>= (select heap i) 0)) :pattern ((select heap i)))))
        (declare-const idx Int)
        (assert (valid idx))
        (assert (= heap2 (store heap idx 42)))
        (assert (not (>= (select heap2 idx) 0)))
        (check-sat)
        "#,
        "array invariant E-matching",
    );
}
