// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An Int binder's synthesized instantiation point must be an Int TERM.
//!
//! `atom_boundary_binder_bases` instantiates an `Int` binder at the value where
//! a comparison atom FLIPS. For a non-unit binder coefficient `c` that point is
//! not an integer, so the arm takes the nearest integer below it — its comment
//! says "via `div`", meaning SMT-LIB `div`, and calls the divisor "constant" so
//! the underspecified `div`-by-zero never arises.
//!
//! It called [`TermStore::mk_div`], which is the REALS `/`: it builds
//! `App("/", [Int, Int])` and interns it at `Sort::Real`. So the "integer
//! instantiation point" for an `Int` binder came out `Real`-sorted over `Int`
//! operands — a term whose declared sort contradicts its own arguments.
//!
//! `mk_div`'s `debug_assert!` says exactly that, and it FIRED: any debug build
//! — which is every test run in this repo — aborted the process on an ordinary
//! quantified LIA query whose binder carries a non-unit coefficient. Measured
//! identical on `origin/main` and on this branch, so pre-existing, not a
//! regression.
//!
//! The fix is `mk_intdiv` (SMT-LIB `div`, interned at `Sort::Int`), which is
//! what the comment always described. The assertion is untouched and still
//! protects the same invariant; see `TermStore::mk_div`'s doc comment for what
//! that invariant is and why it is a debug assertion.
//!
//! [`TermStore::mk_div`]: ay_core::TermStore::mk_div

use super::*;

/// The shape that tripped it, reduced.
///
/// * The binder must carry a NON-UNIT coefficient, so the flip point is
///   fractional and the `div` arm is taken at all: `3·q <= 7` flips between
///   `q = 2` and `q = 3`. With coefficient `1` or `-1` the arm above it
///   returns `-rest` / `rest` and never divides.
/// * The body must apply an UNINTERPRETED function to the binder
///   (`term_mentions_uninterpreted_of_bound_var`), or the synthesis lane that
///   calls `atom_boundary_binder_bases` skips the `forall` as already decided
///   by CEGQI.
///
/// TRUTH, established independently of the answer under test: take `c = 0`,
/// `f(0) = 0` and `f(n) = 1` for every `n != 0`. Then `(f c) = 0` holds, and
/// for each `q`: if `q != 0` the first disjunct `(f q) > 0` holds; if `q = 0`
/// the second holds, since `3·0 = 0 <= 7`. So the query is SATISFIABLE.
#[test]
fn non_unit_binder_coefficient_does_not_abort_the_process() {
    let commands = parse(
        r"
            (set-logic UFLIA)
            (declare-fun f (Int) Int)
            (declare-const c Int)
            (assert (= (f c) 0))
            (assert (forall ((q Int)) (or (> (f q) 0) (<= (* 3 q) 7))))
            (check-sat)
        ",
    )
    .unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    let verdict = outputs.last().cloned().unwrap_or_default();

    // Reaching this line at all is the regression: the run used to panic inside
    // `mk_div` before any verdict existed.
    assert_ne!(
        verdict, "unsat",
        "the query is satisfiable (c = 0, f(0) = 0, f(n) = 1 otherwise), so a \
         refutation would be a WRONG verdict, not a slower one"
    );
}

/// The same arm, reached with a NEGATIVE coefficient — the `(d0, -c)` half of
/// the branch, which divides a different numerator.
///
/// TRUTH: take `c = 0`, `f(0) = 0`, `f(n) = 1` otherwise. `(f c) = 0` holds,
/// and for each `q`: `q != 0` gives `(f q) > 0`; `q = 0` gives
/// `-2·0 = 0 >= -7`. SATISFIABLE.
#[test]
fn negative_non_unit_binder_coefficient_does_not_abort_the_process() {
    let commands = parse(
        r"
            (set-logic UFLIA)
            (declare-fun f (Int) Int)
            (declare-const c Int)
            (assert (= (f c) 0))
            (assert (forall ((q Int)) (or (> (f q) 0) (>= (* (- 2) q) (- 7)))))
            (check-sat)
        ",
    )
    .unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(outputs.last().cloned().unwrap_or_default(), "unsat");
}

/// NON-VACUITY for the two tests above: the same lane, with a UNIT coefficient,
/// never reaches the dividing arm and always worked. If the shapes above ever
/// stop reaching the arm, they stop measuring anything, and this row is the
/// control that says the difference between them is the coefficient and
/// nothing else.
///
/// TRUTH: `c = 0`, `f(0) = 0`, `f(n) = 1` otherwise; `q = 0` satisfies
/// `0 <= 7`. SATISFIABLE.
#[test]
fn unit_binder_coefficient_control() {
    let commands = parse(
        r"
            (set-logic UFLIA)
            (declare-fun f (Int) Int)
            (declare-const c Int)
            (assert (= (f c) 0))
            (assert (forall ((q Int)) (or (> (f q) 0) (<= q 7))))
            (check-sat)
        ",
    )
    .unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(outputs.last().cloned().unwrap_or_default(), "unsat");
}

/// And the constructor-level invariant the caller was violating, pinned
/// directly: SMT-LIB `div` over two `Int` terms is `Int`-sorted. A boundary
/// built with it is a term the Int binder can actually be instantiated at.
#[test]
fn intdiv_over_int_operands_is_int_sorted() {
    let mut terms = ay_core::TermStore::new();
    let x = terms.mk_var("x", ay_core::Sort::Int);
    let three = terms.mk_int(num_bigint::BigInt::from(3));
    let quotient = terms.mk_intdiv(x, three);
    assert_eq!(terms.sort(quotient), &ay_core::Sort::Int);
}
