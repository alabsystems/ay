// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end verdict regression for Z3's special-relations indexed identifiers
//! `(_ partial-order N)`, `(_ linear-order N)`, `(_ tree-order N)`, and
//! `(_ piecewise-linear-order N)`.
//!
//! These are the encoding Verus's prelude emits for its well-founded `height`
//! ordering (`height_le = (_ partial-order 0)`), so they sit on the hot path of
//! every Verus decreases/termination proof. Before this support ay rejected them
//! at elaboration (`unknown indexed identifier: partial-order`), and no Verus
//! file could even load.
//!
//! The frontend lowers `((_ partial-order N) a b)` to an application of a fresh
//! uninterpreted predicate and injects that predicate's order axioms. The tests
//! below pin both COMPLETENESS (the order properties are provable) and — just as
//! important — SOUNDNESS (a partial order is not forced to be total; distinct
//! indices are independent relations), so the axioms cannot silently over- or
//! under-constrain.

use ay_dpll::Executor;
use ay_frontend::parse;

fn verdict(smt: &str) -> String {
    let commands = parse(smt).expect("parse ok");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("exec ok")
        .into_iter()
        .find(|l| matches!(l.trim(), "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| "NORESULT".into())
}

// ---- partial order: reflexive + antisymmetric + transitive ----

#[test]
fn partial_order_is_reflexive() {
    // ¬R(a,a) contradicts reflexivity.
    assert_eq!(
        verdict(
            "(declare-sort H 0)(declare-const a H)\
             (assert (not ((_ partial-order 0) a a)))(check-sat)"
        ),
        "unsat"
    );
}

#[test]
fn partial_order_is_antisymmetric() {
    // R(a,b) ∧ R(b,a) ∧ a≠b contradicts antisymmetry.
    assert_eq!(
        verdict(
            "(declare-sort H 0)(declare-const a H)(declare-const b H)\
             (assert ((_ partial-order 0) a b))(assert ((_ partial-order 0) b a))\
             (assert (not (= a b)))(check-sat)"
        ),
        "unsat"
    );
}

#[test]
fn partial_order_is_transitive() {
    // R(a,b) ∧ R(b,c) ∧ ¬R(a,c) contradicts transitivity. This is Verus's actual
    // height obligation shape.
    assert_eq!(
        verdict(
            "(declare-sort H 0)(declare-const a H)(declare-const b H)(declare-const c H)\
             (assert ((_ partial-order 0) a b))(assert ((_ partial-order 0) b c))\
             (assert (not ((_ partial-order 0) a c)))(check-sat)"
        ),
        "unsat"
    );
}

// ---- soundness guards: the relation is NOT over-constrained ----

#[test]
fn partial_order_is_not_total() {
    // Two incomparable, distinct elements are consistent with a PARTIAL order.
    // If totality were wrongly asserted this would be a wrong `unsat`.
    assert_eq!(
        verdict(
            "(declare-sort H 0)(declare-const a H)(declare-const b H)\
             (assert (not ((_ partial-order 0) a b)))\
             (assert (not ((_ partial-order 0) b a)))\
             (assert (not (= a b)))(check-sat)"
        ),
        "sat"
    );
}

#[test]
fn a_single_edge_is_satisfiable() {
    // R(a,b) alone must be satisfiable — the axioms don't collapse the model.
    assert_eq!(
        verdict(
            "(declare-sort H 0)(declare-const a H)(declare-const b H)\
             (assert ((_ partial-order 0) a b))(check-sat)"
        ),
        "sat"
    );
}

#[test]
fn distinct_indices_are_independent_relations() {
    // R0(a,b) does not entail R1(a,b): different indices are different relations.
    assert_eq!(
        verdict(
            "(declare-sort H 0)(declare-const a H)(declare-const b H)\
             (assert ((_ partial-order 0) a b))\
             (assert (not ((_ partial-order 1) a b)))(check-sat)"
        ),
        "sat"
    );
}

// ---- linear order additionally imposes totality ----

#[test]
fn linear_order_is_total() {
    // Unlike a partial order, a linear order forces comparability, so two
    // incomparable distinct elements are UNSAT.
    assert_eq!(
        verdict(
            "(declare-sort H 0)(declare-const a H)(declare-const b H)\
             (assert (not ((_ linear-order 0) a b)))\
             (assert (not ((_ linear-order 0) b a)))\
             (assert (not (= a b)))(check-sat)"
        ),
        "unsat"
    );
}

// ---- the Verus height ordering shape: height_lt defined from height_le ----

#[test]
fn height_lt_defined_from_partial_order_height_le() {
    // Mirrors Verus's prelude: height_lt(x,y) := height_le(x,y) ∧ x≠y, where
    // height_le = (_ partial-order 0). From height_lt(a,b) and height_lt(b,c) we
    // must derive height_lt(a,c) (strict order is transitive + irreflexive).
    assert_eq!(
        verdict(
            "(declare-sort Height 0)\
             (declare-fun height_lt (Height Height) Bool)\
             (assert (forall ((x Height) (y Height)) \
                (= (height_lt x y) (and ((_ partial-order 0) x y) (not (= x y))))))\
             (declare-const a Height)(declare-const b Height)(declare-const c Height)\
             (assert (height_lt a b))(assert (height_lt b c))\
             (assert (not (height_lt a c)))(check-sat)"
        ),
        "unsat"
    );
}
