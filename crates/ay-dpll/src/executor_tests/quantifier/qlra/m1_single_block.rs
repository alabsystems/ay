// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! M1: single ∀ / ¬∃ block in conjunctive position, complete on both bound
//! sides, published through the existing strict routes.
//!
//! The five depth-1 micro reproducers (p3, p7, p8, k7, k10) were all
//! `unknown` on the base binary (`quantifier-unhandled`); cvc5 1.3.0 and z3
//! answer every file here as stated.

use super::{assert_lane_sat, assert_lane_unsat};

#[test]
fn p3_upper_bounded_universal_is_refuted_by_the_lane() {
    assert_lane_unsat(
        "p3",
        "(set-logic LRA)(assert (forall ((x Real)) (< x 5)))(check-sat)",
    );
}

#[test]
fn p7_contradictory_ground_part_under_the_binder_is_refuted() {
    assert_lane_unsat(
        "p7",
        "(set-logic LRA)(declare-const c Real)\
         (assert (forall ((x Real)) (and (> c 0) (< c 0) (> x 0))))(check-sat)",
    );
}

#[test]
fn p8_universal_against_a_ground_sibling_is_refuted() {
    assert_lane_unsat(
        "p8",
        "(set-logic LRA)(declare-const c Real)(assert (> c 0))\
         (assert (forall ((x Real)) (and (< c 0) (> x 0))))(check-sat)",
    );
}

#[test]
fn k7_bounded_interval_universal_is_refuted() {
    assert_lane_unsat(
        "k7",
        "(set-logic LRA)(declare-const t Real)(declare-const y Real)(declare-const st Real)\
         (assert (forall ((s Real)) (or (> 0 s) (<= s 10))))(check-sat)",
    );
}

#[test]
fn k10_symbolic_upper_bound_universal_is_refuted() {
    assert_lane_unsat(
        "k10",
        "(set-logic LRA)(declare-const t Real)(declare-const y Real)(declare-const st Real)\
         (assert (forall ((s Real)) (=> (>= s 0) (<= s y))))(check-sat)",
    );
}

/// tptp NUM907=1: a three-binder `(not (exists ...))` over a Bool iff.
#[test]
fn num907_negated_exists_iff_is_refuted() {
    assert_lane_unsat(
        "NUM907=1",
        "(set-logic LRA)\
         (assert (not (exists ((?X Real) (?Y Real) (?Z Real)) \
           (= (= (+ ?X ?Y) ?Z) (and (= (- ?Z ?Y) ?X) (= (- ?Z ?X) ?Y))))))\
         (check-sat)",
    );
}

/// keymaera water_tank-node5019: the binder SHADOWS a declared constant of
/// the same name; the certificate's `forall_inst` must still strictly check.
#[test]
fn water_tank_node5019_shadowing_negated_exists_is_refuted() {
    assert_lane_unsat(
        "water_tank-node5019",
        "(set-logic LRA)\
         (declare-fun stuscore2dollarskuscore1 () Real)\
         (declare-fun t1uscore0dollarskuscore0 () Real)\
         (declare-fun yuscore2dollarskuscore1 () Real)\
         (declare-fun ts1uscore0 () Real)\
         (assert (not (exists ((ts1uscore0 Real)) (=> (and (and (and (and (and (=> (and \
           (<= 0 ts1uscore0) (<= ts1uscore0 t1uscore0dollarskuscore0)) \
           (<= (+ ts1uscore0 yuscore2dollarskuscore1) 10)) (>= t1uscore0dollarskuscore0 0)) \
           (< yuscore2dollarskuscore1 10)) (= stuscore2dollarskuscore1 0)) \
           (>= yuscore2dollarskuscore1 1)) (<= yuscore2dollarskuscore1 12)) \
           (or (or (= stuscore2dollarskuscore1 1) (= stuscore2dollarskuscore1 3)) \
           (>= (+ t1uscore0dollarskuscore0 yuscore2dollarskuscore1) 1))))))\
         (check-sat)",
    );
}

#[test]
fn excluded_middle_universal_is_satisfied_by_the_lane() {
    assert_lane_sat(
        "or-lt-ge",
        "(set-logic LRA)(declare-const c Real)\
         (assert (forall ((x Real)) (or (< x c) (>= x c))))(check-sat)",
    );
}

#[test]
fn guarded_shift_universal_is_satisfied_by_the_lane() {
    assert_lane_sat(
        "shift",
        "(set-logic LRA)(declare-const c Real)(assert (> c 0))\
         (assert (forall ((x Real)) (=> (> x 0) (> (+ x c) c))))(check-sat)",
    );
}

/// Two-sided: `∀x. x ≤ a ∨ x ≥ b` holds iff `b ≤ a`; the midpoint of the
/// open cell refutes it when `a < b`.
#[test]
fn open_cell_midpoint_refutes_and_closed_cell_satisfies() {
    assert_lane_unsat(
        "a07u",
        "(set-logic LRA)(declare-const a Real)(declare-const b Real)(assert (< a b))\
         (assert (forall ((x Real)) (or (<= x a) (>= x b))))(check-sat)",
    );
    assert_lane_sat(
        "a07s",
        "(set-logic LRA)(declare-const a Real)(declare-const b Real)(assert (<= b a))\
         (assert (forall ((x Real)) (or (<= x a) (>= x b))))(check-sat)",
    );
}

/// A Skolemized top-level `exists` sibling participates in the refutation.
#[test]
fn skolemized_exists_sibling_joins_the_refutation() {
    assert_lane_unsat(
        "a31",
        "(set-logic LRA)(declare-const a Real)(declare-const b Real)\
         (assert (exists ((z Real)) (and (> z a) (< z b))))\
         (assert (forall ((x Real)) (or (<= x a) (>= x b))))(check-sat)",
    );
}

/// Bool binders take their model value.
#[test]
fn bool_binder_universal_is_refuted() {
    assert_lane_unsat(
        "a12",
        "(set-logic LRA)(declare-const c Real)\
         (assert (forall ((q Bool) (x Real)) (=> q (> x c))))(check-sat)",
    );
}
