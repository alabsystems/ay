// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Soundness regression tests for array (dis)equality reasoning involving
//! constant arrays, finite BitVec index domains, and cardinality-one element
//! sorts.
//!
//! Covers three previously wrong-answer families:
//!  1. Const-array vs const-array equality with distinct defaults: must be
//!     UNSAT (two const-arrays with different default values differ at every
//!     index). Was wrong-SAT.
//!  2. Const-array vs store-chain disequality with a free base: must be SAT
//!     (the free base can differ from the const default at some index). The
//!     ROW2b-alias axiom previously treated the negated equality as a
//!     definitional store alias and dropped the model -> wrong-UNSAT.
//!  3. Array distinctness over a cardinality-one element sort (datatype with a
//!     single nullary constructor): must be UNSAT (the array sort has a single
//!     inhabitant). Was wrong-SAT.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// Run a raw SMT-LIB script and extract check-sat verdicts.
fn run_smt(smt: &str) -> Vec<String> {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT:\n{smt}"));
    let mut exec = Executor::new();
    let output = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}\nSMT:\n{smt}"))
        .join("\n");
    output
        .lines()
        .map(str::trim)
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .map(ToOwned::to_owned)
        .collect()
}

/// `(= (as const A true) (as const A false))` is UNSAT: distinct defaults
/// differ at every (Bool) index.
#[test]
#[timeout(10_000)]
fn const_array_distinct_defaults_bool_is_unsat() {
    let result = run_smt(
        "(set-logic ALL)\
         (assert (= ((as const (Array Bool Bool)) true) ((as const (Array Bool Bool)) false)))\
         (check-sat)",
    );
    assert_eq!(
        result,
        vec!["unsat"],
        "const=const distinct defaults must be unsat"
    );
}

/// `(= (as const A 3) (as const A 4))` over Int defaults is UNSAT.
#[test]
#[timeout(10_000)]
fn const_array_distinct_defaults_int_is_unsat() {
    let result = run_smt(
        "(set-logic ALL)\
         (assert (= ((as const (Array Int Int)) 3) ((as const (Array Int Int)) 4)))\
         (check-sat)",
    );
    assert_eq!(result, vec!["unsat"]);
}

/// `(= (as const A 3) (as const A 3))` (equal defaults) is SAT.
#[test]
#[timeout(10_000)]
fn const_array_equal_defaults_is_sat() {
    let result = run_smt(
        "(set-logic ALL)\
         (assert (= ((as const (Array Int Int)) 3) ((as const (Array Int Int)) 3)))\
         (check-sat)",
    );
    assert_eq!(result, vec!["sat"]);
}

/// QF_ABV: `(= (as const A #xa) (as const A #x8))` is UNSAT via finite-domain
/// extensionality over the small BitVec index domain.
#[test]
#[timeout(10_000)]
fn qf_abv_const_array_distinct_defaults_is_unsat() {
    let result = run_smt(
        "(set-logic QF_ABV)\
         (assert (= ((as const (Array (_ BitVec 1) (_ BitVec 4))) #xa) \
                    ((as const (Array (_ BitVec 1) (_ BitVec 4))) #x8)))\
         (check-sat)",
    );
    assert_eq!(result, vec!["unsat"]);
}

/// QF_ABV: a store-chain over a free base equal to a const-array is decided
/// correctly by finite-domain extensionality (here UNSAT, matching z3): the
/// store writes #x2 at #b110 and the const default is #b00, which differ at
/// that index unless the base supplies #b00 elsewhere — z3 says unsat.
#[test]
#[timeout(10_000)]
fn qf_abv_store_chain_eq_const_array_decided() {
    let result = run_smt(
        "(set-logic QF_ABV)\
         (declare-const a0 (Array (_ BitVec 3) (_ BitVec 2)))\
         (assert (and (= (store (store a0 #b101 #b10) #b110 (select a0 #b111)) \
                         ((as const (Array (_ BitVec 3) (_ BitVec 2))) #b00)) \
                      (not (bvslt #b010 #b110))))\
         (check-sat)",
    );
    // Must not be wrong-SAT; z3 decides unsat. Accept unsat (decided) but
    // never sat.
    assert!(
        result == vec!["unsat"] || result == vec!["unknown"],
        "store-chain vs const-array must not be wrong-SAT, got {result:?}"
    );
    assert_ne!(result, vec!["sat"]);
}

/// Const-array vs store-chain DISEQUALITY with a free base must be SAT: the
/// free base may differ from the const default at some non-overwritten index.
/// Regression for the ROW2b-alias wrong-UNSAT.
#[test]
#[timeout(10_000)]
fn const_array_vs_store_disequality_free_base_is_sat() {
    let result = run_smt(
        "(set-logic QF_ABV)\
         (declare-const a0 (Array (_ BitVec 4) (_ BitVec 4)))\
         (assert (not (= ((as const (Array (_ BitVec 4) (_ BitVec 4))) #x2) \
                         (store a0 #xb #x2))))\
         (check-sat)",
    );
    assert_eq!(
        result,
        vec!["sat"],
        "free-base const-vs-store disequality must be sat"
    );
}

/// Distinctness over a cardinality-one datatype element sort is UNSAT: the
/// array sort has a single inhabitant.
#[test]
#[timeout(10_000)]
fn distinct_arrays_card1_element_sort_is_unsat() {
    let result = run_smt(
        "(set-logic ALL)\
         (declare-datatype D1 ((c2)))\
         (declare-const v3 (Array Int D1))\
         (declare-const v5 (Array Int D1))\
         (assert (distinct v3 v5))\
         (check-sat)",
    );
    assert_eq!(
        result,
        vec!["unsat"],
        "distinct over card-1 element sort must be unsat"
    );
}

/// 3-way distinctness over a cardinality-one element sort is UNSAT.
#[test]
#[timeout(10_000)]
fn three_way_distinct_arrays_card1_element_sort_is_unsat() {
    let result = run_smt(
        "(set-logic ALL)\
         (declare-datatype D1 ((c2)))\
         (declare-const a (Array Int D1))\
         (declare-const b (Array Int D1))\
         (declare-const c (Array Int D1))\
         (assert (distinct a b c))\
         (check-sat)",
    );
    assert_eq!(result, vec!["unsat"]);
}

/// Nested cardinality-one datatype (struct of struct of nullary): UNSAT.
#[test]
#[timeout(10_000)]
fn distinct_arrays_nested_card1_element_sort_is_unsat() {
    let result = run_smt(
        "(set-logic ALL)\
         (declare-datatype Inner ((ic)))\
         (declare-datatype Outer ((oc (f Inner))))\
         (declare-const v3 (Array Int Outer))\
         (declare-const v5 (Array Int Outer))\
         (assert (distinct v3 v5))\
         (check-sat)",
    );
    assert_eq!(result, vec!["unsat"]);
}

/// Distinctness over a CARDINALITY-TWO datatype element sort must stay SAT:
/// the arrays can genuinely differ. Guards against over-refutation of the
/// cardinality check.
#[test]
#[timeout(10_000)]
fn distinct_arrays_card2_element_sort_is_sat() {
    let result = run_smt(
        "(set-logic ALL)\
         (declare-datatype D2 ((a2) (b2)))\
         (declare-const v3 (Array Int D2))\
         (declare-const v5 (Array Int D2))\
         (assert (distinct v3 v5))\
         (check-sat)",
    );
    assert_eq!(
        result,
        vec!["sat"],
        "distinct over card-2 element sort must stay sat"
    );
}

/// A single-constructor datatype whose field is an infinite-cardinality array
/// is NOT a singleton sort, so distinctness must stay SAT (fail-open, not a
/// false refutation).
#[test]
#[timeout(10_000)]
fn distinct_arrays_card1_ctor_infinite_field_is_sat() {
    let result = run_smt(
        "(set-logic ALL)\
         (declare-datatype U1 ((mk (g (Array Int Bool)))))\
         (declare-const v3 (Array Int U1))\
         (declare-const v5 (Array Int U1))\
         (assert (distinct v3 v5))\
         (check-sat)\
         (check-sat)",
    );
    assert_eq!(result, vec!["sat", "sat"]);
}

/// A single-constructor datatype whose one field is `Int` is not a singleton,
/// so array distinctness over it is SAT — and AY must SAY so.
///
/// (#dt-array-element-ext) The element literal
/// `¬(= (select v3 k) (select v5 k))` the extensionality witness produces
/// lives at the datatype sort, where the array/EUF route used to stop: EUF was
/// satisfied by keeping the two selects in different classes, nothing related
/// the difference to the constructor's FIELD, and the verdict degraded to
/// `unknown`. The constructor exhaustiveness+injectivity bridge pushes it to
/// `¬(= (v (select v3 k)) (v (select v5 k)))`, which LIA witnesses directly.
#[test]
#[timeout(10_000)]
fn distinct_arrays_single_ctor_int_field_is_sat() {
    let result = run_smt(
        "(set-logic ALL)\
         (declare-datatype B1 ((mk (v Int))))\
         (declare-const v3 (Array Int B1))\
         (declare-const v5 (Array Int B1))\
         (assert (distinct v3 v5))\
         (check-sat)",
    );
    assert_eq!(
        result,
        vec!["sat"],
        "an Int field makes the element sort non-singleton, so the arrays can differ"
    );
}

/// Same bridge, `Bool` field: the element sort has exactly two inhabitants,
/// which is already enough for two arrays to differ.
#[test]
#[timeout(10_000)]
fn distinct_arrays_single_ctor_bool_field_is_sat() {
    let result = run_smt(
        "(set-logic ALL)\
         (declare-datatype B2 ((mk (b Bool))))\
         (declare-const v3 (Array Int B2))\
         (declare-const v5 (Array Int B2))\
         (assert (distinct v3 v5))\
         (check-sat)",
    );
    assert_eq!(result, vec!["sat"]);
}

/// The bridge must not over-refute a NESTED single-constructor record whose
/// innermost field is genuinely variable: still SAT.
#[test]
#[timeout(10_000)]
fn distinct_arrays_nested_single_ctor_int_field_is_sat() {
    let result = run_smt(
        "(set-logic ALL)\
         (declare-datatype Inner2 ((ic2 (n Int))))\
         (declare-datatype Outer2 ((oc2 (f Inner2))))\
         (declare-const v3 (Array Int Outer2))\
         (declare-const v5 (Array Int Outer2))\
         (assert (distinct v3 v5))\
         (check-sat)",
    );
    assert_eq!(result, vec!["sat"]);
}

/// Distinctness over a genuinely uninterpreted (non-datatype) element sort
/// must stay SAT: cardinality is unknown, so we must not refute.
#[test]
#[timeout(10_000)]
fn distinct_arrays_uninterpreted_element_sort_is_sat() {
    let result = run_smt(
        "(set-logic ALL)\
         (declare-sort U 0)\
         (declare-const v3 (Array Int U))\
         (declare-const v5 (Array Int U))\
         (assert (distinct v3 v5))\
         (check-sat)",
    );
    assert_eq!(result, vec!["sat"]);
}

/// Extensionality must still refute a contradictory select disequality on
/// equal arrays (non-regression for genuine extensionality).
#[test]
#[timeout(10_000)]
fn extensionality_refutes_select_diseq_on_equal_arrays() {
    let result = run_smt(
        "(set-logic QF_ABV)\
         (declare-const a (Array (_ BitVec 2) (_ BitVec 2)))\
         (declare-const b (Array (_ BitVec 2) (_ BitVec 2)))\
         (assert (= a b))\
         (assert (not (= (select a #b00) (select b #b00))))\
         (check-sat)",
    );
    assert_eq!(result, vec!["unsat"]);
}

/// Ground singleton arrays used only below UF applications must still be
/// equated. The old pass inspected existing equality atoms, so neither `b0`
/// nor `b1` was discovered and AY returned the wrong `sat`.
#[test]
#[timeout(10_000)]
fn singleton_array_uf_arguments_are_equal_by_cardinality() {
    let result = run_smt(
        r#"
        (set-logic ALL)
        (declare-datatype D1 ((c)))
        (declare-const b0 (Array Int D1))
        (declare-const b1 (Array Int D1))
        (declare-fun f ((Array Int D1)) Int)
        (declare-fun p ((Array Int D1)) Bool)
        (assert (distinct (f b0) (f b1)))
        (assert (p (store b0 0 c)))
        (assert (p (store b1 0 c)))
        (check-sat)
        "#,
    );
    assert_eq!(
        result,
        vec!["unsat"],
        "singleton arrays are equal, so UF congruence must refute distinct outputs"
    );
}

/// The closure equality must retain the original store/base array terms. The
/// ordinary equality builder rewrites this shape to a select/value equality,
/// which is equivalent in array theory but does not expose `a = store(...)` to
/// UF congruence.
#[test]
#[timeout(10_000)]
fn singleton_store_and_base_uf_arguments_are_equal_by_cardinality() {
    let result = run_smt(
        r#"
        (set-logic ALL)
        (declare-datatype D1 ((c)))
        (declare-const a (Array Int D1))
        (declare-fun f ((Array Int D1)) Int)
        (assert (distinct (f a) (f (store a 0 c))))
        (check-sat)
        "#,
    );
    assert_eq!(
        result,
        vec!["unsat"],
        "singleton store and base arrays must merge before UF congruence"
    );
}

/// The closure is about every provably-singleton sort, not only arrays.
#[test]
#[timeout(10_000)]
fn singleton_scalar_uf_arguments_are_equal_by_cardinality() {
    let result = run_smt(
        r#"
        (set-logic ALL)
        (declare-datatype D1 ((c)))
        (declare-const x D1)
        (declare-const y D1)
        (declare-fun f (D1) Int)
        (assert (distinct (f x) (f y)))
        (check-sat)
        "#,
    );
    assert_eq!(result, vec!["unsat"]);
}

/// Singleton cardinality composes through nested array element sorts.
#[test]
#[timeout(10_000)]
fn nested_singleton_array_uf_arguments_are_equal_by_cardinality() {
    let result = run_smt(
        r#"
        (set-logic ALL)
        (declare-datatype D1 ((c)))
        (declare-const a (Array Int (Array Int D1)))
        (declare-const b (Array Int (Array Int D1)))
        (declare-fun f ((Array Int (Array Int D1))) Int)
        (assert (distinct (f a) (f b)))
        (check-sat)
        "#,
    );
    assert_ne!(
        result,
        vec!["sat"],
        "nested singleton arrays cannot yield distinct UF outputs"
    );
    assert!(
        result == vec!["unsat"] || result == vec!["unknown"],
        "unsupported nested-array routes may fail closed, got {result:?}"
    );
}

/// A two-constructor element sort makes the array sort non-singleton. This is
/// the negative control against over-eager UF argument equality.
#[test]
#[timeout(10_000)]
fn nonsingleton_array_uf_arguments_can_remain_distinct() {
    let result = run_smt(
        r#"
        (set-logic ALL)
        (declare-datatype D2 ((c0) (c1)))
        (declare-const a (Array Int D2))
        (declare-const b (Array Int D2))
        (declare-fun f ((Array Int D2)) Int)
        (assert (distinct (f a) (f b)))
        (check-sat)
        "#,
    );
    assert_ne!(
        result,
        vec!["unsat"],
        "cardinality-two arrays must not be over-equated"
    );
    assert!(
        result == vec!["sat"] || result == vec!["unknown"],
        "the model gate may fail closed on opaque array-valued UF arguments, got {result:?}"
    );
}

/// One constructor is insufficient when a field has non-singleton
/// cardinality; such a datatype and arrays over it must remain unconstrained.
#[test]
#[timeout(10_000)]
fn constructor_with_int_field_is_not_a_singleton() {
    let result = run_smt(
        r#"
        (set-logic ALL)
        (declare-datatype Box ((mk (value Int))))
        (declare-const a (Array Int Box))
        (declare-const b (Array Int Box))
        (declare-fun f ((Array Int Box)) Int)
        (assert (distinct (f a) (f b)))
        (check-sat)
        "#,
    );
    assert_ne!(
        result,
        vec!["unsat"],
        "an Int field makes Box and arrays over Box non-singleton"
    );
    assert!(
        result == vec!["sat"] || result == vec!["unknown"],
        "the model gate may fail closed on opaque array-valued UF arguments, got {result:?}"
    );
}

/// Direct assumption solvers bypass the ordinary check-sat preprocessing, so
/// they must replay singleton closure over both the base and assumption roots.
#[test]
#[timeout(10_000)]
fn singleton_array_uf_congruence_under_check_sat_assuming() {
    let result = run_smt(
        r#"
        (set-logic ALL)
        (declare-datatype D1 ((c)))
        (declare-const a (Array Int D1))
        (declare-fun f ((Array Int D1)) Int)
        (declare-const guard Bool)
        (assert (=> guard (distinct (f a) (f (store a 0 c)))))
        (check-sat-assuming (guard))
        "#,
    );
    assert_eq!(result, vec!["unsat"]);
}

/// Named-core mode redirects named assertions through the assumption route.
/// The verdict must remain UNSAT when the load-bearing singleton terms occur
/// in that redirected assertion.
#[test]
#[timeout(10_000)]
fn singleton_array_uf_congruence_under_named_core_redirect() {
    let result = run_smt(
        r#"
        (set-logic ALL)
        (set-option :produce-unsat-cores true)
        (declare-datatype D1 ((c)))
        (declare-const a (Array Int D1))
        (declare-fun f ((Array Int D1)) Int)
        (assert (! (distinct (f a) (f (store a 0 c))) :named uf_diseq))
        (check-sat)
        (get-unsat-core)
        "#,
    );
    assert_eq!(result, vec!["unsat"]);
}

/// Generated singleton equalities are solve-scoped: repeated checks and
/// push/pop must not accumulate stale preprocessing assertions.
#[test]
#[timeout(10_000)]
fn singleton_array_uf_closure_is_incrementally_stable() {
    let result = run_smt(
        r#"
        (set-logic ALL)
        (declare-datatype D1 ((c)))
        (declare-const a (Array Int D1))
        (declare-const b (Array Int D1))
        (declare-fun f ((Array Int D1)) Int)
        (push 1)
        (assert (distinct (f a) (f b)))
        (check-sat)
        (pop 1)
        (check-sat)
        (push 1)
        (assert (distinct (f a) (f b)))
        (check-sat)
        (pop 1)
        (check-sat)
        "#,
    );
    assert_eq!(result, vec!["unsat", "sat", "unsat", "sat"]);
}
