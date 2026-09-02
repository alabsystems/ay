// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used)]

use super::*;
use crate::pdr::solver::test_helpers::solver_from_str;

const INT_MOD_THREE_LOOP: &str = r#"
(set-logic HORN)
(declare-fun inv (Int Int) Bool)
(assert (inv 0 0))
(assert
  (forall ((x Int) (r Int) (xp Int) (rp Int))
    (=> (and (inv x r)
             (= xp (+ x 1))
             (= rp (ite (= r 2) 0 (+ r 1))))
        (inv xp rp))))
(assert
  (forall ((x Int) (r Int))
    (=> (and (inv x r) (not (= (mod x 3) r))) false)))
(check-sat)
"#;

const BV_MOD_FOUR_LOOP: &str = r#"
(set-logic HORN)
(declare-fun inv ((_ BitVec 8) (_ BitVec 8)) Bool)
(assert (inv #x00 #x00))
(assert
  (forall ((x (_ BitVec 8)) (r (_ BitVec 8))
           (xp (_ BitVec 8)) (rp (_ BitVec 8)))
    (=> (and (inv x r)
             (= xp (bvadd x #x01))
             (= rp (ite (= r #x03) #x00 (bvadd r #x01))))
        (inv xp rp))))
(assert
  (forall ((x (_ BitVec 8)) (r (_ BitVec 8)))
    (=> (and (inv x r) (not (= (bvurem x #x04) r))) false)))
(check-sat)
"#;

const INT_MOD_256_RING: &str = r#"
(set-logic HORN)
(declare-fun ring (Int Int) Bool)
(assert (ring 0 0))
(assert
  (forall ((counter Int) (slot Int))
    (=> (ring counter slot)
        (ring (+ counter 1) (mod (+ counter 1) 256)))))
(check-sat)
"#;

#[test]
fn data_driven_moduli_include_guard_endpoint_successor() {
    let solver = solver_from_str(INT_MOD_THREE_LOOP);
    let pred = solver.problem.lookup_predicate("inv").unwrap();
    let mut nodes = MODULAR_EQUALITY_SCAN_NODE_BUDGET;

    let moduli = solver
        .data_driven_modular_equality_moduli(pred, &mut nodes)
        .expect("small transition scan must fit its structural budget");

    assert!(moduli.contains(&3), "guard r=2 must propose modulus 3");
    assert!(moduli.len() <= 8, "candidate set must remain bounded");
    assert!(moduli.windows(2).all(|pair| pair[0] < pair[1]));
}

#[test]
fn data_free_identity_loop_does_not_restore_a_static_modulus() {
    let solver = solver_from_str(
        r#"
(set-logic HORN)
(declare-fun inv (Int Int) Bool)
(assert (inv 0 0))
(assert (forall ((x Int) (r Int)) (=> (inv x r) (inv x r))))
(check-sat)
"#,
    );
    let pred = solver.problem.lookup_predicate("inv").unwrap();
    let mut nodes = MODULAR_EQUALITY_SCAN_NODE_BUDGET;

    assert_eq!(
        solver.data_driven_modular_equality_moduli(pred, &mut nodes),
        Some(Vec::new()),
        "absence of transition evidence must not silently fall back to modulus 2"
    );
}

#[test]
fn extracts_and_preserves_mod_256_ring_projection() {
    let mut solver = solver_from_str(INT_MOD_256_RING);
    let pred = solver.problem.lookup_predicate("ring").unwrap();
    let mut nodes = MODULAR_EQUALITY_SCAN_NODE_BUDGET;

    assert_eq!(
        solver.data_driven_modular_equality_moduli(pred, &mut nodes),
        Some(vec![256]),
        "the explicit ring projection must survive the bounded candidate scan"
    );
    assert!(
        solver.is_modular_equality_preserved_without_budget(pred, 0, 1, 256),
        "the large-modulus direct query must validate the ring projection"
    );
}

#[test]
fn discovers_integer_mod_three_equality() {
    let mut solver = solver_from_str(INT_MOD_THREE_LOOP);
    let pred = solver.problem.lookup_predicate("inv").unwrap();
    let vars = solver.canonical_vars(pred).unwrap().to_vec();
    let expected = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(vars[0].clone()), ChcExpr::int(3)),
        ChcExpr::var(vars[1].clone()),
    );

    solver.discover_modular_equality_invariants();

    assert!(
        solver.frames[1].contains_lemma(pred, &expected),
        "the preservation check should admit the data-derived mod-3 relation"
    );
}

#[test]
fn rejects_data_derived_modulus_when_transition_breaks_relation() {
    let mut solver = solver_from_str(
        r#"
(set-logic HORN)
(declare-fun inv (Int Int) Bool)
(assert (inv 0 0))
(assert
  (forall ((x Int) (r Int) (xp Int) (rp Int))
    (=> (and (inv x r)
             (= xp (+ x 1))
             (= rp (ite (= r 2) 0 (+ r 2))))
        (inv xp rp))))
(check-sat)
"#,
    );
    let pred = solver.problem.lookup_predicate("inv").unwrap();

    assert!(
        !solver.is_modular_equality_preserved_without_budget(pred, 0, 1, 3),
        "candidate extraction is only a hint; a breaking transition must reject it"
    );
}

#[test]
fn discovers_same_width_bv_mod_four_equality_with_typed_terms() {
    let mut solver = solver_from_str(BV_MOD_FOUR_LOOP);
    let pred = solver.problem.lookup_predicate("inv").unwrap();
    let vars = solver.canonical_vars(pred).unwrap().to_vec();
    let expected = ChcExpr::eq(
        ChcExpr::bv_urem(ChcExpr::var(vars[0].clone()), ChcExpr::BitVec(4, 8)),
        ChcExpr::var(vars[1].clone()),
    );

    solver.discover_modular_equality_invariants();

    assert!(
        solver.frames[1].contains_lemma(pred, &expected),
        "same-width BV pairs must use bvurem and width-matched literals"
    );
}

#[test]
fn bitvector_domain_rejects_width_mismatch_and_unrepresentable_modulus() {
    assert_eq!(
        ModularEqualityDomain::from_sorts(&ChcSort::BitVec(8), &ChcSort::BitVec(16)),
        None
    );
    let two_bit =
        ModularEqualityDomain::from_sorts(&ChcSort::BitVec(2), &ChcSort::BitVec(2)).unwrap();
    assert!(two_bit.supports_modulus(3));
    assert!(!two_bit.supports_modulus(4));

    let bv8 = ModularEqualityDomain::from_sorts(&ChcSort::BitVec(8), &ChcSort::BitVec(8)).unwrap();
    let bv16 =
        ModularEqualityDomain::from_sorts(&ChcSort::BitVec(16), &ChcSort::BitVec(16)).unwrap();
    assert!(!bv8.supports_modulus(256));
    assert!(bv16.supports_modulus(256));
}
