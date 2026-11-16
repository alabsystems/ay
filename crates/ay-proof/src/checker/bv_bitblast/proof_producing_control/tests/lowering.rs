// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn exact_lowered_expression_and_every_poll_match_the_source() {
    let (terms, equality, expected) = raw_identity();
    assert_every_lowering_poll(&terms, &[equality], &expected);
}

#[test]
fn full_cancellation_preserves_source_and_every_lowering_poll() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("cancelled-source", Sort::bitvec(9));
    let zero = terms.mk_bitvec(0.into(), 9);
    let sum = terms.mk_app(Symbol::named("bvadd"), [x, zero], Sort::bitvec(9));
    let equality = terms.mk_app(Symbol::named("="), [sum, x], Sort::Bool);
    let reading = terms.bv_offset_equality(sum, x).unwrap();
    assert_eq!(reading.minuend, x);
    assert_eq!(reading.subtrahend, x);
    let leaf = BvExpr::leaf(&format!("proof_bv_{}", x.index()), 9);
    let expected = BvExpr::eq(leaf.clone(), leaf);
    assert_every_lowering_poll(&terms, &[equality], &expected);
}

#[test]
fn shared_dag_clones_and_nary_combination_keep_control() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("shared-wide", Sort::bitvec(9));
    let mut term = terms.mk_app(Symbol::named("bvmul"), [x, x], Sort::bitvec(9));
    let leaf = BvExpr::leaf(&format!("proof_bv_{}", x.index()), 9);
    let mut expected = BvExpr::mul(leaf.clone(), leaf);
    for _ in 0..3 {
        term = terms.mk_app(Symbol::named("bvadd"), [term, term], Sort::bitvec(9));
        expected = BvExpr::add(expected.clone(), expected);
    }
    let equality = terms.mk_app(Symbol::named("="), [term, term], Sort::Bool);
    let expected = BvExpr::eq(expected.clone(), expected);
    let conjunction = terms.mk_app(Symbol::named("and"), [equality; 3], Sort::Bool);
    let expected = BvExpr::and(BvExpr::and(expected.clone(), expected.clone()), expected);
    assert_every_lowering_poll(&terms, &[conjunction], &expected);
}

#[test]
fn finite_array_counts_and_cell_walks_match_the_compatibility_route() {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::Bool, Sort::bitvec(2));
    let zero = terms.mk_bitvec(0.into(), 2);
    let one = terms.mk_bitvec(1.into(), 2);
    let index = terms.mk_var("array-index", Sort::Bool);
    let constant = terms.mk_app(Symbol::named("const-array"), [zero], sort.clone());
    let stored = terms.mk_app(Symbol::named("store"), [constant, index, one], sort.clone());
    let selected = terms.mk_app(Symbol::named("select"), [stored, index], Sort::bitvec(2));
    let equality = terms.mk_app(Symbol::named("="), [selected, one], Sort::Bool);
    let array_ite = terms.mk_ite_raw(index, stored, constant);
    let array_eq = terms.mk_app(Symbol::named("="), [array_ite, stored], Sort::Bool);
    for root in [equality, array_eq] {
        let mut compatibility = ProofProducingLowerer::new(&terms, deadline());
        let expected = compatibility.lower_bool(root).unwrap();
        assert!(compatibility.used_exact_finite_arrays);
        assert_every_lowering_poll(&terms, &[root], &expected);
    }
}

#[test]
fn lowerer_refusal_and_caught_callback_panic_cannot_resurrect_the_attempt() {
    use std::panic::{catch_unwind, AssertUnwindSafe};
    let (terms, root, _) = raw_identity();
    for panics in [false, true] {
        let mut calls = 0;
        let mut callback = || {
            calls += 1;
            assert!(!panics, "injected lowering callback panic");
            false
        };
        let mut lowerer = ProofProducingLowerer::new(&terms, deadline());
        lowerer.keep_going = Some(&mut callback);
        if panics {
            assert!(catch_unwind(AssertUnwindSafe(|| lowerer.lower_bool(root))).is_err());
        } else {
            assert!(lowerer.lower_bool(root).is_err());
        }
        assert!(lowerer.cancelled);
        assert!(lowerer.lower_bool(root).is_err());
        assert!(lowerer.memo.is_empty());
        drop(lowerer);
        assert_eq!(calls, 1);
    }
}

#[test]
fn unsupported_and_expired_lowering_keep_their_ordinary_diagnostics() {
    let mut terms = TermStore::new();
    let unsupported = terms.mk_app(Symbol::named("not-a-bv-operator"), [], Sort::Bool);
    let expected = "unsupported Bool/BV predicate `not-a-bv-operator`";
    assert_eq!(
        lower_clause(&terms, &[unsupported], deadline(), false, &mut || true),
        Err(Failure::Rejected(expected.to_owned()))
    );
    assert_eq!(
        lower_clause(&terms, &[unsupported], deadline(), false, &mut || false),
        Err(Failure::Cancelled)
    );
    assert_eq!(
        lower_clause(&terms, &[unsupported], Instant::now(), false, &mut || true),
        Err(Failure::Rejected(
            "proof-producing lowering deadline exceeded".to_owned()
        ))
    );
}
