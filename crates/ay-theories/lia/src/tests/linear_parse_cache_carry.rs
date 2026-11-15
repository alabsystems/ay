// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Carrying the term-level parse caches from one `LiaSolver` to a later one
//! (#lazy-auflia-persistent-structure): the lazy AUFLIA split loop builds a
//! fresh solver every round and re-parsed every atom's term DAG each time.
//!
//! A carried entry must answer exactly as a cold parse would, and an entry
//! parsed from a store that has since been rolled back must never be served:
//! its `TermId` can name a different term after the rollback.

use std::sync::Arc;

use super::*;
use crate::linear_cache::CachedLinear;
use crate::types::LinearCoeffs;
use ay_core::term::Symbol;
use num_rational::BigRational;

fn raw(terms: &mut TermStore, op: &str, args: [TermId; 2]) -> TermId {
    terms.mk_app(Symbol::named(op), args, Sort::Int)
}

fn sorted_coeffs(coeffs: &LinearCoeffs) -> (Vec<(TermId, BigRational)>, BigRational) {
    let mut vars: Vec<(TermId, BigRational)> = coeffs
        .vars
        .iter()
        .map(|(term, coeff)| (*term, coeff.clone()))
        .collect();
    vars.sort_by_key(|(term, _)| term.0);
    (vars, coeffs.constant.clone())
}

fn assert_same_linear(warm: &CachedLinear, cold: &CachedLinear) {
    assert_eq!(warm.coeffs, cold.coeffs);
    assert_eq!(warm.constant, cold.constant);
    assert_eq!(warm.gcd, cold.gcd);
    assert_eq!(warm.gcd_divides, cold.gcd_divides);
    assert_eq!(warm.modular_candidates, cold.modular_candidates);
}

#[test]
fn carried_parse_caches_answer_exactly_as_a_cold_solver() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let four = terms.mk_int(BigInt::from(4));
    let seven = terms.mk_int(BigInt::from(7));
    let two_x = raw(&mut terms, "*", [two, x]);
    let four_y = raw(&mut terms, "*", [four, y]);
    let sum = raw(&mut terms, "+", [two_x, four_y]);
    let shifted = raw(&mut terms, "-", [sum, x]);

    let source = LiaSolver::new(&terms);
    let built = source.cached_linear(sum, seven);
    let _ = source.term_to_linear_coeffs(shifted);
    let carry = source
        .export_linear_parse_cache()
        .expect("the source parsed entries to carry");
    assert!(
        source.linear_cache.borrow().is_empty() && source.affine_cache.borrow().is_empty(),
        "export moves the entries out of the source"
    );

    let mut warm = LiaSolver::new(&terms);
    warm.import_linear_parse_cache(carry);
    assert!(warm.linear_cache.borrow().contains_key(&(sum, seven)));
    assert!(warm.affine_cache.borrow().contains_key(&shifted));

    let cold = LiaSolver::new(&terms);
    let hit = warm.cached_linear(sum, seven);
    assert!(
        Arc::ptr_eq(&built, &hit),
        "served from the carry, not re-parsed"
    );
    assert_same_linear(&hit, &cold.cached_linear(sum, seven));
    // 2x + 4y = 7 has no integer solution: the carried GCD verdict is the
    // cold one.
    assert!(!hit.gcd_divides);
    assert_eq!(
        sorted_coeffs(&warm.term_to_linear_coeffs(shifted)),
        sorted_coeffs(&cold.term_to_linear_coeffs(shifted))
    );
}

#[test]
fn carry_is_accepted_after_append_only_growth() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let x_plus_y = raw(&mut terms, "+", [x, y]);
    let carry = {
        let source = LiaSolver::new(&terms);
        let _ = source.cached_linear(x_plus_y, five);
        source.export_linear_parse_cache().expect("parsed")
    };

    // A later refinement round appends split atoms; every carried id still
    // names the same term.
    let z = terms.mk_var("z", Sort::Int);
    let _later = raw(&mut terms, "+", [x_plus_y, z]);

    let mut warm = LiaSolver::new(&terms);
    warm.import_linear_parse_cache(carry);
    assert!(warm.linear_cache.borrow().contains_key(&(x_plus_y, five)));
}

/// Negative twin: a rollback reclaims the suffix and the next term re-mints
/// the same `TermId` with a different meaning. The carried entry for the old
/// meaning must be dropped, and the solver must parse the new term.
#[test]
fn carry_from_a_rolled_back_store_is_dropped() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let seven = terms.mk_int(BigInt::from(7));
    let checkpoint = terms.rollback_checkpoint();
    let x_plus_y = raw(&mut terms, "+", [x, y]);
    let carry = {
        let source = LiaSolver::new(&terms);
        let _ = source.cached_linear(x_plus_y, seven);
        let _ = source.term_to_linear_coeffs(x_plus_y);
        source.export_linear_parse_cache().expect("parsed")
    };

    terms.rollback_to(checkpoint);
    let three_x = raw(&mut terms, "*", [three, x]);
    assert_eq!(three_x, x_plus_y, "the rollback re-minted the same id");

    let mut solver = LiaSolver::new(&terms);
    solver.import_linear_parse_cache(carry);
    assert!(solver.linear_cache.borrow().is_empty());
    assert!(solver.affine_cache.borrow().is_empty());
    let parsed = solver.cached_linear(three_x, seven);
    assert_eq!(parsed.coeffs, vec![(x, BigInt::from(3))]);
    let (vars, _) = sorted_coeffs(&solver.term_to_linear_coeffs(three_x));
    assert_eq!(vars, vec![(x, BigRational::from_integer(BigInt::from(3)))]);
}
