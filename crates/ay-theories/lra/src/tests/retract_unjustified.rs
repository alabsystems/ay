// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #nia-sign-cut-soundness: retracting an unjustified bound (the #A2 path)
//! takes it out of the slot for the rest of the scope, and a pop still
//! restores the pre-scope state exactly — the asserted bound the guess had
//! tightened over comes back with the pop, not before.

use super::*;
use ay_core::TheorySolver;

/// `x >= -2` asserted, then a tentative NIA cut `x >= 0` (reason = the
/// variable term, never an asserted atom) tightens the slot. The cut is
/// unjustified; retracting it empties the slot (the measured choice — see
/// `retract_unjustified_bound_slot`), and the pop must end with `x >= -2`
/// in the slot again, justified.
#[test]
fn retraction_empties_the_slot_and_pop_restores_the_asserted_bound() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let neg2 = terms.mk_int(BigInt::from(-2));
    let x_ge_m2 = terms.mk_ge(x, neg2);

    let mut lra = LraSolver::new(&terms);
    lra.assert_literal(x_ge_m2, true);
    assert!(
        !matches!(
            lra.check(),
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "x >= -2 alone is satisfiable"
    );
    let var = lra.ensure_var_registered(x);
    let asserted_lb = lra
        .get_bounds(x)
        .and_then(|(lb, _)| lb)
        .expect("x >= -2 installed a lower bound");
    assert_eq!(asserted_lb.value_big(), BigRational::from(BigInt::from(-2)));
    assert!(lra.bound_reasons_all_asserted(&asserted_lb));

    lra.push();
    // The NIA's sign cut: `x >= 0` justified by the variable term itself.
    lra.add_gomory_cut(
        &GomoryCut {
            coeffs: vec![(var, BigRational::one())],
            bound: BigRational::zero(),
            is_lower: true,
            reasons: Vec::new(),
            source_term: None,
        },
        x,
    );
    let guessed_lb = lra
        .get_bounds(x)
        .and_then(|(lb, _)| lb)
        .expect("the cut installed a lower bound");
    assert_eq!(guessed_lb.value_big(), BigRational::zero());
    assert!(
        !lra.bound_reasons_all_asserted(&guessed_lb),
        "a bound whose reason is the variable term is unjustified"
    );

    // Retract it the way the #A2 path does when a conflict cites it.
    let retracted = lra.retract_unjustified_var_bounds(var);
    assert_eq!(retracted, 1, "exactly the guess is retracted");
    let (lb, _) = lra.get_bounds(x).expect("registered");
    assert!(
        lb.is_none(),
        "the slot is empty for the rest of the scope (the guess is gone, and the asserted bound \
         it tightened over returns with the pop)"
    );

    // The pop replay ends in the pre-scope state.
    lra.pop();
    let after = lra
        .get_bounds(x)
        .and_then(|(lb, _)| lb)
        .expect("x >= -2 survives the pop");
    assert_eq!(after.value_big(), BigRational::from(BigInt::from(-2)));
    assert!(lra.bound_reasons_all_asserted(&after));
}

/// With nothing under the guess the slot is likewise emptied, the untouched
/// other side stays, and the pop restores nothing.
#[test]
fn retraction_without_a_predecessor_empties_the_slot() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let ten = terms.mk_int(BigInt::from(10));
    let x_le_10 = terms.mk_le(x, ten);

    let mut lra = LraSolver::new(&terms);
    lra.assert_literal(x_le_10, true);
    let _ = lra.check();
    let var = lra.ensure_var_registered(x);
    lra.push();
    lra.add_gomory_cut(
        &GomoryCut {
            coeffs: vec![(var, BigRational::one())],
            bound: BigRational::zero(),
            is_lower: true,
            reasons: Vec::new(),
            source_term: None,
        },
        x,
    );
    assert_eq!(lra.retract_unjustified_var_bounds(var), 1);
    let (lb, ub) = lra.get_bounds(x).expect("registered");
    assert!(lb.is_none(), "no justified predecessor: the slot is empty");
    assert!(ub.is_some(), "the untouched upper bound stays");
    lra.pop();
    let (lb, _) = lra.get_bounds(x).expect("registered");
    assert!(lb.is_none());
}
