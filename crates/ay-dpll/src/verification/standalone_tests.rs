// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{Sort, Symbol, TermId};
use num_bigint::BigInt;

/// `a = b`, `f(a) = f(b)` and `f(b) = c` over an uninterpreted sort.
fn congruence_atoms(terms: &mut TermStore) -> (TermId, TermId, TermId) {
    let u = Sort::Uninterpreted("U".to_string());
    let a = terms.mk_var("a", u.clone());
    let b = terms.mk_var("b", u.clone());
    let c = terms.mk_var("c", u.clone());
    let fa = terms.mk_app(Symbol::named("f"), vec![a], u.clone());
    let fb = terms.mk_app(Symbol::named("f"), vec![b], u);
    (terms.mk_eq(a, b), terms.mk_eq(fa, fb), terms.mk_eq(fb, c))
}

#[test]
fn congruence_conflict_is_refuted_on_its_own() {
    let mut terms = TermStore::new();
    let (a_eq_b, fa_eq_fb, _) = congruence_atoms(&mut terms);
    let conflict = [
        TheoryLit::new(a_eq_b, true),
        TheoryLit::new(fa_eq_fb, false),
    ];
    assert!(conflict_is_refuted_on_its_own(&conflict, &terms));
}

/// The one-literal twin: without `a = b` the literal set is satisfiable.
#[test]
fn satisfiable_literal_set_is_not_refuted() {
    let mut terms = TermStore::new();
    let (a_eq_b, fa_eq_fb, _) = congruence_atoms(&mut terms);
    let conflict = [
        TheoryLit::new(a_eq_b, false),
        TheoryLit::new(fa_eq_fb, false),
    ];
    assert!(!conflict_is_refuted_on_its_own(&conflict, &terms));
}

#[test]
fn integer_bound_conflict_is_refuted_on_its_own() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(5.into());
    let six = terms.mk_int(6.into());
    let x_gt_5 = terms.mk_gt(x, five);
    let x_lt_6 = terms.mk_lt(x, six);
    let conflict = [TheoryLit::new(x_gt_5, true), TheoryLit::new(x_lt_6, true)];
    assert!(conflict_is_refuted_on_its_own(&conflict, &terms));
    let twin = [TheoryLit::new(x_gt_5, true), TheoryLit::new(x_lt_6, false)];
    assert!(!conflict_is_refuted_on_its_own(&twin, &terms));
}

#[test]
fn empty_and_tautological_sets_are_not_carried() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    assert!(!conflict_is_refuted_on_its_own(&[], &terms));
    let both = [TheoryLit::new(p, true), TheoryLit::new(p, false)];
    assert!(!conflict_is_refuted_on_its_own(&both, &terms));
}

/// A conflict the search's gate admits because of a support literal (here
/// `f(b) = c`, standing for a ground instance of an asserted quantifier) is a
/// consequence of THIS query, not of the theory: `a = b`, `f(a) != c` has a
/// model. Carried into a solve whose problem lacks the support, its clause
/// would remove that model.
#[test]
fn a_conflict_the_gate_admits_only_with_support_is_not_refuted_alone() {
    let mut terms = TermStore::new();
    let (a_eq_b, _, fb_eq_c) = congruence_atoms(&mut terms);
    let u = Sort::Uninterpreted("U".to_string());
    let a = terms.mk_var("a", u.clone());
    let c = terms.mk_var("c", u.clone());
    let fa = terms.mk_app(Symbol::named("f"), vec![a], u);
    let fa_eq_c = terms.mk_eq(fa, c);
    let conflict = [TheoryLit::new(a_eq_b, true), TheoryLit::new(fa_eq_c, false)];
    let support = [TheoryLit::new(fb_eq_c, true)];
    assert!(
        matches!(
            verify_conflict_semantic_classified(&conflict, &terms, &support, None, None),
            Ok(ConflictSemanticVerdict::Reproved)
        ),
        "the gate re-proves the conflict with its support"
    );
    assert!(!conflict_is_refuted_on_its_own(&conflict, &terms));
}

/// The arithmetic twin: `x = 5`, `y <= 3` is refuted only by an asserted
/// `x = y` the conflict does not name.
#[test]
fn a_conflict_that_needs_an_asserted_equality_is_not_refuted_alone() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let three = terms.mk_int(3.into());
    let five = terms.mk_int(5.into());
    let x_eq_5 = terms.mk_eq(x, five);
    let y_le_3 = terms.mk_le(y, three);
    let x_eq_y = terms.mk_eq(x, y);
    let conflict = [TheoryLit::new(x_eq_5, true), TheoryLit::new(y_le_3, true)];
    assert!(!conflict_is_refuted_on_its_own(&conflict, &terms));
    let with_context = [
        TheoryLit::new(x_eq_5, true),
        TheoryLit::new(y_le_3, true),
        TheoryLit::new(x_eq_y, true),
    ];
    assert!(conflict_is_refuted_on_its_own(&with_context, &terms));
}

/// An array conflict that only the array solver re-derives is not an
/// independent check of that solver, so it is not carried, though the gate
/// lets the search learn it.
#[test]
fn an_array_conflict_reproved_by_the_array_solver_is_not_carried() {
    let mut terms = TermStore::new();
    let array = terms.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let stored = terms.mk_store(array, i, v);
    let read = terms.mk_select(stored, j);
    let read_eq_v = terms.mk_eq(read, v);
    let i_eq_j = terms.mk_eq(i, j);
    let conflict = [
        TheoryLit::new(i_eq_j, true),
        TheoryLit::new(read_eq_v, false),
    ];
    let verdict = verify_conflict_semantic_classified(&conflict, &terms, &[], None, None);
    assert!(
        matches!(verdict, Ok(ConflictSemanticVerdict::ReprovedByArrayTheory)),
        "the gate re-derives it with the array solver, got {verdict:?}"
    );
    assert!(!conflict_is_refuted_on_its_own(&conflict, &terms));
}

/// Bit-vector conflicts are checked structurally only: nothing re-derives
/// them, so none is carried.
#[test]
fn a_bitvector_conflict_is_not_carried() {
    let mut terms = TermStore::new();
    let bv8 = Sort::bitvec(8);
    let x = terms.mk_var("x", bv8);
    let zero = terms.mk_bitvec(BigInt::from(0), 8);
    let x_eq_zero = terms.mk_eq(x, zero);
    let zero_ult_x = terms.mk_bvult(zero, x);
    let conflict = [
        TheoryLit::new(x_eq_zero, true),
        TheoryLit::new(zero_ult_x, true),
    ];
    assert!(!conflict_is_refuted_on_its_own(&conflict, &terms));
}
