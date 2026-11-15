// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::resource::{ChildSpec, Guard, NodeLabel};
use ay_core::term::{Symbol, TermData, TermId, TermStore};
use ay_core::{Sort, TheoryResult, TheorySolver};
use num_bigint::BigInt;

use crate::NiaSolver;

fn admitted(terms: &TermStore, roots: Vec<TermId>) -> bool {
    let shared = super::is_integer_unit_conjunction(terms, &roots);
    let mut solver = NiaSolver::new(terms);
    solver.set_root_assertions(roots);
    let scheduled = solver.root_assertions_are_integer_unit_conjunction();
    assert_eq!(shared, scheduled);
    scheduled
}

#[test]
fn polarity_distinguishes_unit_conjunctions_from_boolean_alternatives() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let positive = terms.mk_gt(x, zero);
    let negative = terms.mk_lt(x, zero);
    let conjunction = terms.mk_and(vec![positive, negative]);
    let disjunction = terms.mk_or(vec![positive, negative]);
    let not_conjunction = terms.mk_not(conjunction);
    let not_disjunction = terms.mk_not(disjunction);
    assert!(admitted(&terms, vec![conjunction]));
    assert!(admitted(&terms, vec![not_disjunction]));
    assert!(!admitted(&terms, vec![disjunction]));
    assert!(!admitted(&terms, vec![not_conjunction]));
}

#[test]
fn nested_integer_ite_and_boolean_equality_retain_the_early_offer() {
    let mut terms = TermStore::new();
    let flag = terms.mk_var("flag", Sort::Bool);
    let other = terms.mk_var("other", Sort::Bool);
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let selected = terms.mk_ite(flag, x, y);
    let sum = terms.mk_add(vec![selected, x]);
    let arithmetic = terms.mk_gt(sum, zero);
    let boolean = terms.mk_eq(flag, other);
    assert!(!admitted(&terms, vec![arithmetic]));
    assert!(!admitted(&terms, vec![boolean]));
}

#[test]
fn unsupported_sorts_and_applications_retain_the_early_offer() {
    let mut terms = TermStore::new();
    let real = terms.mk_var("real", Sort::Real);
    let other_real = terms.mk_var("other_real", Sort::Real);
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let real_eq = terms.mk_eq(real, other_real);
    let opaque = terms.mk_app(Symbol::named("opaque"), vec![x], Sort::Int);
    let opaque_eq = terms.mk_eq(opaque, zero);
    assert!(!admitted(&terms, vec![real_eq]));
    assert!(!admitted(&terms, vec![opaque_eq]));
    assert!(!admitted(&terms, vec![]));
}

#[test]
fn wide_and_repeated_edges_cannot_exceed_the_inventory_budget() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let atom = terms.mk_ge(x, zero);
    let wide = terms.mk_app(
        Symbol::named("and"),
        vec![atom; super::MAX_SKELETON_WORK + 1],
        Sort::Bool,
    );
    assert!(
        matches!(terms.get(wide), TermData::App(_, args) if args.len() > super::MAX_SKELETON_WORK)
    );
    assert!(!admitted(&terms, vec![wide]));
    assert!(!admitted(&terms, vec![atom; super::MAX_SKELETON_WORK + 1]));
    assert!(admitted(&terms, vec![atom]));
}

#[test]
fn a_stopped_inventory_does_not_claim_a_completed_scan() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let root = terms.mk_ge(x, zero);
    {
        let check = Guard::root_child(ChildSpec::new(NodeLabel::Check));
        check.cancel();
        let _scope = check.enter();
        assert!(!admitted(&terms, vec![root]));
    }
    assert!(admitted(&terms, vec![root]));
}

#[test]
fn source_units_can_precede_generated_branches_without_changing_search_roots() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let division = terms.mk_app(Symbol::named("div"), vec![a, b], Sort::Int);
    let source = vec![
        terms.mk_gt(a, zero),
        terms.mk_gt(b, zero),
        terms.mk_lt(division, zero),
    ];
    let divisor_zero = terms.mk_eq(b, zero);
    let positive = terms.mk_gt(b, zero);
    let branch = terms.mk_or(vec![divisor_zero, positive]);
    let working = vec![branch];
    let mut solver = NiaSolver::new(&terms);
    solver.set_root_assertions(working.clone());
    assert!(!solver.root_assertions_are_integer_unit_conjunction());
    solver.set_local_search_source_roots(&source);
    assert!(solver.root_assertions_are_integer_unit_conjunction());
    assert_eq!(solver.root_assertions, working);
    assert!(!solver.local_search_done);
    assert!(solver.bounded_enum_model.is_none());
}

#[test]
fn source_alternatives_retain_the_first_offer_and_replacing_roots_clears_shape() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let positive = terms.mk_gt(x, zero);
    let negative = terms.mk_lt(x, zero);
    let source = terms.mk_or(vec![positive, negative]);
    let mut solver = NiaSolver::new(&terms);
    solver.set_root_assertions(vec![positive]);
    assert!(solver.root_assertions_are_integer_unit_conjunction());
    solver.set_local_search_source_roots(&[source]);
    assert!(!solver.root_assertions_are_integer_unit_conjunction());
    solver.set_root_assertions(vec![positive]);
    assert!(solver.root_assertions_are_integer_unit_conjunction());
    assert!(solver.local_search_first_offer.is_none());
}

#[test]
fn an_incomplete_or_stopped_source_scan_keeps_the_first_offer() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let root = terms.mk_ge(x, zero);
    let mut solver = NiaSolver::new(&terms);
    solver.set_root_assertions(vec![root]);
    solver.set_local_search_source_roots(&vec![root; super::MAX_SKELETON_WORK + 1]);
    assert!(!solver.root_assertions_are_integer_unit_conjunction());
    {
        let check = Guard::root_child(ChildSpec::new(NodeLabel::Check));
        check.cancel();
        let _scope = check.enter();
        solver.set_local_search_source_roots(&[root]);
    }
    assert!(!solver.root_assertions_are_integer_unit_conjunction());
    solver.set_local_search_source_roots(&[root]);
    assert!(solver.root_assertions_are_integer_unit_conjunction());
}

#[test]
fn compound_bound_refines_to_a_conflict_before_sat_only_search() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Int);
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let main = terms.mk_var("main", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let three = terms.mk_int(BigInt::from(3));
    let minus_three = terms.mk_int(BigInt::from(-3));
    let minus_five = terms.mk_int(BigInt::from(-5));
    let minus_one = terms.mk_int(BigInt::from(-1));
    let main_bound = terms.mk_add(vec![main, minus_three]);
    let c_bound = terms.mk_add(vec![c, main]);
    let neg_x = terms.mk_mul(vec![minus_one, x]);
    let equality = terms.mk_add(vec![neg_x, y, z]);
    let three_x = terms.mk_mul(vec![three, x]);
    let minus_five_y = terms.mk_mul(vec![minus_five, y]);
    let c_z = terms.mk_mul(vec![c, z]);
    let expression = terms.mk_add(vec![three_x, minus_five_y, c_z, minus_one]);
    let roots = vec![
        terms.mk_eq(main_bound, zero),
        terms.mk_le(c_bound, zero),
        terms.mk_ge(x, zero),
        terms.mk_ge(y, zero),
        terms.mk_ge(z, zero),
        terms.mk_eq(equality, zero),
        terms.mk_gt(expression, zero),
    ];
    let mut solver = NiaSolver::new(&terms);
    solver.set_root_assertions(roots.clone());
    for root in roots {
        solver.assert_literal(root, true);
    }
    assert!(solver.root_assertions_are_integer_unit_conjunction());
    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "{result:?}"
    );
    assert!(
        !solver.local_search_done,
        "exact refinement must precede the SAT-only search"
    );
}

#[test]
fn boolean_alternatives_keep_the_first_whole_formula_search() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let xy = terms.mk_mul(vec![x, y]);
    let six = terms.mk_int(BigInt::from(6));
    let two = terms.mk_int(BigInt::from(2));
    let thirty_five = terms.mk_int(BigInt::from(35));
    let five = terms.mk_int(BigInt::from(5));
    let a1 = terms.mk_eq(xy, six);
    let a2 = terms.mk_ge(x, two);
    let b1 = terms.mk_eq(xy, thirty_five);
    let b2 = terms.mk_ge(x, five);
    let left = terms.mk_and(vec![a1, a2]);
    let right = terms.mk_and(vec![b1, b2]);
    let root = terms.mk_or(vec![left, right]);
    let mut solver = NiaSolver::new(&terms);
    solver.set_root_assertions(vec![root]);
    solver.assert_literal(a1, true);
    solver.assert_literal(a2, true);
    assert!(!solver.root_assertions_are_integer_unit_conjunction());
    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat), "{result:?}");
    assert!(solver.local_search_done);
    let model = solver
        .extract_model()
        .expect("the successful lane retains its witness");
    let xv = model.values.get(&x).expect("x");
    let yv = model.values.get(&y).expect("y");
    let product = xv * yv;
    assert!(
        (product == BigInt::from(6) && xv >= &BigInt::from(2))
            || (product == BigInt::from(35) && xv >= &BigInt::from(5))
    );
}
