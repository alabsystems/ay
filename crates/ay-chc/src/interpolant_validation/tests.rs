// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::smt::SmtContext;
use crate::{ChcSort, ChcVar};

fn check_sat_via_smt(query: &ChcExpr) -> SmtResult {
    let mut smt = SmtContext::new();
    smt.check_sat(query)
}

#[test]
fn valid_interpolant_accepted() {
    // A: x <= 5, B: x >= 10, I: x <= 5
    let x = ChcVar::new("x", ChcSort::Int);
    let a = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let b = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10));
    let i = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name]);

    assert!(is_valid_interpolant_with_check_sat(
        &a,
        &b,
        &i,
        &shared,
        check_sat_via_smt
    ));
}

#[test]
fn rejects_non_shared_variable() {
    // A: x <= 5 AND y = 3, B: x >= 10, I: x <= 5 AND y = 3
    // I mentions y which is not shared.
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let a = ChcExpr::and(
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5)),
        ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(3)),
    );
    let b = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10));
    let i = ChcExpr::and(
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5)),
        ChcExpr::eq(ChcExpr::var(y), ChcExpr::int(3)),
    );
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name]);

    assert!(!is_valid_interpolant_with_check_sat(
        &a,
        &b,
        &i,
        &shared,
        check_sat_via_smt
    ));
}

#[test]
fn rejects_interpolant_not_implied_by_a() {
    // A: x <= 5, B: x >= 10, I: x <= 3
    // A does not imply I (x=4 satisfies A but not I).
    let x = ChcVar::new("x", ChcSort::Int);
    let a = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let b = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10));
    let i = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(3));
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name]);

    assert!(!is_valid_interpolant_with_check_sat(
        &a,
        &b,
        &i,
        &shared,
        check_sat_via_smt
    ));
}

#[test]
fn rejects_interpolant_consistent_with_b() {
    // A: x <= 5, B: x >= 3, I: x <= 5
    // I /\ B is SAT (x=4 satisfies both x<=5 and x>=3).
    let x = ChcVar::new("x", ChcSort::Int);
    let a = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let b = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(3));
    let i = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name]);

    assert!(!is_valid_interpolant_with_check_sat(
        &a,
        &b,
        &i,
        &shared,
        check_sat_via_smt
    ));
}

#[test]
fn is_unsat_result_classification() {
    assert!(is_unsat_result(&SmtResult::Unsat));
    assert!(is_unsat_result(&SmtResult::UnsatWithCore(
        crate::smt::types::UnsatCore {
            conjuncts: vec![],
            farkas_conflicts: vec![],
            diagnostics: Default::default(),
        }
    )));
    assert!(!is_unsat_result(&SmtResult::Unknown));
}

#[test]
fn is_unsat_result_farkas_variant() {
    // UnsatWithFarkas should also be classified as unsat
    let farkas = SmtResult::UnsatWithFarkas(crate::smt::FarkasConflict {
        conflict_terms: vec![],
        polarities: vec![],
        farkas: ay_core::FarkasAnnotation::from_ints(&[]),
        origins: vec![],
    });
    assert!(is_unsat_result(&farkas));
}

#[test]
fn is_unsat_result_sat_variant() {
    // Sat should not be classified as unsat
    let sat = SmtResult::Sat(ay_core::kani_compat::DetHashMap::default());
    assert!(!is_unsat_result(&sat));
}

#[test]
fn constant_interpolant_no_variables() {
    // A: x <= 5, B: x >= 10, I: true (constant, no variables)
    // true is not a valid interpolant here because A does not imply true
    // (well actually A does imply true, but true AND B is SAT, so it fails check 2)
    let x = ChcVar::new("x", ChcSort::Int);
    let a = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let b = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10));
    let i = ChcExpr::Bool(true);
    // Empty shared vars — constant interpolant has no vars to violate locality
    let shared: FxHashSet<String> = FxHashSet::default();

    // true AND B is SAT (B is satisfiable), so this should fail
    assert!(!is_valid_interpolant_with_check_sat(
        &a,
        &b,
        &i,
        &shared,
        check_sat_via_smt
    ));
}

#[test]
fn false_interpolant_passes_when_a_is_unsat() {
    // A: (x <= 5 AND x >= 10) which is UNSAT, B: (x >= 0)
    // I: false — A implies false (vacuously true since A is UNSAT), and false AND B is UNSAT
    let x = ChcVar::new("x", ChcSort::Int);
    let a = ChcExpr::and(
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5)),
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10)),
    );
    let b = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));
    let i = ChcExpr::Bool(false);
    let shared: FxHashSet<String> = FxHashSet::default();

    assert!(is_valid_interpolant_with_check_sat(
        &a,
        &b,
        &i,
        &shared,
        check_sat_via_smt
    ));
}

#[test]
fn mock_check_sat_unknown_rejects() {
    // When check_sat returns Unknown for A AND NOT I, the interpolant should be rejected
    let x = ChcVar::new("x", ChcSort::Int);
    let a = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let b = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10));
    let i = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name]);

    // Mock that always returns Unknown
    let result =
        is_valid_interpolant_with_check_sat(&a, &b, &i, &shared, |_: &ChcExpr| SmtResult::Unknown);
    assert!(!result, "Unknown result should cause rejection");
}

#[test]
fn empty_shared_vars_rejects_variable_interpolant() {
    // Interpolant has variables but shared_vars is empty — locality check fails
    let x = ChcVar::new("x", ChcSort::Int);
    let a = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let b = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10));
    let i = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(5));
    let shared: FxHashSet<String> = FxHashSet::default(); // empty

    assert!(!is_valid_interpolant_with_check_sat(
        &a,
        &b,
        &i,
        &shared,
        check_sat_via_smt,
    ));
}

/// A disjunctive invariant is validated disjunct by disjunct: `x ∈ {0, 1}`
/// under `x' = 1 - x` is inductive (also strengthened by `¬query`), while
/// `x ∈ {0, 2}` is not.
#[test]
fn disjunctive_invariant_is_validated_one_disjunct_at_a_time() {
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);
    let xe = ChcExpr::var(x.clone());
    let ts = TransitionSystem::new(
        crate::PredicateId::new(0),
        vec![x],
        ChcExpr::eq(xe.clone(), ChcExpr::int(0)),
        ChcExpr::eq(
            ChcExpr::var(x_next),
            ChcExpr::sub(ChcExpr::int(1), xe.clone()),
        ),
        ChcExpr::eq(xe.clone(), ChcExpr::int(5)),
    );
    let is = |n: i64| ChcExpr::eq(xe.clone(), ChcExpr::int(n));
    let inv = ChcExpr::or(is(0), is(1));
    assert_eq!(
        validate_inductive_invariant(&ts, &inv, check_sat_via_smt),
        None
    );
    let strengthened = ChcExpr::and(inv, ChcExpr::not(is(5)));
    assert_eq!(
        validate_inductive_invariant(&ts, &strengthened, check_sat_via_smt),
        None
    );
    assert_eq!(
        validate_inductive_invariant(&ts, &ChcExpr::or(is(0), is(2)), check_sat_via_smt),
        Some("inductiveness")
    );
}
