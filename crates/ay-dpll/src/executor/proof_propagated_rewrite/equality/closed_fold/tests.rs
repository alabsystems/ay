// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Direct tests of `closed_fold_evaluation_route` on folds the planner
//! harness cannot present.
//!
//! The `Fixture` in `proof_propagated_rewrite/tests.rs` recomputes every fold
//! with `PropagateValues::fold_rebuild`, so a record whose fold disagrees
//! with the ground evaluator is declined as a record mismatch before any
//! route is chosen. These tests hand the route a WRONG fold directly: it must
//! get no closing step at any width, so the planner never emits an
//! `evaluate` (or a `BvLiaTautology`) that only the mandatory strict
//! certification would catch.

use super::*;

const WIDE: u128 = 147_573_952_589_676_412_932;

/// The route for `(= (head left right) folded)` over `width`-bit literals in
/// a plan with no constant target and no #ppp-c7 bridge.
fn route(
    width: u32,
    head: &str,
    left: u128,
    right: u128,
    folded: bool,
) -> Option<ClosedFoldEvaluation> {
    let mut terms = TermStore::new();
    let left = terms.mk_bitvec(num_bigint::BigInt::from(left), width);
    let right = terms.mk_bitvec(num_bigint::BigInt::from(right), width);
    let rebuilt = terms.mk_app(Symbol::named(head), [left, right], Sort::Bool);
    let folded = if folded {
        terms.true_term()
    } else {
        terms.false_term()
    };
    let equality = terms.mk_app(Symbol::named("="), [rebuilt, folded], Sort::Bool);
    let problem_set = HashSet::default();
    let records = HashMap::default();
    let entries = HashMap::default();
    let cx = PlanCx::new(&problem_set, &[], &records, &entries, &[], false);
    let mut planner = PropagationChainPlanner { terms: &mut terms };
    planner.closed_fold_evaluation_route(&cx, rebuilt, &[left, right], equality)
}

/// GREEN twin: a correct 128-bit unsigned comparison, in either polarity,
/// closes with `evaluate`.
#[test]
fn correct_wide_comparison_fold_closes_with_evaluate() {
    assert!(matches!(
        route(128, "bvult", WIDE, WIDE + 1, true),
        Some(ClosedFoldEvaluation::Evaluate)
    ));
    assert!(matches!(
        route(128, "bvult", WIDE + 1, WIDE, false),
        Some(ClosedFoldEvaluation::Evaluate)
    ));
}

/// NEGATIVE: a wrong 128-bit fold gets no route. The bounded interpreter
/// refuses the 128-bit root, and the ground evaluator refutes the equality,
/// so neither the `BvLiaTautology` nor the `evaluate` route may close it.
#[test]
fn wrong_wide_comparison_fold_gets_no_route() {
    assert!(route(128, "bvult", WIDE + 1, WIDE, true).is_none());
    assert!(route(128, "bvult", WIDE, WIDE + 1, false).is_none());
}

/// NEGATIVE, in fragment: the bounded interpreter does not prove a wrong
/// fold's root UNSAT, and the ground evaluator refutes it. The correct twin
/// keeps the unchanged `BvLiaTautology` route.
#[test]
fn wrong_in_fragment_comparison_fold_gets_no_route() {
    assert!(route(64, "bvult", 43, 42, true).is_none());
    assert!(matches!(
        route(64, "bvult", 42, 43, true),
        Some(ClosedFoldEvaluation::BvLiaTautology { .. })
    ));
}
