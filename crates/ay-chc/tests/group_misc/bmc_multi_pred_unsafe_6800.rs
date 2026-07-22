// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! Regression tests for #6800: BMC false-UNSAT on multi-predicate problems.
//!
//! BMC produces witness-less `Unsafe` results with `predicate: PredicateId(0)`
//! for every step. This is insufficient to justify multi-predicate unsafety
//! because the verifier only handles single-predicate transition-system
//! encodings. The portfolio must suppress witness-less BMC Unsafe results
//! on multi-predicate problems.

use ay_chc::{
    testing, BmcConfig, ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, EngineConfig,
    HornClause, PortfolioConfig, PortfolioResult,
};
use ntest::timeout;

/// Synthetic multi-predicate problem where BMC's witness-less Unsafe is wrong.
///
/// Two predicates: P and Q with P(x) => Q(x) => false.
/// BMC may find an assignment satisfying the query but cannot produce a
/// valid derivation witness across the predicate chain.
fn create_multi_pred_safe_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Fact: x = 0 => P(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));

    // P(x) /\ x < 5 => Q(x)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(5))),
        ),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
    ));

    // Q(x) /\ x >= 10 => false
    // This is SAFE: Q(x) only holds for x in {0..4}, never for x >= 10.
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    problem
}

/// Regression: BMC-only portfolio must not return Unsafe on a multi-predicate
/// safe problem (#6800).
///
/// Before fix: BMC returns Unsafe with witness-less counterexample, portfolio
/// accepts it because predicate count is not checked.
/// After fix: Portfolio suppresses witness-less BMC Unsafe on multi-predicate
/// problems, returning Unknown instead.
#[test]
#[timeout(5_000)]
fn test_bmc_multi_pred_witness_less_unsafe_suppressed() {
    let problem = create_multi_pred_safe_problem();
    assert!(
        problem.predicates().len() > 1,
        "test requires multi-predicate problem"
    );

    let config = PortfolioConfig::with_engines(vec![EngineConfig::Bmc(
        BmcConfig::with_engine_config(10, false, None),
    )])
    .preprocessing(false);

    let solver = testing::new_portfolio_solver(problem, config);
    let result = solver.solve();

    match result {
        PortfolioResult::Unknown | PortfolioResult::NotApplicable | PortfolioResult::Safe(_) => {
            // Correct: BMC witness-less Unsafe suppressed on multi-predicate problem
        }
        PortfolioResult::Unsafe(_) => {
            panic!(
                "SOUNDNESS BUG (#6800): Portfolio accepted witness-less BMC Unsafe \
                 on a multi-predicate safe problem. The verifier cannot check \
                 multi-predicate witness-less counterexamples."
            );
        }
        _ => panic!("unexpected result variant"),
    }
}

/// Regression: single-predicate BMC Unsafe must still be accepted.
///
/// The multi-predicate guard must NOT suppress single-predicate BMC results.
#[test]
#[timeout(5_000)]
fn test_bmc_single_pred_unsafe_still_accepted() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Fact: x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) => Inv(x + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) /\ x >= 3 => false (UNSAFE: x can reach 3)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(3))),
        ),
        ClauseHead::False,
    ));

    assert_eq!(
        problem.predicates().len(),
        1,
        "test requires single-predicate problem"
    );

    let config = PortfolioConfig::with_engines(vec![EngineConfig::Bmc(
        BmcConfig::with_engine_config(10, false, None),
    )])
    .preprocessing(false);

    let solver = testing::new_portfolio_solver(problem, config);
    let result = solver.solve();

    match result {
        PortfolioResult::Unsafe(_) => {
            // Correct: single-predicate BMC Unsafe is still accepted
        }
        other => {
            panic!("Single-predicate BMC Unsafe should be accepted, got {other:?}");
        }
    }
}
