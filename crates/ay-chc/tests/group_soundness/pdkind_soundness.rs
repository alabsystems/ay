// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! PDKIND soundness tests: verify that Safe invariants are truly inductive
//! and that unsafe systems are never reported as Safe.
//!
//! ## Background
//!
//! PDKIND has two verification paths for stable frames:
//! - **Non-incremental** (FreshOnly/Degraded mode): Uses `verify_non_incremental_stable_invariant`
//!   which only checks `init => inv` and `inv => not(query)`, skipping the inductiveness check.
//! - **Incremental** (default): Uses `validate_inductive_invariant` which checks all three
//!   properties including inductiveness.
//!
//! Since #5213, the portfolio marks ALL engines (including PDKIND) with `needs_val = true`,
//! so Safe results always go through portfolio-level validation via `validate_safe()`.
//! After #5745, all engines (including k-inductive) use the standard non-zero budget
//! that checks init, transition, and query clauses — no skip paths remain.
//!
//! These tests verify Safe results from the default (incremental) path using the PDR model
//! verifier as an independent oracle. Non-incremental tests require PdkindConfig to be
//! publicly re-exported (pending: Worker should add to lib.rs re-exports).
//!
//! Part of #4729 Part of #341

use ay_chc::{
    testing, ChcEngineResult, ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead,
    HornClause, PdrConfig,
};
use ntest::timeout;

/// Simple safe problem: x=0, x'=x+1 while x<5, unsafe at x>=10.
/// Safe because x only reaches 5.
fn create_safe_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(5))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    problem
}

/// Simple unsafe problem: x=0, x'=x+1 (unbounded), unsafe at x>=1.
/// Unsafe because x reaches 1 in one step.
fn create_unsafe_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(1))),
        ),
        ClauseHead::False,
    ));

    problem
}

/// SOUNDNESS: When PDKIND (default/incremental config) returns Safe, the invariant
/// model must satisfy ALL original CHC clauses (verified by PDR's verify_model).
///
/// This provides defense-in-depth for the portfolio's `needs_val = false` exemption.
#[test]
#[timeout(60_000)]
fn pdkind_safe_model_verified_by_pdr() {
    let problem = create_safe_problem();
    let solver = testing::pdkind_solver_defaults(problem.clone());
    let result = solver.solve();

    // Must return Safe — this is a trivial 1-variable bounded counter.
    // Accepting Unknown masks completeness regressions (#3015).
    let model = match result {
        ChcEngineResult::Safe(model) => model,
        other => panic!("expected Safe for simple bounded counter, got {other:?}"),
    };
    assert!(!model.is_empty(), "expected non-empty invariant model");
    let mut verifier = testing::new_pdr_solver(problem, PdrConfig::default());
    assert!(
        verifier.verify_model(&model),
        "PDKIND Safe model failed PDR verify_model — invariant may not be inductive"
    );
}

/// SOUNDNESS: PDKIND must NOT return Safe on an unsafe system.
///
/// The verify_non_incremental_stable_invariant gap (init+query only, no inductiveness)
/// could theoretically accept a non-inductive invariant that satisfies init and query
/// but allows transitions to bad states. On an unsafe system, this would be unsound.
#[test]
#[timeout(10_000)]
fn pdkind_never_safe_on_unsafe_system() {
    let problem = create_unsafe_problem();
    let solver = testing::pdkind_solver_defaults(problem);
    let result = solver.solve();

    // PDKIND must return Unsafe — this is a trivial 1-step counterexample.
    // Accepting Unknown masks completeness regressions (#3015).
    assert!(
        matches!(result, ChcEngineResult::Unsafe(_)),
        "PDKIND should find trivial 1-step counterexample, got {result:?}.\n\
         Unknown here indicates a completeness regression."
    );
}

/// SOUNDNESS: Verify PDKIND result agrees with PDR on a safe problem.
/// Both must return Safe (cross-engine validation).
#[test]
#[timeout(60_000)]
fn pdkind_agrees_with_pdr_on_safe_problem() {
    let problem = create_safe_problem();

    let pdkind_result = testing::pdkind_solver_defaults(problem.clone()).solve();
    let pdr_result = testing::new_pdr_solver(problem.clone(), PdrConfig::default()).solve();

    // PDR should definitely solve this
    assert!(
        matches!(pdr_result, ay_chc::PdrResult::Safe(_)),
        "PDR should solve simple safe problem, got {pdr_result:?}"
    );

    // PDKIND must also return Safe — this is a trivial bounded counter.
    // Accepting Unknown masks completeness regressions (#3015).
    let pdkind_model = match pdkind_result {
        ChcEngineResult::Safe(model) => model,
        other => panic!(
            "PDKIND should solve trivial bounded counter, got {other:?}.\n\
             Unknown here indicates a completeness regression."
        ),
    };
    let mut verifier = testing::new_pdr_solver(problem, PdrConfig::default());
    assert!(
        verifier.verify_model(&pdkind_model),
        "PDKIND model rejected by PDR verifier — invariant may not satisfy all clauses"
    );
}

/// SOUNDNESS: Verify PDKIND result agrees with PDR on an unsafe problem.
/// PDR must find Unsafe (trivial 1-step counterexample). PDKIND must not claim Safe.
#[test]
#[timeout(10_000)]
fn pdkind_agrees_with_pdr_on_unsafe_problem() {
    let problem = create_unsafe_problem();

    let pdkind_result = testing::pdkind_solver_defaults(problem.clone()).solve();
    let pdr_result = testing::new_pdr_solver(problem, PdrConfig::default()).solve();

    // PDR must find Unsafe — this is a trivial 1-step counterexample (x=0 → x=1 ≥ 1).
    // Accepting Unknown masks completeness regressions (#3015).
    assert!(
        matches!(pdr_result, ay_chc::PdrResult::Unsafe(_)),
        "expected PDR Unsafe on trivial unsafe problem, got {pdr_result:?}"
    );
    // PDKIND must return Unsafe — this is a trivial 1-step counterexample (x=0 → x=1 ≥ 1).
    // Accepting Unknown masks completeness regressions (#3015).
    assert!(
        matches!(pdkind_result, ChcEngineResult::Unsafe(_)),
        "PDKIND should find trivial 1-step counterexample, got {pdkind_result:?}.\n\
         Unknown here indicates a completeness regression."
    );
}
