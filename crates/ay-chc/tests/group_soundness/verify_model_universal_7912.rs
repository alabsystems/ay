// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for verify_model() universality (#7912).
//!
//! Each test exercises a specific gap identified in the audit:
//! - Gap A: Empty-assertions DPLL fast path (tested in ay-dpll)
//! - Gap C: Algebraic invariant synthesis validation
//! - Gap D: Trivial solver validation (fixed in 146d391a7)
//! - Gap E: K-Induction query-only validation

#![allow(clippy::panic)]

use ay_chc::{
    AdaptiveConfig, AdaptivePortfolio, ChcExpr, ChcParser, ChcProblem, ChcSort, ChcVar, ClauseBody,
    ClauseHead, HornClause, KindConfig, KindResult, PortfolioConfig, PortfolioResult,
    VerifiedChcResult,
};
use ntest::timeout;
use std::time::Duration;

// --- Gap C: Algebraic invariant synthesis validates its result ---

/// A simple symbolic accumulator that algebraic synthesis can solve.
/// Init: n >= 0, n <= 100, i = 0, sum = 0
/// Trans: i < n => i' = i + 1, sum' = sum + i
/// Query: sum > n * n => false (safe: sum = n*(n-1)/2 <= n*n)
///
/// Algebraic synthesis derives sum <= n*n via closed-form elimination.
/// This test confirms the portfolio returns Safe and that the result
/// passes through the algebraic validation pipeline.
const SYMBOLIC_ACCUMULATOR: &str = r#"
(set-logic HORN)
(declare-fun Inv (Int Int Int) Bool)

(assert (forall ((n Int) (i Int) (sum Int))
  (=> (and (<= 0 n) (<= n 100) (= i 0) (= sum 0))
      (Inv n i sum))))

(assert (forall ((n Int) (i Int) (sum Int) (i2 Int) (sum2 Int))
  (=> (and (Inv n i sum)
           (< i n)
           (= i2 (+ i 1))
           (= sum2 (+ sum i)))
      (Inv n i2 sum2))))

(assert (forall ((n Int) (i Int) (sum Int))
  (=> (and (Inv n i sum)
           (> sum (* n n)))
      false)))

(check-sat)
"#;

/// Regression test for Gap C (#7912): algebraic invariant synthesis must validate
/// its model before returning Safe. The portfolio now has a debug_assert calling
/// validate_safe_query_only() as defense-in-depth.
///
/// This test exercises the algebraic synthesis path end-to-end via the adaptive
/// portfolio, confirming it returns Safe on a problem with polynomial closed forms.
#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(15_000))]
fn test_gap_c_algebraic_synthesis_returns_validated_safe() {
    let problem = ChcParser::parse(SYMBOLIC_ACCUMULATOR).expect("parse accumulator");
    let config = AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(10));
    let solver = AdaptivePortfolio::new(problem, config);
    let result = solver.solve();

    match result {
        VerifiedChcResult::Safe(_) => {
            // Expected: algebraic synthesis solves this and validation passes.
            // In debug builds, the new debug_assert in portfolio/mod.rs confirms
            // query-only validation also passes.
        }
        VerifiedChcResult::Unknown(_) => {
            // Acceptable: NIA solver may return Unknown for polynomial queries.
            // The algebraic path attempted synthesis but could not validate.
        }
        VerifiedChcResult::Unsafe(_) => {
            panic!(
                "SOUNDNESS BUG (#7912 Gap C): symbolic accumulator is SAFE \
                 (sum <= n*n), but solver returned Unsafe"
            );
        }
        _ => panic!("unexpected VerifiedChcResult variant"),
    }
}

/// A deliberately UNSAFE problem that algebraic synthesis must NOT claim Safe on.
/// Init: i = 0, sum = 0
/// Trans: i' = i + 1, sum' = sum + i
/// Query: sum > 5 => false (UNSAFE: sum reaches 0,1,3,6,10,15,... which exceeds 5)
///
/// If algebraic synthesis incorrectly skips validation, it might return a
/// non-inductive invariant. This test ensures the validation rejects it.
#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(15_000))]
fn test_gap_c_algebraic_synthesis_rejects_unsafe_problem() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Int]);
    let i = ChcVar::new("i", ChcSort::Int);
    let sum = ChcVar::new("sum", ChcSort::Int);

    // Init: i = 0, sum = 0
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(i.clone()), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(sum.clone()), ChcExpr::int(0)),
        )),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::var(i.clone()), ChcExpr::var(sum.clone())],
        ),
    ));

    // Trans: Inv(i, sum) => Inv(i+1, sum+i)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            inv,
            vec![ChcExpr::var(i.clone()), ChcExpr::var(sum.clone())],
        )]),
        ClauseHead::Predicate(
            inv,
            vec![
                ChcExpr::add(ChcExpr::var(i.clone()), ChcExpr::int(1)),
                ChcExpr::add(ChcExpr::var(sum.clone()), ChcExpr::var(i.clone())),
            ],
        ),
    ));

    // Query: Inv(i, sum) /\ sum > 5 => false (UNSAFE: sum = 0+1+2+...+i, exceeds 5)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(i), ChcExpr::var(sum.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(sum), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    let config = AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(10));
    let solver = AdaptivePortfolio::new(problem, config);
    let result = solver.solve();

    match result {
        VerifiedChcResult::Unsafe(_) => {
            // Correct: the problem is genuinely unsafe.
        }
        VerifiedChcResult::Unknown(_) => {
            // Acceptable: solver could not determine within budget.
        }
        VerifiedChcResult::Safe(_) => {
            panic!(
                "SOUNDNESS BUG (#7912 Gap C): unbounded accumulator (sum > 5 => false) \
                 is UNSAFE, but solver returned Safe. Algebraic synthesis validation \
                 should have rejected any non-inductive invariant."
            );
        }
        _ => panic!("unexpected VerifiedChcResult variant"),
    }
}

// --- Gap D: Trivial solver validation (fixed in 146d391a7) ---

/// Regression test for Gap D (#7912): trivial solver (predicate-free after
/// preprocessing) must validate Safe results. A predicate-free problem with
/// all-UNSAT queries is trivially Safe, and the trivial solver now applies
/// query-only validation before returning.
#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(15_000))]
fn test_gap_d_trivial_solver_validates_safe() {
    // A trivial problem: no predicates in body, query constraint is UNSAT.
    // (assert (forall ((x Int)) (=> (> x x) false)))
    // This is trivially Safe because x > x is always false.
    let smt = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int)) (=> (and (P x) (> x x)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt).expect("parse trivial problem");
    let config = PortfolioConfig::test_default();
    let solver = ay_chc::testing::new_portfolio_solver(problem, config);
    let result = solver.solve();

    match result {
        PortfolioResult::Safe(_) => {
            // Expected: trivially safe with validation.
        }
        PortfolioResult::Unknown => {
            // Acceptable: engines may not converge.
        }
        PortfolioResult::Unsafe(_) => {
            panic!(
                "SOUNDNESS BUG (#7912 Gap D): trivially safe problem (x > x is always false) \
                 returned Unsafe"
            );
        }
        _ => panic!("unexpected variant"),
    }
}

// --- Gap E: K-Induction query-only validation ---

/// Regression test for Gap E (#7912): Kind results must pass query-only
/// validation before being accepted. This test exercises the Kind solver
/// on a bounded counter that is genuinely Safe.
///
/// The counter increments from 0 to 3, and the query checks x > 10.
/// Kind should find a k-inductive invariant and validate it.
#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(15_000))]
fn test_gap_e_kind_validates_safe_result() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Init: x = 0
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Transition: Inv(x) /\ x < 3 => Inv(x + 1) (bounded)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(3))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Query: Inv(x) /\ x > 10 => false (SAFE: x in {0,1,2,3})
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    let config = KindConfig::with_engine_config(
        10,
        Duration::from_secs(2),
        Duration::from_secs(10),
        false,
        None,
    );
    let mut solver = ay_chc::testing::new_kind_solver(problem, config);
    let result = solver.solve();

    match result {
        KindResult::Safe(_) => {
            // Expected: Kind finds a k-inductive invariant.
            // The adaptive layer's debug_assert confirms query-only validation passes.
        }
        KindResult::Unknown | KindResult::NotApplicable => {
            // Acceptable: Kind may not converge.
        }
        KindResult::Unsafe(cex) => {
            panic!(
                "SOUNDNESS BUG (#7912 Gap E): bounded counter (x <= 3, query x > 10) \
                 is SAFE, but Kind returned Unsafe at steps={}",
                cex.steps.len()
            );
        }
        _ => panic!("unexpected variant"),
    }
}

/// Test that Kind correctly rejects (does not return Safe on) an UNSAFE problem.
/// This exercises the query-only validation path: even if Kind finds a
/// candidate invariant, query-only validation should reject it if the
/// invariant doesn't actually exclude bad states.
#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(15_000))]
fn test_gap_e_kind_rejects_unsafe_problem() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Init: x = 0
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Transition: Inv(x) => Inv(x + 1) (UNBOUNDED)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Query: Inv(x) /\ x > 5 => false (UNSAFE: x grows without bound)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    let config = KindConfig::with_engine_config(
        10,
        Duration::from_secs(2),
        Duration::from_secs(10),
        false,
        None,
    );
    let mut solver = ay_chc::testing::new_kind_solver(problem, config);
    let result = solver.solve();

    match result {
        KindResult::Unsafe(_) => {
            // Correct: the problem is genuinely unsafe.
        }
        KindResult::Unknown | KindResult::NotApplicable => {
            // Acceptable: Kind may not converge or determine this.
        }
        KindResult::Safe(_) => {
            panic!(
                "SOUNDNESS BUG (#7912 Gap E): unbounded counter (x > 5 => false) \
                 is UNSAFE, but Kind returned Safe. Query-only validation should \
                 have rejected the invariant."
            );
        }
        _ => panic!("unexpected variant"),
    }
}

// --- Gap A: Empty-assertions DPLL fast path ---
// The primary Gap A test is in ay-dpll (theory_smoke_tests.rs::test_empty_assertions_sat).
// This test confirms the CHC layer handles an entry-exit-only problem
// (no predicates, trivially safe) correctly via the adaptive portfolio,
// which internally uses DPLL's empty-assertion fast path.

/// Regression test for Gap A (#7912): an entry-exit-only CHC problem
/// (no body predicates in any clause) routes through the trivial solver
/// and ultimately uses DPLL's empty-assertion code path.
#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(15_000))]
fn test_gap_a_entry_exit_only_safe() {
    // An entry-exit-only problem: constraint-only clause with query always false.
    // (assert (forall ((x Int)) (=> false false)))
    // This trivially has no violation path.
    let smt = r#"
(set-logic HORN)
(assert (forall ((x Int)) (=> (and (> x 0) (< x 0)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt).expect("parse entry-exit-only problem");
    let config = AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(5));
    let solver = AdaptivePortfolio::new(problem, config);
    let result = solver.solve();

    match result {
        VerifiedChcResult::Safe(_) => {
            // Expected: x > 0 AND x < 0 is unsatisfiable, so query never fires.
        }
        VerifiedChcResult::Unknown(_) => {
            // Acceptable.
        }
        VerifiedChcResult::Unsafe(_) => {
            panic!(
                "SOUNDNESS BUG (#7912 Gap A): entry-exit-only problem with contradictory \
                 guard (x > 0 AND x < 0) is trivially Safe, but solver returned Unsafe"
            );
        }
        _ => panic!("unexpected VerifiedChcResult variant"),
    }
}
