// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! Soundness tests for CHC preprocessing pipeline.
//!
//! These tests verify that preprocessing transformations preserve satisfiability:
//! - A SAFE problem must remain SAFE after preprocessing.
//! - An UNSAFE problem must remain UNSAFE after preprocessing.
//! - The portfolio with preprocessing ON must agree with preprocessing OFF.
//!
//! The preprocessing pipeline includes:
//! - `expand_mod_div_in_clauses` (mod/div -> fresh variables with Euclidean axioms)
//! - `expand_nullary_fail_queries` (nullary fail predicate -> direct queries)
//! - `ClauseInliner` (inline single-use predicates)
//! - `DeadParamEliminator` (remove unused predicate parameters)
//! - `LocalVarEliminator` (substitute equality-defined variables)
//! - `BvToBoolBitBlaster` / `BvToIntAbstractor` (bit-vector transformations)
//!
//! Part of #209: formal verification of CHC engine.

use ay_chc::{
    engines, testing, BmcConfig, ChcExpr, ChcParser, ChcProblem, ChcSort, ChcVar, ClauseBody,
    ClauseHead, EngineConfig, HornClause, PdrConfig, PortfolioConfig, PortfolioResult,
};
use ntest::timeout;
use std::time::Duration;

// ============================================================================
// Helper: compare results with preprocessing on vs. off
// ============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Safety {
    Safe,
    Unsafe,
    Unknown,
}

impl From<PortfolioResult> for Safety {
    fn from(r: PortfolioResult) -> Self {
        match r {
            PortfolioResult::Safe(_) => Self::Safe,
            PortfolioResult::Unsafe(_) => Self::Unsafe,
            _ => Self::Unknown,
        }
    }
}

fn run_portfolio(problem: ChcProblem, preprocessing: bool) -> Safety {
    // Use test_default() (PDR + BMC + Kind) to reduce thread count from 12 to 3.
    // This is sufficient for preprocessing soundness testing.
    let config = PortfolioConfig::test_default()
        .parallel_timeout(Some(Duration::from_secs(10)))
        .preprocessing(preprocessing);

    let solver = engines::new_portfolio_solver(problem, config);
    Safety::from(solver.solve())
}

/// Verify that preprocessing does not flip a definitive result.
/// If both runs produce definitive (non-Unknown) results, they must agree.
fn assert_preprocessing_preserves_result(problem: ChcProblem, label: &str) {
    let with_pp = run_portfolio(problem.clone(), true);
    let without_pp = run_portfolio(problem, false);

    // Only check when both are definitive
    if with_pp != Safety::Unknown && without_pp != Safety::Unknown {
        assert_eq!(
            with_pp, without_pp,
            "PREPROCESSING SOUNDNESS BUG on {label}: \
             preprocessing={with_pp:?} vs no-preprocessing={without_pp:?}. \
             The preprocessing pipeline changed the answer."
        );
    }
}

// ============================================================================
// Test: mod/div expansion preserves satisfiability
// ============================================================================

/// A problem with mod that is SAFE: x starts at 0, increments by 1.
/// Invariant: (mod x 3) < 3 always holds.
///
/// The mod/div preprocessing expands `(mod x 3)` into fresh variables with
/// Euclidean axioms. This test verifies the expansion preserves safety.
///
/// Timeout: 30s
#[test]
#[timeout(30_000)]
fn test_mod_expansion_preserves_safe() {
    let smt = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)

(assert (forall ((x Int))
  (=> (= x 0) (Inv x))))

(assert (forall ((x Int) (x2 Int))
  (=> (and (Inv x) (= x2 (+ x 1)))
      (Inv x2))))

(assert (forall ((x Int))
  (=> (and (Inv x) (>= (mod x 3) 3))
      false)))

(check-sat)
"#;
    let problem = ChcParser::parse(smt).expect("parse mod-safe problem");
    assert_preprocessing_preserves_result(problem, "mod_expansion_safe");
}

/// A problem with mod that is UNSAFE: x starts at 0, increments by 1.
/// Query: x >= 0 AND (mod x 5) = 0 => false, which is violated when x = 5.
///
/// Timeout: 30s
#[test]
#[timeout(30_000)]
fn test_mod_expansion_preserves_unsafe() {
    let smt = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)

(assert (forall ((x Int))
  (=> (= x 0) (Inv x))))

(assert (forall ((x Int) (x2 Int))
  (=> (and (Inv x) (= x2 (+ x 1)))
      (Inv x2))))

(assert (forall ((x Int))
  (=> (and (Inv x) (> x 0) (= (mod x 5) 0))
      false)))

(check-sat)
"#;
    let problem = ChcParser::parse(smt).expect("parse mod-unsafe problem");
    assert_preprocessing_preserves_result(problem, "mod_expansion_unsafe");
}

// ============================================================================
// Test: nullary fail predicate expansion preserves satisfiability
// ============================================================================

/// Problem using the nullary "fail" pattern common in CHC-COMP benchmarks.
/// The system is SAFE.
///
/// Pattern:
///   init => Inv(x)
///   Inv(x) AND x < 5 => Inv(x + 1)
///   Inv(x) AND x >= 100 => fail
///   fail => false
///
/// Timeout: 30s
#[test]
#[timeout(30_000)]
fn test_nullary_fail_expansion_preserves_safe() {
    let smt = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(declare-fun fail () Bool)

(assert (forall ((x Int))
  (=> (= x 0) (Inv x))))

(assert (forall ((x Int) (x2 Int))
  (=> (and (Inv x) (< x 5) (= x2 (+ x 1)))
      (Inv x2))))

(assert (forall ((x Int))
  (=> (and (Inv x) (>= x 100))
      fail)))

(assert (=> fail false))

(check-sat)
"#;
    let problem = ChcParser::parse(smt).expect("parse nullary-fail-safe problem");
    assert_preprocessing_preserves_result(problem, "nullary_fail_safe");
}

/// Same nullary fail pattern but the system is UNSAFE.
///
/// Pattern:
///   init => Inv(x)
///   Inv(x) => Inv(x + 1)     (unbounded)
///   Inv(x) AND x >= 5 => fail
///   fail => false
///
/// Timeout: 30s
#[test]
#[timeout(30_000)]
fn test_nullary_fail_expansion_preserves_unsafe() {
    let smt = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(declare-fun fail () Bool)

(assert (forall ((x Int))
  (=> (= x 0) (Inv x))))

(assert (forall ((x Int) (x2 Int))
  (=> (and (Inv x) (= x2 (+ x 1)))
      (Inv x2))))

(assert (forall ((x Int))
  (=> (and (Inv x) (>= x 5))
      fail)))

(assert (=> fail false))

(check-sat)
"#;
    let problem = ChcParser::parse(smt).expect("parse nullary-fail-unsafe problem");
    assert_preprocessing_preserves_result(problem, "nullary_fail_unsafe");
}

// ============================================================================
// Test: clause inlining preserves satisfiability
// ============================================================================

/// Multi-predicate SAFE problem where ClauseInliner should inline intermediate
/// predicates. After inlining, the safety result must be preserved.
///
/// Pattern:
///   init(0) => P(x)
///   P(x) AND x < 5 => Q(x + 1)
///   Q(x) => P(x)
///   P(x) AND x >= 100 => false
///
/// (P and Q cycle but x is bounded by < 5 guard)
///
/// Timeout: 30s
#[test]
#[timeout(30_000)]
fn test_clause_inlining_preserves_safe_multi_pred() {
    let smt = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)

(assert (forall ((x Int))
  (=> (= x 0) (P x))))

(assert (forall ((x Int) (x2 Int))
  (=> (and (P x) (< x 5) (= x2 (+ x 1)))
      (Q x2))))

(assert (forall ((x Int))
  (=> (Q x) (P x))))

(assert (forall ((x Int))
  (=> (and (P x) (>= x 100))
      false)))

(check-sat)
"#;
    let problem = ChcParser::parse(smt).expect("parse multi-pred-safe problem");
    assert_preprocessing_preserves_result(problem, "clause_inlining_safe");
}

/// Multi-predicate UNSAFE problem where inlining must preserve the counterexample.
///
/// Pattern:
///   init(0) => P(x)
///   P(x) => Q(x + 1)
///   Q(x) => P(x)
///   P(x) AND x > 3 => false
///
/// Timeout: 30s
#[test]
#[timeout(30_000)]
fn test_clause_inlining_preserves_unsafe_multi_pred() {
    let smt = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)

(assert (forall ((x Int))
  (=> (= x 0) (P x))))

(assert (forall ((x Int) (x2 Int))
  (=> (and (P x) (= x2 (+ x 1)))
      (Q x2))))

(assert (forall ((x Int))
  (=> (Q x) (P x))))

(assert (forall ((x Int))
  (=> (and (P x) (> x 3))
      false)))

(check-sat)
"#;
    let problem = ChcParser::parse(smt).expect("parse multi-pred-unsafe problem");
    assert_preprocessing_preserves_result(problem, "clause_inlining_unsafe");
}

// ============================================================================
// Test: dead parameter elimination preserves satisfiability
// ============================================================================

/// A problem with a dead parameter (y is never queried and doesn't affect safety).
/// After dead parameter elimination, the result must be preserved.
///
/// Timeout: 30s
#[test]
#[timeout(30_000)]
fn test_dead_param_elim_preserves_safe() {
    let smt = r#"
(set-logic HORN)
(declare-fun Inv (Int Int) Bool)

(assert (forall ((x Int) (y Int))
  (=> (and (= x 0) (= y 42))
      (Inv x y))))

(assert (forall ((x Int) (y Int) (x2 Int) (y2 Int))
  (=> (and (Inv x y) (< x 5) (= x2 (+ x 1)) (= y2 (+ y 1)))
      (Inv x2 y2))))

(assert (forall ((x Int) (y Int))
  (=> (and (Inv x y) (>= x 100))
      false)))

(check-sat)
"#;
    let problem = ChcParser::parse(smt).expect("parse dead-param-safe problem");
    assert_preprocessing_preserves_result(problem, "dead_param_elim_safe");
}

// ============================================================================
// Test: Safe proof verification via PDR model checker
// ============================================================================

/// Verify that when the portfolio returns Safe WITH preprocessing,
/// the invariant model can be verified against the ORIGINAL problem.
///
/// This catches bugs where preprocessing transforms the problem in a way
/// that the model is valid for the transformed problem but not the original.
///
/// Timeout: 30s
#[test]
#[timeout(30_000)]
fn test_safe_proof_verified_against_original() {
    // A simple safe problem
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);

    // Init: x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Trans: Inv(x) AND x < 10 AND x_next = x + 1 => Inv(x_next)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::and(
                ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10)),
                ChcExpr::eq(
                    ChcExpr::var(x_next.clone()),
                    ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                ),
            )),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x_next)]),
    ));

    // Query: Inv(x) AND x < 0 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    // Solve with preprocessing enabled
    let config = PortfolioConfig::test_default()
        .parallel_timeout(Some(Duration::from_secs(10)))
        .preprocessing(true);
    let solver = engines::new_portfolio_solver(problem.clone(), config);
    let result = solver.solve();

    match result {
        PortfolioResult::Safe(model) => {
            // Verify the model against the ORIGINAL problem using PDR verifier
            let mut verifier = testing::new_pdr_solver(problem, PdrConfig::default());
            assert!(
                verifier.verify_model(&model),
                "PREPROCESSING SOUNDNESS BUG: Portfolio returned Safe with preprocessing, \
                 but the model fails verification against the original problem. \
                 The preprocessing pipeline may have altered the problem's semantics."
            );
        }
        PortfolioResult::Unknown | PortfolioResult::NotApplicable => {
            // Acceptable: engines didn't converge
        }
        PortfolioResult::Unsafe(_) => {
            panic!(
                "Portfolio returned Unsafe on a safe problem (x starts at 0, \
                 bounded by < 10, query x < 0)"
            );
        }
        _ => panic!("unexpected variant"),
    }
}

// ============================================================================
// Test: cross-engine agreement on benchmark problems
// ============================================================================

/// Cross-validate that the portfolio catches PDR false-Safe on an UNSAFE problem.
///
/// This tests a simple unbounded counter where x starts at 0, grows by 1
/// each step, and the query says x >= 3 => false (reachable after 3 steps).
///
/// PDR alone may return Safe with a non-inductive invariant (observed:
/// `0 <= x < 2`). However, the portfolio must reject this via verify_model
/// and fall through to BMC's counterexample.
///
/// Timeout: 30s
#[test]
#[timeout(30_000)]
fn test_cross_engine_portfolio_catches_pdr_false_safe() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Init: x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Trans: Inv(x) => Inv(x + 1) (unbounded)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Query: Inv(x) AND x >= 3 => false  (UNSAFE: x grows without bound)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(3))),
        ),
        ClauseHead::False,
    ));

    // Run BMC standalone: must find the counterexample
    let bmc_result = testing::new_bmc_solver(
        problem.clone(),
        BmcConfig::with_engine_config(10, false, None),
    )
    .solve();
    assert!(
        matches!(bmc_result, ay_chc::ChcEngineResult::Unsafe(_)),
        "BMC should find counterexample for trivial unsafe counter, got {bmc_result:?}"
    );

    // Run the PORTFOLIO (which includes PDR + BMC + verify_model validation).
    // The portfolio must NOT return Safe, because verify_model should catch
    // the non-inductive PDR invariant.
    let config = PortfolioConfig::with_engines(vec![
        EngineConfig::Pdr(PdrConfig::default()),
        EngineConfig::Bmc(BmcConfig::with_engine_config(10, false, None)),
    ])
    .parallel_timeout(Some(Duration::from_secs(10)));

    let portfolio_result = engines::new_portfolio_solver(problem, config).solve();

    assert!(
        !matches!(portfolio_result, PortfolioResult::Safe(_)),
        "PORTFOLIO SOUNDNESS BUG: BMC finds counterexample at x=3, \
         but portfolio returned Safe. verify_model should reject \
         non-inductive PDR invariants."
    );
}

/// Cross-validate PDR vs Kind on a SAFE bounded problem.
///
/// Timeout: 30s (release only - too slow in debug)
#[cfg(not(debug_assertions))]
#[test]
#[timeout(30_000)]
fn test_cross_engine_pdr_vs_kind_safe() {
    use ay_chc::{KindConfig, KindResult, PdrResult};

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Init: x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Trans: Inv(x) AND x < 5 => Inv(x + 1)
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

    // Query: Inv(x) AND x > 100 => false  (SAFE: x in {0..5})
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(100))),
        ),
        ClauseHead::False,
    ));

    // Run PDR
    let pdr_result = testing::new_pdr_solver(problem.clone(), PdrConfig::default()).solve();

    // Run Kind
    let kind_config = KindConfig::with_engine_config(
        20,
        Duration::from_secs(2),
        Duration::from_secs(10),
        false,
        None,
    );
    let kind_result = testing::new_kind_solver(problem, kind_config).solve();

    // PDR should solve this
    assert!(
        matches!(pdr_result, PdrResult::Safe(_)),
        "PDR should prove trivial bounded counter safe, got {pdr_result:?}"
    );

    // Kind must not claim Unsafe
    assert!(
        !matches!(kind_result, KindResult::Unsafe(_)),
        "CROSS-ENGINE DISAGREEMENT: PDR says Safe but Kind says Unsafe"
    );
}

// ============================================================================
// Test: ITE in preprocessing preserves satisfiability
// ============================================================================

/// Verify that ITE expressions survive preprocessing correctly.
/// ITE in transition clauses is a common source of soundness bugs (see #187).
///
/// Timeout: 30s
#[test]
#[timeout(30_000)]
fn test_preprocessing_preserves_ite_semantics() {
    let smt = r#"
(set-logic HORN)
(declare-fun Inv (Int Int) Bool)

; Init: x = 0, y = 0
(assert (forall ((x Int) (y Int))
  (=> (and (= x 0) (= y 0))
      (Inv x y))))

; Trans: x' = x + 1, y' = ite(x >= 0, y + 1, y - 1)
; Since x starts at 0 and grows, x >= 0 is always true, so y always grows.
(assert (forall ((x Int) (y Int) (x2 Int) (y2 Int))
  (=> (and (Inv x y)
           (= x2 (+ x 1))
           (= y2 (ite (>= x 0) (+ y 1) (- y 1))))
      (Inv x2 y2))))

; Query: y < 0 => false (SAFE: y starts at 0, always incremented since x >= 0)
(assert (forall ((x Int) (y Int))
  (=> (and (Inv x y) (< y 0))
      false)))

(check-sat)
"#;
    let problem = ChcParser::parse(smt).expect("parse ITE problem");
    assert_preprocessing_preserves_result(problem, "ite_semantics");
}

// ============================================================================
// Test: combined preprocessing on benchmarks from the examples directory
// ============================================================================

/// Solve counter_safe.smt2 with and without preprocessing. Results must agree.
///
/// Timeout: 30s
#[test]
#[timeout(30_000)]
fn test_preprocessing_counter_safe_example() {
    let content = include_str!("../../examples/counter_safe.smt2");
    let problem = ChcParser::parse(content).expect("parse counter_safe.smt2");
    assert_preprocessing_preserves_result(problem, "counter_safe.smt2");
}

/// Solve counter_unsafe.smt2 with and without preprocessing. Results must agree.
///
/// Timeout: 30s
#[test]
#[timeout(30_000)]
fn test_preprocessing_counter_unsafe_example() {
    let content = include_str!("../../examples/counter_unsafe.smt2");
    let problem = ChcParser::parse(content).expect("parse counter_unsafe.smt2");
    assert_preprocessing_preserves_result(problem, "counter_unsafe.smt2");
}

/// Solve bounded_loop.smt2 with and without preprocessing. Results must agree.
///
/// Timeout: 30s
#[test]
#[timeout(30_000)]
fn test_preprocessing_bounded_loop_example() {
    let content = include_str!("../../examples/bounded_loop.smt2");
    let problem = ChcParser::parse(content).expect("parse bounded_loop.smt2");
    assert_preprocessing_preserves_result(problem, "bounded_loop.smt2");
}

// ============================================================================
// Test: expand_mod_div_in_clauses unit-level soundness
// ============================================================================

/// Direct test of expand_mod_div_in_clauses: verify the expansion axioms are
/// equisatisfiable with the original problem on a concrete case.
///
/// Problem: x starts at 0, increments by 1, query: (mod x 3) = 1 AND x > 0 => false
/// (UNSAFE: x=1 has mod 3 = 1)
///
/// Timeout: 30s
#[test]
#[timeout(30_000)]
fn test_expand_mod_div_equisatisfiable() {
    let smt = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)

(assert (forall ((x Int))
  (=> (= x 0) (Inv x))))

(assert (forall ((x Int) (x2 Int))
  (=> (and (Inv x) (= x2 (+ x 1)))
      (Inv x2))))

(assert (forall ((x Int))
  (=> (and (Inv x) (> x 0) (= (mod x 3) 1))
      false)))

(check-sat)
"#;
    let problem = ChcParser::parse(smt).expect("parse mod-div problem");

    // Solve the original
    let original_result = {
        let config = PortfolioConfig::test_default()
            .parallel_timeout(Some(Duration::from_secs(10)))
            .preprocessing(false);
        Safety::from(engines::new_portfolio_solver(problem.clone(), config).solve())
    };

    // Solve with mod/div expansion via preprocessing
    let expanded_result = {
        let config = PortfolioConfig::test_default()
            .parallel_timeout(Some(Duration::from_secs(10)))
            .preprocessing(true);
        Safety::from(engines::new_portfolio_solver(problem, config).solve())
    };

    // Both should agree this is Unsafe
    if original_result != Safety::Unknown && expanded_result != Safety::Unknown {
        assert_eq!(
            original_result, expanded_result,
            "mod/div expansion changed the result: original={original_result:?}, expanded={expanded_result:?}"
        );
    }
}

// ============================================================================
// Test: two-predicate chain with intermediate constraint
// ============================================================================

/// Two-predicate chain where the intermediate predicate adds a constraint.
/// After clause inlining, the constraint must be preserved.
///
/// P(x) with x = 0  =>  Q(x) with x < 10  =>  P(x+1) with loop
/// Query: P(x) AND x >= 100 => false
///
/// This is SAFE (bounded by x < 10 guard in Q).
///
/// Timeout: 30s
#[test]
#[timeout(30_000)]
fn test_inlining_preserves_intermediate_constraints() {
    let smt = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)

; init: P(0)
(assert (forall ((x Int))
  (=> (= x 0) (P x))))

; P(x) AND x < 10 => Q(x)
(assert (forall ((x Int))
  (=> (and (P x) (< x 10))
      (Q x))))

; Q(x) => P(x + 1)
(assert (forall ((x Int) (x2 Int))
  (=> (and (Q x) (= x2 (+ x 1)))
      (P x2))))

; query: P(x) AND x >= 100 => false (SAFE: x bounded by < 10)
(assert (forall ((x Int))
  (=> (and (P x) (>= x 100))
      false)))

(check-sat)
"#;
    let problem = ChcParser::parse(smt).expect("parse chain problem");
    let result = run_portfolio(problem, true);

    // The system is safe - x is bounded by the x < 10 guard
    assert!(
        result != Safety::Unsafe,
        "PREPROCESSING BUG: intermediate constraint lost during inlining. \
         The x < 10 guard through Q should prevent x from reaching 100."
    );
}
