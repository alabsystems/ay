// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! Regression tests for BMC soundness bug (#103)
//!
//! Issue: BMC ignores predicate applications in query clause bodies.
//! For a query like `P(x) ∧ x >= 5 => false`, BMC only checks `x >= 5`
//! without verifying that P actually holds - producing false counterexamples.
//!
//! These tests MUST fail (when run) if the bug exists.
//!
//! NOTE: Some benchmark-based tests in this module are ignored by default because they can be
//! very slow and may block the org-wide cargo lock (see #390).
//! - Run ignored tests only: `cargo test -p ay-chc --test bmc_soundness -- --ignored`
//! - Run all tests: `cargo test -p ay-chc --test bmc_soundness -- --include-ignored`

use ay_chc::{testing, BmcConfig, ChcEngineResult};
use ay_chc::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};
use ntest::timeout;

/// Create a CHC problem that is SAFE but BMC incorrectly reports UNSAFE.
///
/// The problem:
/// - Fact: x = 0 => Inv(x)                 // Initial state
/// - Transition: Inv(x) ∧ x < 3 => Inv(x+1)  // Increment only if x < 3
/// - Query: Inv(x) ∧ x >= 10 => false      // Assert x never reaches 10
///
/// This is SAFE because x can only reach values {0, 1, 2, 3} due to the guard.
/// The bug: BMC ignores Inv(x) in the query and just checks if x >= 10 is
/// satisfiable at some step, which it trivially is without predicate constraints.
fn create_bmc_soundness_bug_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Fact: x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Transition: Inv(x) ∧ x < 3 => Inv(x + 1)
    // The guard `x < 3` means x can only reach {0, 1, 2, 3}
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

    // Query: Inv(x) ∧ x >= 10 => false
    // This should be SAFE because Inv can never hold for x >= 10
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])], // Body predicate - BMC bug ignores this!
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    problem
}

/// Regression test for #103: BMC must NOT return Unsafe on safe problems.
///
/// Before fix: BMC returns Unsafe because it ignores Inv(x) in the query body.
/// After fix: BMC returns Unknown because it can't find a valid counterexample.
///
/// Timeout: 1s (measured <10ms)
#[test]
#[timeout(1_000)]
fn test_bmc_soundness_issue_103() {
    let problem = create_bmc_soundness_bug_problem();
    // Keep this test fast: the bug triggers immediately (spurious UNSAFE)
    // regardless of unroll depth.
    let config = BmcConfig::with_engine_config(0, false, None);
    let solver = testing::new_bmc_solver(problem, config);
    let result = solver.solve();

    match result {
        ChcEngineResult::Unknown => {
            // CORRECT: BMC cannot prove safety, but also cannot find a valid
            // counterexample because there isn't one.
        }
        ChcEngineResult::Unsafe(cex) => {
            panic!(
                "BMC SOUNDNESS BUG: Incorrectly reported UNSAFE at depth {}.\n\
                 This is a SAFE problem - x never reaches 10 due to the x < 3 guard.\n\
                 Bug: BMC ignores body predicates in query clauses.\n\
                 See issue #103.",
                cex.steps.len()
            );
        }
        ChcEngineResult::Safe(_) => {
            // Also acceptable: BMC proves safety
        }
        ChcEngineResult::NotApplicable => panic!("unexpected NotApplicable"),
        _ => panic!("unexpected ChcEngineResult variant"),
    }
}

/// Test that BMC fails closed when a query has no replayable predicate trace.
///
/// The problem:
/// - Query: x >= 5 => false            // No predicate in body, just constraint
///
/// The query constraint is satisfiable with a free `x`, but there is no
/// predicate derivation trace to replay. BMC must not expose this as UNSAFE
/// unless it can provide replayable original-CHC witness material.
///
/// Timeout: 1s (measured <10ms)
#[test]
#[timeout(1_000)]
fn test_bmc_correct_unsafe_no_body_predicate() {
    let mut problem = ChcProblem::new();
    problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Query: x >= 5 => false (NOTE: No Inv(x) in body - just a constraint)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5))),
        ClauseHead::False,
    ));

    let config = BmcConfig::with_engine_config(0, false, None);
    let solver = testing::new_bmc_solver(problem, config);
    let result = solver.solve();

    match result {
        ChcEngineResult::Unsafe(cex) => {
            panic!(
                "BMC must fail closed without a replayable derivation witness; got {} steps",
                cex.steps.len()
            );
        }
        ChcEngineResult::Unknown => {
            // Correct: satisfiable bodyless query without replayable trace.
        }
        ChcEngineResult::Safe(_) => {
            panic!("BMC should not report Safe on this unsafe problem");
        }
        ChcEngineResult::NotApplicable => panic!("unexpected NotApplicable"),
        _ => panic!("unexpected ChcEngineResult variant"),
    }
}

/// Variant: Query has ONLY a body predicate, no constraint.
///
/// Query: Inv(x) => false
///
/// This is UNSAFE because Inv can be established from the fact clause.
///
/// Timeout: 1s (measured <10ms)
#[test]
#[timeout(1_000)]
fn test_bmc_query_with_only_body_predicate() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Fact: true => Inv(0)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(inv, vec![ChcExpr::int(0)]),
    ));

    // Query: Inv(x) => false
    // This is UNSAFE because Inv(0) holds from the fact
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x)])]),
        ClauseHead::False,
    ));

    let config = BmcConfig::with_engine_config(0, false, None);
    let solver = testing::new_bmc_solver(problem, config);
    let result = solver.solve();

    match result {
        ChcEngineResult::Unsafe(cex) => {
            // depth 0 = initial state only = 1 step in the trace
            assert_eq!(
                cex.steps.len(),
                1,
                "Expected counterexample at depth 0 (1 step), got {} steps",
                cex.steps.len()
            );
        }
        ChcEngineResult::Unknown => {
            panic!("BMC should find the depth-0 counterexample");
        }
        ChcEngineResult::Safe(_) => {
            panic!("BMC should not report Safe on this unsafe problem");
        }
        ChcEngineResult::NotApplicable => panic!("unexpected NotApplicable"),
        _ => panic!("unexpected ChcEngineResult variant"),
    }
}

// ============================================================================
// dillig01 Benchmark BMC Soundness Test (re-added per #624)
// ============================================================================

use ay_chc::ChcParser;

/// Regression test for #103 using actual dillig01 benchmark.
///
/// This benchmark is confirmed SAFE by Z3 (returns `sat`).
/// BMC must NOT return Unsafe on it.
///
/// Timeout: 60s (may be slow)
#[test]
#[timeout(60_000)]
fn test_bmc_soundness_dillig01() {
    // Embedded benchmark: dillig01.c_000.smt2 (#981: hermetic tests)
    let content = r#"(set-logic HORN)


(declare-fun |state| ( Bool Bool Bool Bool Int Int Int Int ) Bool)

(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Int) (E Int) (F Int) (G Int) (H Bool) )
    (=>
      (and
        (and (not B) (= A true) (not H) (not C))
      )
      (state C A B H D E F G)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Bool) )
    (=>
      (and
        (state C A B Q I K M O)
        (let ((a!1 (and (not G)
                F
                E
                (not D)
                (= I H)
                (= K J)
                (= O N)
                (= (+ I K (* (- 1) L)) 0)))
      (a!2 (and (not G) F E D (= I H) (= K J) (= M L) (= (+ I K (* (- 1) N)) 0)))
      (a!3 (and G (not F) E D (= I H) (= K J) (= M L) (= O N)))
      (a!4 (and (not G) (not F) (not E) (not D) (= I H) (= K J) (= M L) (= O N))))
  (and (or A
           B
           C
           (not Q)
           (not (<= 1 O))
           (and G (not F) (not E) D (= I H) (= K J) (= M L) (= O N)))
       (or A
           B
           Q
           (not C)
           (= P 0)
           (and G (not F) (not E) (not D) (= I H) (= K J) (= M L) (= O N)))
       (or A
           B
           Q
           (not C)
           (not (= P 0))
           (and (not G) (not F) E D (= I H) (= K J) (= M L) (= O N)))
       (or C Q (not B) (not A) a!1)
       (or A Q (not B) (not C) a!2)
       (or B (not Q) (not C) (not A) a!3)
       (or B
           C
           (not Q)
           (not A)
           (and G (not F) E (not D) (= I H) (= K J) (= M L) (= O N)))
       (or Q
           (not B)
           (not C)
           (not A)
           (and (not G) (not F) E (not D) (= I H) (= K J) (= M L) (= O N)))
       (or A B C Q a!4)
       (or A B (not Q) (not C) a!4)
       (or B
           Q
           (not C)
           (not A)
           (and (not G) F (not E) (not D) (= H M) (= K J) (= M L) (= O N)))
       (or A
           C
           Q
           (not B)
           (and (not G) F (not E) D (= J O) (= I H) (= M L) (= O N)))
       (or B
           C
           Q
           (not A)
           (and (not G) (not F) E (not D) (= N 1) (= L 1) (= I H) (= K J)))
       (or A B C (not Q) (<= 1 O) a!3)))
      )
      (state E D F G H J L N)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Int) (E Int) (F Int) (G Int) (H Bool) )
    (=>
      (and
        (state C A B H D E F G)
        (and (not B) (= A true) (= H true) (= C true))
      )
      false
    )
  )
)

(check-sat)
(exit)
"#;
    let problem = ChcParser::parse(content).expect("parse benchmark");

    let config = BmcConfig::with_engine_config(0, false, None);
    let solver = testing::new_bmc_solver(problem, config);
    let result = solver.solve();

    match result {
        ChcEngineResult::Unknown => {
            // CORRECT: BMC cannot prove safety but also cannot find a counterexample
        }
        ChcEngineResult::Unsafe(cex) => {
            panic!(
                "BMC SOUNDNESS BUG (#103): dillig01.c_000.smt2 is SAFE (Z3 says sat),\n\
                 but BMC incorrectly reported UNSAFE at depth {}.\n\
                 Bug: BMC ignores body predicates in query clauses.",
                cex.steps.len()
            );
        }
        ChcEngineResult::Safe(_) => {
            // Also acceptable: BMC proves safety
        }
        ChcEngineResult::NotApplicable => panic!("unexpected NotApplicable"),
        _ => panic!("unexpected ChcEngineResult variant"),
    }
}
