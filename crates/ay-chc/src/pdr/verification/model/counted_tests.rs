// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used, clippy::panic)]

use super::{PerRule, RuleWork, PREPROCESSED_SAFE_RULE_WORK};
use crate::pdr::{InvariantModel, PdrConfig, PdrResult, PdrSolver, PredicateInterpretation};
use crate::smt::executor_work::executor_work_spent;
use crate::{AdaptiveConfig, AdaptivePortfolio, CancellationToken};
use crate::{ChcExpr, ChcParser, ChcProblem, ChcVar};
use ay_core::time::Instant;
use ntest::timeout;
use std::time::Duration;

const COUNTER: &str = r#"(set-logic HORN)
(declare-var x Int)
(declare-var x2 Int)
(declare-rel inv (Int))
(rule (=> (= x 0) (inv x)))
(rule (=> (and (inv x) (= x2 (+ x 1))) (inv x2)))
(rule (=> (and (inv x) (< x 0)) false))"#;

/// `inv := true` is valid, but its query clause is a 10-bit distributivity
/// check that the internal DPLL(T) loop cannot settle within its pre-slice
/// (it is still searching after thousands of conflicts) and the executor
/// settles at once.
const DISTRIBUTIVITY: &str = r#"(set-logic HORN)
(declare-var x (_ BitVec 10))
(declare-var y (_ BitVec 10))
(declare-var z (_ BitVec 10))
(declare-rel inv ((_ BitVec 10) (_ BitVec 10) (_ BitVec 10)))
(rule (=> (and (= x #b0000000011) (= y #b0000000101) (= z #b0000000001)) (inv x y z)))
(rule (=> (and (inv x y z) (not (= (bvmul x (bvadd y z)) (bvadd (bvmul x y) (bvmul x z)))))
          false))"#;

/// `inv := (x != 0)` is valid (2^31 - 1 is prime, so no two 16-bit factors
/// greater than one reach it), but the transition check is a factorization
/// only a long executor search refutes.
const PRIME_STEP: &str = r#"(set-logic HORN)
(declare-var x (_ BitVec 32))
(declare-var y (_ BitVec 32))
(declare-var x2 (_ BitVec 32))
(declare-rel inv ((_ BitVec 32) (_ BitVec 32)))
(rule (=> (and (= x #x00000003) (= y #x00000005)) (inv x y)))
(rule (=> (and (inv x y)
               (bvult x #x00010000) (bvult y #x00010000)
               (bvugt x #x00000001) (bvugt y #x00000001)
               (= x2 (bvsub (bvmul x y) #x7fffffff)))
          (inv x2 y)))"#;

/// The same factorization at 128 bits (2^127 - 1 is prime; x, y < 2^64). The
/// executor's proof-mode search on it spends its time in LRAT bookkeeping
/// that charges no work unit and polls only the clock. Measured with the
/// deadline as the rule's only wall: it ran to the 120 s deadline having
/// counted 2,597 units.
const PRIME_STEP_128: &str = r#"(set-logic HORN)
(declare-var x (_ BitVec 128))
(declare-var y (_ BitVec 128))
(declare-var x2 (_ BitVec 128))
(declare-rel inv ((_ BitVec 128) (_ BitVec 128)))
(rule (=> (and (= x (_ bv3 128)) (= y (_ bv5 128))) (inv x y)))
(rule (=> (and (inv x y)
               (bvult x #x00000000000000010000000000000000)
               (bvult y #x00000000000000010000000000000000)
               (bvugt x (_ bv1 128)) (bvugt y (_ bv1 128))
               (= x2 (bvsub (bvmul x y) #x7fffffffffffffffffffffffffffffff)))
          (inv x2 y)))"#;

/// A 0/1 knapsack whose target no subset reaches: `inv := true` is valid, and
/// its query clause is an infeasible linear system the proof-mode LIA search
/// refutes only slowly, at 7-14 ms per work unit. Measured with the deadline
/// as the rule's only wall: one executor run took 28-58 s and counted 4,070
/// units.
const KNAPSACK_QUERY: &str = r#"(set-logic HORN)
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)
(declare-var x6 Int)
(declare-var x7 Int)
(declare-var x8 Int)
(declare-var x9 Int)
(declare-var x10 Int)
(declare-var x11 Int)
(declare-var x12 Int)
(declare-var x13 Int)
(declare-var x14 Int)
(declare-var x15 Int)
(declare-var x16 Int)
(declare-var x17 Int)
(declare-var x18 Int)
(declare-var x19 Int)
(declare-rel inv (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int))
(rule (=> (and (= x0 0) (= x1 0) (= x2 0) (= x3 0) (= x4 0) (= x5 0) (= x6 0) (= x7 0) (= x8 0) (= x9 0)
               (= x10 0) (= x11 0) (= x12 0) (= x13 0) (= x14 0) (= x15 0) (= x16 0) (= x17 0) (= x18 0) (= x19 0))
          (inv x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19)))
(rule (=> (and (inv x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19)
               (<= 0 x0) (<= x0 1) (<= 0 x1) (<= x1 1) (<= 0 x2) (<= x2 1) (<= 0 x3) (<= x3 1)
               (<= 0 x4) (<= x4 1) (<= 0 x5) (<= x5 1) (<= 0 x6) (<= x6 1) (<= 0 x7) (<= x7 1)
               (<= 0 x8) (<= x8 1) (<= 0 x9) (<= x9 1) (<= 0 x10) (<= x10 1) (<= 0 x11) (<= x11 1)
               (<= 0 x12) (<= x12 1) (<= 0 x13) (<= x13 1) (<= 0 x14) (<= x14 1) (<= 0 x15) (<= x15 1)
               (<= 0 x16) (<= x16 1) (<= 0 x17) (<= x17 1) (<= 0 x18) (<= x18 1) (<= 0 x19) (<= x19 1)
               (= (+ (* 574354 x0) (* 686963 x1) (* 998485 x2) (* 919166 x3) (* 588269 x4)
                     (* 573780 x5) (* 632510 x6) (* 996580 x7) (* 715917 x8) (* 299126 x9)
                     (* 293630 x10) (* 942950 x11) (* 636775 x12) (* 598873 x13) (* 760479 x14)
                     (* 743782 x15) (* 931496 x16) (* 295217 x17) (* 198695 x18) (* 568286 x19))
                  6477668))
          false))"#;

/// The verifier `validate_preprocessed_safe_model` builds.
fn boundary_verifier(problem: &ChcProblem) -> PdrSolver {
    PdrSolver::new(
        problem.clone(),
        PdrConfig {
            strict_proofs: true,
            disable_array_scalarization: true,
            preserve_original_clauses: true,
            ..PdrConfig::default()
        },
    )
}

/// Validate `model` where the adaptive portfolio does, through
/// `validate_preprocessed_safe_model`, under `deadline`.
fn at_boundary(problem: &ChcProblem, model: &InvariantModel, deadline: Duration) -> bool {
    AdaptivePortfolio::new(problem.clone(), AdaptiveConfig::test_default())
        .validate_preprocessed_safe_model(
            model,
            "counted-boundary-test",
            Instant::now() + deadline,
            &CancellationToken::new(),
        )
}

fn solved_counter() -> (ChcProblem, InvariantModel) {
    let problem = ChcParser::parse(COUNTER).unwrap();
    let PdrResult::Safe(model) = PdrSolver::solve_problem(&problem, PdrConfig::default()) else {
        panic!("the counter is safe");
    };
    (problem, model)
}

/// `inv` interpreted as `formula(first argument)`.
fn inv_model(problem: &ChcProblem, formula: impl Fn(ChcExpr) -> ChcExpr) -> InvariantModel {
    let inv = problem.lookup_predicate("inv").unwrap();
    let vars: Vec<ChcVar> = problem.predicates()[inv.index()]
        .arg_sorts
        .iter()
        .enumerate()
        .map(|(i, sort)| ChcVar::new(format!("a{i}"), sort.clone()))
        .collect();
    let body = formula(ChcExpr::var(vars[0].clone()));
    let mut model = InvariantModel::new();
    model.set(inv, PredicateInterpretation::new(vars, body));
    model
}

/// The wall `open_rule_allotment` gives a counted rule when `deadline` remains.
fn counted_wall(deadline: Duration) -> (Option<Duration>, Duration) {
    let (problem, _) = solved_counter();
    let mut verifier = boundary_verifier(&problem);
    verifier.solve_deadline = Some(Instant::now() + deadline);
    let (mut budget, mut start, mut timeout) = (None, None, Duration::ZERO);
    let allowance = verifier.open_rule_allotment(
        PerRule::Counted(PREPROCESSED_SAFE_RULE_WORK),
        &mut budget,
        &mut start,
        &mut timeout,
    );
    assert!(allowance.is_some(), "a counted rule installs its allowance");
    assert!(start.is_some());
    assert!(!executor_work_spent());
    (budget, timeout)
}

#[test]
fn a_counted_rule_has_a_wall_that_follows_the_deadline() {
    // A quarter of what remains, not the 1.5 s this boundary used to cap
    // every rule at; the first check's timeout is that wall.
    let (budget, timeout) = counted_wall(Duration::from_mins(1));
    assert!(
        budget.is_some_and(|b| b > Duration::from_secs(14) && b <= Duration::from_secs(15)),
        "{budget:?}"
    );
    assert_eq!(budget, Some(timeout));
    // Never above 30 s, and never below 2 s while the deadline allows it.
    let (budget, _) = counted_wall(Duration::from_mins(10));
    assert_eq!(budget, Some(Duration::from_secs(30)));
    let (budget, _) = counted_wall(Duration::from_secs(4));
    assert_eq!(budget, Some(Duration::from_secs(2)));
    let (budget, _) = counted_wall(Duration::from_secs(1));
    assert!(
        budget.is_some_and(|b| b <= Duration::from_secs(1)),
        "{budget:?}"
    );
    // A wall budget still restarts its clock and installs nothing.
    let (problem, _) = solved_counter();
    let verifier = boundary_verifier(&problem);
    let (mut budget, mut start, mut timeout) = (Some(Duration::from_secs(2)), None, Duration::ZERO);
    let allowance =
        verifier.open_rule_allotment(PerRule::Wall, &mut budget, &mut start, &mut timeout);
    assert!(allowance.is_none());
    assert_eq!(budget, Some(Duration::from_secs(2)));
    assert!(start.is_some());
}

#[test]
fn the_boundary_admits_a_valid_model() {
    let (problem, model) = solved_counter();
    assert!(at_boundary(&problem, &model, Duration::from_mins(1)));
}

#[test]
fn the_boundary_still_refuses_a_non_inductive_model() {
    // Soundness control: the allowance only decides when a check gives up; a
    // model the check refutes (x <= 5 is not preserved by x' = x + 1) stays
    // refused.
    let (problem, _) = solved_counter();
    let wrong = inv_model(&problem, |x| ChcExpr::le(x, ChcExpr::int(5)));
    assert!(!at_boundary(&problem, &wrong, Duration::from_mins(1)));
}

#[test]
#[timeout(120_000)]
fn the_internal_pre_slice_does_not_spend_the_executor_allowance() {
    // The internal loop spends thousands of conflicts before its pre-slice
    // ends; when that work was charged to the rule's allowance, nothing was
    // left for the executor that settles the check, and this valid model was
    // refused. A 1,024-unit allowance is spent by that loop on any host.
    let problem = ChcParser::parse(DISTRIBUTIVITY).unwrap();
    let model = inv_model(&problem, |_| ChcExpr::Bool(true));
    let work = RuleWork {
        units: 1_024,
        ..PREPROCESSED_SAFE_RULE_WORK
    };
    let mut verifier = boundary_verifier(&problem);
    assert!(verifier.verify_model_per_rule_counted(
        &model,
        work,
        Instant::now() + Duration::from_mins(2)
    ));
}

#[test]
#[timeout(60_000)]
fn the_allowance_and_not_the_wall_ends_an_unsettled_search() {
    // A bound, not a goal: this model is valid, but its transition check
    // needs far more executor search than the 1,024 units allowed here. The
    // rule is refused once the allowance is spent, at the same count on every
    // host, long before its 30 s wall. (If a later executor settles this
    // check, pick a harder factorization.)
    let problem = ChcParser::parse(PRIME_STEP).unwrap();
    let model = inv_model(&problem, |x| {
        ChcExpr::not(ChcExpr::eq(x, ChcExpr::BitVec(0, 32)))
    });
    let work = RuleWork {
        units: 1_024,
        ..PREPROCESSED_SAFE_RULE_WORK
    };
    let mut verifier = boundary_verifier(&problem);
    let started = Instant::now();
    let work_before = ay_core::resource::thread_work_units();
    assert!(!verifier.verify_model_per_rule_counted(
        &model,
        work,
        Instant::now() + Duration::from_mins(10)
    ));
    assert!(
        started.elapsed() < Duration::from_secs(15),
        "{:?}",
        started.elapsed()
    );
    let spent = ay_core::resource::thread_work_units() - work_before;
    assert!(spent >= work.units, "spent {spent}");
}

#[test]
#[timeout(120_000)]
fn a_transition_the_count_cannot_stop_ends_at_the_rule_wall_not_the_deadline() {
    // A bound, not a goal: the model is valid, but the executor run on its
    // transition outlives the allowance in phases that charge no work. The
    // rule's wall (a quarter of the 40 s deadline) ends it; with the deadline
    // as the only wall it ran for all 40 s.
    let problem = ChcParser::parse(PRIME_STEP_128).unwrap();
    let model = inv_model(&problem, |x| {
        ChcExpr::not(ChcExpr::eq(x, ChcExpr::BitVec(0, 128)))
    });
    let started = Instant::now();
    assert!(!at_boundary(&problem, &model, Duration::from_secs(40)));
    assert!(
        started.elapsed() < Duration::from_secs(25),
        "{:?}",
        started.elapsed()
    );
}

#[test]
#[timeout(120_000)]
fn a_query_clause_the_count_cannot_stop_ends_at_the_rule_wall_not_the_deadline() {
    // A bound, not a goal: as above, for a query clause, whose checks retry
    // past an expired rule budget.
    let problem = ChcParser::parse(KNAPSACK_QUERY).unwrap();
    let model = inv_model(&problem, |_| ChcExpr::Bool(true));
    let started = Instant::now();
    assert!(!at_boundary(&problem, &model, Duration::from_secs(40)));
    assert!(
        started.elapsed() < Duration::from_secs(25),
        "{:?}",
        started.elapsed()
    );
}
