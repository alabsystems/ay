// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used, clippy::panic)]

use super::{
    draw_executor_work, executor_work_spent, narrow_internal_slice, ExecutorDraw, ExecutorWork,
    ScopedExecutorWork, ALLOWANCE,
};
use crate::smt::{SmtContext, SmtResult};
use crate::{ChcExpr, ChcParser};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::time::Instant;
use ntest::timeout;
use std::cell::Cell;
use std::time::Duration;

fn allowance(units: u64, round_trips: u64) -> ExecutorWork {
    ExecutorWork {
        units,
        round_trips,
        internal_slice: Duration::from_millis(375),
    }
}

fn installed() -> Option<ExecutorWork> {
    ALLOWANCE.with(Cell::get)
}

#[test]
fn without_an_allowance_a_run_is_unmetered() {
    assert!(installed().is_none());
    assert!(matches!(draw_executor_work(), ExecutorDraw::Unmetered));
    assert!(!executor_work_spent());
    let slice = Duration::from_secs(2);
    assert_eq!(narrow_internal_slice(slice), slice);
}

#[test]
fn a_run_is_charged_the_work_it_spends() {
    let _allowance = ScopedExecutorWork::install(allowance(100, 10));
    assert_eq!(
        narrow_internal_slice(Duration::from_secs(2)),
        Duration::from_millis(375)
    );
    assert_eq!(
        narrow_internal_slice(Duration::from_millis(25)),
        Duration::from_millis(25),
        "a narrower slice stays as it is"
    );
    {
        let ExecutorDraw::Open(_draw) = draw_executor_work() else {
            panic!("an unspent allowance opens the run");
        };
        ay_core::resource::work().add_sat_work(40, 0);
        for _ in 0..3 {
            ay_core::resource::work().note_round_trip();
        }
    }
    let left = installed().unwrap();
    // A round trip is a work unit as well.
    assert_eq!((left.units, left.round_trips), (57, 7));
    assert!(!executor_work_spent());
}

#[test]
fn a_spent_allowance_stops_the_run_and_refuses_the_next() {
    let _allowance = ScopedExecutorWork::install(allowance(10, 10));
    {
        let ExecutorDraw::Open(_draw) = draw_executor_work() else {
            panic!("an unspent allowance opens the run");
        };
        assert!(!ay_core::resource::work_ceiling_reached());
        ay_core::resource::work().add_sat_work(10, 0);
        assert!(
            ay_core::resource::work_ceiling_reached(),
            "the run's own stop polls see the spent allowance"
        );
    }
    assert!(
        !ay_core::resource::work_ceiling_reached(),
        "only while the run is open"
    );
    assert!(executor_work_spent());
    assert!(matches!(draw_executor_work(), ExecutorDraw::Spent));
}

#[test]
fn a_scope_restores_the_allowance_around_it() {
    let outer = ScopedExecutorWork::install(allowance(100, 10));
    {
        let _inner = ScopedExecutorWork::install(allowance(0, 10));
        assert!(executor_work_spent());
    }
    assert_eq!(installed(), Some(allowance(100, 10)));
    drop(outer);
    assert!(installed().is_none());
}

/// A query only search refutes: 2^31 - 1 is prime, so it has no factorization
/// into two 16-bit numbers greater than one.
fn prime_product_query() -> ChcExpr {
    let problem = ChcParser::parse(
        r#"(set-logic HORN)
(declare-var x (_ BitVec 32))
(declare-var y (_ BitVec 32))
(declare-rel inv ((_ BitVec 32) (_ BitVec 32)))
(rule (=> (and (= x #x00000003) (= y #x00000005)) (inv x y)))
(rule (=> (and (inv x y)
               (bvult x #x00010000) (bvult y #x00010000)
               (bvugt x #x00000001) (bvugt y #x00000001)
               (= (bvmul x y) #x7fffffff))
          false))"#,
    )
    .unwrap();
    let query = problem.clauses().iter().find(|c| c.is_query()).unwrap();
    query.body.constraint.clone().unwrap()
}

#[test]
#[timeout(300_000)]
fn an_executor_run_stops_at_its_allowance_and_not_at_its_wall() {
    let query = prime_product_query();
    let run = || {
        let _allowance = ScopedExecutorWork::install(allowance(256, 256));
        let smt = SmtContext::new();
        let before = ay_core::resource::thread_work_units();
        let started = Instant::now();
        let result =
            smt.check_sat_via_executor(&query, &FxHashMap::default(), Duration::from_mins(10));
        let spent = ay_core::resource::thread_work_units() - before;
        (result, spent, started.elapsed(), executor_work_spent())
    };
    let (result, spent, elapsed, exhausted) = run();
    assert!(matches!(result, SmtResult::Unknown), "{result:?}");
    assert!(
        exhausted,
        "the allowance, not the 600 s wall, ended the run"
    );
    assert!(spent >= 256, "spent {spent}");
    assert!(elapsed < Duration::from_mins(5), "{elapsed:?}");
    // A count stops the same input at the same step, however long it took.
    let (_, spent_again, _, _) = run();
    assert_eq!(spent, spent_again);
}

/// `inv := true` is valid; its query clause (10-bit distributivity) is
/// settled by an executor run.
const BOUNDARY_DISTRIBUTIVITY: &str = r#"(set-logic HORN)
(declare-var x (_ BitVec 10))
(declare-var y (_ BitVec 10))
(declare-var z (_ BitVec 10))
(declare-rel inv ((_ BitVec 10) (_ BitVec 10) (_ BitVec 10)))
(rule (=> (and (= x #b0000000011) (= y #b0000000101) (= z #b0000000001)) (inv x y z)))
(rule (=> (and (inv x y z) (not (= (bvmul x (bvadd y z)) (bvadd (bvmul x y) (bvmul x z)))))
          false))"#;

#[test]
#[timeout(120_000)]
fn the_preprocessed_safe_boundary_gives_its_executor_runs_the_rule_wall_not_a_fixed_cap() {
    use crate::smt::check_sat::take_executor_session_budgets_for_tests;
    let problem = ChcParser::parse(BOUNDARY_DISTRIBUTIVITY).unwrap();
    let inv = problem.lookup_predicate("inv").unwrap();
    let vars: Vec<crate::ChcVar> = problem.predicates()[inv.index()]
        .arg_sorts
        .iter()
        .enumerate()
        .map(|(i, sort)| crate::ChcVar::new(format!("a{i}"), sort.clone()))
        .collect();
    let mut model = crate::pdr::InvariantModel::new();
    model.set(
        inv,
        crate::pdr::PredicateInterpretation::new(vars, ChcExpr::Bool(true)),
    );
    let adaptive = crate::AdaptivePortfolio::new(problem, crate::AdaptiveConfig::test_default());
    take_executor_session_budgets_for_tests();
    let deadline = Instant::now() + Duration::from_mins(1);
    assert!(adaptive.validate_preprocessed_safe_model(
        &model,
        "counted-boundary",
        deadline,
        &crate::CancellationToken::new(),
    ));
    // Counted: the executor run is handed the rule's wall, a quarter of what
    // remains of the deadline (15 s). The fixed 1.5 s per-rule cap handed it
    // about 1.1 s, and a per-rule wall alone about 1.5 s (the first check's
    // VERIFY_INITIAL_TIMEOUT). A session recorded at all also shows the
    // check reached its executor, which the internal loop cannot settle.
    let budgets = take_executor_session_budgets_for_tests();
    assert!(
        budgets.iter().any(|b| *b > Duration::from_secs(10)),
        "{budgets:?}"
    );
}

#[test]
fn a_lifted_scope_runs_unmetered_under_a_spent_allowance() {
    let _spent = ScopedExecutorWork::install(allowance(0, 10));
    assert!(matches!(draw_executor_work(), ExecutorDraw::Spent));
    {
        let _guard = ScopedExecutorWork::lift();
        assert!(matches!(draw_executor_work(), ExecutorDraw::Unmetered));
        assert!(!executor_work_spent());
    }
    assert!(executor_work_spent(), "the rule's allowance is restored");
}

/// PHP(8,7) over 0/1 integers: neither the native loop nor a spent executor
/// settles it.
const PIGEONHOLE_LIA: &str = r#"(set-logic HORN)
(declare-var x0_0 Int)
(declare-var x0_1 Int)
(declare-var x0_2 Int)
(declare-var x0_3 Int)
(declare-var x0_4 Int)
(declare-var x0_5 Int)
(declare-var x0_6 Int)
(declare-var x1_0 Int)
(declare-var x1_1 Int)
(declare-var x1_2 Int)
(declare-var x1_3 Int)
(declare-var x1_4 Int)
(declare-var x1_5 Int)
(declare-var x1_6 Int)
(declare-var x2_0 Int)
(declare-var x2_1 Int)
(declare-var x2_2 Int)
(declare-var x2_3 Int)
(declare-var x2_4 Int)
(declare-var x2_5 Int)
(declare-var x2_6 Int)
(declare-var x3_0 Int)
(declare-var x3_1 Int)
(declare-var x3_2 Int)
(declare-var x3_3 Int)
(declare-var x3_4 Int)
(declare-var x3_5 Int)
(declare-var x3_6 Int)
(declare-var x4_0 Int)
(declare-var x4_1 Int)
(declare-var x4_2 Int)
(declare-var x4_3 Int)
(declare-var x4_4 Int)
(declare-var x4_5 Int)
(declare-var x4_6 Int)
(declare-var x5_0 Int)
(declare-var x5_1 Int)
(declare-var x5_2 Int)
(declare-var x5_3 Int)
(declare-var x5_4 Int)
(declare-var x5_5 Int)
(declare-var x5_6 Int)
(declare-var x6_0 Int)
(declare-var x6_1 Int)
(declare-var x6_2 Int)
(declare-var x6_3 Int)
(declare-var x6_4 Int)
(declare-var x6_5 Int)
(declare-var x6_6 Int)
(declare-var x7_0 Int)
(declare-var x7_1 Int)
(declare-var x7_2 Int)
(declare-var x7_3 Int)
(declare-var x7_4 Int)
(declare-var x7_5 Int)
(declare-var x7_6 Int)
(declare-rel inv (Int))
(rule (=> (= x0_0 0) (inv x0_0)))
(rule (=> (and (inv x0_0) (>= x0_0 0) (<= x0_0 1) (>= x0_1 0) (<= x0_1 1) (>= x0_2 0) (<= x0_2 1) (>= x0_3 0) (<= x0_3 1) (>= x0_4 0) (<= x0_4 1) (>= x0_5 0) (<= x0_5 1) (>= x0_6 0) (<= x0_6 1) (>= x1_0 0) (<= x1_0 1) (>= x1_1 0) (<= x1_1 1) (>= x1_2 0) (<= x1_2 1) (>= x1_3 0) (<= x1_3 1) (>= x1_4 0) (<= x1_4 1) (>= x1_5 0) (<= x1_5 1) (>= x1_6 0) (<= x1_6 1) (>= x2_0 0) (<= x2_0 1) (>= x2_1 0) (<= x2_1 1) (>= x2_2 0) (<= x2_2 1) (>= x2_3 0) (<= x2_3 1) (>= x2_4 0) (<= x2_4 1) (>= x2_5 0) (<= x2_5 1) (>= x2_6 0) (<= x2_6 1) (>= x3_0 0) (<= x3_0 1) (>= x3_1 0) (<= x3_1 1) (>= x3_2 0) (<= x3_2 1) (>= x3_3 0) (<= x3_3 1) (>= x3_4 0) (<= x3_4 1) (>= x3_5 0) (<= x3_5 1) (>= x3_6 0) (<= x3_6 1) (>= x4_0 0) (<= x4_0 1) (>= x4_1 0) (<= x4_1 1) (>= x4_2 0) (<= x4_2 1) (>= x4_3 0) (<= x4_3 1) (>= x4_4 0) (<= x4_4 1) (>= x4_5 0) (<= x4_5 1) (>= x4_6 0) (<= x4_6 1) (>= x5_0 0) (<= x5_0 1) (>= x5_1 0) (<= x5_1 1) (>= x5_2 0) (<= x5_2 1) (>= x5_3 0) (<= x5_3 1) (>= x5_4 0) (<= x5_4 1) (>= x5_5 0) (<= x5_5 1) (>= x5_6 0) (<= x5_6 1) (>= x6_0 0) (<= x6_0 1) (>= x6_1 0) (<= x6_1 1) (>= x6_2 0) (<= x6_2 1) (>= x6_3 0) (<= x6_3 1) (>= x6_4 0) (<= x6_4 1) (>= x6_5 0) (<= x6_5 1) (>= x6_6 0) (<= x6_6 1) (>= x7_0 0) (<= x7_0 1) (>= x7_1 0) (<= x7_1 1) (>= x7_2 0) (<= x7_2 1) (>= x7_3 0) (<= x7_3 1) (>= x7_4 0) (<= x7_4 1) (>= x7_5 0) (<= x7_5 1) (>= x7_6 0) (<= x7_6 1) (>= (+ x0_0 x0_1 x0_2 x0_3 x0_4 x0_5 x0_6) 1) (>= (+ x1_0 x1_1 x1_2 x1_3 x1_4 x1_5 x1_6) 1) (>= (+ x2_0 x2_1 x2_2 x2_3 x2_4 x2_5 x2_6) 1) (>= (+ x3_0 x3_1 x3_2 x3_3 x3_4 x3_5 x3_6) 1) (>= (+ x4_0 x4_1 x4_2 x4_3 x4_4 x4_5 x4_6) 1) (>= (+ x5_0 x5_1 x5_2 x5_3 x5_4 x5_5 x5_6) 1) (>= (+ x6_0 x6_1 x6_2 x6_3 x6_4 x6_5 x6_6) 1) (>= (+ x7_0 x7_1 x7_2 x7_3 x7_4 x7_5 x7_6) 1) (<= (+ x0_0 x1_0 x2_0 x3_0 x4_0 x5_0 x6_0 x7_0) 1) (<= (+ x0_1 x1_1 x2_1 x3_1 x4_1 x5_1 x6_1 x7_1) 1) (<= (+ x0_2 x1_2 x2_2 x3_2 x4_2 x5_2 x6_2 x7_2) 1) (<= (+ x0_3 x1_3 x2_3 x3_3 x4_3 x5_3 x6_3 x7_3) 1) (<= (+ x0_4 x1_4 x2_4 x3_4 x4_4 x5_4 x6_4 x7_4) 1) (<= (+ x0_5 x1_5 x2_5 x3_5 x4_5 x5_5 x6_5 x7_5) 1) (<= (+ x0_6 x1_6 x2_6 x3_6 x4_6 x5_6 x6_6 x7_6) 1)) false))"#;

#[test]
#[timeout(60_000)]
fn the_executor_fallback_native_attempt_keeps_the_narrow_slice_under_an_allowance() {
    let problem = ChcParser::parse(PIGEONHOLE_LIA).unwrap();
    let query = problem.clauses().iter().find(|c| c.is_query()).unwrap();
    let query = query.body.constraint.clone().unwrap();
    let _spent = ScopedExecutorWork::install(allowance(0, 10));
    let mut smt = SmtContext::new();
    let started = Instant::now();
    let result = smt.check_sat_with_executor_fallback_timeout(&query, Duration::from_secs(15));
    assert!(matches!(result, SmtResult::Unknown), "{result:?}");
    // Narrowed: 0.375 s. Unnarrowed, min(15 s / 4, 2 s) = 2 s.
    assert!(
        started.elapsed() < Duration::from_millis(1200),
        "{:?}",
        started.elapsed()
    );
}
