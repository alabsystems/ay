// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

fn timed_single_config() -> PortfolioConfig {
    PortfolioConfig {
        // A single TRL lane skips the algebraic prepass, so both public solve
        // methods must reach the scheduler under test.
        engines: vec![EngineConfig::Trl(TrlConfig::default())],
        parallel: true,
        timeout: Some(Duration::from_secs(2)),
        parallel_timeout: Some(Duration::from_millis(500)),
        enable_preprocessing: false,
        strict_proofs: true,
        ..PortfolioConfig::test_default()
    }
}

fn safe_model(problem: &ChcProblem) -> InvariantModel {
    let x = ChcVar::new("x", ChcSort::Int);
    let mut model = InvariantModel::new();
    model.set(
        problem.predicates()[0].id,
        PredicateInterpretation::new(
            vec![x.clone()],
            ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(10)),
        ),
    );
    model
}

#[test]
fn explicit_sequential_mode_ignores_a_zero_parallel_timeout() {
    let config = PortfolioConfig {
        parallel: false,
        timeout: Some(Duration::from_secs(1)),
        parallel_timeout: Some(Duration::ZERO),
        enable_preprocessing: false,
        strict_proofs: true,
        ..PortfolioConfig::test_default()
    };
    let solver = PortfolioSolver::new(ChcProblem::new(), config);

    assert!(matches!(solver.solve(), PortfolioResult::Safe(_)));
    let (result, report) = solver.solve_with_budget_report();
    assert!(matches!(result, PortfolioResult::Safe(_)));
    assert!(report
        .entries
        .iter()
        .all(|entry| entry.stop_reason == EngineStopReason::NotStarted));
}

#[test]
#[timeout(10000)]
fn timed_single_parallel_lane_rejects_completion_after_its_window() {
    for with_report in [false, true] {
        let problem = create_safe_problem();
        let model = safe_model(&problem);
        let invoked = Arc::new(AtomicBool::new(false));
        let observed = invoked.clone();
        let solver = PortfolioSolver::new(problem, timed_single_config())
            .with_sequential_test_engine(move |_idx, cancellation| {
                observed.store(true, Ordering::SeqCst);
                while !cancellation.is_cancelled() {
                    thread::yield_now();
                }
                EngineResult::Unified(PortfolioResult::Safe(model.clone()), "TEST_LATE_SINGLE")
            });

        let result = if with_report {
            let (result, report) = solver.solve_with_budget_report();
            assert_eq!(report.entries.len(), 1);
            assert_eq!(report.entries[0].stop_reason, EngineStopReason::Timeout);
            assert!(report.entries[0].budget_allocated > Duration::ZERO);
            assert!(report.entries[0].budget_allocated <= Duration::from_millis(500));
            result
        } else {
            solver.solve()
        };
        assert!(invoked.load(Ordering::SeqCst));
        assert!(matches!(result, PortfolioResult::Unknown));
    }
}

#[test]
#[timeout(10000)]
fn timed_single_parallel_lane_keeps_predeadline_completion_grace() {
    for with_report in [false, true] {
        let problem = create_safe_problem();
        let model = safe_model(&problem);
        let solver = PortfolioSolver::new(problem, timed_single_config())
            .with_sequential_test_engine(move |_idx, _cancellation| {
                EngineResult::Unified(PortfolioResult::Safe(model.clone()), "TEST_SINGLE_GRACE")
            })
            // Completion occurs before the window closes; only publication is
            // delayed. The existing parallel grace must still recover it.
            .with_sequential_test_publish_delay(Duration::from_millis(650));

        let result = if with_report {
            let (result, report) = solver.solve_with_budget_report();
            assert_eq!(report.entries.len(), 1);
            assert_eq!(report.entries[0].stop_reason, EngineStopReason::Completed);
            result
        } else {
            solver.solve()
        };
        assert!(matches!(result, PortfolioResult::Safe(_)));
    }
}

#[test]
fn deterministic_flag_keeps_fixed_sequential_shares_with_parallel_config() {
    let config = PortfolioConfig {
        engines: vec![
            EngineConfig::Pdr(PdrConfig::default()),
            EngineConfig::Bmc(BmcConfig::default()),
        ],
        parallel: true,
        timeout: Some(Duration::from_secs(6)),
        parallel_timeout: Some(Duration::from_secs(30)),
        enable_preprocessing: false,
        ..PortfolioConfig::test_default()
    };
    let launched = Arc::new(Mutex::new(Vec::new()));
    let observed = launched.clone();
    let solver = PortfolioSolver::new(create_safe_problem(), config)
        .with_deterministic_sequential_schedule(None)
        .with_sequential_test_engine(move |idx, _cancellation| {
            observed.lock().unwrap().push(idx);
            EngineResult::Unified(PortfolioResult::Unknown, "TEST_DETERMINISTIC_MODE")
        });

    let (result, report) = solver.solve_with_budget_report();
    assert!(matches!(result, PortfolioResult::Unknown));
    assert_eq!(*launched.lock().unwrap(), vec![0, 1]);
    assert_eq!(report.entries.len(), 2);
    assert!(report.entries.iter().all(|entry| {
        entry.budget_allocated == Duration::from_secs(3)
            && entry.stop_reason == EngineStopReason::Unknown
    }));
}
