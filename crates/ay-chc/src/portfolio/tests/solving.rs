// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

fn bounded_parallel_test_config(
    engine_count: usize,
    parallel_timeout: Duration,
) -> PortfolioConfig {
    PortfolioConfig {
        external_cancellation: None,
        engines: (0..engine_count)
            .map(|_| EngineConfig::Pdr(PdrConfig::default()))
            .collect(),
        parallel: true,
        timeout: None,
        parallel_timeout: Some(parallel_timeout),
        verbose: false,
        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: true,
    }
}

#[test]
fn test_sequential_portfolio_enforces_per_engine_timeout() {
    use std::time::Duration;

    // Run BMC on a safe problem with a huge max_depth so it will not terminate quickly.
    // The sequential portfolio timeout should cancel the engine and return Unknown.
    let problem = create_safe_problem();
    let token = CancellationToken::new();

    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![EngineConfig::Bmc(BmcConfig::with_engine_config(
            1_000_000_000,
            false,
            Some(token.clone()),
        ))],
        parallel: false,
        timeout: Some(Duration::from_millis(10)),
        parallel_timeout: None,
        verbose: false,

        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let solver = PortfolioSolver::new(problem, config);

    // Run in a thread so we can fail fast if the timeout is not enforced.
    let (tx, rx) = mpsc::channel();
    let handle = thread::spawn(move || {
        let result = solver.solve();
        let _ = tx.send(result);
    });

    // The sequential portfolio adds a grace period (SEQUENTIAL_ENGINE_GRACE_PERIOD)
    // after the engine timeout before returning Unknown (#7899). Account for this
    // by waiting longer than engine_timeout + grace_period.
    let result = match rx.recv_timeout(Duration::from_secs(2)) {
        Ok(result) => result,
        Err(mpsc::RecvTimeoutError::Timeout) => {
            token.cancel();
            let _ = handle.join();
            panic!("Sequential portfolio did not enforce PortfolioConfig.timeout");
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            token.cancel();
            let _ = handle.join();
            panic!("Solver thread disconnected without returning a result");
        }
    };

    handle.join().unwrap();
    // With the sequential grace period (#7899), the engine may complete
    // during the grace window on simple problems. Both outcomes are correct:
    // - Unknown: engine didn't finish within budget + grace (timeout enforced)
    // - Safe: engine finished during grace period (correct result captured)
    // The key invariant is that the portfolio returned within bounded time
    // (verified by the recv_timeout above not hitting the 2000ms watchdog).
    assert!(
        matches!(result, PortfolioResult::Unknown | PortfolioResult::Safe(_)),
        "Expected Unknown or Safe, got: {result:?}"
    );
}

#[test]
fn test_default_portfolio_includes_pdr_splits_variants() {
    let config = PortfolioConfig::production_default();

    let mut saw_pdr_with_splits = false;
    let mut saw_pdr_without_splits = false;
    for engine in &config.engines {
        if let EngineConfig::Pdr(pdr) = engine {
            if pdr.use_negated_equality_splits {
                saw_pdr_with_splits = true;
            } else {
                saw_pdr_without_splits = true;
            }
        }
    }

    assert!(
        saw_pdr_with_splits,
        "Default portfolio missing PDR with negated equality splits"
    );
    assert!(
        saw_pdr_without_splits,
        "Default portfolio missing PDR without negated equality splits"
    );
}

#[test]
#[timeout(5000)]
fn parallel_winner_reaps_delayed_loser_before_return() {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;

    let problem = create_safe_problem();
    let predicate = problem.predicates()[0].id;
    let x = ChcVar::new("x", ChcSort::Int);
    let mut winning_model = InvariantModel::new();
    winning_model.set(
        predicate,
        PredicateInterpretation::new(
            vec![x.clone()],
            ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(10)),
        ),
    );
    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![
            EngineConfig::Pdr(PdrConfig::default()),
            EngineConfig::Bmc(BmcConfig::default()),
        ],
        parallel: true,
        timeout: None,
        parallel_timeout: Some(Duration::from_secs(2)),
        verbose: false,
        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: true,
    };
    let loser_started = Arc::new(AtomicBool::new(false));
    let loser_alive = Arc::new(AtomicBool::new(false));
    let loser_saw_cancel = Arc::new(AtomicBool::new(false));
    let observed_started = loser_started.clone();
    let observed_alive = loser_alive.clone();
    let observed_cancel = loser_saw_cancel.clone();
    let solver = PortfolioSolver::new(problem, config)
        .with_sequential_test_engine(move |idx, cancellation| {
            if idx == 0 {
                while !observed_started.load(Ordering::SeqCst) {
                    thread::yield_now();
                }
                EngineResult::Unified(PortfolioResult::Safe(winning_model.clone()), "TEST_WINNER")
            } else {
                observed_alive.store(true, Ordering::SeqCst);
                observed_started.store(true, Ordering::SeqCst);
                while !cancellation.is_cancelled() {
                    thread::yield_now();
                }
                observed_cancel.store(true, Ordering::SeqCst);
                thread::sleep(Duration::from_millis(100));
                observed_alive.store(false, Ordering::SeqCst);
                EngineResult::Unified(PortfolioResult::Unknown, "TEST_LOSER")
            }
        })
        .with_sequential_test_publish_delay(Duration::from_millis(50));

    let result = solver.solve_parallel();

    assert!(matches!(result, PortfolioResult::Safe(_)));
    assert!(loser_saw_cancel.load(Ordering::SeqCst));
    assert!(
        !loser_alive.load(Ordering::SeqCst),
        "the accepted winner must not return while a delayed losing worker remains alive"
    );
}

#[test]
#[timeout(5000)]
fn parallel_timeout_worker_cancellation_does_not_poison_grace_validation() {
    let problem = create_safe_problem();
    let predicate = problem.predicates()[0].id;
    let x = ChcVar::new("x", ChcSort::Int);
    let mut safe_model = InvariantModel::new();
    safe_model.set(
        predicate,
        PredicateInterpretation::new(
            vec![x.clone()],
            ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(10)),
        ),
    );
    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![
            EngineConfig::Pdr(PdrConfig::default()),
            EngineConfig::Bmc(BmcConfig::default()),
        ],
        parallel: true,
        timeout: None,
        parallel_timeout: Some(Duration::from_millis(200)),
        verbose: false,
        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: true,
    };
    let solver = PortfolioSolver::new(problem, config)
        .with_sequential_test_engine(move |idx, cancellation| {
            if idx == 0 {
                EngineResult::Unified(PortfolioResult::Safe(safe_model.clone()), "TEST_GRACE_SAFE")
            } else {
                while !cancellation.is_cancelled() {
                    thread::yield_now();
                }
                EngineResult::Unified(PortfolioResult::Unknown, "TEST_GRACE_UNKNOWN")
            }
        })
        // The candidate is complete before timeout, but its publication loses
        // the timeout race. Grace may recover it by its completion timestamp.
        .with_sequential_test_publish_delay(Duration::from_millis(300));

    let result = solver.solve_parallel();

    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "scheduler-local timeout cancellation must not make a queued valid candidate fail validation"
    );
}

#[test]
#[timeout(5000)]
fn parallel_timeout_rejects_postdeadline_completion_during_grace() {
    let problem = create_safe_problem();
    let predicate = problem.predicates()[0].id;
    let x = ChcVar::new("x", ChcSort::Int);
    let mut safe_model = InvariantModel::new();
    safe_model.set(
        predicate,
        PredicateInterpretation::new(
            vec![x.clone()],
            ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(10)),
        ),
    );
    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![
            EngineConfig::Pdr(PdrConfig::default()),
            EngineConfig::Bmc(BmcConfig::default()),
        ],
        parallel: true,
        timeout: None,
        parallel_timeout: Some(Duration::from_millis(20)),
        verbose: false,
        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: true,
    };
    let solver = PortfolioSolver::new(problem, config).with_sequential_test_engine(
        move |idx, cancellation| {
            while !cancellation.is_cancelled() {
                thread::yield_now();
            }
            if idx == 0 {
                EngineResult::Unified(PortfolioResult::Safe(safe_model.clone()), "TEST_LATE_SAFE")
            } else {
                EngineResult::Unified(PortfolioResult::Unknown, "TEST_LATE_UNKNOWN")
            }
        },
    );

    assert!(matches!(solver.solve_parallel(), PortfolioResult::Unknown));
}

#[test]
#[timeout(5000)]
fn parallel_report_does_not_count_a_rejected_candidate_as_completed() {
    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![
            EngineConfig::Pdr(PdrConfig::default()),
            EngineConfig::Bmc(BmcConfig::default()),
        ],
        parallel: true,
        timeout: None,
        parallel_timeout: Some(Duration::from_secs(2)),
        verbose: false,
        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: true,
    };
    let solver = PortfolioSolver::new(create_safe_problem(), config).with_sequential_test_engine(
        |idx, _cancellation| {
            if idx == 0 {
                // Missing the required predicate interpretation, so mandatory
                // Safe validation rejects this raw definitive candidate.
                EngineResult::Unified(
                    PortfolioResult::Safe(InvariantModel::new()),
                    "TEST_REJECTED_SAFE",
                )
            } else {
                EngineResult::Unified(PortfolioResult::Unknown, "TEST_UNKNOWN")
            }
        },
    );

    let mut report = BudgetReport::new();
    let result = solver.solve_parallel_with_report(&mut report);

    assert!(matches!(result, PortfolioResult::Unknown));
    assert_eq!(report.completed_count(), 0);
    assert_eq!(report.entries.len(), 2);
    assert_eq!(report.entries[0].index, 0);
    assert_eq!(report.entries[0].stop_reason, EngineStopReason::Unknown);
}

#[test]
#[timeout(5000)]
fn bounded_parallel_queue_runs_every_engine_without_exceeding_capacity() {
    let active = Arc::new(AtomicUsize::new(0));
    let peak = Arc::new(AtomicUsize::new(0));
    let launched = Arc::new(Mutex::new(Vec::new()));
    let observed_active = active.clone();
    let observed_peak = peak.clone();
    let observed_launched = launched.clone();
    let solver = PortfolioSolver::new(
        create_safe_problem(),
        bounded_parallel_test_config(5, Duration::from_secs(2)),
    )
    .with_parallel_worker_limit(2)
    .with_sequential_test_engine(move |idx, _cancellation| {
        observed_launched.lock().unwrap().push(idx);
        let now_active = observed_active.fetch_add(1, Ordering::SeqCst) + 1;
        observed_peak.fetch_max(now_active, Ordering::SeqCst);
        if idx < 2 {
            let rendezvous_deadline = ay_core::time::Instant::now() + Duration::from_secs(1);
            while observed_active.load(Ordering::SeqCst) < 2
                && ay_core::time::Instant::now() < rendezvous_deadline
            {
                thread::yield_now();
            }
        }
        thread::sleep(Duration::from_millis(20));
        observed_active.fetch_sub(1, Ordering::SeqCst);
        EngineResult::Unified(PortfolioResult::Unknown, "TEST_BOUNDED_QUEUE")
    });

    let mut report = BudgetReport::new();
    let result = solver.solve_parallel_with_report(&mut report);

    assert!(matches!(result, PortfolioResult::Unknown));
    assert_eq!(peak.load(Ordering::SeqCst), 2);
    let mut launched = launched.lock().unwrap().clone();
    launched.sort_unstable();
    assert_eq!(launched, vec![0, 1, 2, 3, 4]);
    assert_eq!(report.entries.len(), 5);
    assert_eq!(
        report
            .entries
            .iter()
            .map(|entry| entry.index)
            .collect::<Vec<_>>(),
        vec![0, 1, 2, 3, 4]
    );
    assert!(report
        .entries
        .iter()
        .all(|entry| entry.stop_reason == EngineStopReason::Unknown));
}

#[test]
#[timeout(5000)]
fn bounded_parallel_tail_winner_cancels_active_and_skips_queued_engine() {
    let problem = create_safe_problem();
    let predicate = problem.predicates()[0].id;
    let x = ChcVar::new("bounded_tail_x", ChcSort::Int);
    let mut winning_model = InvariantModel::new();
    winning_model.set(
        predicate,
        PredicateInterpretation::new(
            vec![x.clone()],
            ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(10)),
        ),
    );

    let sibling_started = Arc::new(AtomicBool::new(false));
    let sibling_alive = Arc::new(AtomicBool::new(false));
    let sibling_cancelled = Arc::new(AtomicBool::new(false));
    let launched = Arc::new(Mutex::new(Vec::new()));
    let observed_started = sibling_started.clone();
    let observed_alive = sibling_alive.clone();
    let observed_cancelled = sibling_cancelled.clone();
    let observed_launched = launched.clone();
    let solver = PortfolioSolver::new(
        problem,
        bounded_parallel_test_config(4, Duration::from_secs(2)),
    )
    .with_parallel_worker_limit(2)
    .with_sequential_test_engine(move |idx, cancellation| {
        observed_launched.lock().unwrap().push(idx);
        match idx {
            0 => {
                while !observed_started.load(Ordering::SeqCst) {
                    thread::yield_now();
                }
                EngineResult::Unified(PortfolioResult::Unknown, "TEST_QUEUE_PREFIX")
            }
            1 => {
                observed_alive.store(true, Ordering::SeqCst);
                observed_started.store(true, Ordering::SeqCst);
                while !cancellation.is_cancelled() {
                    thread::yield_now();
                }
                observed_cancelled.store(true, Ordering::SeqCst);
                thread::sleep(Duration::from_millis(50));
                observed_alive.store(false, Ordering::SeqCst);
                EngineResult::Unified(PortfolioResult::Unknown, "TEST_QUEUE_SIBLING")
            }
            2 => EngineResult::Unified(
                PortfolioResult::Safe(winning_model.clone()),
                "TEST_QUEUE_WINNER",
            ),
            _ => EngineResult::Unified(PortfolioResult::Unknown, "TEST_MUST_STAY_QUEUED"),
        }
    });

    let mut report = BudgetReport::new();
    let result = solver.solve_parallel_with_report(&mut report);

    assert!(matches!(result, PortfolioResult::Safe(_)));
    assert!(sibling_cancelled.load(Ordering::SeqCst));
    assert!(!sibling_alive.load(Ordering::SeqCst));
    let mut launched = launched.lock().unwrap().clone();
    launched.sort_unstable();
    assert_eq!(launched, vec![0, 1, 2]);
    assert_eq!(report.entries.len(), 4);
    assert_eq!(report.entries[2].stop_reason, EngineStopReason::Completed);
    assert_eq!(report.entries[3].stop_reason, EngineStopReason::NotStarted);
    assert_eq!(report.entries[3].budget_allocated, Duration::ZERO);
    assert_eq!(report.entries[3].elapsed, Duration::ZERO);
}

#[test]
#[timeout(5000)]
fn bounded_parallel_lane_timeouts_release_slots_for_every_engine() {
    let launched = Arc::new(Mutex::new(Vec::new()));
    let observed_launched = launched.clone();
    let solver = PortfolioSolver::new(
        create_safe_problem(),
        bounded_parallel_test_config(3, Duration::from_millis(600)),
    )
    .with_parallel_worker_limit(1)
    .with_sequential_test_engine(move |idx, cancellation| {
        observed_launched.lock().unwrap().push(idx);
        while !cancellation.is_cancelled() {
            thread::yield_now();
        }
        EngineResult::Unified(PortfolioResult::Unknown, "TEST_QUEUE_TIMEOUT")
    });

    let mut report = BudgetReport::new();
    let solve_start = ay_core::time::Instant::now();
    let result = solver.solve_parallel_with_report(&mut report);
    let solve_elapsed = solve_start.elapsed();

    assert!(matches!(result, PortfolioResult::Unknown));
    assert!(
        solve_elapsed < Duration::from_millis(1800),
        "closed worker senders must end timeout grace promptly: {solve_elapsed:?}"
    );
    assert_eq!(*launched.lock().unwrap(), vec![0, 1, 2]);
    assert_eq!(report.entries.len(), 3);
    assert!(report
        .entries
        .iter()
        .all(|entry| entry.stop_reason == EngineStopReason::Timeout));
    for entry in &report.entries {
        assert!(entry.budget_allocated > Duration::ZERO);
        assert!(entry.elapsed > Duration::ZERO);
    }
}

#[test]
#[timeout(5000)]
fn bounded_parallel_lane_timeout_reaches_tail_winner() {
    let problem = create_safe_problem();
    let predicate = problem.predicates()[0].id;
    let x = ChcVar::new("bounded_budget_tail_x", ChcSort::Int);
    let mut winning_model = InvariantModel::new();
    winning_model.set(
        predicate,
        PredicateInterpretation::new(
            vec![x.clone()],
            ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(10)),
        ),
    );
    let launched = Arc::new(Mutex::new(Vec::new()));
    let observed_launched = launched.clone();
    let solver = PortfolioSolver::new(
        problem,
        bounded_parallel_test_config(3, Duration::from_millis(300)),
    )
    .with_parallel_worker_limit(1)
    .with_sequential_test_engine(move |idx, cancellation| {
        observed_launched.lock().unwrap().push(idx);
        match idx {
            0 => {
                while !cancellation.is_cancelled() {
                    thread::yield_now();
                }
                EngineResult::Unified(PortfolioResult::Unknown, "TEST_LANE_TIMEOUT")
            }
            1 => EngineResult::Unified(
                PortfolioResult::Safe(winning_model.clone()),
                "TEST_BUDGETED_TAIL_WINNER",
            ),
            _ => EngineResult::Unified(PortfolioResult::Unknown, "TEST_MUST_STAY_QUEUED"),
        }
    });

    let mut report = BudgetReport::new();
    let result = solver.solve_parallel_with_report(&mut report);

    assert!(matches!(result, PortfolioResult::Safe(_)));
    assert_eq!(*launched.lock().unwrap(), vec![0, 1]);
    assert_eq!(report.entries.len(), 3);
    assert_eq!(report.entries[0].stop_reason, EngineStopReason::Timeout);
    assert_eq!(report.entries[1].stop_reason, EngineStopReason::Completed);
    assert_eq!(report.entries[2].stop_reason, EngineStopReason::NotStarted);
    assert!(report.entries[0].budget_allocated > Duration::ZERO);
    assert!(report.entries[1].budget_allocated > Duration::ZERO);
    assert_eq!(report.entries[2].budget_allocated, Duration::ZERO);
}

#[test]
#[timeout(5000)]
fn bounded_parallel_fixed_probe_reclaims_slot_for_tail_winner() {
    let problem = create_safe_problem();
    let predicate = problem.predicates()[0].id;
    let x = ChcVar::new("fixed_probe_tail_x", ChcSort::Int);
    let mut winning_model = InvariantModel::new();
    winning_model.set(
        predicate,
        PredicateInterpretation::new(
            vec![x.clone()],
            ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(10)),
        ),
    );

    let launched = Arc::new(Mutex::new(Vec::new()));
    let observed_launched = launched.clone();
    let mut config = bounded_parallel_test_config(0, Duration::from_millis(600));
    config.engines = vec![
        EngineConfig::Bmc(BmcConfig::default()),
        EngineConfig::Pdr(PdrConfig::default()),
    ];
    config.engine_budgets.insert(
        EngineType::Bmc,
        BudgetPolicy::Fixed(Duration::from_millis(20)),
    );
    let solver = PortfolioSolver::new(problem, config)
        .with_parallel_worker_limit(1)
        .with_sequential_test_engine(move |idx, cancellation| {
            observed_launched.lock().unwrap().push(idx);
            if idx == 0 {
                while !cancellation.is_cancelled() {
                    thread::yield_now();
                }
                EngineResult::Unified(PortfolioResult::Unknown, "TEST_FIXED_PROBE")
            } else {
                EngineResult::Unified(
                    PortfolioResult::Safe(winning_model.clone()),
                    "TEST_FIXED_PROBE_TAIL_WINNER",
                )
            }
        });

    let mut report = BudgetReport::new();
    let result = solver.solve_parallel_with_report(&mut report);

    assert!(matches!(result, PortfolioResult::Safe(_)));
    assert_eq!(*launched.lock().unwrap(), vec![0, 1]);
    assert_eq!(report.entries.len(), 2);
    assert_eq!(report.entries[0].engine, EngineType::Bmc);
    assert_eq!(
        report.entries[0].budget_allocated,
        Duration::from_millis(20)
    );
    assert_eq!(report.entries[0].stop_reason, EngineStopReason::Timeout);
    assert_eq!(report.entries[1].engine, EngineType::Pdr);
    assert_eq!(report.entries[1].stop_reason, EngineStopReason::Completed);
}

#[test]
#[timeout(5000)]
fn bounded_parallel_zero_fixed_budget_skips_only_that_engine() {
    let launched = Arc::new(Mutex::new(Vec::new()));
    let observed_launched = launched.clone();
    let mut config = bounded_parallel_test_config(0, Duration::from_secs(1));
    config.engines = vec![
        EngineConfig::Bmc(BmcConfig::default()),
        EngineConfig::Pdr(PdrConfig::default()),
    ];
    config
        .engine_budgets
        .insert(EngineType::Bmc, BudgetPolicy::Fixed(Duration::ZERO));
    let solver = PortfolioSolver::new(create_safe_problem(), config)
        .with_parallel_worker_limit(1)
        .with_sequential_test_engine(move |idx, _cancellation| {
            observed_launched.lock().unwrap().push(idx);
            EngineResult::Unified(PortfolioResult::Unknown, "TEST_ZERO_FIXED_PARALLEL")
        });

    let mut report = BudgetReport::new();
    let result = solver.solve_parallel_with_report(&mut report);

    assert!(matches!(result, PortfolioResult::Unknown));
    assert_eq!(*launched.lock().unwrap(), vec![1]);
    assert_eq!(report.entries.len(), 2);
    assert_eq!(report.entries[0].index, 0);
    assert_eq!(report.entries[0].budget_allocated, Duration::ZERO);
    assert_eq!(report.entries[0].stop_reason, EngineStopReason::NotStarted);
    assert_eq!(report.entries[1].index, 1);
    assert_eq!(report.entries[1].stop_reason, EngineStopReason::Unknown);
}

#[test]
#[timeout(5000)]
fn bounded_parallel_external_cancellation_skips_queued_engines() {
    let parent = crate::CancellationToken::new();
    let mut config = bounded_parallel_test_config(3, Duration::from_secs(2));
    config.external_cancellation = Some(parent.clone());
    let launched = Arc::new(Mutex::new(Vec::new()));
    let observed_launched = launched.clone();
    let worker_parent = parent.clone();
    let solver = PortfolioSolver::new(create_safe_problem(), config)
        .with_parallel_worker_limit(1)
        .with_sequential_test_engine(move |idx, cancellation| {
            observed_launched.lock().unwrap().push(idx);
            worker_parent.cancel();
            while !cancellation.is_cancelled() {
                thread::yield_now();
            }
            EngineResult::Unified(PortfolioResult::Unknown, "TEST_EXTERNAL_CANCEL")
        });

    let mut report = BudgetReport::new();
    let result = solver.solve_parallel_with_report(&mut report);

    assert!(matches!(result, PortfolioResult::Unknown));
    assert_eq!(*launched.lock().unwrap(), vec![0]);
    assert_eq!(report.entries.len(), 3);
    assert_eq!(report.entries[0].stop_reason, EngineStopReason::Unknown);
    assert!(report.entries[1..]
        .iter()
        .all(|entry| entry.stop_reason == EngineStopReason::NotStarted));
}

#[test]
#[timeout(5000)]
fn bounded_parallel_uses_earlier_construction_deadline_for_lane_budgets() {
    let solver = PortfolioSolver::new_with_solve_limits(
        create_safe_problem(),
        bounded_parallel_test_config(3, Duration::from_secs(20)),
        Some(ay_core::time::Instant::now() + Duration::from_secs(3)),
    )
    .with_parallel_worker_limit(1)
    .with_sequential_test_engine(|_idx, _cancellation| {
        EngineResult::Unified(PortfolioResult::Unknown, "TEST_CONSTRUCTION_DEADLINE")
    });

    let mut report = BudgetReport::new();
    let result = solver.solve_parallel_with_report(&mut report);

    assert!(matches!(result, PortfolioResult::Unknown));
    assert_eq!(report.entries.len(), 3);
    assert!(report.entries.iter().all(|entry| {
        entry.budget_allocated > Duration::ZERO && entry.budget_allocated < Duration::from_secs(2)
    }));
}

#[test]
fn bounded_parallel_expired_deadline_never_invokes_engine_body() {
    let invoked = Arc::new(AtomicBool::new(false));
    let observed_invoked = invoked.clone();
    let solver = PortfolioSolver::new_with_solve_limits(
        create_safe_problem(),
        bounded_parallel_test_config(2, Duration::from_secs(1)),
        Some(ay_core::time::Instant::now()),
    )
    .with_parallel_worker_limit(1)
    .with_sequential_test_engine(move |_idx, _cancellation| {
        observed_invoked.store(true, Ordering::SeqCst);
        EngineResult::Unified(PortfolioResult::Unknown, "TEST_MUST_NOT_RUN")
    });

    let mut report = BudgetReport::new();
    let result = solver.solve_parallel_with_report(&mut report);

    assert!(matches!(result, PortfolioResult::Unknown));
    assert!(!invoked.load(Ordering::SeqCst));
    assert_eq!(report.entries.len(), 2);
    assert!(report
        .entries
        .iter()
        .all(|entry| entry.stop_reason == EngineStopReason::NotStarted));
}

struct ParallelPrepareDelayGuard;

impl ParallelPrepareDelayGuard {
    fn for_engine(index: usize, delay: Duration) -> Self {
        PARALLEL_TEST_PREPARE_DELAY.with(|configured| configured.set(Some((index, delay))));
        Self
    }
}

impl Drop for ParallelPrepareDelayGuard {
    fn drop(&mut self) {
        PARALLEL_TEST_PREPARE_DELAY.with(|configured| configured.set(None));
    }
}

#[test]
fn bounded_parallel_lane_admission_timeout_does_not_strand_tail() {
    let _prepare_delay = ParallelPrepareDelayGuard::for_engine(0, Duration::from_millis(100));
    let launched = Arc::new(Mutex::new(Vec::new()));
    let observed_launched = launched.clone();
    let mut config = bounded_parallel_test_config(0, Duration::from_secs(1));
    config.engines = vec![
        EngineConfig::Pdr(PdrConfig::default()),
        EngineConfig::Bmc(BmcConfig::default()),
        EngineConfig::Kind(KindConfig::default()),
    ];
    config.engine_budgets.insert(
        EngineType::Pdr,
        BudgetPolicy::Fixed(Duration::from_millis(50)),
    );
    let solver = PortfolioSolver::new(create_safe_problem(), config)
        .with_parallel_worker_limit(1)
        .with_sequential_test_engine(move |idx, _cancellation| {
            observed_launched.lock().unwrap().push(idx);
            EngineResult::Unified(PortfolioResult::Unknown, "TEST_ADMISSION_TAIL")
        });

    let mut report = BudgetReport::new();
    let result = solver.solve_parallel_with_report(&mut report);

    assert!(matches!(result, PortfolioResult::Unknown));
    assert_eq!(*launched.lock().unwrap(), vec![1, 2]);
    assert_eq!(report.entries.len(), 3);
    assert_eq!(report.entries[0].stop_reason, EngineStopReason::Timeout);
    assert_eq!(
        report.entries[0].budget_allocated,
        Duration::from_millis(50)
    );
    assert!(report.entries[1..]
        .iter()
        .all(|entry| entry.stop_reason == EngineStopReason::Unknown));
}

#[test]
fn parallel_fixed_policy_is_a_live_lane_allocation() {
    let mut config = bounded_parallel_test_config(3, Duration::from_millis(300));
    config.engines = vec![
        EngineConfig::Pdr(PdrConfig::default()),
        EngineConfig::Bmc(BmcConfig::default()),
        EngineConfig::Kind(KindConfig::default()),
    ];
    config.engine_budgets.insert(
        EngineType::Pdr,
        BudgetPolicy::Fixed(Duration::from_millis(30)),
    );

    let budgets = PortfolioSolver::parallel_engine_budgets(Duration::from_millis(300), &config, 1);

    assert_eq!(budgets[0], Duration::from_millis(30));
    assert_eq!(budgets[1], Duration::from_millis(100));
    assert_eq!(budgets[2], Duration::from_millis(100));
}

#[test]
fn parallel_default_budgets_account_for_overlapping_worker_capacity() {
    let full_width = bounded_parallel_test_config(4, Duration::from_millis(400));
    assert_eq!(
        PortfolioSolver::parallel_engine_budgets(Duration::from_millis(400), &full_width, 4,),
        vec![Duration::from_millis(400); 4],
        "a one-wave portfolio must retain the full wall budget per concurrent lane"
    );

    let three_waves = bounded_parallel_test_config(5, Duration::from_millis(600));
    assert_eq!(
        PortfolioSolver::parallel_engine_budgets(Duration::from_millis(600), &three_waves, 2,),
        vec![Duration::from_millis(200); 5],
        "five engines at capacity two require three reserved waves"
    );

    let floor_limited = bounded_parallel_test_config(21, Duration::from_millis(100));
    assert_eq!(
        PortfolioSolver::parallel_engine_budgets(Duration::from_millis(100), &floor_limited, 1,),
        vec![Duration::from_millis(5); 21],
        "bounded waves must preserve the documented default 5% floor"
    );
}

#[test]
fn public_budget_report_keeps_active_and_disabled_indices_distinct() {
    let mut config = bounded_parallel_test_config(0, Duration::from_secs(1));
    config.engines = vec![
        EngineConfig::Pdr(PdrConfig::default()),
        EngineConfig::Bmc(BmcConfig::default()),
    ];
    config
        .engine_budgets
        .insert(EngineType::Pdr, BudgetPolicy::Disabled);
    let solver = PortfolioSolver::new(create_safe_problem(), config)
        .with_deterministic_sequential_schedule(None)
        .with_sequential_test_engine(|_idx, _cancellation| {
            EngineResult::Unified(PortfolioResult::Unknown, "TEST_ACTIVE_REPORT")
        });

    let (result, report) = solver.solve_with_budget_report();

    assert!(matches!(result, PortfolioResult::Unknown));
    assert_eq!(report.entries.len(), 2);
    assert_eq!(report.entries[0].index, 0);
    assert_eq!(report.entries[0].engine, EngineType::Bmc);
    assert_eq!(report.entries[0].stop_reason, EngineStopReason::Unknown);
    assert_eq!(report.entries[1].index, 1);
    assert_eq!(report.entries[1].engine, EngineType::Pdr);
    assert_eq!(report.entries[1].stop_reason, EngineStopReason::Disabled);
}

#[test]
fn public_budget_report_lists_all_disabled_engine_types() {
    let mut config = bounded_parallel_test_config(0, Duration::from_secs(1));
    config.engines = vec![
        EngineConfig::Pdr(PdrConfig::default()),
        EngineConfig::Bmc(BmcConfig::default()),
    ];
    config
        .engine_budgets
        .insert(EngineType::Pdr, BudgetPolicy::Disabled);
    config
        .engine_budgets
        .insert(EngineType::Bmc, BudgetPolicy::Disabled);
    let solver = PortfolioSolver::new(create_safe_problem(), config);

    let (result, report) = solver.solve_with_budget_report();

    assert!(matches!(result, PortfolioResult::Unknown));
    assert_eq!(report.entries.len(), 2);
    assert_eq!(
        report
            .entries
            .iter()
            .map(|entry| entry.index)
            .collect::<Vec<_>>(),
        vec![0, 1]
    );
    assert!(report.entries.iter().all(|entry| {
        entry.stop_reason == EngineStopReason::Disabled
            && entry.budget_allocated == Duration::ZERO
            && entry.elapsed == Duration::ZERO
    }));
}

#[test]
fn public_budget_report_marks_active_engines_not_started_at_expired_boundary() {
    let solver = PortfolioSolver::new_with_solve_limits(
        create_safe_problem(),
        bounded_parallel_test_config(2, Duration::from_secs(1)),
        Some(ay_core::time::Instant::now()),
    );

    let (result, report) = solver.solve_with_budget_report();

    assert!(matches!(result, PortfolioResult::Unknown));
    assert_eq!(report.entries.len(), 2);
    assert!(report.entries.iter().all(|entry| {
        entry.stop_reason == EngineStopReason::NotStarted
            && entry.budget_allocated == Duration::ZERO
            && entry.elapsed == Duration::ZERO
    }));
}

#[test]
fn public_budget_report_marks_active_engines_not_started_on_trivial_result() {
    let solver = PortfolioSolver::new(
        ChcProblem::new(),
        bounded_parallel_test_config(2, Duration::from_secs(1)),
    );

    let (result, report) = solver.solve_with_budget_report();

    assert!(matches!(result, PortfolioResult::Safe(_)));
    assert_eq!(report.entries.len(), 2);
    assert!(report.entries.iter().all(|entry| {
        entry.stop_reason == EngineStopReason::NotStarted
            && entry.budget_allocated == Duration::ZERO
            && entry.elapsed == Duration::ZERO
    }));
}

#[test]
#[timeout(5000)]
fn bounded_parallel_wrapper_panic_releases_slot_for_tail_winner() {
    let problem = create_safe_problem();
    let predicate = problem.predicates()[0].id;
    let x = ChcVar::new("bounded_panic_x", ChcSort::Int);
    let mut winning_model = InvariantModel::new();
    winning_model.set(
        predicate,
        PredicateInterpretation::new(
            vec![x.clone()],
            ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(10)),
        ),
    );
    let launched = Arc::new(Mutex::new(Vec::new()));
    let observed_launched = launched.clone();
    let solver = PortfolioSolver::new(
        problem,
        bounded_parallel_test_config(2, Duration::from_secs(2)),
    )
    .with_parallel_worker_limit(1)
    .with_sequential_test_engine(move |idx, _cancellation| {
        observed_launched.lock().unwrap().push(idx);
        if idx == 0 {
            std::panic::panic_any("intentional bounded-queue wrapper panic");
        }
        EngineResult::Unified(
            PortfolioResult::Safe(winning_model.clone()),
            "TEST_PANIC_TAIL_WINNER",
        )
    });

    let mut report = BudgetReport::new();
    assert!(matches!(
        solver.solve_parallel_with_report(&mut report),
        PortfolioResult::Safe(_)
    ));
    assert_eq!(*launched.lock().unwrap(), vec![0, 1]);
    assert_eq!(report.entries[0].stop_reason, EngineStopReason::Unknown);
    assert_eq!(report.entries[1].stop_reason, EngineStopReason::Completed);
}

#[test]
fn explicit_term_memory_budget_is_divided_by_live_worker_capacity() {
    let mut config = bounded_parallel_test_config(5, Duration::from_secs(1));
    config.memory_budget = Some(300);
    assert_eq!(config.per_engine_term_budget(3), Some(100));
    assert_eq!(config.per_engine_term_budget(1), Some(300));
}

#[test]
fn test_algebraic_prepass_does_not_emit_placeholder_unsafe_9691() {
    let source = include_str!("../mod.rs");
    let prepass = source
        .split("fn try_algebraic_prepass(&self) -> Option<PortfolioResult>")
        .nth(1)
        .and_then(|rest| rest.split("fn bv_to_int_for_algebraic(&self)").next())
        .expect("portfolio algebraic prepass should be present");

    assert!(
        !prepass.contains("PortfolioResult::Unsafe"),
        "raw PortfolioSolver algebraic prepass must not expose Unsafe without a replayable original witness"
    );
    assert!(
        prepass.contains("produced no replayable witness; returning Unknown"),
        "algebraic Unsafe must fail closed with an explicit replayability reason"
    );
}

#[test]
fn test_portfolio_safe_sequential() {
    let problem = create_safe_problem();
    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![EngineConfig::Pdr(PdrConfig::default())],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,

        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();

    match result {
        PortfolioResult::Safe(_) => {
            // Expected: PDR proves safety
        }
        PortfolioResult::Unsafe(_) => {
            panic!("Problem is safe, should not be unsafe");
        }
        PortfolioResult::Unknown | PortfolioResult::NotApplicable => {
            panic!("Sequential portfolio returned Unknown/NotApplicable on a small safe problem.")
        }
    }
}

/// Test BMC finds counterexample in problem with body predicate in query.
/// With level-based encoding (#108), BMC correctly handles body predicates.
#[test]
fn test_portfolio_bmc_with_body_predicate_finds_unsafe() {
    // The unsafe problem has a query with body predicate (Inv(x) /\ x >= 5 => false).
    // With level-based encoding (#108): BMC correctly finds counterexamples.
    let problem = create_unsafe_problem();
    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![EngineConfig::Bmc(BmcConfig::with_engine_config(
            10, false, None,
        ))],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,

        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();

    match result {
        PortfolioResult::Unsafe(_) => {
            // Expected: BMC correctly handles body predicates with level-based encoding
        }
        PortfolioResult::Unknown | PortfolioResult::NotApplicable => {
            panic!("BMC should find counterexample with level-based encoding (#108)");
        }
        PortfolioResult::Safe(_) => {
            panic!("Problem is unsafe, should not be safe");
        }
    }
}

/// Test BMC-only portfolio with a problem that has NO body predicate in query.
///
/// BMC can find a counterexample, but portfolio validation returns Unknown because it cannot
/// verify counterexamples for non-transition-system problems (query has no body predicate).
/// This is the correct conservative behavior after the #571 validation fix.
#[test]
fn test_portfolio_unsafe_bmc_no_body_predicate() {
    // Create a problem with a query that has no body predicate.
    // The query `x >= 5 => false` is semantically "for all x, x >= 5 implies false",
    // which is a pure constraint (not a transition system property).
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
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

    // Query: x >= 5 => false (NO Inv(x) in body!)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5))),
        ClauseHead::False,
    ));

    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![EngineConfig::Bmc(BmcConfig::with_engine_config(
            10, false, None,
        ))],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,

        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();

    // BMC finds a counterexample, but validation rejects it because:
    // 1. transition_system_encoding() returns None (query has no body predicate)
    // 2. verify_counterexample_without_witness() returns false
    // 3. Portfolio returns Unknown (can't verify the result)
    // This is the correct conservative behavior (#571).
    // Note: validate must be true for this test — without it, BMC results
    // bypass validation and are returned as-is (#5918).
    match result {
        PortfolioResult::Unknown | PortfolioResult::NotApplicable => {
            // Expected: BMC finds counterexample but validation can't verify it
        }
        PortfolioResult::Unsafe(_) => {
            // Would be incorrect - validation should have rejected this
            panic!("Non-transition-system BMC results should not pass validation");
        }
        PortfolioResult::Safe(_) => {
            panic!("Problem is semantically unsafe, should not be safe");
        }
    }
}

#[test]
fn test_portfolio_parallel_safe() {
    let problem = create_safe_problem();
    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![
            EngineConfig::Pdr(PdrConfig::default()),
            EngineConfig::Bmc(BmcConfig::default()),
        ],
        parallel: true,
        timeout: None,
        parallel_timeout: None,
        verbose: false,

        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();

    match result {
        PortfolioResult::Safe(_) => {
            // Expected: PDR wins the race
        }
        PortfolioResult::Unsafe(_) => {
            panic!("Problem is safe, should not be unsafe");
        }
        PortfolioResult::Unknown | PortfolioResult::NotApplicable => {
            panic!("Parallel portfolio returned Unknown/NotApplicable on a small safe problem.")
        }
    }
}

#[test]
fn test_portfolio_parallel_unsafe() {
    let problem = create_unsafe_problem();
    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![
            EngineConfig::Bmc(BmcConfig::with_engine_config(10, false, None)),
            EngineConfig::Pdr(PdrConfig::default()),
        ],
        parallel: true,
        timeout: None,
        parallel_timeout: None,
        verbose: false,

        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();

    match result {
        PortfolioResult::Unsafe(_) => {
            // Expected: either BMC or PDR finds counterexample
        }
        PortfolioResult::Safe(_) => {
            panic!("Problem is unsafe, should not be safe");
        }
        PortfolioResult::Unknown | PortfolioResult::NotApplicable => {
            // Should find counterexample
            panic!("Should find counterexample");
        }
    }
}

#[test]
fn test_portfolio_default_config() {
    let config = PortfolioConfig::production_default();
    // Source of truth: EngineSelector::default_engines() (#7946).
    // Decomposition + 2xPDR + BMC + PDKIND + IMC + DAR + TPA + CEGAR + TRL + Kind + LAWI = 12.
    assert_eq!(config.engines.len(), 12);
    assert!(
        config
            .engines
            .iter()
            .any(|engine| matches!(engine, EngineConfig::Dar(_))),
        "Default portfolio should include DAR"
    );
    assert!(
        config
            .engines
            .iter()
            .any(|engine| matches!(engine, EngineConfig::Cegar(_))),
        "Default portfolio should include CEGAR"
    );
    assert!(
        config
            .engines
            .iter()
            .any(|engine| matches!(engine, EngineConfig::Trl(_))),
        "Default portfolio should include TRL"
    );
    assert!(
        config
            .engines
            .iter()
            .any(|engine| matches!(engine, EngineConfig::Kind(_))),
        "Default portfolio should include Kind"
    );
    assert!(config.parallel);
    assert!(config.enable_preprocessing);
}

/// Validates that the default portfolio engine set is exactly the expected
/// set, in the expected order. This catches both accidental removals and
/// ensures new engines are deliberately placed.
#[test]
fn test_portfolio_default_engine_set_exact() {
    let config = PortfolioConfig::production_default();
    let engine_names: Vec<&str> = config
        .engines
        .iter()
        .map(|e| match e {
            EngineConfig::Decomposition(_) => "Decomposition",
            EngineConfig::Pdr(_) => "Pdr",
            EngineConfig::Bmc(_) => "Bmc",
            EngineConfig::Pdkind(_) => "Pdkind",
            EngineConfig::Imc(_) => "Imc",
            EngineConfig::Dar(_) => "Dar",
            EngineConfig::Tpa(_) => "Tpa",
            EngineConfig::Cegar(_) => "Cegar",
            EngineConfig::Trl(_) => "Trl",
            EngineConfig::Kind(_) => "Kind",
            EngineConfig::Lawi(_) => "Lawi",
        })
        .collect();
    assert_eq!(
        engine_names,
        vec![
            "Decomposition",
            "Pdr",
            "Pdr",
            "Bmc",
            "Pdkind",
            "Imc",
            "Dar",
            "Tpa",
            "Cegar",
            "Trl",
            "Kind",
            "Lawi",
        ],
        "Production portfolio engine set mismatch — update PortfolioConfig::production_default() or this test"
    );
}

#[test]
fn test_portfolio_empty_engines() {
    let problem = create_safe_problem();
    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,

        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();

    match result {
        PortfolioResult::Unknown => {
            // Expected: no engines means unknown
        }
        _ => panic!("Empty engines should return Unknown"),
    }
}

#[test]
fn test_portfolio_default_includes_decomposition() {
    let config = PortfolioConfig::production_default();

    let has_decomposition = config
        .engines
        .iter()
        .any(|e| matches!(e, EngineConfig::Decomposition(_)));

    assert!(
        has_decomposition,
        "Default portfolio should include Decomposition engine"
    );
}

/// Test budget_for_engine splits time correctly (#7932).
///
/// With 60s total and 2 engines, the first engine should get 1/2 of
/// remaining budget (30s), leaving at least 30s for the fallback.
#[test]
fn test_budget_for_engine_splits_evenly() {
    let total = Duration::from_mins(1);
    let deadline = ay_core::time::Instant::now() + total;

    // First of 2 engines: equal share = 60s / 2 = 30s.
    let budget = PortfolioSolver::budget_for_engine(total, deadline, 2);
    // Allow a small epsilon for time elapsed between now() calls.
    assert!(
        budget <= Duration::from_millis(30_100),
        "First engine budget should be ~30s (60/2), got {:.1}s",
        budget.as_secs_f64()
    );
    assert!(
        budget >= Duration::from_millis(29_500),
        "First engine budget should be close to 30s, got {:.1}s",
        budget.as_secs_f64()
    );

    // Last engine (1 remaining): gets all remaining budget.
    let budget_last = PortfolioSolver::budget_for_engine(total, deadline, 1);
    assert!(
        budget_last >= Duration::from_millis(59_500),
        "Last engine should get full remaining budget, got {:.1}s",
        budget_last.as_secs_f64()
    );
}

/// Test budget_for_engine with 3 engines (#7932).
///
/// With 60s total and equal-share allocation:
/// - Engine 0 (3 remaining): gets 60s / 3 = 20s
/// - Engine 1 (2 remaining): gets remaining 40s / 2 = 20s
/// - Engine 2 (1 remaining): gets all remaining 20s
#[test]
fn test_budget_for_engine_three_engines() {
    let total = Duration::from_mins(1);
    let deadline = ay_core::time::Instant::now() + total;

    // Engine 0: equal share = 60s / 3 = 20s.
    let b0 = PortfolioSolver::budget_for_engine(total, deadline, 3);
    assert!(
        b0 <= Duration::from_millis(20_100),
        "Engine 0/3 should get ~20s (60/3), got {:.1}s",
        b0.as_secs_f64()
    );
    assert!(
        b0 >= Duration::from_millis(19_500),
        "Engine 0/3 should get ~20s (60/3), got {:.1}s",
        b0.as_secs_f64()
    );

    // Simulate engine 0 consuming its full budget (~20s used, ~40s remaining).
    let deadline_after_e0 = deadline.checked_sub(b0).unwrap();
    let b1 = PortfolioSolver::budget_for_engine(total, deadline_after_e0, 2);
    // Engine 1: equal share of remaining ~40s / 2 = ~20s.
    assert!(
        b1 <= Duration::from_millis(20_200),
        "Engine 1/3 should get ~20s (40/2), got {:.1}s",
        b1.as_secs_f64()
    );
    assert!(
        b1 >= Duration::from_millis(19_500),
        "Engine 1/3 should get ~20s (40/2), got {:.1}s",
        b1.as_secs_f64()
    );
}

/// Test budget_for_engine respects total_timeout cap (#7932).
///
/// If total_timeout is 10s but remaining wall-clock is 60s, the per-engine
/// budget is still capped at 10s (the configured per-engine timeout).
#[test]
fn test_budget_for_engine_respects_timeout_cap() {
    let total = Duration::from_secs(10);
    // Deadline is 60s from now, but per-engine timeout is only 10s.
    let deadline = ay_core::time::Instant::now() + Duration::from_mins(1);

    let budget = PortfolioSolver::budget_for_engine(total, deadline, 2);
    // Equal share of 60s / 2 = 30s, but capped at total_timeout of 10s.
    assert!(
        budget <= Duration::from_millis(10_100),
        "Budget should be capped at total_timeout, got {:.1}s",
        budget.as_secs_f64()
    );
}

/// Test budget_for_engine with 11 engines avoids starvation (#7932).
///
/// With equal-share allocation: 60s / 11 = ~5.45s per engine. Even the
/// 11th engine gets a fair share. Under the old 50% halving scheme,
/// engine 11 would get only 60s * (1/2)^10 = 0.06s -- starvation.
#[test]
fn test_budget_for_engine_eleven_engines_no_starvation() {
    let total = Duration::from_mins(1);
    let deadline = ay_core::time::Instant::now() + total;

    // Simulate 11 engines each consuming their full budget.
    let mut remaining_deadline = deadline;
    let mut budgets = Vec::new();
    for engines_remaining in (1..=11).rev() {
        let b = PortfolioSolver::budget_for_engine(total, remaining_deadline, engines_remaining);
        budgets.push(b);
        remaining_deadline -= b;
    }

    // Every engine should get at least 4s (60s / 11 = 5.45s, minus epsilon).
    for (i, b) in budgets.iter().enumerate() {
        assert!(
            *b >= Duration::from_secs(4),
            "Engine {} of 11 got only {:.2}s -- budget starvation",
            i,
            b.as_secs_f64()
        );
    }

    // The first engine should get approximately 60/11 = 5.45s.
    assert!(
        budgets[0] <= Duration::from_millis(5_600),
        "Engine 0/11 should get ~5.45s (60/11), got {:.2}s",
        budgets[0].as_secs_f64()
    );
}

#[test]
fn deterministic_schedule_reports_exact_policy_aware_allocations() {
    use std::sync::{Arc, Mutex};

    let total = Duration::from_secs(90);
    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![
            EngineConfig::Bmc(BmcConfig::default()),
            EngineConfig::Pdr(PdrConfig::default()),
            EngineConfig::Kind(KindConfig::default()),
        ],
        parallel: false,
        timeout: Some(total),
        parallel_timeout: None,
        verbose: false,
        enable_preprocessing: false,
        engine_budgets: [
            (EngineType::Bmc, BudgetPolicy::MinPercent(50)),
            (
                EngineType::Pdr,
                BudgetPolicy::Fixed(Duration::from_secs(40)),
            ),
        ]
        .into_iter()
        .collect(),
        memory_budget: None,
        strict_proofs: false,
    };
    let launch_order = Arc::new(Mutex::new(Vec::new()));
    let observed_order = launch_order.clone();
    let solver = PortfolioSolver::new(create_safe_problem(), config)
        .with_deterministic_sequential_schedule(None)
        .with_sequential_test_engine(move |idx, _cancellation| {
            observed_order.lock().unwrap().push(idx);
            EngineResult::Unified(PortfolioResult::Unknown, "TEST_UNKNOWN")
        });

    let planned = PortfolioSolver::deterministic_engine_budgets(total, &solver.config);
    assert_eq!(
        planned,
        vec![
            Duration::from_secs(45),
            Duration::from_secs(40),
            Duration::from_secs(5),
        ],
        "the ordered cap must honor both policies and reserve the exact remainder deterministically"
    );

    let mut report = BudgetReport::new();
    let result = solver.solve_sequential_with_report(&mut report);

    assert!(matches!(result, PortfolioResult::Unknown));
    assert_eq!(*launch_order.lock().unwrap(), vec![0, 1, 2]);
    assert_eq!(report.entries.len(), 3);
    assert_eq!(report.entries[0].budget_allocated, planned[0]);
    assert_eq!(report.entries[1].budget_allocated, planned[1]);
    assert_eq!(report.entries[2].budget_allocated, planned[2]);
    assert!(report
        .entries
        .iter()
        .all(|entry| entry.stop_reason == EngineStopReason::Unknown));
}

#[test]
fn zero_fixed_budget_skips_only_that_sequential_engine() {
    let problem = create_safe_problem();
    let predicate = problem.predicates()[0].id;
    let x = ChcVar::new("zero_fixed_tail_x", ChcSort::Int);
    let mut winning_model = InvariantModel::new();
    winning_model.set(
        predicate,
        PredicateInterpretation::new(
            vec![x.clone()],
            ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(10)),
        ),
    );

    let mut config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![
            EngineConfig::Bmc(BmcConfig::default()),
            EngineConfig::Pdr(PdrConfig::default()),
        ],
        parallel: false,
        timeout: Some(Duration::from_secs(1)),
        parallel_timeout: None,
        verbose: false,
        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    config
        .engine_budgets
        .insert(EngineType::Bmc, BudgetPolicy::Fixed(Duration::ZERO));
    let launched = Arc::new(Mutex::new(Vec::new()));
    let observed_launched = launched.clone();
    let solver = PortfolioSolver::new(problem, config).with_sequential_test_engine(
        move |idx, _cancellation| {
            observed_launched.lock().unwrap().push(idx);
            EngineResult::Unified(
                PortfolioResult::Safe(winning_model.clone()),
                "TEST_ZERO_FIXED_TAIL_WINNER",
            )
        },
    );

    let mut report = BudgetReport::new();
    let result = solver.solve_sequential_with_report(&mut report);

    assert!(matches!(result, PortfolioResult::Safe(_)));
    assert_eq!(*launched.lock().unwrap(), vec![1]);
    assert_eq!(report.entries.len(), 2);
    assert_eq!(report.entries[0].index, 0);
    assert_eq!(report.entries[0].budget_allocated, Duration::ZERO);
    assert_eq!(report.entries[0].stop_reason, EngineStopReason::NotStarted);
    assert_eq!(report.entries[1].index, 1);
    assert_eq!(report.entries[1].stop_reason, EngineStopReason::Completed);
}

#[test]
fn deterministic_completion_deadline_is_half_open() {
    let before = ay_core::time::Instant::now();
    let deadline = before + Duration::from_millis(10);

    assert!(PortfolioSolver::deterministic_completion_within_budget(
        before, deadline
    ));
    assert!(!PortfolioSolver::deterministic_completion_within_budget(
        deadline, deadline
    ));
    assert!(!PortfolioSolver::deterministic_completion_within_budget(
        deadline + Duration::from_nanos(1),
        deadline,
    ));
}

#[test]
fn deterministic_expired_global_deadline_rejects_before_every_pre_engine_path() {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;

    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![EngineConfig::Pdr(PdrConfig::default())],
        parallel: false,
        timeout: Some(Duration::from_secs(1)),
        parallel_timeout: None,
        verbose: false,
        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let launched = Arc::new(AtomicBool::new(false));
    let observed_launch = launched.clone();
    let solver = PortfolioSolver::new(create_safe_problem(), config)
        .with_deterministic_sequential_schedule(Some(ay_core::time::Instant::now()))
        .with_sequential_test_engine(move |_idx, _cancellation| {
            observed_launch.store(true, Ordering::SeqCst);
            EngineResult::Unified(
                PortfolioResult::Safe(InvariantModel::new()),
                "TEST_MUST_NOT_LAUNCH",
            )
        });

    let result = solver.solve();
    let (reported_result, report) = solver.solve_with_budget_report();

    assert!(matches!(result, PortfolioResult::Unknown));
    assert!(matches!(reported_result, PortfolioResult::Unknown));
    assert_eq!(report.entries.len(), 1);
    assert_eq!(report.entries[0].index, 0);
    assert_eq!(report.entries[0].engine, EngineType::Pdr);
    assert_eq!(report.entries[0].stop_reason, EngineStopReason::NotStarted);
    assert_eq!(report.entries[0].budget_allocated, Duration::ZERO);
    assert_eq!(report.entries[0].elapsed, Duration::ZERO);
    assert!(
        !launched.load(Ordering::SeqCst),
        "an expired outer deadline must be checked before trivial/prepass/engine dispatch"
    );
}

#[test]
fn constructor_preprocessing_fails_closed_before_engine_dispatch() {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;

    let parent = crate::CancellationToken::new();
    parent.cancel();
    let config = PortfolioConfig {
        external_cancellation: Some(parent),
        engines: vec![EngineConfig::Pdr(PdrConfig::default())],
        parallel: false,
        timeout: Some(Duration::from_secs(1)),
        parallel_timeout: None,
        verbose: false,
        enable_preprocessing: true,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let launched = Arc::new(AtomicBool::new(false));
    let observed_launch = launched.clone();
    let solver = PortfolioSolver::new_with_solve_limits(
        create_safe_problem(),
        config,
        Some(ay_core::time::Instant::now() + Duration::from_secs(1)),
    )
    .with_sequential_test_engine(move |_idx, _cancellation| {
        observed_launch.store(true, Ordering::SeqCst);
        EngineResult::Unified(PortfolioResult::Unknown, "TEST_MUST_NOT_LAUNCH")
    });

    let (result, report) = solver.solve_with_budget_report();

    assert!(matches!(result, PortfolioResult::Unknown));
    assert_eq!(report.entries.len(), 1);
    assert_eq!(report.entries[0].index, 0);
    assert_eq!(report.entries[0].engine, EngineType::Pdr);
    assert_eq!(report.entries[0].stop_reason, EngineStopReason::NotStarted);
    assert_eq!(report.entries[0].budget_allocated, Duration::ZERO);
    assert_eq!(report.entries[0].elapsed, Duration::ZERO);
    assert!(!launched.load(Ordering::SeqCst));
}

#[test]
fn expired_constructor_deadline_seals_portfolio_as_unknown() {
    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![EngineConfig::Pdr(PdrConfig::default())],
        parallel: false,
        timeout: Some(Duration::from_secs(1)),
        parallel_timeout: None,
        verbose: false,
        enable_preprocessing: true,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let solver = PortfolioSolver::new_with_solve_limits(
        create_safe_problem(),
        config,
        Some(ay_core::time::Instant::now()),
    );

    assert!(matches!(solver.solve(), PortfolioResult::Unknown));
}

#[test]
fn expired_from_summary_deadline_seals_portfolio_before_dispatch() {
    use std::sync::atomic::{AtomicBool, Ordering};

    let summary = PreprocessSummary::build(create_safe_problem(), false);
    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![EngineConfig::Pdr(PdrConfig::default())],
        parallel: false,
        timeout: Some(Duration::from_secs(20)),
        parallel_timeout: None,
        verbose: false,
        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let launched = Arc::new(AtomicBool::new(false));
    let observed_launch = launched.clone();
    let solver = PortfolioSolver::from_summary_with_solve_limits(
        summary,
        config,
        Some(ay_core::time::Instant::now()),
    )
    .with_sequential_test_engine(move |_idx, _cancellation| {
        observed_launch.store(true, Ordering::SeqCst);
        EngineResult::Unified(PortfolioResult::Unknown, "TEST_MUST_NOT_LAUNCH")
    });

    let (result, report) = solver.solve_with_budget_report();

    assert!(matches!(result, PortfolioResult::Unknown));
    assert_eq!(report.entries.len(), 1);
    assert_eq!(report.entries[0].stop_reason, EngineStopReason::NotStarted);
    assert!(!launched.load(Ordering::SeqCst));
}

#[test]
#[timeout(2000)]
fn deterministic_timeout_recovers_predeadline_completion_delayed_before_publish() {
    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![EngineConfig::Pdr(PdrConfig::default())],
        parallel: false,
        timeout: Some(Duration::from_millis(100)),
        parallel_timeout: None,
        verbose: false,
        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let solver = PortfolioSolver::new(create_safe_problem(), config)
        .with_deterministic_sequential_schedule(None)
        .with_sequential_test_engine(|_idx, _cancellation| {
            EngineResult::Unified(PortfolioResult::Unknown, "TEST_PREDEADLINE")
        })
        .with_sequential_test_publish_delay(Duration::from_millis(150));

    let mut report = BudgetReport::new();
    let result = solver.solve_sequential_with_report(&mut report);

    assert!(matches!(result, PortfolioResult::Unknown));
    assert_eq!(report.entries.len(), 1);
    assert_eq!(
        report.entries[0].stop_reason,
        EngineStopReason::Unknown,
        "a pre-deadline completion must not become Timeout solely because publication was delayed"
    );
}

#[test]
#[timeout(2000)]
fn deterministic_timeout_reaps_before_starting_successor() {
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use std::sync::Arc;

    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![
            EngineConfig::Pdr(PdrConfig::default()),
            EngineConfig::Bmc(BmcConfig::default()),
        ],
        parallel: false,
        timeout: Some(Duration::from_millis(300)),
        parallel_timeout: None,
        verbose: false,
        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let launches = Arc::new([AtomicUsize::new(0), AtomicUsize::new(0)]);
    let active = Arc::new(AtomicUsize::new(0));
    let max_active = Arc::new(AtomicUsize::new(0));
    let cancellation_seen = Arc::new(AtomicBool::new(false));
    let observed_launches = launches.clone();
    let observed_active = active.clone();
    let observed_max_active = max_active.clone();
    let observed_cancellation = cancellation_seen.clone();
    let solver = PortfolioSolver::new(create_safe_problem(), config)
        .with_deterministic_sequential_schedule(None)
        .with_sequential_test_engine(move |idx, cancellation| {
            observed_launches[idx].fetch_add(1, Ordering::SeqCst);
            let now_active = observed_active.fetch_add(1, Ordering::SeqCst) + 1;
            observed_max_active.fetch_max(now_active, Ordering::SeqCst);

            if idx == 0 {
                // Deliberately ignore cancellation and produce a definitive
                // result after the exact 150ms share. The scheduler must
                // reject it, synchronously reap this worker, and only then
                // start engine 1 with the remaining whole-run time.
                thread::sleep(Duration::from_millis(200));
                observed_cancellation.store(cancellation.is_cancelled(), Ordering::SeqCst);
            }

            observed_active.fetch_sub(1, Ordering::SeqCst);
            if idx == 0 {
                EngineResult::Unified(
                    PortfolioResult::Safe(InvariantModel::new()),
                    "TEST_LATE_SAFE",
                )
            } else {
                EngineResult::Unified(PortfolioResult::Unknown, "TEST_SUCCESSOR")
            }
        });

    let mut report = BudgetReport::new();
    let started = ay_core::time::Instant::now();
    let result = solver.solve_sequential_with_report(&mut report);
    let elapsed = started.elapsed();

    assert!(
        matches!(result, PortfolioResult::Unknown),
        "a result produced after the deterministic boundary must not be accepted"
    );
    assert_eq!(report.entries.len(), 2);
    assert_eq!(report.entries[0].index, 0);
    assert_eq!(
        report.entries[0].budget_allocated,
        Duration::from_millis(150)
    );
    assert_eq!(report.entries[0].stop_reason, EngineStopReason::Timeout);
    assert!(report.entries[0].elapsed >= Duration::from_millis(195));
    assert_eq!(launches[0].load(Ordering::SeqCst), 1);
    assert!(
        elapsed >= Duration::from_millis(195),
        "deterministic solve returned before the timed-out worker was synchronously reaped: {elapsed:?}"
    );
    assert_eq!(active.load(Ordering::SeqCst), 0);
    assert!(cancellation_seen.load(Ordering::SeqCst));
    assert_eq!(
        launches[1].load(Ordering::SeqCst),
        1,
        "the deterministic scheduler should use remaining whole-run time after reaping"
    );

    assert_eq!(max_active.load(Ordering::SeqCst), 1);
    assert_eq!(report.entries.len(), 2);
    assert_eq!(report.entries[1].index, 1);
    assert_eq!(report.entries[1].stop_reason, EngineStopReason::Unknown);
    assert!(report.entries[1].budget_allocated > Duration::ZERO);
}

#[test]
#[timeout(2000)]
fn unbounded_sequential_engine_observes_external_cancellation() {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;

    let parent = crate::CancellationToken::new();
    let config = PortfolioConfig {
        external_cancellation: Some(parent.clone()),
        engines: vec![EngineConfig::Pdr(PdrConfig::default())],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,
        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let observed = Arc::new(AtomicBool::new(false));
    let worker_observed = observed.clone();
    let solver = PortfolioSolver::new(create_safe_problem(), config).with_sequential_test_engine(
        move |_idx, cancellation| {
            let started = ay_core::time::Instant::now();
            while started.elapsed() < Duration::from_secs(1) {
                if cancellation.is_cancelled() {
                    worker_observed.store(true, Ordering::SeqCst);
                    break;
                }
                thread::yield_now();
            }
            EngineResult::Unified(PortfolioResult::Unknown, "TEST_CANCELLED")
        },
    );

    let _cancel_guard = parent.cancel_after(Duration::from_millis(20));
    let result = solver.solve_sequential();

    assert!(matches!(result, PortfolioResult::Unknown));
    assert!(
        observed.load(Ordering::SeqCst),
        "an unbounded sequential engine must receive the external parent token"
    );
}

/// Test that sequential portfolio with budget splitting lets fallback engines run (#7932).
///
/// Creates a 2-engine sequential portfolio with a tight timeout. Engine 0 is
/// a slow BMC (huge depth, will timeout). Engine 1 is PDR (should solve quickly).
/// Without budget splitting, engine 0 would consume the entire timeout and
/// engine 1 would never run. With splitting, engine 0 gets ~50% of the budget,
/// leaving enough for engine 1 to solve.
#[test]
fn test_sequential_budget_split_allows_fallback_engine() {
    let problem = create_safe_problem();
    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![
            // Engine 0: BMC with huge depth - will not terminate within budget.
            EngineConfig::Bmc(BmcConfig::with_engine_config(1_000_000_000, false, None)),
            // Engine 1: PDR - should solve this trivial problem in <100ms.
            EngineConfig::Pdr(PdrConfig::default()),
        ],
        parallel: false,
        // Total budget: 2s. Without splitting, BMC would get all 2s and PDR gets 0s.
        // With splitting, BMC gets ~1s, PDR gets ~1s, and solves the problem.
        timeout: Some(Duration::from_secs(2)),
        parallel_timeout: None,
        verbose: false,

        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let solver = PortfolioSolver::new(problem, config);
    let start = ay_core::time::Instant::now();
    let result = solver.solve();
    let elapsed = start.elapsed();

    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "Fallback PDR engine should solve the problem, got: {result:?}"
    );
    // The total time should be roughly: BMC budget (~1s) + PDR solve (<0.5s).
    // It should be well under the 2s total budget.
    assert!(
        elapsed < Duration::from_secs(3),
        "Sequential solve should complete within 3s, took {:.1}s",
        elapsed.as_secs_f64()
    );
}
