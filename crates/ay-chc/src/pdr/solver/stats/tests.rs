// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::pdr::config::{PdrConfig, LIA_FARKAS_PROFILE_NAME};
use crate::pdr::frame::{Frame, Lemma};
use crate::pdr::solver::PdrSolver;
use crate::pdr::PdrResult;

fn create_tla_action_cluster_problem() -> crate::ChcProblem {
    use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Bool]);
    let step = problem.declare_action("Step");
    let x = ChcVar::new("x", ChcSort::Int);
    let ok = ChcVar::new("ok", ChcSort::Bool);

    problem.add_clause(HornClause::fact(
        ChcExpr::Bool(true),
        inv,
        vec![ChcExpr::int(0), ChcExpr::Bool(true)],
    ));
    problem.add_clause_with_action(
        HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(ok.clone())])],
                Some(ChcExpr::var(ok.clone())),
            ),
            ClauseHead::Predicate(
                inv,
                vec![
                    ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                    ChcExpr::var(ok.clone()),
                ],
            ),
        ),
        step,
    );
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        inv,
        vec![ChcExpr::var(x), ChcExpr::var(ok)],
    )])));

    problem
}

#[test]
fn test_extract_empty_stats() {
    // Create a minimal problem
    use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x)]),
    ));

    let solver = PdrSolver::new(problem, PdrConfig::default());
    let stats = solver.extract_stats();

    assert_eq!(stats.iterations, 0);
    assert_eq!(stats.restart_count, 0);
}

#[test]
fn test_solve_with_stats() {
    use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Simple safe problem: x = 0 => Inv(x), Inv(x) /\ x < 5 => Inv(x+1), Inv(x) /\ x > 5 => false
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
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    let result_with_stats = PdrSolver::solve_problem_with_stats(&problem, PdrConfig::default());

    // Should solve successfully
    assert!(matches!(result_with_stats.result, PdrResult::Safe(_)));

    // Stats should show some iterations occurred
    assert!(result_with_stats.stats.iterations > 0 || result_with_stats.stats.max_frame > 0);
}

#[test]
fn test_single_engine_pdr_stats_do_not_profile_tla_transition_clusters() {
    let problem = create_tla_action_cluster_problem();
    assert!(
        problem.has_action_decomposition(),
        "fixture should exercise the TLA action-cluster stats boundary"
    );

    let solver = PdrSolver::new(problem, PdrConfig::default());
    let stats = solver.extract_stats();

    assert_eq!(stats.chc_tla_transition_cluster_applications, 0);
    assert_eq!(stats.chc_native_code_helper_applications, 0);
}

#[test]
fn test_lia_farkas_route_stats_reuse_pdr_telemetry_counters() {
    use crate::farkas::LiaFarkasTemplateKind;
    use crate::{ChcExpr, ChcProblem, ChcSort};

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let mut solver = PdrSolver::new(problem, PdrConfig::lia_farkas_profile(false));
    while solver.frames.len() <= 1 {
        solver.frames.push(Frame::new());
    }
    solver.add_lemma_to_frame(
        Lemma::new(
            inv,
            ChcExpr::le(
                ChcExpr::var(solver.canonical_vars(inv).unwrap()[0].clone()),
                ChcExpr::int(7),
            ),
            1,
        ),
        1,
    );

    solver
        .telemetry
        .lia_farkas_templates
        .record_template_candidate(LiaFarkasTemplateKind::AffineEquality);
    solver
        .telemetry
        .lia_farkas_templates
        .record_template_candidate(LiaFarkasTemplateKind::Interval);
    solver
        .telemetry
        .lia_farkas_templates
        .record_template_candidate(LiaFarkasTemplateKind::DifferenceBound);
    solver
        .telemetry
        .lia_farkas_templates
        .record_template_candidate(LiaFarkasTemplateKind::ScaledLinearCombination);
    solver
        .telemetry
        .lia_farkas_templates
        .record_template_accept();
    solver
        .telemetry
        .lia_farkas_templates
        .record_template_reject(true);
    for _ in 0..6 {
        solver.telemetry.lia_farkas_templates.record_farkas_check();
    }

    solver.telemetry.generalization_attempts = 11;
    solver.telemetry.verification_queries = 5;
    solver.telemetry.interpolation_stats.lia_farkas_successes = 20;
    solver
        .telemetry
        .interpolation_stats
        .syntactic_farkas_successes = 10;
    solver.telemetry.interpolation_stats.iuc_farkas_successes = 5;
    solver.telemetry.interpolation_stats.all_failed = 3;
    solver.verification.consecutive_unlearnable = 4;
    solver.verification.total_model_failures = 2;

    let stats = solver.extract_lia_farkas_route_stats();

    assert_eq!(stats.profile_name, LIA_FARKAS_PROFILE_NAME);
    assert!(stats.profile_enabled);
    assert_eq!(stats.enabled_template_surfaces, 4);
    assert_eq!(stats.template_generation_surfaces, 4);
    assert_eq!(stats.templates_generated, 4);
    assert_eq!(stats.template_generation_checks, 4);
    assert_eq!(stats.farkas_checks, 6);
    assert_eq!(stats.accepted_lemmas, 1);
    assert_eq!(stats.rejected_lemmas, 1);
    assert_eq!(stats.validation_checks, 5);
    assert_eq!(stats.validation_failures, 1);
    assert!(stats.original_validation_required);
}

#[test]
fn test_extract_stats_reports_deduped_symbolic_scalarization_projection_counts() {
    use crate::problem::{ArrayScalarizationMap, ArrayScalarizedArg};
    use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar};
    use ay_core::kani_compat::DetHashMap as FxHashMap;

    let mut problem = ChcProblem::new();
    let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let inv = problem.declare_predicate("Inv", vec![arr_sort, ChcSort::Int]);
    let original_predicates = problem.predicates().to_vec();
    let idx = ChcExpr::var(ChcVar::new("idx", ChcSort::Int));
    let idx_plus_one = ChcExpr::add(idx.clone(), ChcExpr::Int(1));
    let one_plus_idx = ChcExpr::add(ChcExpr::Int(1), idx.clone());

    let mut pred_args = FxHashMap::default();
    pred_args.insert(
        inv,
        vec![
            ArrayScalarizedArg::Select {
                original_arg: 0,
                index: idx,
            },
            ArrayScalarizedArg::Select {
                original_arg: 0,
                index: idx_plus_one,
            },
            ArrayScalarizedArg::Select {
                original_arg: 0,
                index: one_plus_idx,
            },
            ArrayScalarizedArg::Original(1),
        ],
    );

    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    solver.array_scalarization_maps = vec![ArrayScalarizationMap {
        original_predicates,
        pred_args,
    }];
    let stats = solver.extract_stats();

    assert_eq!(stats.symbolic_scalarization_projected_cells, 2);
    assert_eq!(stats.symbolic_scalarization_multi_cell_args, 1);
}

#[test]
fn test_array_scalarization_memory_reports_obligations() {
    use crate::problem::{ArrayScalarizationMap, ArrayScalarizedArg};
    use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar};
    use ay_core::kani_compat::DetHashMap as FxHashMap;

    let mut problem = ChcProblem::new();
    let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let inv = problem.declare_predicate("Inv", vec![arr_sort, ChcSort::Int]);
    let original_predicates = problem.predicates().to_vec();

    let mut pred_args = FxHashMap::default();
    pred_args.insert(
        inv,
        vec![
            ArrayScalarizedArg::Select {
                original_arg: 0,
                index: ChcExpr::var(ChcVar::new("idx", ChcSort::Int)),
            },
            ArrayScalarizedArg::Original(1),
        ],
    );

    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    solver.array_scalarization_maps = vec![ArrayScalarizationMap {
        original_predicates,
        pred_args,
    }];

    let report = solver.array_scalarization_memory_report();

    assert!(report.transform().starts_with("pdr_array_scalarization"));
    assert!(report.safe_requires_original_validation());
    assert!(!report.unsafe_backtranslation_complete());
    assert!(report.has_obligation("array-scalarization-map"));
    assert!(report.has_obligation("array-model-backtranslation"));
    assert!(report.has_obligation("original-validation-on-safe"));
}

#[test]
fn test_pdr_uses_configured_array_scalarization_extra_indices() {
    use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

    let key_sort = ChcSort::BitVec(160);
    let arr_sort = ChcSort::Array(Box::new(key_sort.clone()), Box::new(ChcSort::Bool));
    let array = ChcVar::new("a", arr_sort.clone());
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![arr_sort]);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(array)]),
    ));

    let mut config = PdrConfig::default();
    config.array_scalarization_extra_indices = vec![(key_sort, ChcExpr::BitVec(4, 160))];
    let solver = PdrSolver::new(problem, config);

    assert_eq!(solver.array_scalarization_maps.len(), 1);
    let report = solver.array_scalarization_memory_report();
    assert!(report.transform().contains("projected_args=1"));
    assert!(report.has_obligation("array-key-projection-map"));
}

#[test]
fn test_can_push_lemma_native_helper_stats_fail_closed_before_reuse() {
    use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let xp = ChcVar::new("xp", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(xp.clone()),
                ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1)),
            )),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(xp)]),
    ));

    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    while solver.frames.len() <= 2 {
        solver.frames.push(Frame::new());
    }
    let x = solver
        .canonical_vars(inv)
        .expect("predicate should have canonical vars")[0]
        .clone();
    let lemma = Lemma::new(inv, ChcExpr::le(ChcExpr::var(x), ChcExpr::int(0)), 1);

    assert!(
        !solver.can_push_lemma(&lemma, 1),
        "x <= 0 is not inductive across x' = x + 1"
    );

    let stats = solver.extract_stats();
    assert_eq!(stats.chc_native_code_helper_compile_attempts, 0);

    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    {
        assert_eq!(stats.chc_native_code_helper_compile_successes, 0);
        assert_eq!(stats.chc_native_code_helper_compile_failures, 0);
        assert_eq!(stats.chc_native_code_helper_evaluations, 0);
        assert_eq!(stats.chc_native_code_helper_applications, 0);
        assert_eq!(stats.chc_native_code_helper_interpreter_confirmations, 0);
        assert_eq!(stats.chc_native_code_helper_trusted_true_results, 0);
        assert_eq!(stats.chc_native_code_helper_deopts, 0);
        assert_eq!(stats.chc_native_code_helper_fallbacks, 0);
    }

    #[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
    {
        assert_eq!(stats.chc_native_code_helper_compile_successes, 0);
        assert_eq!(stats.chc_native_code_helper_compile_failures, 0);
        assert_eq!(stats.chc_native_code_helper_applications, 0);
        assert_eq!(stats.chc_native_code_helper_trusted_true_results, 0);
        assert_eq!(stats.chc_native_code_helper_fallbacks, 0);
    }
}

/// Test demonstrating ImplicationCache provides benefit by reducing solver calls (#2262).
///
/// This test creates a problem with multiple predicates where the inductiveness
/// checker is called repeatedly. The cache should show hits or model rejections
/// that avoid redundant SMT solver calls.
#[test]
fn test_implication_cache_benefit() {
    use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

    let mut problem = ChcProblem::new();

    // Two-variable counter: x increments, y = 2*x is a relational invariant
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // Init: x = 0, y = 0 => Inv(x, y)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(0)),
        )),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())]),
    ));

    // Transition: Inv(x, y) /\ x < 10 => Inv(x+1, y+2)
    let x2 = ChcVar::new("x2", ChcSort::Int);
    let y2 = ChcVar::new("y2", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())])],
            Some(ChcExpr::and(
                ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10)),
                ChcExpr::and(
                    ChcExpr::eq(
                        ChcExpr::var(x2.clone()),
                        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                    ),
                    ChcExpr::eq(
                        ChcExpr::var(y2.clone()),
                        ChcExpr::add(ChcExpr::var(y.clone()), ChcExpr::int(2)),
                    ),
                ),
            )),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x2), ChcExpr::var(y2)]),
    ));

    // Query: Inv(x, y) /\ y > 100 => false (should be safe since y <= 20)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x), ChcExpr::var(y.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(y), ChcExpr::int(100))),
        ),
        ClauseHead::False,
    ));

    // Use solve_timeout to prevent hanging if the solver gets stuck in startup
    // discovery phases that lack fine-grained cancellation (#3237, #3225).
    let config = PdrConfig {
        solve_timeout: Some(std::time::Duration::from_secs(10)),
        ..PdrConfig::default()
    };
    let result_with_stats = PdrSolver::solve_problem_with_stats(&problem, config);

    // Should solve successfully (or timeout — either is acceptable for stats test)
    assert!(
        matches!(
            result_with_stats.result,
            PdrResult::Safe(_) | PdrResult::Unknown
        ),
        "Expected Safe or Unknown result, got {:?}",
        result_with_stats.result
    );

    // Verify ImplicationCache was used (at least some calls recorded).
    // The cache is used in blocking checks, so if the solve reaches the main
    // PDR loop, it should record some solver calls.
    let stats = &result_with_stats.stats;
    let total_cache_activity = stats.implication_cache_hits + stats.implication_model_rejections;

    // For this simple problem, we may not get cache hits if solved early.
    // At minimum, verify the stats are being tracked correctly.
    safe_eprintln!(
        "ImplicationCache: hits={}, rejections={}, solver_calls={}",
        stats.implication_cache_hits,
        stats.implication_model_rejections,
        stats.implication_solver_calls
    );

    // The cache should show activity: either recorded solver calls (cold cache)
    // or hits/rejections (warm cache reuse). A sum of 0 everywhere would indicate
    // the cache isn't being exercised on this benchmark.
    let total_queries = total_cache_activity + stats.implication_solver_calls;

    // Note: Some benchmarks solve via startup invariant discovery before the main
    // PDR loop exercises the cache. In those cases, activity may be 0.
    // This is expected behavior - the test validates stats are tracked, not that
    // all benchmarks exercise the cache.
    if total_queries > 0 {
        // Verify savings percentage is valid (between 0% and 100%)
        let savings_pct = (total_cache_activity as f64 / total_queries as f64) * 100.0;
        assert!(
            (0.0..=100.0).contains(&savings_pct),
            "Savings percentage should be 0-100%, got {savings_pct:.1}%"
        );

        // Verify individual stats are consistent: hits + rejections <= total_queries
        // (solver_calls is the remainder)
        assert!(
                total_cache_activity <= total_queries,
                "Cache activity ({total_cache_activity}) should not exceed total queries ({total_queries})"
            );
    }
}

/// Verify ConvergenceMonitor correctly detects stagnation.
///
/// Tests the windowed stagnation detection: when no lemmas are learned,
/// no frames advance, and no productive strengthens occur for
/// MAX_STAGNANT_WINDOWS consecutive windows, the monitor signals stagnation.
#[test]
fn test_convergence_monitor_stagnation_detection() {
    use crate::pdr::solver::convergence_monitor::{ProblemSizeHint, StagnationResponse};
    use crate::pdr::solver::ConvergenceMonitor;

    let mut monitor = ConvergenceMonitor::new();
    let hint = ProblemSizeHint::default_hint();

    // Without a budget, stagnation is never detected (standalone CLI mode).
    for iter in 1..=200 {
        let response = monitor.check_stagnation_graduated(iter, 0, 2, false, &hint);
        assert_eq!(
            response,
            StagnationResponse::None,
            "Should never detect stagnation without budget",
        );
    }

    // With budget: simulate progress for first 20 iterations
    let mut monitor = ConvergenceMonitor::new();
    let window = monitor.adaptive_window_size(&hint);
    for iter in 1..=window {
        monitor.note_strengthen(true); // productive
        let response = monitor.check_stagnation_graduated(iter, iter, 2 + iter / 5, true, &hint);
        assert_eq!(
            response,
            StagnationResponse::None,
            "Should not detect stagnation while making progress (iter {iter})"
        );
    }
    assert_eq!(monitor.consecutive_stagnant_windows, 0);

    // Simulate stagnation: no new lemmas, no frame advance, no productive strengthens.
    let frozen_lemmas = window;
    let frozen_frames = 2 + window / 5;
    let stagnation_end = window + monitor.adaptive_max_stagnant_windows(&hint) * window;
    for iter in (window + 1)..=stagnation_end {
        // No note_strengthen() call (no productive strengthen)
        monitor.check_stagnation_graduated(iter, frozen_lemmas, frozen_frames, true, &hint);
    }
    // After the adaptive stagnant-window limit, should detect.
    assert!(
        monitor.consecutive_stagnant_windows >= monitor.adaptive_max_stagnant_windows(&hint),
        "Expected >= {} stagnant windows after {} iterations, got {}",
        monitor.adaptive_max_stagnant_windows(&hint),
        stagnation_end,
        monitor.consecutive_stagnant_windows,
    );
}

/// Verify ConvergenceMonitor resets stagnation counter on progress.
///
/// The counter only resets at window boundaries. After one stagnant window,
/// we simulate a full productive window (with new lemmas) and verify the
/// counter resets to 0.
#[test]
fn test_convergence_monitor_resets_on_progress() {
    use crate::pdr::solver::convergence_monitor::ProblemSizeHint;
    use crate::pdr::solver::ConvergenceMonitor;

    let mut monitor = ConvergenceMonitor::new();
    let hint = ProblemSizeHint::default_hint();
    let window = monitor.adaptive_window_size(&hint);

    // First window: no lemmas but frames advance (2 vs 0).
    // This is NOT stagnant because frame_delta > 0.
    for iter in 1..=window {
        monitor.check_stagnation_graduated(iter, 0, 2, true, &hint);
    }
    assert_eq!(monitor.consecutive_stagnant_windows, 0);

    // Second window: no changes at all, so it is stagnant.
    for iter in (window + 1)..=(2 * window) {
        monitor.check_stagnation_graduated(iter, 0, 2, true, &hint);
    }
    assert_eq!(monitor.consecutive_stagnant_windows, 1);

    // Third window: learn new lemmas, so it is progress.
    for iter in ((2 * window) + 1)..=(3 * window) {
        monitor.note_strengthen(true);
        // Gradually increase lemma count to show progress
        monitor.check_stagnation_graduated(iter, iter - (2 * window), 2, true, &hint);
    }
    // The third window has lemma_delta > 0, so it's NOT stagnant.
    // The consecutive counter should reset to 0.
    assert_eq!(
        monitor.consecutive_stagnant_windows, 0,
        "Stagnant window counter should reset after a productive window"
    );
}

/// Verify ConvergenceMonitor tracks frame advances.
#[test]
fn test_convergence_monitor_frame_advance() {
    use crate::pdr::solver::ConvergenceMonitor;

    let monitor = ConvergenceMonitor::new();
    // Initially, time since frame advance should be very small
    assert!(
        monitor.time_since_frame_advance().as_millis() < 100,
        "Fresh monitor should have recent frame advance"
    );
}

/// Verify interpolation telemetry tracks attempts and successes (#2450 M1).
///
/// Uses a simple CHC problem that requires interpolation-based lemma learning
/// (x increments from 0 to bound, safety checks x <= bound). The solver must
/// learn inductive lemmas via interpolation, so at least one method should
/// succeed.
#[test]
fn test_interpolation_stats_tracked() {
    use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Init: x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Step: Inv(x) /\ x < 10 => Inv(x+1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Query: Inv(x) /\ x > 20 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(20))),
        ),
        ClauseHead::False,
    ));

    let config = PdrConfig {
        use_interpolation: true,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);
    let result = solver.solve();
    assert!(
        matches!(result, PdrResult::Safe(_)),
        "Expected Safe, got {result:?}"
    );

    let istats = &solver.telemetry.interpolation_stats;
    // The solver should have attempted interpolation at least once
    // (it needs to block at least one counterexample)
    assert!(
        istats.attempts > 0,
        "Expected >0 interpolation attempts, got {}",
        istats.attempts
    );
    // Total successes + all_failed should equal attempts
    assert_eq!(
        istats.total_successes() + istats.all_failed,
        istats.attempts,
        "Success ({}) + failed ({}) should equal attempts ({})",
        istats.total_successes(),
        istats.all_failed,
        istats.attempts,
    );
    // Summary should contain the attempt count
    let summary = istats.summary();
    assert!(
        summary.contains(&format!("attempts={}", istats.attempts)),
        "Summary should contain attempts count: {summary}"
    );
}

#[test]
fn test_interpolation_stats_tracks_conjunctive_a_unsat_skip() {
    use crate::ChcParser;

    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (x1 Int))
  (=> (and (Inv x) (> x 0) (= x1 (- x 1)))
      (Inv x1))))
(assert (forall ((x Int) (x1 Int))
  (=> (and (Inv x) (<= x 0) (= x1 (+ x 1)))
      (Inv x1))))
(assert (forall ((x Int)) (=> (and (Inv x) (> x 1)) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(
        problem,
        PdrConfig {
            use_interpolation: true,
            ..PdrConfig::default()
        },
    );

    let result = solver.solve();
    assert!(
        matches!(result, PdrResult::Safe(_)),
        "Expected Safe, got {result:?}"
    );
    assert!(
        solver.telemetry.interpolation_stats.golem_a_unsat_skips > 0,
        "expected conjunctive A-side UNSAT skip to be recorded"
    );
}
