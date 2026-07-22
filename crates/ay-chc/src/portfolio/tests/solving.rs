// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

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
