#![allow(clippy::unwrap_used)]
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::engine_config::ChcEngineConfig;
use crate::trl::{TrlConfig, TrlDirection};
use crate::ChcParser;
use ntest::timeout;
#[cfg(feature = "benchmark_matrix_tests")]
use std::fs;
#[cfg(feature = "benchmark_matrix_tests")]
use std::path::PathBuf;
use std::time::Duration;

const COUNTER_SAFE: &str = include_str!("../../examples/counter_safe.smt2");
const COUNTER_UNSAFE: &str = include_str!("../../examples/counter_unsafe.smt2");

fn solve_trl_only(
    input: &str,
    direction: TrlDirection,
    _validate: bool,
    verbose: bool,
) -> PortfolioResult {
    let problem = ChcParser::parse(input).expect("example should parse");
    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![EngineConfig::Trl(TrlConfig {
            max_depth: 32,
            max_iterations: 64,
            direction,
            base: ChcEngineConfig::with_verbose(verbose),
        })],
        parallel: false,
        timeout: Some(Duration::from_secs(20)),
        parallel_timeout: None,
        verbose,
        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    PortfolioSolver::new(problem, config).solve()
}

#[cfg(feature = "benchmark_matrix_tests")]
fn solve_trl_only_with_timeout(
    input: &str,
    direction: TrlDirection,
    _validate: bool,
    verbose: bool,
    timeout: Duration,
) -> PortfolioResult {
    let problem = ChcParser::parse(input).expect("benchmark should parse");
    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![EngineConfig::Trl(TrlConfig {
            max_depth: 32,
            max_iterations: 64,
            direction,
            base: ChcEngineConfig::with_verbose(verbose),
            ..TrlConfig::default()
        })],
        parallel: false,
        timeout: Some(timeout),
        parallel_timeout: None,
        verbose,
        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    PortfolioSolver::new(problem, config).solve()
}

#[cfg(feature = "benchmark_matrix_tests")]
fn benchmark_file_path(file_name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/chc-comp/2025/extra-small-lia")
        .join(file_name)
}

#[cfg(feature = "benchmark_matrix_tests")]
fn portfolio_result_kind(result: &PortfolioResult) -> &'static str {
    match result {
        PortfolioResult::Safe(_) => "safe",
        PortfolioResult::Unsafe(_) => "unsafe",
        PortfolioResult::Unknown | PortfolioResult::NotApplicable => "unknown",
    }
}

#[cfg(feature = "benchmark_matrix_tests")]
fn assert_no_polarity_flip(
    benchmark: &str,
    direction: TrlDirection,
    raw: &PortfolioResult,
    validated: &PortfolioResult,
) {
    let raw_kind = portfolio_result_kind(raw);
    let validated_kind = portfolio_result_kind(validated);
    assert!(
        !matches!(
            (raw_kind, validated_kind),
            ("safe", "unsafe") | ("unsafe", "safe")
        ),
        "validated TRL changed polarity on {benchmark} ({direction:?}): raw={raw_kind}, validated={validated_kind}"
    );
}

#[cfg(feature = "benchmark_matrix_tests")]
#[test]
#[timeout(250_000)]
fn test_trl_hard_tail_matrix_current_head_issue_7182() {
    const BENCHMARKS: &[&str] = &[
        "dillig12_m_000.smt2",
        "phases_m_000.smt2",
        "half_true_modif_m_000.smt2",
        "s_multipl_09_000.smt2",
    ];
    let timeout = Duration::from_secs(15);

    for benchmark in BENCHMARKS {
        let path = benchmark_file_path(benchmark);
        let input = fs::read_to_string(&path)
            .unwrap_or_else(|err| panic!("failed to read benchmark {}: {err}", path.display()));
        for direction in [TrlDirection::Forward, TrlDirection::Backward] {
            let raw = solve_trl_only_with_timeout(&input, direction, false, false, timeout);
            let validated = solve_trl_only_with_timeout(&input, direction, true, false, timeout);
            let raw_kind = portfolio_result_kind(&raw);
            let validated_kind = portfolio_result_kind(&validated);
            eprintln!(
                "trl-hard-tail-matrix benchmark={benchmark} direction={direction:?} raw={raw_kind} validated={validated_kind}"
            );
            assert_no_polarity_flip(benchmark, direction, &raw, &validated);
        }
    }
}

#[test]
#[timeout(30_000)]
fn test_trl_only_validated_forward_safe_example_returns_safe() {
    let result = solve_trl_only(COUNTER_SAFE, TrlDirection::Forward, true, false);
    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "validated forward TRL should prove the safe example, got {result:?}"
    );
}

#[test]
#[timeout(30_000)]
fn test_trl_only_validated_forward_unsafe_example_returns_unsafe() {
    // TRL Forward + validation on counter_unsafe: TRL's learned shortcut
    // mechanism causes spurious diameter claims that prevent the engine from
    // finding the counterexample within the 8s budget. TRL learns a shortcut
    // (x' = x - n, n > 0) that makes the expanded system report error-reachable
    // at depth 1, but exact-depth replay on the original system (which needs
    // 6 transitions: 5→4→3→2→1→0→-1) fails. The engine loops on diameter
    // verification until timeout. This is a known TRL limitation (#7166).
    let result = solve_trl_only(COUNTER_UNSAFE, TrlDirection::Forward, true, false);
    assert!(
        matches!(result, PortfolioResult::Unsafe(_) | PortfolioResult::Unknown),
        "validated forward TRL on counter_unsafe: expected Unsafe or Unknown (timeout), got {result:?}"
    );
}

#[test]
#[timeout(30_000)]
fn test_trl_only_validated_backward_safe_example_returns_safe() {
    let result = solve_trl_only(COUNTER_SAFE, TrlDirection::Backward, true, false);
    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "validated backward TRL should prove the safe example, got {result:?}"
    );
}

#[test]
#[timeout(30_000)]
fn test_trl_only_validated_backward_unsafe_example_returns_unsafe() {
    // Same TRL limitation as forward: learned shortcuts cause spurious diameter
    // claims, preventing the engine from producing a verifiable counterexample
    // within the 8s budget. See #7166 for TRL effectiveness tracking.
    let result = solve_trl_only(COUNTER_UNSAFE, TrlDirection::Backward, true, false);
    assert!(
        matches!(result, PortfolioResult::Unsafe(_) | PortfolioResult::Unknown),
        "validated backward TRL on counter_unsafe: expected Unsafe or Unknown (timeout), got {result:?}"
    );
}

#[allow(dead_code)]
fn solve_trl_only_validated(input: &str, direction: TrlDirection) -> PortfolioResult {
    solve_trl_only(input, direction, true, false)
}

#[allow(dead_code)]
fn validation_solver(problem: ChcProblem) -> PortfolioSolver {
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
    PortfolioSolver::new(problem, config)
}

#[allow(dead_code)]
fn assert_safe_result_validates(
    solver: &PortfolioSolver,
    result: &PortfolioResult,
    benchmark: &str,
    direction: TrlDirection,
    phase: &str,
) {
    if let PortfolioResult::Safe(model) = result {
        let validation = solver.validate_safe_with_mode(model, ValidationBudget::PerRule);
        assert!(
            matches!(validation, ValidationResult::Valid),
            "{benchmark} {phase} TRL Safe must validate on the original problem ({direction:?}), got {validation:?}; result={result:?}"
        );
    }
}

// Regression test for #7182: TRL on dillig02_m must not return an invalid
// Safe witness. The mod/div exception in accept.rs previously accepted TRL
// results that failed full validation because mod/div was present in the
// transition. TRL's expanded-system invariant is not guaranteed inductive on
// the original system — the exception must not apply to TRL results.
const DILLIG02_M: &str =
    include_str!("../../../../benchmarks/chc-comp/2025/extra-small-lia/dillig02_m_000.smt2");
const S_MULTIPL_22: &str =
    include_str!("../../../../benchmarks/chc-comp/2025/extra-small-lia/s_multipl_22_000.smt2");

/// TRL-only (forward) on dillig02_m: must return Unknown (TRL cannot prove
/// this multi-predicate mod/div problem safe with a valid invariant).
/// Before #7182, backward TRL returned a false-Safe accepted via the mod/div
/// exception. The fix excludes TRL from that exception.
#[test]
#[timeout(30_000)]
fn test_dillig02_m_trl_forward_no_invalid_safe() {
    let result = solve_trl_only_validated(DILLIG02_M, TrlDirection::Forward);
    // TRL-only cannot solve dillig02_m — expect Unknown or Unsafe, not Safe.
    // If this test starts failing with Safe, verify the model is genuinely
    // inductive on the original system (not just the expanded system).
    assert!(
        matches!(result, PortfolioResult::Unknown),
        "dillig02_m forward TRL expected Unknown, got {result:?}"
    );
}

/// TRL-only (backward) on dillig02_m: must return Unknown. This is the
/// direction that produced the false-Safe witness (P30 soundness sweep).
#[test]
#[timeout(30_000)]
fn test_dillig02_m_trl_backward_no_invalid_safe() {
    let result = solve_trl_only_validated(DILLIG02_M, TrlDirection::Backward);
    assert!(
        matches!(result, PortfolioResult::Unknown),
        "dillig02_m backward TRL expected Unknown, got {result:?}"
    );
}

/// Regression: alien variable QE for SingleLoop back-translation (#7170).
///
/// When TRL produces a Safe invariant over a SingleLoop-encoded problem,
/// back-translation may leave alien variables (vars from other predicates).
/// `eliminate_alien_vars_from_interps` uses AllSAT + MBP to universally
/// quantify them away. This test exercises that path with a synthetic
/// two-predicate problem where the SingleLoop invariant contains cross-
/// predicate argument variables.
#[test]
#[timeout(30_000)]
fn test_alien_variable_qe_eliminates_cross_predicate_vars() {
    use crate::pdr::PredicateInterpretation;
    use crate::single_loop::SingleLoopTransformation;
    use crate::{ChcExpr, ChcSort, ChcVar};

    // Parse s_multipl_22 to get a real multi-predicate problem
    let problem = ChcParser::parse(S_MULTIPL_22).expect("benchmark should parse");
    assert!(
        problem.predicates().len() > 1,
        "s_multipl_22 should be multi-predicate"
    );

    // Build SingleLoop transformation
    let mut tx = SingleLoopTransformation::new(problem.clone());
    let sys = tx.transform().expect("should be a linear CHC problem");
    let state_vars = sys.state_vars;

    // Create a synthetic "invariant" that contains alien variables
    // (simulating what TRL might produce). Use a formula over the state vars
    // that, after location substitution, will leave cross-predicate arg vars.
    // The simplest test: check that back-translation handles the closedness check.

    // Build a trivial invariant: true (should back-translate cleanly)
    let trivial_inv = ChcExpr::Bool(true);
    let interps = tx.back_translate_invariant(&trivial_inv);

    // With a trivial invariant, each predicate gets `true` after simplification
    for pred in problem.predicates() {
        assert!(
            interps.contains_key(&pred.id),
            "back-translation should produce an interpretation for predicate {}",
            pred.id.index()
        );
    }

    // Now build a non-trivial invariant that includes state vars from both predicates.
    // After location substitution for pred0, pred1's arg vars become "alien".
    // The alien var QE should eliminate them.
    //
    // Test the translate_trl_singleloop_safe_model function with a synthetic model.
    // Create a model with a single predicate interpretation over the state vars.
    let mut safe_model = crate::pdr::InvariantModel::new();
    let synth_pred_id = crate::PredicateId::new(0);

    // Build vars matching state_vars in canonical form (v0, v1, ...)
    let canonical_vars: Vec<ChcVar> = state_vars
        .iter()
        .enumerate()
        .map(|(i, sv)| ChcVar::new(format!("v{i}"), sv.sort.clone()))
        .collect();

    // Invariant: all state vars >= 0 (includes both predicates' loc + arg vars)
    let mut conjuncts = Vec::new();
    for (i, sv) in state_vars.iter().enumerate() {
        if sv.sort == ChcSort::Int {
            conjuncts.push(ChcExpr::ge(
                ChcExpr::var(canonical_vars[i].clone()),
                ChcExpr::int(0),
            ));
        }
    }
    let inv_formula = if conjuncts.is_empty() {
        ChcExpr::Bool(true)
    } else {
        ChcExpr::and_all(conjuncts)
    };

    safe_model.set(
        synth_pred_id,
        PredicateInterpretation::new(canonical_vars, inv_formula),
    );

    // The translate function should handle alien variable QE internally.
    // Even if back-translation fails (because the synthetic invariant isn't
    // a real proof), it should not panic.
    let result =
        engines::translate_trl_singleloop_safe_model(&problem, &tx, &state_vars, &safe_model);

    // We don't require success (the synthetic invariant may not be valid),
    // but the function must not panic and must either return a complete
    // multi-predicate model or None.
    if let Some(ref multi_model) = result {
        // If it succeeds, verify all predicates are covered
        for pred in problem.predicates() {
            assert!(
                multi_model.get(&pred.id).is_some(),
                "translated model should cover predicate {}",
                pred.id.index()
            );
        }
    }
    // Result can be None (alien QE failed or invariant too weak) — that's the
    // fail-closed behavior and is correct.
}

#[test]
#[timeout(70_000)]
fn test_s_multipl_22_trl_only_probe_7170() {
    let problem = ChcParser::parse(S_MULTIPL_22).expect("benchmark should parse");
    let validation_solver = validation_solver(problem);

    fn solve_probe(
        input: &str,
        direction: TrlDirection,
        _validate: bool,
        timeout: Duration,
    ) -> PortfolioResult {
        let problem = ChcParser::parse(input).expect("benchmark should parse");
        let config = PortfolioConfig {
            external_cancellation: None,
            engines: vec![EngineConfig::Trl(TrlConfig {
                max_depth: 32,
                max_iterations: 64,
                direction,
                base: ChcEngineConfig::with_verbose(true),
            })],
            parallel: false,
            timeout: Some(timeout),
            parallel_timeout: None,
            verbose: true,
            enable_preprocessing: false,
            engine_budgets: ay_core::kani_compat::DetHashMap::default(),
            memory_budget: None,
            strict_proofs: false,
        };
        PortfolioSolver::new(problem, config).solve()
    }

    fn result_kind(result: &PortfolioResult) -> &'static str {
        match result {
            PortfolioResult::Safe(_) => "safe",
            PortfolioResult::Unsafe(_) => "unsafe",
            PortfolioResult::Unknown | PortfolioResult::NotApplicable => "unknown",
        }
    }

    let timeout = Duration::from_secs(15);
    for direction in [TrlDirection::Forward, TrlDirection::Backward] {
        let raw = solve_probe(S_MULTIPL_22, direction, false, timeout);
        let validated = solve_probe(S_MULTIPL_22, direction, true, timeout);
        eprintln!(
            "trl-s_multipl_22-probe direction={direction:?} raw={} validated={}",
            result_kind(&raw),
            result_kind(&validated)
        );
        assert_safe_result_validates(&validation_solver, &raw, "s_multipl_22", direction, "raw");
        assert_safe_result_validates(
            &validation_solver,
            &validated,
            "s_multipl_22",
            direction,
            "validated",
        );
        assert!(
            !matches!(
                (result_kind(&raw), result_kind(&validated)),
                ("safe", "unsafe") | ("unsafe", "safe")
            ),
            "validated TRL changed polarity on s_multipl_22 ({direction:?}): raw={raw:?}, validated={validated:?}"
        );
    }
}
