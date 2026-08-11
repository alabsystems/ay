// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// Re-export the stable engine constructors so existing test code using
// `testing::new_pdr_solver` and `testing::new_portfolio_solver` continues
// to compile without changes.
pub use super::engines::{new_pdr_solver, new_portfolio_solver};

/// Construct a [`BmcSolver`] for testing.
pub fn new_bmc_solver(problem: ChcProblem, config: BmcConfig) -> BmcSolver {
    BmcSolver::new(problem, config)
}

/// Construct a [`PdkindSolver`] for testing.
pub fn new_pdkind_solver(problem: ChcProblem, config: PdkindConfig) -> PdkindSolver {
    PdkindSolver::new(problem, config)
}

/// Construct a [`PdkindSolver`] with default config for testing.
pub fn pdkind_solver_defaults(problem: ChcProblem) -> PdkindSolver {
    PdkindSolver::with_defaults(problem)
}

/// Construct a [`PdkindSolver`] with cancellation for testing.
pub fn pdkind_solver_cancellation(problem: ChcProblem, token: CancellationToken) -> PdkindSolver {
    PdkindSolver::with_cancellation(problem, token)
}

/// Construct a [`KindSolver`] for testing.
pub fn new_kind_solver(problem: ChcProblem, config: KindConfig) -> KindSolver {
    KindSolver::new(problem, config)
}

/// Run PDR on a problem for testing (convenience wrapper for
/// `PdrSolver::solve_problem`).
pub fn pdr_solve_problem(problem: &ChcProblem, config: PdrConfig) -> PdrResult {
    PdrSolver::solve_problem(problem, config)
}

/// Parse a CHC input string and run PDR for testing (convenience wrapper
/// for `PdrSolver::solve_from_str`).
pub fn pdr_solve_from_str(input: &str, config: PdrConfig) -> ChcResult<PdrResult> {
    PdrSolver::solve_from_str(input, config)
}

/// Parse a CHC file and run PDR for testing (convenience wrapper for
/// `PdrSolver::solve_from_file`).
pub fn pdr_solve_from_file(
    path: impl AsRef<std::path::Path>,
    config: PdrConfig,
) -> ChcResult<PdrResult> {
    PdrSolver::solve_from_file(path, config)
}

/// Report whether adaptive classification selects the direct BV-native
/// simple-loop route for the given problem.
pub fn adaptive_uses_bv_native_direct_route(problem: &ChcProblem) -> bool {
    let adaptive = AdaptivePortfolio::new(problem.clone(), AdaptiveConfig::default());
    let features = classifier::ProblemClassifier::classify(problem);
    adaptive.use_bv_native_direct_route(&features)
}

/// Parse an SMT model value through the CHC SMT backend's model parser.
///
/// This stays under `testing` so integration tests can verify parser
/// regressions without depending on the crate's internal module layout.
pub fn parse_smt_model_value_for_testing(input: &str, sort: &ay_core::Sort) -> Option<SmtValue> {
    smt::parse_model_value_for_testing(input, sort)
}

/// Direction for TRL-only test runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TrlTestDirection {
    /// Run TRL on the original transition system.
    Forward,
    /// Run TRL on the reversed transition system (init/query swapped).
    Backward,
}

/// Parse a CHC problem from a string and run TRL-only in the given direction.
///
/// Returns a [`PortfolioResult`] (which is a type alias for [`ChcEngineResult`]).
/// If `validate` is true, the TRL config enables verbose mode for diagnostics.
pub fn solve_trl_only_from_str(
    input: &str,
    direction: TrlTestDirection,
    validate: bool,
    timeout: std::time::Duration,
) -> ChcResult<PortfolioResult> {
    use crate::engine_config::ChcEngineConfig;
    use crate::transition_system::TransitionSystem;
    use crate::trl::{TrlConfig, TrlSolver};

    let problem = ChcParser::parse(input).map_err(|e| ChcError::Parse(e.to_string()))?;
    let ts = TransitionSystem::from_chc_problem(&problem).map_err(ChcError::Parse)?;

    let ts = match direction {
        TrlTestDirection::Forward => ts,
        TrlTestDirection::Backward => ts.reverse(),
    };

    let token = CancellationToken::new();
    let _timeout_guard = token.cancel_after(timeout);

    let config = TrlConfig {
        base: ChcEngineConfig {
            verbose: validate,
            cancellation_token: Some(token),
        },
        ..TrlConfig::default()
    };

    let mut solver = TrlSolver::new(ts, config);
    let result = solver.solve();
    // _timeout_guard is dropped here, immediately stopping the timer thread.
    Ok(result)
}
