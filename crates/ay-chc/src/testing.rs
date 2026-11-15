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

/// Board-level counters of one direct PDR solve (Workstream B locks L-V/L2;
/// `DESIGN_spacer_pob_lemma_pipeline.md` §6 S11).
#[derive(Debug, Clone, Default, PartialEq)]
pub struct PdrTestStats {
    /// Lemmas in the frames at the end of the solve.
    pub lemmas_learned: usize,
    /// Highest frame index reached.
    pub max_frame: usize,
    /// Proof obligations popped by `strengthen`.
    pub pobs_processed: usize,
    /// POBs that were blocked with a lemma.
    pub blocked_pobs: usize,
    /// Lemmas recorded by the board (legacy + lane).
    pub board_lemmas: usize,
    /// Share of processed POBs that were point cubes.
    pub point_cube_share: f64,
    /// Lemmas per blocked POB.
    pub lemmas_per_blocked_pob: f64,
    /// The full board counter block (`SpacerCoreStats::json()`).
    pub counters: serde_json::Value,
    /// Candidate models that failed verification during the solve.
    pub model_verification_failures: usize,
}

/// Run one direct PDR solve (no case-split prepass) and return the result
/// with the board counters.
pub fn pdr_solve_with_stats(problem: &ChcProblem, config: PdrConfig) -> (PdrResult, PdrTestStats) {
    let mut solver = PdrSolver::new(problem.clone(), config);
    let run = solver.solve_with_stats();
    let stats = PdrTestStats {
        lemmas_learned: run.stats.lemmas_learned,
        max_frame: run.stats.max_frame,
        pobs_processed: run.stats.spacer_pobs_processed,
        blocked_pobs: run.stats.spacer_blocked_pobs,
        board_lemmas: run.stats.spacer_lemmas,
        point_cube_share: run.stats.spacer_point_cube_share,
        lemmas_per_blocked_pob: run.stats.spacer_lemmas_per_blocked_pob,
        counters: run.stats.spacer_counters,
        model_verification_failures: run.stats.model_verification_failures,
    };
    (run.result, stats)
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

/// The `HornSmt` session's differential harness (#horn-smt-session Rung 1,
/// design §8 / §10.1; WP-4) for out-of-crate tests such as
/// `tests/group_soundness/session_pushpop_vs_z3.rs`, which needs z3 on
/// `PATH`. Each driver returns a report whose `passed()` is the 0-disagreement
/// bar; `disagreements` carries the offending scripts verbatim.
pub mod session_harness {
    pub use crate::smt::session::harness::{
        run_diff_lra, run_pushpop_files, run_pushpop_fuzz, run_replay, DiffReport, ReplayReport,
        Verdict, Z3,
    };
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
