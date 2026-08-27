// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn finish_dimacs_solve(
    solver: &mut SatSolver,
    result: SatResult,
    stats_cfg: stats_output::StatsConfig,
    content: &str,
    proof_config: Option<&ProofConfig>,
    guard_cover: Option<&GuardCoverSidecarRunStats>,
    separator_cover: Option<&SeparatorCoverSidecarRunStats>,
) {
    finish_dimacs_solve_with_source(
        solver,
        result,
        stats_cfg,
        DimacsInputSource::Content(content),
        proof_config,
        guard_cover,
        separator_cover,
        None,
    );
}

fn emit_startup_capability_plan(solver: &SatSolver) {
    for decision in solver.capability_ledger().entries() {
        safe_eprintln!(
            "c startup_capability: {:<12} {:<10} {:<8} {}",
            decision.capability,
            decision.state.label(),
            decision.source.label(),
            decision.because
        );
    }
}

fn emit_startup_capability_plan_unavailable(route: &str, because: &str) {
    safe_eprintln!("c startup_capability_plan: unavailable route={route} because={because}");
}

fn insert_startup_capability_plan_stats(
    run_stats: &mut stats_output::RunStatistics,
    solver: &SatSolver,
) {
    run_stats.insert("sat.capability_plan.available", 1);
    run_stats.insert_text("sat.capability_plan.status", "available");
    for decision in solver.capability_ledger().entries() {
        let prefix = format!("sat.capability.{}", decision.capability);
        let source_code = match decision.source {
            DecisionSource::Cli => 0,
            DecisionSource::Auto => 1,
            DecisionSource::Default => 2,
            DecisionSource::EnvShim(_) => 3,
        };
        run_stats.insert(&format!("{prefix}.source"), source_code);
        run_stats.insert_text(&format!("{prefix}.source_label"), decision.source.label());
        run_stats.insert_text(&format!("{prefix}.state"), decision.state.label());
        run_stats.insert_text(&format!("{prefix}.because"), decision.because.clone());
    }
}

fn insert_startup_capability_plan_unavailable_stats(
    run_stats: &mut stats_output::RunStatistics,
    route: &str,
    reason: &str,
) {
    run_stats.insert("sat.capability_plan.available", 0);
    run_stats.insert_text("sat.capability_plan.status", "unavailable");
    run_stats.insert_text("sat.capability_plan.route", route);
    run_stats.insert_text("sat.capability_plan.reason", reason);
}

/// Identifies which solver survived finalize rescue and owns emitted statistics.
///
/// Both variants refer to the post-rescue authority selected before proof
/// publication validation, statistics, or verdict output begins.
#[derive(Clone, Copy)]
enum DimacsFinishStatisticsRoute {
    Primary,
    Rescue,
}

/// Mutable statistics view over the single authoritative post-rescue solver.
///
/// This view only assembles an in-memory record. The pipeline validates any
/// publication token before emitting that record or the verdict. Mutable
/// access is retained because proof telemetry may flush the writer.
struct DimacsStructuredStatistics<'solver, 'input, 'stats> {
    solver: &'solver mut SatSolver,
    source: DimacsInputSource<'input>,
    proof: Option<&'input ProofConfig>,
    guard_cover: Option<&'input GuardCoverSidecarRunStats>,
    separator_cover: Option<&'input SeparatorCoverSidecarRunStats>,
    proof_writer_telemetry: Option<DimacsProofWriterTelemetry>,
    run_stats: &'stats mut stats_output::RunStatistics,
}
