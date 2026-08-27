// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

/// Ordered statistics request after solver selection and UNSAT authorization.
///
/// `solver` is the post-rescue authority. The publication token is validated
/// after in-memory statistics assembly but before statistics or the verdict can
/// expose an UNSAT result.
struct DimacsFinishStatisticsRequest<'solver, 'input, 'authority> {
    solver: &'solver mut SatSolver,
    result: &'input SatResult,
    stats: stats_output::StatsConfig,
    source: DimacsInputSource<'input>,
    proof: Option<&'input ProofConfig>,
    guard_cover: Option<&'input GuardCoverSidecarRunStats>,
    separator_cover: Option<&'input SeparatorCoverSidecarRunStats>,
    proof_writer_telemetry: Option<DimacsProofWriterTelemetry>,
    route: DimacsFinishStatisticsRoute,
    unsat_authority: &'authority mut Option<AuthorizedDimacsUnsatPublication>,
    route_profile: VariantRouteProfile,
}

fn dimacs_result_label(result: &SatResult) -> &'static str {
    match result {
        SatResult::Sat(_) => "sat",
        SatResult::Unsat(_) => "unsat",
        SatResult::Unknown => "unknown",
        #[allow(unreachable_patterns)]
        _ => "unknown",
    }
}

fn insert_dimacs_finish_capability_plan(
    solver: &SatSolver,
    route: DimacsFinishStatisticsRoute,
    run_stats: &mut stats_output::RunStatistics,
) {
    match route {
        DimacsFinishStatisticsRoute::Primary => {
            insert_startup_capability_plan_stats(run_stats, solver);
        }
        DimacsFinishStatisticsRoute::Rescue => insert_startup_capability_plan_unavailable_stats(
            run_stats,
            "finalize-rescue",
            "retry startup plan differs from the discarded first attempt",
        ),
    }
}

fn emit_dimacs_finish_statistics(request: DimacsFinishStatisticsRequest<'_, '_, '_>) {
    if request.stats.human {
        emit_dimacs_human_core(request.solver, request.guard_cover, request.separator_cover);
        emit_dimacs_human_preprocessing(request.solver, request.route);
        emit_dimacs_human_tail(request.solver);
    }
    let mut run_stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        dimacs_result_label(request.result),
        global_elapsed(),
    );
    {
        let mut statistics = DimacsStructuredStatistics {
            solver: &mut *request.solver,
            source: request.source,
            proof: request.proof,
            guard_cover: request.guard_cover,
            separator_cover: request.separator_cover,
            proof_writer_telemetry: request.proof_writer_telemetry,
            run_stats: &mut run_stats,
        };
        insert_dimacs_structured_core(&mut statistics);
        insert_dimacs_structured_bcp_core(&mut statistics);
        insert_dimacs_structured_bcp_buckets(&mut statistics);
        insert_dimacs_structured_identity(&mut statistics);
        insert_dimacs_structured_identity_rows(&mut statistics);
        insert_dimacs_structured_search(&mut statistics);
        insert_dimacs_structured_techniques(&mut statistics);
        insert_dimacs_structured_runtime(&mut statistics);
        insert_dimacs_structured_backbone(&mut statistics);
    }
    insert_dimacs_finish_capability_plan(request.solver, request.route, &mut run_stats);
    if let Some(authority) = request.unsat_authority.as_mut() {
        validate_dimacs_unsat_publication_before_verdict(authority);
    }
    emit_dimacs_run_stats(&run_stats, request.stats, request.route_profile);
}
