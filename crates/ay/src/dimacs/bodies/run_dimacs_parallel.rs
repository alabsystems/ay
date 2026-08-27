// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#[derive(Clone, Copy)]
enum ParallelDimacsRoute {
    Portfolio { threads: usize },
    CubeAndConquer { depth: usize, threads: usize },
}

impl ParallelDimacsRoute {
    fn label(self) -> &'static str {
        match self {
            Self::Portfolio { .. } => "parallel-portfolio",
            Self::CubeAndConquer { .. } => "cube-and-conquer",
        }
    }

    fn source(self) -> &'static str {
        match self {
            Self::Portfolio { .. } => "--parallel",
            Self::CubeAndConquer { .. } => "--cube-and-conquer",
        }
    }

    fn unavailable_reason(self) -> &'static str {
        match self {
            Self::Portfolio { .. } => "workers use distinct portfolio startup strategies",
            Self::CubeAndConquer { .. } => "cube and conquer workers do not share one startup plan",
        }
    }
}

fn emit_parallel_dimacs_statistics(
    route: ParallelDimacsRoute,
    result: &SatResult,
    stats_cfg: stats_output::StatsConfig,
    unsat_authority: &mut Option<AuthorizedDimacsUnsatPublication>,
) {
    if !stats_cfg.any() {
        return;
    }
    if stats_cfg.human {
        emit_startup_capability_plan_unavailable(route.label(), route.unavailable_reason());
    }
    let result_str = match result {
        SatResult::Sat(_) => "sat",
        SatResult::Unsat(_) => "unsat",
        SatResult::Unknown => "unknown",
        #[allow(unreachable_patterns)]
        _ => "unknown",
    };
    let mut stats = stats_output::RunStatistics::new(
        stats_output::SolveMode::DimacsSat,
        result_str,
        global_elapsed(),
    );
    insert_startup_capability_plan_unavailable_stats(
        &mut stats,
        route.label(),
        route.unavailable_reason(),
    );
    match route {
        ParallelDimacsRoute::Portfolio { threads } => {
            stats.insert("sat.parallel_threads", threads as u64);
        }
        ParallelDimacsRoute::CubeAndConquer { depth, threads } => {
            stats.insert("sat.cube_and_conquer_depth", depth as u64);
            stats.insert("sat.cube_and_conquer_threads", threads as u64);
        }
    }
    stats.insert(
        "resource.rss_peak_bytes",
        ay_sys::current_rss_bytes() as u64,
    );
    stats.insert(
        "resource.memory_limit_bytes",
        ay_sys::get_process_memory_limit() as u64,
    );
    stats.insert("time.total_ms", global_elapsed().as_millis() as u64);
    if let Some(authority) = unsat_authority {
        validate_dimacs_unsat_publication_before_verdict(authority);
    }
    stats.emit(stats_cfg);
}

fn publish_parallel_dimacs_result(
    route: ParallelDimacsRoute,
    result: SatResult,
    mut unsat_authority: Option<AuthorizedDimacsUnsatPublication>,
) {
    match result {
        SatResult::Sat(model) => {
            crate::mark_verdict_printed();
            safe_println!("s SATISFIABLE");
            emit_dimacs_sat_model(&model);
            let _ = io::stdout().flush();
            let _ = io::stderr().flush();
            std::process::exit(crate::dimacs_verdict_exit_code(10));
        }
        SatResult::Unsat(_) => {
            let Some(authority) = &mut unsat_authority else {
                let reason = match route {
                    ParallelDimacsRoute::Portfolio { .. } => {
                        "parallel UNSAT route lost its publication authority"
                    }
                    ParallelDimacsRoute::CubeAndConquer { .. } => {
                        "cube-and-conquer UNSAT route lost its publication authority"
                    }
                };
                fail_dimacs_certification_or_exit(reason);
            };
            validate_dimacs_unsat_publication_before_verdict(authority);
            crate::mark_verdict_printed();
            safe_println!("s UNSATISFIABLE");
            authority.commit_after_verdict();
            let _ = io::stdout().flush();
            let _ = io::stderr().flush();
            std::process::exit(crate::dimacs_verdict_exit_code(20));
        }
        SatResult::Unknown => {
            dimacs_exit_if_timed_out(None);
            // Same memout-honesty rule as the sequential publication arm
            // (finish_pipeline.rs): an Unknown caused by the memory budget
            // reports the memout grammar/exit code, never generic-incomplete.
            if crate::memout_abort_requested() {
                crate::hard_memory_fallback_exit();
            }
            match route {
                ParallelDimacsRoute::Portfolio { .. } => safe_eprintln!(
                    "c reason: incomplete (parallel portfolio could not determine satisfiability)"
                ),
                ParallelDimacsRoute::CubeAndConquer { .. } => safe_eprintln!(
                    "c reason: incomplete (cube-and-conquer could not determine satisfiability)"
                ),
            }
            safe_println!("s UNKNOWN");
        }
        #[allow(unreachable_patterns)]
        _ => {
            safe_eprintln!("c reason: unknown");
            safe_println!("s UNKNOWN");
        }
    }
}

fn parallel_unsat_authority(
    content: &str,
    proof_config: Option<&ProofConfig>,
    formula: &ay_sat::DimacsFormula,
    result: &SatResult,
) -> Option<AuthorizedDimacsUnsatPublication> {
    matches!(result, SatResult::Unsat(_)).then(|| {
        authorize_dimacs_unsat_artifacts(
            DimacsInputSource::Content(content),
            proof_config,
            ProofArtifactTheoryMetadata::dimacs_sat(formula.num_vars, formula.clauses.len()),
        )
    })
}

fn run_dimacs_parallel_body(
    content: &str,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
    num_threads: usize,
) {
    reject_dimacs_decision_trace_or_exit();
    enforce_required_dimacs_proof_gate(proof_config);
    let formula = match parse_dimacs(content) {
        Ok(formula) => formula,
        Err(error) => {
            cleanup_dimacs_non_unsat_proof_paths(proof_config);
            safe_eprintln!("c Parse error: {error}");
            safe_println!("s UNKNOWN");
            std::process::exit(1);
        }
    };
    safe_eprintln!(
        "c parallel portfolio: {num_threads} threads, {} vars, {} clauses",
        formula.num_vars,
        formula.clauses.len()
    );
    let start = std::time::Instant::now();
    let mut portfolio = PortfolioSolver::new_adaptive(num_threads, &formula);
    if proof_config.is_some() {
        portfolio.set_proof_mode(true);
    }
    if let Some(handle) = INTERRUPT_HANDLE.get() {
        portfolio.set_external_cancel(handle.clone());
    }
    let (result, raw_proof_bytes) = portfolio.solve_with_proof_bytes(&formula);
    safe_eprintln!(
        "c parallel portfolio: solved in {:.3}s",
        start.elapsed().as_secs_f64()
    );
    cleanup_dimacs_non_unsat_proof_paths_for_result(&result, proof_config);
    if let (SatResult::Unsat(cert), Some(proof)) = (&result, proof_config) {
        let original = dimacs_original_clauses_from_literals(&formula.clauses);
        write_parallel_proof(raw_proof_bytes.as_deref(), cert, proof, &original);
    }
    let mut authority = parallel_unsat_authority(content, proof_config, &formula, &result);
    let route = ParallelDimacsRoute::Portfolio {
        threads: num_threads,
    };
    emit_parallel_dimacs_statistics(route, &result, stats_cfg, &mut authority);
    if let Some(authority) = &mut authority {
        validate_dimacs_unsat_publication_before_verdict(authority);
    }
    emit_sat_applied_run_summary(
        route.label(),
        route.source(),
        VariantRouteProfile::Standard,
        proof_config,
    );
    publish_parallel_dimacs_result(route, result, authority);
}
