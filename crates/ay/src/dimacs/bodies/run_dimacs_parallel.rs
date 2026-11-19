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
            crate::claim_decisive_verdict_or_yield(crate::dimacs_verdict_exit_code(10));
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
            crate::claim_decisive_verdict_or_yield(crate::dimacs_verdict_exit_code(20));
            safe_println!("s UNSATISFIABLE");
            authority.commit_after_verdict();
            let _ = io::stdout().flush();
            let _ = io::stderr().flush();
            std::process::exit(crate::dimacs_verdict_exit_code(20));
        }
        SatResult::Unknown => {
            dimacs_exit_if_timed_out(None, None);
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
            settle_unanswered_dimacs_exit();
            if !crate::mark_verdict_printed() {
                safe_println!("s UNKNOWN");
            }
        }
        #[allow(unreachable_patterns)]
        _ => {
            settle_unanswered_dimacs_exit();
            safe_eprintln!("c reason: unknown");
            if !crate::mark_verdict_printed() {
                safe_println!("s UNKNOWN");
            }
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

/// Stack of the race's sequential member, the size the sequential DIMACS
/// route is given when it runs alone (`run_dimacs_from_file_on_dedicated_stack`).
const PARALLEL_SEQUENTIAL_MEMBER_STACK_SIZE: usize = 64 * 1024 * 1024;

/// One `--parallel N` portfolio solve and what its publication needs.
struct ParallelPortfolioRun<'a> {
    content: &'a str,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&'a ProofConfig>,
    formula: &'a ay_sat::DimacsFormula,
    portfolio: &'a PortfolioSolver,
    /// The `N` of `--parallel N`, the sequential member included.
    num_threads: usize,
    start: std::time::Instant,
}

impl ParallelPortfolioRun<'_> {
    /// Publish the portfolio's result: the proof, the statistics, the verdict.
    /// A decisive result ends the process here.
    fn finish(&self, result: SatResult, raw_proof_bytes: Option<Vec<u8>>) {
        safe_eprintln!(
            "c parallel portfolio: solved in {:.3}s",
            self.start.elapsed().as_secs_f64()
        );
        if let Some(winner) = self.portfolio.last_winner() {
            safe_eprintln!("c parallel portfolio: answer from worker {winner}");
        }
        cleanup_dimacs_non_unsat_proof_paths_for_result(&result, self.proof_config);
        if let (SatResult::Unsat(cert), Some(proof)) = (&result, self.proof_config) {
            let original = dimacs_original_clauses_from_literals(&self.formula.clauses);
            write_parallel_proof(raw_proof_bytes.as_deref(), cert, proof, &original);
        }
        let mut authority =
            parallel_unsat_authority(self.content, self.proof_config, self.formula, &result);
        let route = ParallelDimacsRoute::Portfolio {
            threads: self.num_threads,
        };
        emit_parallel_dimacs_statistics(route, &result, self.stats_cfg, &mut authority);
        if let Some(authority) = &mut authority {
            validate_dimacs_unsat_publication_before_verdict(authority);
        }
        emit_sat_applied_run_summary(
            route.label(),
            route.source(),
            VariantRouteProfile::Standard,
            self.proof_config,
        );
        publish_parallel_dimacs_result(route, result, authority);
    }

    /// Run the portfolio on the calling thread while the sequential default
    /// route solves the same input on a thread of its own, and publish
    /// whichever answers first.
    ///
    /// The sequential member is the plain `ay solve <cnf>` route, entered
    /// through the same function with the same (absent) proof configuration,
    /// so an answer from it is exactly the answer the sequential run gives: it
    /// publishes through the sequential finish pipeline and exits the process.
    /// The race's referee (`claim_verdict_race_or_yield`) lets one member
    /// report:
    ///
    ///  * a decisive portfolio result claims the race and is published at
    ///    once, from inside the thread scope, because leaving the scope would
    ///    wait for a member that may search for the rest of the budget; if
    ///    the sequential member claimed first, this thread parks and the
    ///    member's exit ends the run;
    ///  * a portfolio that ends without an answer while the budget lasts
    ///    waits for the sequential member, whose answer ends the process. A
    ///    member that ends without an answer returns silently, and the
    ///    unanswered run is reported here, as it is when the budget is over.
    ///
    /// The member runs on `member_unit`, an extra unit of the process compute
    /// budget (`ay_sys::compute_budget`) reserved beside the calling thread's
    /// own unit, which the portfolio's inline worker reuses; the portfolio's
    /// further workers take only the units left, so the race never runs more
    /// search threads than the ceiling.
    fn race_sequential_member(&self, member_unit: ay_sys::compute_budget::ExtraPermit) {
        crate::begin_verdict_race();
        let (content, stats_cfg) = (self.content, self.stats_cfg);
        std::thread::scope(|scope| {
            let member = std::thread::Builder::new()
                .name("ay-dimacs-seq-member".to_string())
                .stack_size(PARALLEL_SEQUENTIAL_MEMBER_STACK_SIZE)
                .spawn_scoped(scope, move || {
                    let entered = member_unit.run(|| {
                        run_dimacs_from_content_impl_body(content, stats_cfg, None, None);
                    });
                    if entered.is_err() {
                        safe_eprintln!(
                            "c parallel: the sequential-route member could not enter its CPU unit; portfolio only"
                        );
                    }
                });
            if member.is_err() {
                safe_eprintln!(
                    "c parallel: could not start the sequential-route member; portfolio only"
                );
            }
            let (result, raw_proof_bytes) = self.portfolio.solve_with_proof_bytes(self.formula);
            if matches!(result, SatResult::Sat(_) | SatResult::Unsat(_)) {
                crate::claim_verdict_race_or_yield();
                safe_eprintln!("c parallel: answer from the portfolio");
            } else if let Ok(member) = member {
                if !is_timed_out() && !crate::memout_abort_requested() {
                    // A member that answers never returns from this join.
                    if member.join().is_err() {
                        safe_eprintln!("c parallel: the sequential-route member panicked");
                    }
                }
            }
            self.finish(result, raw_proof_bytes);
        });
    }
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
    // The sequential default route detects structure the portfolio workers
    // never look for (orbitope and PHP symmetry, the XOR/Gaussian extension,
    // the variant auto-router, the streaming loader), and the workers are
    // weaker than it one for one (see `ay_sat::portfolio`). Without a proof to
    // write, one of the N threads therefore runs that route unchanged, as the
    // race's sequential member, beside a portfolio of N-1. A proof run keeps
    // the portfolio alone: the two members would write the same proof path,
    // and the sequential proof route has its own custody.
    //
    // The member counts against the process compute budget like every
    // portfolio worker (2026-11-13): this thread enters its own unit, which
    // the portfolio's inline worker reuses, and the member runs only on an
    // extra unit reserved before the portfolio takes its own extras. When
    // the ceiling leaves no extra unit (one CPU), the run has the width of
    // `--parallel 1` and takes its route, the portfolio alone, as before the
    // race; the member never runs uncounted.
    let (_compute, member_unit) = if proof_config.is_none() && num_threads >= 2 {
        reserve_sequential_member_unit()
    } else {
        (None, None)
    };
    let sequential_member = member_unit.is_some();
    let portfolio_threads = if sequential_member {
        num_threads - 1
    } else {
        num_threads
    };
    if sequential_member {
        safe_eprintln!(
            "c parallel: {num_threads} threads: the sequential default route on 1, the portfolio on up to {portfolio_threads} within the process CPU ceiling"
        );
    }
    safe_eprintln!(
        "c parallel portfolio: {portfolio_threads} threads, {} vars, {} clauses",
        formula.num_vars,
        formula.clauses.len()
    );
    let start = std::time::Instant::now();
    let mut portfolio = PortfolioSolver::new_adaptive(portfolio_threads, &formula);
    if proof_config.is_some() {
        portfolio.set_proof_mode(true);
    }
    if let Some(handle) = INTERRUPT_HANDLE.get() {
        portfolio.set_external_cancel(handle.clone());
    }
    let run = ParallelPortfolioRun {
        content,
        stats_cfg,
        proof_config,
        formula: &formula,
        portfolio: &portfolio,
        num_threads,
        start,
    };
    if let Some(member_unit) = member_unit {
        run.race_sequential_member(member_unit);
    } else {
        let (result, raw_proof_bytes) = portfolio.solve_with_proof_bytes(&formula);
        run.finish(result, raw_proof_bytes);
    }
}

/// Enter this thread's compute unit and reserve one extra unit for the race's
/// sequential member. Returns the entered scope with the member's unit, or
/// no scope and no unit when the ceiling leaves no extra unit (or the budget
/// cannot be entered before the deadline): the portfolio then enters the
/// budget on its own, exactly as it does without the race.
fn reserve_sequential_member_unit() -> (
    Option<ay_sys::compute_budget::ComputeScope>,
    Option<ay_sys::compute_budget::ExtraPermit>,
) {
    let cancelled = || {
        INTERRUPT_HANDLE
            .get()
            .is_some_and(|handle| handle.load(Ordering::Relaxed))
    };
    let Ok(Some(compute)) = ay_sys::compute_budget::ComputeScope::enter_until(cancelled) else {
        return (None, None);
    };
    match compute.try_extra() {
        Ok(Some(member_unit)) => (Some(compute), Some(member_unit)),
        Ok(None) | Err(_) => {
            safe_eprintln!(
                "c parallel: the process CPU ceiling leaves no unit for the sequential-route member; portfolio only"
            );
            (None, None)
        }
    }
}
