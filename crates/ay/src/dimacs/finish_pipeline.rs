// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Inputs required to settle and publish one sequential DIMACS solve.
struct DimacsFinishRequest<'solver, 'input> {
    solver: &'solver mut SatSolver,
    result: SatResult,
    stats: stats_output::StatsConfig,
    source: DimacsInputSource<'input>,
    proof: Option<&'input ProofConfig>,
    guard_cover: Option<&'input GuardCoverSidecarRunStats>,
    separator_cover: Option<&'input SeparatorCoverSidecarRunStats>,
    proof_writer_telemetry: Option<DimacsProofWriterTelemetry>,
}

/// Owns either the caller's solver or the authoritative finalize-rescue retry.
enum DimacsFinishSolver<'solver> {
    Primary(&'solver mut SatSolver),
    Rescue(Box<SatSolver>),
}

impl DimacsFinishSolver<'_> {
    fn as_ref(&self) -> &SatSolver {
        match self {
            Self::Primary(solver) => solver,
            Self::Rescue(solver) => solver,
        }
    }

    fn as_mut(&mut self) -> &mut SatSolver {
        match self {
            Self::Primary(solver) => solver,
            Self::Rescue(solver) => solver,
        }
    }

    fn is_rescue(&self) -> bool {
        matches!(self, Self::Rescue(_))
    }
}

/// Ordered finish state: post-rescue authority precedes result-bearing statistics and verdicts.
struct DimacsFinishState<'solver, 'input> {
    solver: DimacsFinishSolver<'solver>,
    result: SatResult,
    stats: stats_output::StatsConfig,
    source: DimacsInputSource<'input>,
    proof: Option<&'input ProofConfig>,
    guard_cover: Option<&'input GuardCoverSidecarRunStats>,
    separator_cover: Option<&'input SeparatorCoverSidecarRunStats>,
    proof_writer_telemetry: Option<DimacsProofWriterTelemetry>,
    route_profile: VariantRouteProfile,
    unsat_authority: Option<AuthorizedDimacsUnsatPublication>,
}

impl<'solver, 'input> DimacsFinishState<'solver, 'input> {
    /// Select the authoritative solver and establish initial UNSAT publication authority.
    fn prepare(request: DimacsFinishRequest<'solver, 'input>) -> Self {
        let variant = selected_sat_variant();
        let policy = format!("variant={}", variant.as_str());
        let route_profile = summary_route_profile(variant, request.proof);
        emit_sat_applied_run_summary(
            &policy,
            sat_variant_source_label(),
            route_profile,
            request.proof,
        );

        let mut proof_writer_telemetry = request.proof_writer_telemetry.or_else(|| {
            cleanup_dimacs_non_unsat_proof_sidecar(request.solver, &request.result, request.proof)
        });
        let rescue = finalize_rescue_applicable(request.solver, &request.result, request.proof)
            .then(|| run_finalize_rescue(request.source, request.proof))
            .flatten();
        let (solver, result) = match rescue {
            Some((retry_result, retry_solver)) => {
                proof_writer_telemetry = None;
                (
                    DimacsFinishSolver::Rescue(Box::new(retry_solver)),
                    retry_result,
                )
            }
            None => (DimacsFinishSolver::Primary(request.solver), request.result),
        };
        let mut state = Self {
            solver,
            result,
            stats: request.stats,
            source: request.source,
            proof: request.proof,
            guard_cover: request.guard_cover,
            separator_cover: request.separator_cover,
            proof_writer_telemetry,
            route_profile,
            unsat_authority: None,
        };
        state.authorize_unsat();
        state
    }

    /// Finalize proof bytes and authenticate every artifact needed for UNSAT.
    fn authorize_unsat(&mut self) {
        if !matches!(self.result, SatResult::Unsat(_)) {
            return;
        }
        if let Some(proof) = self.proof {
            if self.proof_writer_telemetry.is_none() {
                self.proof_writer_telemetry = dimacs_proof_writer_telemetry(self.solver.as_ref());
            }
            finalize_solver_dimacs_proof_or_exit(self.solver.as_mut(), proof);
        }
        let theory = {
            let solver = self.solver.as_ref();
            ProofArtifactTheoryMetadata::dimacs_sat(
                solver.user_num_vars(),
                solver.num_original_clauses(),
            )
        };
        self.unsat_authority = Some(authorize_dimacs_unsat_artifacts(
            self.source,
            self.proof,
            theory,
        ));
    }

    /// Emit statistics only after any rescue and proof authority have settled.
    fn emit_statistics(&mut self) {
        if !self.stats.any() {
            return;
        }
        let route = if self.solver.is_rescue() {
            DimacsFinishStatisticsRoute::Rescue
        } else {
            DimacsFinishStatisticsRoute::Primary
        };
        emit_dimacs_finish_statistics(DimacsFinishStatisticsRequest {
            solver: self.solver.as_mut(),
            result: &self.result,
            stats: self.stats,
            source: self.source,
            proof: self.proof,
            guard_cover: self.guard_cover,
            separator_cover: self.separator_cover,
            proof_writer_telemetry: self.proof_writer_telemetry,
            route,
            unsat_authority: &mut self.unsat_authority,
            route_profile: self.route_profile,
        });
    }

    /// Publish the SAT-competition verdict after all required validation.
    fn publish_verdict(self) {
        let Self {
            mut solver,
            result,
            mut unsat_authority,
            ..
        } = self;
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
                    fail_dimacs_certification_or_exit(
                        "sequential UNSAT route lost its publication authority",
                    );
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
                dimacs_exit_if_timed_out(Some(solver.as_mut()));
                // A memory abort must not masquerade as a decision gap: when
                // the memory watchdog latched a breach (or the budget is still
                // exceeded at publication), report the memout grammar and the
                // memout exit code — the same output the watchdog's own
                // hard-exit path produces — instead of a generic
                // `incomplete` with exit 0 that a sweep cannot tell from
                // incompleteness.
                if crate::memout_abort_requested() {
                    crate::hard_memory_fallback_exit();
                }
                safe_eprintln!(
                    "c reason: incomplete (SAT solver could not determine satisfiability)"
                );
                safe_println!("s UNKNOWN");
            }
            #[allow(unreachable_patterns)]
            _ => {
                safe_eprintln!("c reason: unknown");
                safe_println!("s UNKNOWN");
            }
        }
    }
}

fn finish_dimacs_solve_with_source(
    solver: &mut SatSolver,
    result: SatResult,
    stats_cfg: stats_output::StatsConfig,
    source: DimacsInputSource<'_>,
    proof_config: Option<&ProofConfig>,
    guard_cover: Option<&GuardCoverSidecarRunStats>,
    separator_cover: Option<&SeparatorCoverSidecarRunStats>,
    proof_writer_telemetry_override: Option<DimacsProofWriterTelemetry>,
) {
    let request = DimacsFinishRequest {
        solver,
        result,
        stats: stats_cfg,
        source,
        proof: proof_config,
        guard_cover,
        separator_cover,
        proof_writer_telemetry: proof_writer_telemetry_override,
    };
    let mut state = DimacsFinishState::prepare(request);
    state.emit_statistics();
    state.publish_verdict();
}
