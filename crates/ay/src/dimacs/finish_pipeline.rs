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
    /// The proof write failure the solver's writer latched, read before the
    /// non-UNSAT cleanup drops that writer. A SAT answered after it is a real
    /// answer without a proof, and the note says so.
    proof_write_failure: Option<String>,
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

        let proof_write_failure = request.solver.proof_write_failure();
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
            proof_write_failure,
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
            proof,
            mut unsat_authority,
            proof_write_failure,
            ..
        } = self;
        match result {
            SatResult::Sat(model) => {
                // A SAT answer needs no proof: found after the writer latched,
                // it is still the answer, and the note says the proof is gone.
                if let Some(detail) = proof_write_failure {
                    safe_eprintln!("c {detail}; answering with the model, without a proof");
                }
                crate::claim_decisive_verdict_or_yield(crate::dimacs_verdict_exit_code(10));
                safe_println!("s SATISFIABLE");
                let visible = solver.as_ref().visible_model_vars().min(model.len());
                emit_dimacs_sat_model(&model[..visible]);
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
                crate::claim_decisive_verdict_or_yield(crate::dimacs_verdict_exit_code(20));
                safe_println!("s UNSATISFIABLE");
                authority.commit_after_verdict();
                let _ = io::stdout().flush();
                let _ = io::stderr().flush();
                std::process::exit(crate::dimacs_verdict_exit_code(20));
            }
            SatResult::Unknown => {
                dimacs_exit_if_timed_out(Some(solver.as_mut()), proof);
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
                // A lost proof (disk full) names its cause instead of a
                // generic `incomplete`; the partial proof was already
                // discarded by the non-UNSAT sidecar cleanup.
                let reason = proof_write_failure_note(
                    solver.as_ref().last_unknown_reason(),
                    solver.as_ref().last_unknown_detail(),
                )
                .unwrap_or_else(|| {
                    "c reason: incomplete (SAT solver could not determine satisfiability)"
                        .to_string()
                });
                settle_unanswered_dimacs_exit();
                safe_eprintln!("{reason}");
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
    // The sequential member of the parallel race (run_dimacs_parallel.rs)
    // finishes here like any sequential solve, with two differences. A
    // decisive answer first claims the race, before anything is written, so
    // the two members never both report. A solve that ends without an answer
    // (and that the finalize rescue cannot retry) says nothing: the portfolio
    // is still searching, and the race's unanswered exits belong to it.
    let racing = crate::verdict_race_active();
    if racing {
        if matches!(result, SatResult::Sat(_) | SatResult::Unsat(_)) {
            crate::claim_verdict_race_or_yield();
            safe_eprintln!("c parallel: answer from the sequential-route member");
        } else if !finalize_rescue_applicable(solver, &result, proof_config) {
            return;
        }
    }
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
    if racing {
        // Only a finalize rescue changes the result inside `prepare`.
        if !matches!(state.result, SatResult::Sat(_) | SatResult::Unsat(_)) {
            return;
        }
        crate::claim_verdict_race_or_yield();
    }
    state.emit_statistics();
    state.publish_verdict();
}

/// The stderr note for an unknown caused by a failed proof write, for example
/// `c proof write failed: No space left on device (os error 28); answering
/// unknown`. `None` for every other unknown.
fn proof_write_failure_note(
    reason: Option<ay_sat::SatUnknownReason>,
    detail: Option<&str>,
) -> Option<String> {
    (reason == Some(ay_sat::SatUnknownReason::ProofWriteFailure)).then(|| {
        let detail = detail.unwrap_or("proof write failed");
        format!("c {detail}; answering unknown")
    })
}

#[cfg(test)]
mod proof_write_failure_note_tests {
    use super::proof_write_failure_note;
    use ay_sat::SatUnknownReason;

    #[test]
    fn names_the_os_error_only_for_a_proof_write_failure() {
        assert_eq!(
            proof_write_failure_note(
                Some(SatUnknownReason::ProofWriteFailure),
                Some("proof write failed: No space left on device (os error 28)"),
            )
            .as_deref(),
            Some("c proof write failed: No space left on device (os error 28); answering unknown")
        );
        assert_eq!(
            proof_write_failure_note(Some(SatUnknownReason::ProofWriteFailure), None).as_deref(),
            Some("c proof write failed; answering unknown")
        );
        assert_eq!(
            proof_write_failure_note(Some(SatUnknownReason::DeadlineExceeded), Some("x")),
            None
        );
        assert_eq!(proof_write_failure_note(None, None), None);
    }
}
