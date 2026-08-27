// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn create_streaming_proof_output(proof: &ProofConfig, num_original_clauses: u64) -> ProofOutput {
    match proof.format {
        ProofFormat::Alethe => ProofOutput::lrat_text(io::sink(), num_original_clauses),
        ProofFormat::Lean4 => ProofOutput::lrat_text(Vec::<u8>::new(), num_original_clauses),
        ProofFormat::Drat | ProofFormat::Lrat | ProofFormat::Veripb => {
            match create_configured_dimacs_proof_file(proof)
                .and_then(|file| solver_proof_output_writer(file, proof))
            {
                Ok(writer) => match (proof.format, proof.binary) {
                    (ProofFormat::Veripb, _) => ProofOutput::veripb(writer),
                    (ProofFormat::Drat, false) => ProofOutput::drat_text(writer),
                    (ProofFormat::Drat, true) => ProofOutput::drat_binary(writer),
                    (ProofFormat::Lrat, false) => {
                        ProofOutput::lrat_text(writer, num_original_clauses)
                    }
                    (ProofFormat::Lrat, true) => {
                        ProofOutput::lrat_binary(writer, num_original_clauses)
                    }
                    (ProofFormat::Alethe | ProofFormat::Lean4, _) => {
                        sink_proof_output_after_optional_create_failure(
                            proof,
                            num_original_clauses,
                            &io::Error::other("post-solve proof format reached streaming writer"),
                        )
                    }
                },
                Err(error) => sink_proof_output_after_optional_create_failure(
                    proof,
                    num_original_clauses,
                    &error,
                ),
            }
        }
    }
}

struct ProofStreamingLoad<'a> {
    proof: &'a ProofConfig,
    content_max_var: Option<usize>,
    solver: Option<SatSolver>,
    features: Option<SatFeatureAccumulator>,
    original_clauses: Vec<(u64, Vec<i32>)>,
    num_vars: usize,
    num_clauses_declared: usize,
    clause_buf: Vec<Literal>,
    dense_route_requested: bool,
    dense_route_clauses: Option<Vec<Vec<Literal>>>,
}

impl<'a> ProofStreamingLoad<'a> {
    fn new(proof: &'a ProofConfig, content_max_var: Option<usize>) -> Self {
        Self {
            proof,
            content_max_var,
            solver: None,
            features: None,
            original_clauses: Vec::new(),
            num_vars: 0,
            num_clauses_declared: 0,
            clause_buf: Vec::with_capacity(32),
            dense_route_requested: ay_core::sat_ab_switches().dense_clique_php_proof_route,
            dense_route_clauses: None,
        }
    }

    fn accept_header(
        &mut self,
        header: ay_sat::dimacs_core::DimacsHeader,
    ) -> Result<(), DimacsCoreError> {
        self.num_vars = header.num_vars;
        self.num_clauses_declared = header.num_clauses;
        let num_original_clauses = if matches!(
            self.proof.format,
            ProofFormat::Alethe | ProofFormat::Lean4 | ProofFormat::Lrat
        ) {
            checked_lrat_original_clause_count(header.num_clauses)?
        } else {
            0
        };
        let proof_output = create_streaming_proof_output(self.proof, num_original_clauses);
        let solver_num_vars = self.content_max_var.unwrap_or(header.num_vars);
        if solver_num_vars > ay_sat::dimacs_core::MAX_DIMACS_VARS {
            return Err(DimacsCoreError::HeaderCountTooLarge {
                what: "variable",
                declared: solver_num_vars,
                max: ay_sat::dimacs_core::MAX_DIMACS_VARS,
            });
        }
        self.num_vars = solver_num_vars;
        let mut solver = SatSolver::with_proof_output(solver_num_vars, proof_output);
        solver.set_symmetry_oneshot(true);
        self.solver = Some(solver);
        self.features = Some(SatFeatureAccumulator::new(solver_num_vars));
        if self.dense_route_requested
            && dense_clique_php_route_header_candidate(header.num_vars, header.num_clauses)
        {
            self.dense_route_clauses = Some(Vec::with_capacity(header.num_clauses.min(1 << 20)));
        }
        Ok(())
    }

    fn accept_clause(&mut self, raw: &[i32]) -> Result<(), DimacsCoreError> {
        let solver = self.solver.as_mut().ok_or(DimacsCoreError::MissingHeader)?;
        let features = self
            .features
            .as_mut()
            .ok_or(DimacsCoreError::MissingHeader)?;
        if self.proof.format == ProofFormat::Lean4 {
            self.original_clauses
                .push((self.original_clauses.len() as u64 + 1, raw.to_vec()));
        }
        features.add_dimacs_clause_to_buffer(raw, &mut self.clause_buf);
        if let Some(clauses) = self.dense_route_clauses.as_mut() {
            clauses.push(self.clause_buf.clone());
        }
        solver.add_clause_reusing_buffer(&mut self.clause_buf);
        Ok(())
    }

    fn accept_event(&mut self, event: DimacsEvent<'_>) -> Result<(), DimacsCoreError> {
        match event {
            DimacsEvent::Header(header) => self.accept_header(header),
            DimacsEvent::Record(DimacsRecordRef::Clause(raw)) => self.accept_clause(raw),
            DimacsEvent::Record(DimacsRecordRef::Tagged { tag, .. }) => {
                Err(unexpected_tag_error(tag))
            }
            _ => Ok(()),
        }
    }
}

fn exit_after_streaming_proof_parse_error(
    mut solver: Option<SatSolver>,
    proof: &ProofConfig,
    error: DimacsCoreError,
) -> ! {
    if let Some(solver) = solver.as_mut() {
        let _ = cleanup_dimacs_non_unsat_proof_sidecar(solver, &SatResult::Unknown, Some(proof));
    } else {
        cleanup_dimacs_non_unsat_proof_paths(Some(proof));
    }
    let error: DimacsError = error.into();
    safe_eprintln!("c Parse error: {}", error);
    safe_println!("s UNKNOWN");
    std::process::exit(1);
}

fn require_streaming_proof_solver(solver: Option<SatSolver>) -> SatSolver {
    let Some(solver) = solver else {
        safe_eprintln!(
            "c Parse error: missing problem line, expected \"p cnf <num_vars> <num_clauses>\""
        );
        safe_println!("s UNKNOWN");
        std::process::exit(1);
    };
    solver
}

fn dispatch_streaming_proof_solve(
    solver: &mut SatSolver,
    stats_cfg: stats_output::StatsConfig,
    proof: &ProofConfig,
    source: DimacsInputSource<'_>,
    original_clauses: &[(u64, Vec<i32>)],
) {
    match proof.format {
        ProofFormat::Alethe => fail_closed_satcomp_proof_setup(
            "Alethe proof output is unavailable for DIMACS input; use LRAT or DRAT",
        ),
        ProofFormat::Lean4 => run_dimacs_solver_lean4_with_source(
            solver,
            stats_cfg,
            &proof.path,
            source,
            Some(proof),
            original_clauses,
        ),
        ProofFormat::Drat | ProofFormat::Lrat | ProofFormat::Veripb => {
            run_dimacs_solver_with_source(solver, stats_cfg, source, Some(proof));
        }
    }
}

fn run_proof_streaming_reader_body<R: Read>(
    reader: R,
    stats_cfg: stats_output::StatsConfig,
    variant: SolverVariant,
    proof: &ProofConfig,
    source: DimacsInputSource<'_>,
    content_max_var: Option<usize>,
) {
    let mut load = ProofStreamingLoad::new(proof, content_max_var);
    if let Err(error) =
        ay_sat::dimacs_core::parse_dimacs_events(reader, |event| load.accept_event(event))
    {
        exit_after_streaming_proof_parse_error(load.solver, proof, error);
    }
    let mut solver = require_streaming_proof_solver(load.solver);
    let features = load
        .features
        .map(SatFeatureAccumulator::finish)
        .unwrap_or_else(|| SatFeatures::from_streaming_counters(load.num_vars, 0, 0, 0));
    variant_profile_plan_for_dimacs_features(
        variant,
        load.num_vars,
        load.num_clauses_declared,
        DimacsProofPosture::from_proof(proof),
        &features,
    )
    .apply_to_solver(&mut solver);
    let dense_route = if load.dense_route_requested {
        DenseCliquePhpRouteRequest::Requested
    } else {
        DenseCliquePhpRouteRequest::Disabled
    };
    maybe_run_dense_clique_php_proof_route(
        dense_route,
        &mut solver,
        load.num_vars,
        load.num_clauses_declared,
        load.dense_route_clauses.as_deref(),
        stats_cfg,
        proof,
        source,
    );
    dispatch_streaming_proof_solve(
        &mut solver,
        stats_cfg,
        proof,
        source,
        &load.original_clauses,
    );
}
