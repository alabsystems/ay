// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn run_dimacs_proof_content_route(
    content: &str,
    stats_cfg: stats_output::StatsConfig,
    variant: SolverVariant,
    proof: &ProofConfig,
    separator_cover: Option<&SeparatorCoverSidecarRunStats>,
) {
    exit_if_circuit_multiplier22_retained_sat_model_authority_admits(content, stats_cfg);
    if separator_cover.is_some_and(|sidecar| sidecar.accepted) {
        cleanup_dimacs_non_unsat_proof_paths(Some(proof));
        fail_closed_satcomp_proof_setup(
            "separator-cover sidecar accepted but proof-mode public artifact replay is not implemented",
        );
    }
    run_proof_streaming(content, stats_cfg, variant, proof);
}

enum BufferedDimacsRoute {
    Required,
    Streaming,
}

#[derive(Clone, Copy)]
enum DimacsAutomaticRouting {
    Allowed,
    Pinned,
}

impl DimacsAutomaticRouting {
    fn is_allowed(self) -> bool {
        matches!(self, Self::Allowed)
    }
}

fn select_buffered_dimacs_route(
    content: &str,
    guard_cover: Option<&GuardCoverSidecarRunStats>,
    separator_cover: Option<&SeparatorCoverSidecarRunStats>,
) -> BufferedDimacsRoute {
    let Some((_, clauses)) = scan_dimacs_header(content) else {
        return BufferedDimacsRoute::Required;
    };
    if clauses <= STREAMING_CLAUSE_THRESHOLD {
        return BufferedDimacsRoute::Required;
    }
    if guard_cover.is_none() && separator_cover.is_none() {
        BufferedDimacsRoute::Streaming
    } else {
        safe_eprintln!(
            "c structural-sidecar: adjacent sidecar present; using checked non-streaming DIMACS load"
        );
        BufferedDimacsRoute::Required
    }
}

fn enable_dimacs_tla_trace(solver: &mut SatSolver) {
    if !ay_core::trace_file_available() {
        return;
    }
    if let Some(path) = &ay_core::trace_config().trace_file_path {
        ay_core::claim_trace_file();
        solver.enable_tla_trace(path, SatSolver::tla_module(), SatSolver::tla_variables());
    }
}

fn run_separator_cover_formula(
    formula: ay_sat::DimacsFormula,
    stats_cfg: stats_output::StatsConfig,
    content: &str,
    variant: SolverVariant,
    automatic_routing: DimacsAutomaticRouting,
    mut sidecar: SeparatorCoverSidecarRunStats,
    guard_cover: Option<&GuardCoverSidecarRunStats>,
) {
    let mut solver = formula.into_solver_with_variant_routed_source(
        variant,
        automatic_routing.is_allowed(),
        sat_variant_decision_source(),
    );
    sidecar.injected_empty_cut = true;
    let _ = solver.add_preserved_learned(Vec::new());
    run_dimacs_solver_with_research_sidecar_stats(
        &mut solver,
        stats_cfg,
        content,
        None,
        guard_cover,
        Some(&sidecar),
    );
}

fn run_guard_cover_formula(
    formula: ay_sat::DimacsFormula,
    stats_cfg: stats_output::StatsConfig,
    content: &str,
    variant: SolverVariant,
    automatic_routing: DimacsAutomaticRouting,
    mut sidecar: GuardCoverSidecarRunStats,
    separator_cover: Option<&SeparatorCoverSidecarRunStats>,
) {
    let mut solver = formula.into_solver_with_variant_routed_source(
        variant,
        automatic_routing.is_allowed(),
        sat_variant_decision_source(),
    );
    sidecar.injected_empty_cut = true;
    let _ = solver.add_preserved_learned(Vec::new());
    run_dimacs_solver_with_research_sidecar_stats(
        &mut solver,
        stats_cfg,
        content,
        None,
        Some(&sidecar),
        separator_cover,
    );
}

struct XorDimacsRun<'a> {
    num_vars: usize,
    num_clauses: usize,
    remaining: Vec<Vec<Literal>>,
    extension: ay_xor::XorExtension,
    xor_stats: ay_xor::XorPreprocessStats,
    features: SatFeatures,
    stats_cfg: stats_output::StatsConfig,
    content: &'a str,
    guard_cover: Option<&'a GuardCoverSidecarRunStats>,
    separator_cover: Option<&'a SeparatorCoverSidecarRunStats>,
    variant: SolverVariant,
}

fn freeze_xor_extension_variables(solver: &mut SatSolver, extension: &ay_xor::XorExtension) {
    let mut seen = std::collections::HashSet::new();
    for constraint in extension.constraints() {
        for &var_id in &constraint.vars {
            if seen.insert(var_id) {
                solver.freeze(Variable::new(var_id));
            }
        }
    }
}

fn run_xor_dimacs_formula(mut run: XorDimacsRun<'_>) {
    safe_eprintln!(
        "c XOR: detected {} constraints, {} clauses consumed, {} remaining, {} components",
        run.xor_stats.xors_detected,
        run.xor_stats.clauses_consumed,
        run.remaining.len(),
        run.extension.num_components()
    );
    let mut solver = SatSolver::new(run.num_vars);
    solver.set_symmetry_oneshot(true);
    variant_profile_plan_for_dimacs_features(
        run.variant,
        run.num_vars,
        run.num_clauses,
        DimacsProofPosture::NoProof,
        &run.features,
    )
    .apply_to_solver(&mut solver);
    enable_dimacs_tla_trace(&mut solver);
    for clause in run.remaining {
        solver.add_clause(clause);
    }
    freeze_xor_extension_variables(&mut solver, &run.extension);
    solver.set_extension_trusted_lemmas(true);
    run_dimacs_solver_with_extension(
        &mut solver,
        &mut run.extension,
        run.stats_cfg,
        run.content,
        None,
        run.guard_cover,
        run.separator_cover,
    );
}

fn try_run_xor_dimacs_formula(
    formula: &ay_sat::DimacsFormula,
    stats_cfg: stats_output::StatsConfig,
    content: &str,
    variant: SolverVariant,
    guard_cover: Option<&GuardCoverSidecarRunStats>,
    separator_cover: Option<&SeparatorCoverSidecarRunStats>,
) -> bool {
    let (remaining, extension, xor_stats) = ay_xor::preprocess_clauses_with_stats(&formula.clauses);
    let Some(extension) = extension else {
        return false;
    };
    if extension.num_components() == 0
        || !should_enable_xor_extension(
            &formula.clauses,
            xor_stats.clauses_consumed,
            remaining.len(),
            xor_stats.xors_detected,
        )
    {
        return false;
    }
    let run = XorDimacsRun {
        num_vars: formula.num_vars,
        num_clauses: formula.num_clauses,
        remaining,
        extension,
        xor_stats,
        features: SatFeatures::extract(formula.num_vars, &formula.clauses),
        stats_cfg,
        content,
        guard_cover,
        separator_cover,
        variant,
    };
    run_xor_dimacs_formula(run);
    true
}

fn run_plain_dimacs_formula(
    formula: ay_sat::DimacsFormula,
    stats_cfg: stats_output::StatsConfig,
    content: &str,
    variant: SolverVariant,
    automatic_routing: DimacsAutomaticRouting,
    guard_cover: Option<&GuardCoverSidecarRunStats>,
    separator_cover: Option<&SeparatorCoverSidecarRunStats>,
) {
    let mut solver = formula.into_solver_with_variant_routed_source(
        variant,
        automatic_routing.is_allowed(),
        sat_variant_decision_source(),
    );
    enable_dimacs_tla_trace(&mut solver);
    run_dimacs_solver_with_research_sidecar_stats(
        &mut solver,
        stats_cfg,
        content,
        None,
        guard_cover,
        separator_cover,
    );
}

struct ParsedDimacsRun<'a> {
    stats_cfg: stats_output::StatsConfig,
    content: &'a str,
    variant: SolverVariant,
    automatic_routing: DimacsAutomaticRouting,
    guard_cover: Option<GuardCoverSidecarRunStats>,
    separator_cover: Option<SeparatorCoverSidecarRunStats>,
}

fn run_parsed_dimacs_formula(formula: ay_sat::DimacsFormula, mut run: ParsedDimacsRun<'_>) {
    if let Some(model) =
        formula.circuit_multiplier22_retained_sat_model_from_env(run.content.as_bytes())
    {
        exit_with_circuit_multiplier22_retained_sat_model(&model, run.stats_cfg);
    }
    if run
        .separator_cover
        .as_ref()
        .is_some_and(|sidecar| sidecar.accepted)
    {
        if let Some(sidecar) = run.separator_cover.take() {
            run_separator_cover_formula(
                formula,
                run.stats_cfg,
                run.content,
                run.variant,
                run.automatic_routing,
                sidecar,
                run.guard_cover.as_ref(),
            );
        }
        return;
    }
    if run
        .guard_cover
        .as_ref()
        .is_some_and(|sidecar| sidecar.accepted)
    {
        if let Some(sidecar) = run.guard_cover.take() {
            run_guard_cover_formula(
                formula,
                run.stats_cfg,
                run.content,
                run.variant,
                run.automatic_routing,
                sidecar,
                run.separator_cover.as_ref(),
            );
        }
        return;
    }
    if try_run_xor_dimacs_formula(
        &formula,
        run.stats_cfg,
        run.content,
        run.variant,
        run.guard_cover.as_ref(),
        run.separator_cover.as_ref(),
    ) {
        return;
    }
    run_plain_dimacs_formula(
        formula,
        run.stats_cfg,
        run.content,
        run.variant,
        run.automatic_routing,
        run.guard_cover.as_ref(),
        run.separator_cover.as_ref(),
    );
}

fn run_dimacs_from_content_impl_body(
    content: &str,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
    input_path: Option<&str>,
) {
    reject_dimacs_decision_trace_or_exit();
    enforce_required_dimacs_proof_gate(proof_config);
    let variant = selected_sat_variant();
    let automatic_routing = if sat_variant_explicitly_selected() {
        DimacsAutomaticRouting::Pinned
    } else {
        DimacsAutomaticRouting::Allowed
    };
    let separator_cover =
        discover_and_check_separator_cover_sidecar(input_path, content.as_bytes());
    if let Some(proof) = proof_config {
        run_dimacs_proof_content_route(
            content,
            stats_cfg,
            variant,
            proof,
            separator_cover.as_ref(),
        );
        return;
    }
    let guard_cover = discover_and_check_guard_cover_sidecar(input_path, content.as_bytes());
    if matches!(
        select_buffered_dimacs_route(content, guard_cover.as_ref(), separator_cover.as_ref()),
        BufferedDimacsRoute::Streaming
    ) {
        let (streaming_variant, source) = streaming_auto_route(
            content,
            variant,
            automatic_routing,
            sat_variant_decision_source(),
        );
        run_streaming(content, stats_cfg, streaming_variant, source);
        return;
    }
    match parse_dimacs(content) {
        Ok(formula) => run_parsed_dimacs_formula(
            formula,
            ParsedDimacsRun {
                stats_cfg,
                content,
                variant,
                automatic_routing,
                guard_cover,
                separator_cover,
            },
        ),
        Err(error) => {
            safe_eprintln!("c Parse error: {}", error);
            safe_println!("s UNKNOWN");
            std::process::exit(1);
        }
    }
}
