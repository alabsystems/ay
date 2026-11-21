// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// AY-SAT-2: CNFs that are pure or near-pure XOR systems. The XOR/Gauss
// extension declines them (a single component wider than the 1,000-column
// matrix cap is dropped, leaving no component; the 95% binary+ternary guard
// declines the rest), and where it does run the CDCL search with Gauss
// propagation cannot settle a cardinality bound over parities. Before either,
// `ay_xor::solve_parity_space` walks the affine solution space of the XOR
// system and answers only with a model it checked against every clause. Every
// other outcome, an inconsistent system included, falls through to the
// ordinary routes unchanged: this route never answers UNSAT and writes no
// proof (AY-SAT-2). It has its own wall budget
// (`--sat-parity-space-budget-ms`, default 8 s) and an opt-out
// (`--sat-parity-space-route false`).

/// The route's wall budget when `--sat-parity-space-budget-ms` names none.
/// The finder has its own 3 s budget and elimination and the probe are
/// work-bounded; this bounds the walk, which polls it per candidate and once
/// per 65,536 steps. A 2^32-point filtered walk takes a few seconds.
const PARITY_SPACE_ROUTE_DEFAULT_BUDGET_MS: u64 = 8_000;

/// The route's wall budget, or `None` when it is switched off
/// (`--sat-parity-space-route false` or `--sat-parity-space-budget-ms 0`).
fn parity_space_route_budget() -> Option<std::time::Duration> {
    let switches = ay_core::sat_ab_switches();
    if !switches.parity_space_route.unwrap_or(true) {
        return None;
    }
    match switches
        .parity_space_budget_ms
        .unwrap_or(PARITY_SPACE_ROUTE_DEFAULT_BUDGET_MS)
    {
        0 => None,
        ms => Some(std::time::Duration::from_millis(ms)),
    }
}

/// Whether `clauses` can be one the walk takes. Every clause the finder
/// recovers as part of an XOR has 2 to 8 literals, and the walk needs those to
/// be at least half of the formula, so a formula with fewer such clauses is
/// declined here in one pass, before the finder runs.
fn parity_space_shape_admits(clauses: &[Vec<Literal>]) -> bool {
    let candidates = clauses
        .iter()
        .filter(|clause| (2..=8).contains(&clause.len()))
        .count();
    candidates.saturating_mul(2) >= clauses.len()
}

/// A model of `formula` from the parity-space walk, re-checked here against
/// every parsed clause, or `None`.
fn parity_space_model(formula: &ay_sat::DimacsFormula) -> Option<Vec<bool>> {
    let budget = parity_space_route_budget()?;
    if formula.clauses.len() > XOR_EXTENSION_MAX_CLAUSES
        || !parity_space_shape_admits(&formula.clauses)
    {
        return None;
    }
    let start = std::time::Instant::now();
    let should_stop = || is_timed_out() || start.elapsed() >= budget;
    let (outcome, stats) =
        ay_xor::solve_parity_space(formula.num_vars, &formula.clauses, &should_stop);
    let model = match outcome {
        ay_xor::ParitySpaceOutcome::Model(model) => model,
        ay_xor::ParitySpaceOutcome::Declined(decline) => {
            // One line for every formula the walk got as far as recovering
            // XORs for; nothing for formulas without them.
            if stats.xors > 0 {
                safe_eprintln!(
                    "c parity-space: declined ({decline:?}) after {} ms: {} XOR constraints, {} columns, rank {}, dimension {}, {} residual clauses, filter {:?}, {} points, {} completed",
                    start.elapsed().as_millis(),
                    stats.xors,
                    stats.columns,
                    stats.rank,
                    stats.dimension,
                    stats.residual_clauses,
                    stats.weight_filter,
                    stats.points,
                    stats.candidates
                );
            }
            return None;
        }
    };
    let satisfied = formula.clauses.iter().all(|clause| {
        clause.iter().any(|lit| {
            model
                .get(lit.variable().index())
                .is_some_and(|&value| value == lit.is_positive())
        })
    });
    if !satisfied {
        safe_eprintln!("c parity-space: model failed the original-clause check; ignored");
        return None;
    }
    safe_eprintln!(
        "c parity-space: model from the affine solution space of {} XOR constraints (rank {}, dimension {}, {} residual clauses, filter {:?}, {} points, {} completed) in {} ms",
        stats.xors,
        stats.rank,
        stats.dimension,
        stats.residual_clauses,
        stats.weight_filter,
        stats.points,
        stats.candidates,
        start.elapsed().as_millis()
    );
    Some(model)
}

/// Answer SAT with the parity-space model of `formula`, if there is one.
fn exit_if_parity_space_model(
    formula: &ay_sat::DimacsFormula,
    stats_cfg: stats_output::StatsConfig,
    proof: Option<&ProofConfig>,
) {
    let Some(model) = parity_space_model(formula) else {
        return;
    };
    // A SAT answer carries no proof; this route never created one, and any
    // owned proof path is released as on every non-UNSAT answer.
    cleanup_dimacs_non_unsat_proof_paths(proof);
    exit_with_parity_space_sat_model(&model, stats_cfg);
}

/// The proof-mode entry, for both the in-memory content route and
/// `run_dimacs_proof_from_file` (the path of `ay solve --proof P file.cnf`):
/// parse `content` (bounded by its header) and answer SAT with a parity-space
/// model, if there is one.
fn exit_if_parity_space_model_in_content(
    content: &str,
    stats_cfg: stats_output::StatsConfig,
    proof: &ProofConfig,
) {
    if parity_space_route_budget().is_none() {
        return;
    }
    if let Some((_, header_clauses)) = scan_dimacs_header(content) {
        if header_clauses > XOR_EXTENSION_MAX_CLAUSES {
            return;
        }
    }
    let Ok(formula) = parse_dimacs(content) else {
        return;
    };
    exit_if_parity_space_model(&formula, stats_cfg, Some(proof));
}

fn exit_with_parity_space_sat_model(model: &[bool], stats_cfg: stats_output::StatsConfig) -> ! {
    reject_dimacs_decision_trace_or_exit();
    if crate::verdict_race_active() {
        crate::claim_decisive_verdict_or_yield(crate::dimacs_verdict_exit_code(10));
    }
    if stats_cfg.any() {
        let route = "parity-space";
        let reason = "parity-space model answers before solver startup";
        if stats_cfg.human {
            emit_startup_capability_plan_unavailable(route, reason);
        }
        let mut run_stats = stats_output::RunStatistics::new(
            stats_output::SolveMode::DimacsSat,
            "sat",
            global_elapsed(),
        );
        insert_startup_capability_plan_unavailable_stats(&mut run_stats, route, reason);
        emit_dimacs_run_stats(
            &run_stats,
            stats_cfg,
            summary_route_profile(selected_sat_variant(), None),
        );
    }
    crate::mark_verdict_printed();
    safe_println!("s SATISFIABLE");
    emit_dimacs_sat_model(model);
    let _ = io::stdout().flush();
    let _ = io::stderr().flush();
    std::process::exit(crate::dimacs_verdict_exit_code(10));
}
