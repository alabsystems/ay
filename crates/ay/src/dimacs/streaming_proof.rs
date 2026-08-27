// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Quick header scan to get (num_vars, num_clauses) without full parsing.
fn scan_dimacs_header(content: &str) -> Option<(usize, usize)> {
    for line in content.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("p cnf") {
            let parts: Vec<&str> = trimmed.split_whitespace().collect();
            if parts.len() >= 4 {
                if let (Ok(v), Ok(c)) = (parts[2].parse::<usize>(), parts[3].parse::<usize>()) {
                    return Some((v, c));
                }
            }
        }
        if !trimmed.is_empty() && !trimmed.starts_with('c') && !trimmed.starts_with("p ") {
            break;
        }
    }
    None
}

fn unexpected_tag_error(tag: char) -> DimacsCoreError {
    DimacsCoreError::InvalidLiteral {
        token: format!("unexpected tagged line '{tag}' in CNF input"),
        line_number: 0,
    }
}

fn checked_lrat_original_clause_count(declared: usize) -> Result<u64, DimacsCoreError> {
    let max = usize::try_from(ay_sat::MAX_LRAT_ORIGINAL_CLAUSES).unwrap_or(usize::MAX);
    if declared > max {
        return Err(DimacsCoreError::HeaderCountTooLarge {
            what: "LRAT original-clause",
            declared,
            max,
        });
    }
    u64::try_from(declared).map_err(|_| DimacsCoreError::HeaderCountTooLarge {
        what: "LRAT original-clause",
        declared,
        max,
    })
}

/// Task #20: XOR/GE uses DRAT; LRAT stays ordinary because TrustedTransform
/// additions lack explicit chains. Every default run synthesizes a proof,
/// `run_proof_streaming` is the live dispatch for the whole corpus — the
/// legacy no-proof XOR arm below it is unreachable in the shipping
/// configuration, which silently disabled GF(2) elimination everywhere. The
/// extension now emits latched derived-row helper clauses (ay-xor), making
/// its conflict and reason clauses RUP against the original CNF;
/// `run_dimacs_solver_with_extension` has carried a proof parameter since
/// #4533. Returns true when the XOR route handled the solve.
fn try_run_xor_proof_route(
    content: &str,
    stats_cfg: stats_output::StatsConfig,
    sat_variant: SolverVariant,
    proof: &ProofConfig,
) -> bool {
    // The chunked Tseitin ladders are RAT additions over fresh extension
    // variables, which both the DRAT writer (plain `a`-lines) and the VeriPB
    // writer (`red C : pivot -> 1`, exactly the RAT condition) can serialize.
    if !matches!(proof.format, ProofFormat::Drat | ProofFormat::Veripb) {
        return false;
    }
    // M7 default flip (2026-08-21): ON unless opted out — the paired A/B
    // was strictly dominant at both budgets and every certificate verified.
    if !ay_core::sat_ab_switches().xor_proof_route.unwrap_or(true) {
        return false;
    }
    // Giant gate (#xz-memout family): the 50k-clause acceptance cap
    // (XOR_EXTENSION_MAX_CLAUSES, consulted inside should_enable_xor_extension)
    // used to run only AFTER parse_dimacs had materialized the full
    // Vec<Vec<i32>> clause list AND preprocess_clauses_with_stats had built a
    // second near-copy — ~0.5-2 GB extra live and a doubled wall clock on the
    // 6.7-18.9M-var giants (3.xz: 10 s with the probe vs 4 s without), for a
    // probe whose answer on such instances is always "no". Bound the clause
    // count from the header first — a scan of the leading comment lines only —
    // and skip the probe outright when no accepted instance could follow.
    // `--xor-allow-large` keeps its override semantics, exactly as it does at
    // the post-parse cap.
    if !ay_core::misc_cli_flags().xor_allow_large {
        if let Some((_, header_clauses)) = scan_dimacs_header(content) {
            if header_clauses > XOR_EXTENSION_MAX_CLAUSES {
                return false;
            }
        }
    }
    let Ok(formula) = parse_dimacs(content) else {
        return false;
    };
    let (remaining, mut xor_ext, xor_stats) =
        ay_xor::preprocess_clauses_with_stats(&formula.clauses);
    // Wide-XOR traces outside the monolithic ladder envelope can still be
    // certified via Tseitin-chunked chains over fresh DRAT extension
    // variables allocated above the DIMACS header range. Safe on this route:
    // extension solves disable every variable-introducing inprocessing pass
    // and the oneshot symmetry constructions are aux-free, so nothing else
    // allocates variables during the solve.
    if let (Some(ext), Ok(num_vars)) = (xor_ext.as_mut(), u32::try_from(formula.num_vars)) {
        ext.set_proof_fresh_var_base(num_vars);
    }
    let use_xor = xor_ext.as_ref().is_some_and(|ext| {
        ext.num_components() > 0
            && ext.has_complete_proof_ladders()
            && should_enable_xor_extension(
                &formula.clauses,
                xor_stats.clauses_consumed,
                remaining.len(),
                xor_stats.xors_detected,
            )
    });
    if !use_xor {
        return false;
    }
    let num_original_clauses = formula.clauses.len() as u64;
    let features = SatFeatures::extract(formula.num_vars, &formula.clauses);
    let mut ext = xor_ext.expect("use_xor implies Some");
    safe_eprintln!(
        "c XOR: detected {} constraints, {} clauses consumed, {} remaining, {} components (proof mode)",
        xor_stats.xors_detected,
        xor_stats.clauses_consumed,
        remaining.len(),
        ext.num_components()
    );
    let output = match create_configured_dimacs_proof_file(proof)
        .and_then(|file| solver_proof_output_writer(file, proof))
    {
        Ok(writer) => match (proof.format, proof.binary) {
            (ProofFormat::Veripb, _) => ProofOutput::veripb(writer),
            (ProofFormat::Drat, false) => ProofOutput::drat_text(writer),
            (ProofFormat::Drat, true) => ProofOutput::drat_binary(writer),
            (ProofFormat::Lrat, false) => ProofOutput::lrat_text(writer, num_original_clauses),
            (ProofFormat::Lrat, true) => ProofOutput::lrat_binary(writer, num_original_clauses),
            (ProofFormat::Alethe | ProofFormat::Lean4, _) => {
                unreachable!("guarded by the matches! above")
            }
        },
        Err(error) => {
            sink_proof_output_after_optional_create_failure(proof, num_original_clauses, &error)
        }
    };
    let mut solver = SatSolver::with_proof_output(formula.num_vars, output);
    solver.set_symmetry_oneshot(true);
    let xor_plan = variant_profile_plan_for_dimacs_features(
        sat_variant,
        formula.num_vars,
        formula.num_clauses,
        DimacsProofPosture::from_proof(proof),
        &features,
    );
    xor_plan.apply_to_solver(&mut solver);
    for clause in remaining {
        solver.add_clause(clause);
    }
    {
        let mut seen = std::collections::HashSet::new();
        for constraint in ext.constraints() {
            for &var_id in &constraint.vars {
                if seen.insert(var_id) {
                    solver.freeze(Variable::new(var_id));
                }
            }
        }
    }
    solver.set_extension_trusted_lemmas(true);
    run_dimacs_solver_with_extension(
        &mut solver,
        &mut ext,
        stats_cfg,
        content,
        Some(proof),
        None,
        None,
    );
    true
}

fn run_proof_streaming(
    content: &str,
    stats_cfg: stats_output::StatsConfig,
    variant: SolverVariant,
    proof: &ProofConfig,
) {
    if try_run_xor_proof_route(content, stats_cfg, variant, proof) {
        return;
    }
    run_proof_streaming_reader(
        content.as_bytes(),
        stats_cfg,
        variant,
        proof,
        DimacsInputSource::Content(content),
        Some(scan_max_variable(content.as_bytes())),
    );
}

fn run_proof_streaming_reader<R>(
    reader: R,
    stats_cfg: stats_output::StatsConfig,
    variant: SolverVariant,
    proof: &ProofConfig,
    source: DimacsInputSource<'_>,
    // Content-driven variable count when the whole input is in memory (the
    // actual maximum variable referenced); `None` for true single-pass streams.
    content_max_var: Option<usize>,
) where
    R: Read,
{
    run_proof_streaming_reader_body(reader, stats_cfg, variant, proof, source, content_max_var)
}
