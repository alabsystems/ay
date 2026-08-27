// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

const CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_ENV: &str =
    "AY_SAT_CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_ROUTE";

struct AuthenticatedLeanSnapshot {
    descriptor: File,
    identity: ProofFileIdentity,
    len: u64,
    sha256: Sha256Digest,
}

impl AuthenticatedLeanSnapshot {
    #[cfg(target_os = "linux")]
    fn create(public_path: &str, published: PublishedDimacsProof) -> io::Result<Self> {
        let bytes = read_published_dimacs_proof(public_path, published.sha256)?;
        if bytes.len() as u64 != published.len || sha256_digest(&bytes) != published.sha256 {
            return Err(io::Error::other(
                "sealed DIMACS proof bytes changed before Lean snapshot creation",
            ));
        }

        let resolved = resolved_dimacs_proof_path(public_path)?;
        let mut descriptor = create_anonymous_dimacs_staging_file(&resolved)?;
        descriptor.write_all(&bytes)?;
        descriptor.sync_all()?;
        {
            use std::os::unix::fs::PermissionsExt as _;
            descriptor.set_permissions(std::fs::Permissions::from_mode(0o400))?;
        }
        let identity = regular_file_identity(&descriptor, &resolved)?;
        descriptor.seek(SeekFrom::Start(0))?;
        Ok(Self {
            descriptor,
            identity,
            len: published.len,
            sha256: published.sha256,
        })
    }

    #[cfg(not(target_os = "linux"))]
    fn create(_public_path: &str, _published: PublishedDimacsProof) -> io::Result<Self> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "Lean verification requires a re-openable authenticated anonymous descriptor path, which is unavailable on this platform",
        ))
    }

    fn validate(&mut self) -> io::Result<()> {
        let metadata = self.descriptor.metadata()?;
        if ProofFileIdentity::from_file(&self.descriptor)? != self.identity
            || metadata.len() != self.len
        {
            return Err(io::Error::other(
                "authenticated Lean snapshot descriptor changed",
            ));
        }
        let (descriptor_len, descriptor_sha256) = hash_file(&mut self.descriptor)?;
        if descriptor_len != self.len || descriptor_sha256 != self.sha256 {
            return Err(io::Error::other(
                "authenticated Lean snapshot bytes changed",
            ));
        }
        self.descriptor.seek(SeekFrom::Start(0))?;
        Ok(())
    }
}

fn cleanup_owned_dimacs_proof_state(
    resolved: &Path,
    state: &mut OwnedDimacsProof,
) -> io::Result<bool> {
    if state.location == OwnedDimacsProofLocation::Anonymous {
        invalidate_dimacs_descriptor(&state.descriptor, state.invalidation)?;
        state.location = OwnedDimacsProofLocation::Removed;
        return Ok(true);
    }
    if state.location == OwnedDimacsProofLocation::Removed {
        return Ok(false);
    }

    let visible_path = match state.location {
        OwnedDimacsProofLocation::Anonymous | OwnedDimacsProofLocation::Removed => {
            unreachable!("handled above")
        }
        OwnedDimacsProofLocation::Staged => state
            .staging_path
            .as_deref()
            .ok_or_else(|| io::Error::other("DIMACS proof staging path is missing"))?,
        OwnedDimacsProofLocation::Public => resolved,
    };
    let settled = remove_authenticated_visible_file(
        visible_path,
        &state.descriptor,
        state.identity,
        "DIMACS proof generation",
        state.invalidation,
    )?;
    state.staging_path = None;
    state.location = OwnedDimacsProofLocation::Removed;
    Ok(settled)
}

fn remove_owned_dimacs_proof(path: &str) -> io::Result<bool> {
    let resolved = resolved_dimacs_proof_path(path)?;
    let mut owned = owned_dimacs_proofs()
        .lock()
        .map_err(|_| dimacs_proof_registry_error())?;
    let Some(state) = owned.get_mut(&resolved) else {
        return Ok(false);
    };
    let status_cleanup = match state.status_reservation.take() {
        Some(reservation) => {
            publish_reserved_dimacs_proof_status(reservation, "stale-not-current", None).map(drop)
        }
        None => Ok(()),
    };
    let proof_cleanup = cleanup_owned_dimacs_proof_state(&resolved, state);
    if proof_cleanup.is_ok() && status_cleanup.is_ok() {
        // Retain both the authoritative descriptor and the registry entry until
        // proof and status cleanup have each either removed the owned
        // generation or restored an unrelated replacement. Retryable failures
        // keep the remaining authority in place.
        owned.remove(&resolved);
    }
    match (proof_cleanup, status_cleanup) {
        (Ok(removed), Ok(())) => Ok(removed),
        (Err(proof_error), Ok(())) => Err(proof_error),
        (Ok(_), Err(status_error)) => Err(status_error),
        (Err(proof_error), Err(status_error)) => Err(io::Error::other(format!(
            "{proof_error}; failed to release synthesized-default proof status transaction: {status_error}"
        ))),
    }
}

fn flush_dimacs_timeout_outputs(solver: Option<&mut SatSolver>) {
    if let Some(solver) = solver {
        retain_fmla_learned_lrat_dry_run_artifact_from_env(solver);
        if let Some(mut proof_output) = solver.take_proof_writer() {
            if let Err(error) = proof_output.flush() {
                safe_eprintln!("c Warning: failed to flush proof output on timeout: {error}");
            }
        }
    }
}

fn retain_fmla_learned_lrat_dry_run_artifact_from_env(solver: &SatSolver) {
    let Ok(path) = std::env::var(
        ay_sat::fmla_runtime_ledger::FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_PATH_ENV,
    ) else {
        return;
    };
    let path = path.trim();
    if path.is_empty() {
        return;
    }
    if let Err(error) = solver.write_fmla_learned_lrat_dry_run_proof_artifact_json(path) {
        safe_eprintln!(
            "c Warning: failed to retain Fmla learned-LRAT dry-run artifact on DIMACS timeout/cleanup: {error}"
        );
    }
}

fn emit_dimacs_sat_model(model: &[bool]) {
    let stdout = io::stdout();
    let mut out = BufWriter::with_capacity(DIMACS_MODEL_OUTPUT_BUFFER_CAPACITY, stdout.lock());
    if let Err(error) = emit_dimacs_sat_model_to_writer(model, &mut out).and_then(|()| out.flush())
    {
        safe_eprintln!("c Warning: failed to write DIMACS SAT model: {error}");
    }
}

fn circuit_multiplier22_retained_sat_model_authority_requested() -> bool {
    std::env::var(CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_ENV).is_ok_and(|value| {
        matches!(
            value.trim().to_ascii_lowercase().as_str(),
            "1" | "true" | "yes" | "on"
        )
    })
}

fn exit_if_circuit_multiplier22_retained_sat_model_authority_admits(
    content: &str,
    stats_cfg: stats_output::StatsConfig,
) {
    if !circuit_multiplier22_retained_sat_model_authority_requested() {
        return;
    }
    let Ok(formula) = parse_dimacs(content) else {
        return;
    };
    if let Some(model) =
        formula.circuit_multiplier22_retained_sat_model_from_env(content.as_bytes())
    {
        exit_with_circuit_multiplier22_retained_sat_model(&model, stats_cfg);
    }
}

fn exit_with_circuit_multiplier22_retained_sat_model(
    model: &[bool],
    stats_cfg: stats_output::StatsConfig,
) -> ! {
    reject_dimacs_decision_trace_or_exit();
    safe_eprintln!("c Circuit_multiplier22 retained original-DIMACS SAT model authority admitted");
    if stats_cfg.any() {
        let route = "retained-model-authority";
        let reason = "retained model authority bypasses solver startup";
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

fn emit_dimacs_sat_model_to_writer<W: Write>(model: &[bool], out: &mut W) -> io::Result<()> {
    out.write_all(b"v")?;
    let mut line_len = 1usize;
    for (index, &value) in model.iter().enumerate() {
        let var = index + 1;
        let token_len = 1 + usize::from(!value) + decimal_digits(var);
        if line_len + token_len + " 0".len() > DIMACS_MODEL_LINE_LIMIT {
            out.write_all(b"\n")?;
            out.write_all(b"v")?;
            line_len = 1;
        }
        if value {
            out.write_all(b" ")?;
        } else {
            out.write_all(b" -")?;
        }
        write_decimal_usize(out, var)?;
        line_len += token_len;
    }
    out.write_all(b" 0\n")
}

fn decimal_digits(mut value: usize) -> usize {
    let mut digits = 1;
    while value >= 10 {
        value /= 10;
        digits += 1;
    }
    digits
}

fn write_decimal_usize<W: Write>(out: &mut W, mut value: usize) -> io::Result<()> {
    let mut buf = [0u8; 20];
    let mut cursor = buf.len();
    loop {
        cursor -= 1;
        buf[cursor] = b'0' + (value % 10) as u8;
        value /= 10;
        if value == 0 {
            break;
        }
    }
    out.write_all(&buf[cursor..])
}

/// DIMACS-specific timeout handling: prints "s UNKNOWN" in SAT competition
/// format instead of the SMT-LIB "unknown" that `exit_if_timed_out` produces
/// (#8674), and drains proof output before the caller exits (#2971).
fn dimacs_timeout_exit_code_for_policy(
    solver: Option<&mut SatSolver>,
    sat_competition_wrapper: bool,
) -> Option<i32> {
    if TIMED_OUT.load(Ordering::SeqCst) {
        if !VERDICT_PRINTED.swap(true, Ordering::SeqCst) {
            safe_println!("s UNKNOWN");
        }
        safe_eprintln!("c timeout");
        flush_dimacs_timeout_outputs(solver);
        let _ = io::stdout().flush();
        let _ = io::stderr().flush();
        return Some(timeout_exit_code_for_sat_competition_wrapper(
            sat_competition_wrapper,
        ));
    }
    None
}

fn dimacs_timeout_exit_code(solver: Option<&mut SatSolver>) -> Option<i32> {
    dimacs_timeout_exit_code_for_policy(solver, sat_competition_wrapper_timeout_policy())
}

/// DIMACS-specific timeout exit: prints "s UNKNOWN" in SAT competition format
/// instead of the SMT-LIB "unknown" that `exit_if_timed_out` produces (#8674).
fn dimacs_exit_if_timed_out(solver: Option<&mut SatSolver>) {
    if let Some(code) = dimacs_timeout_exit_code(solver) {
        std::process::exit(code);
    }
}
use ay_sat::auto::DecisionSource;
use ay_sat::dimacs_core::{DimacsCoreError, DimacsEvent, DimacsRecordRef};
use ay_sat::guard_cover_sidecar::{self, GuardCoverPackingEvidence, SeparatorCoverEvidence};
use ay_sat::{
    parse_dimacs, DimacsError, Extension, Literal, PortfolioSolver, ProofCertificate, ProofOutput,
    SatFeatureAccumulator, SatFeatures, SatResult, Solver as SatSolver, SolverVariant,
    TlaTraceable, Variable, VariantInput, VariantProfilePlan, VariantProofMode,
    VariantRouteProfile, VariantStartupPolicy,
};
