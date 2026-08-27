// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn synthesized_default_dimacs_proof_is_optional(proof: &ProofConfig) -> bool {
    proof.synthesized_default
        && required_dimacs_proof_gate_name().is_none()
        && !super::EXPLICIT_VERIFY_PROOF_ENABLED.load(Ordering::SeqCst)
        && proof.artifact_path.is_none()
        && !super::LEAN_VERIFY_ENABLED.load(Ordering::SeqCst)
}

pub(super) fn dimacs_proof_status_path(path: &str) -> PathBuf {
    dimacs_proof_status_path_from_path(Path::new(path))
}

fn dimacs_proof_status_path_from_path(path: &Path) -> PathBuf {
    let mut status = path.as_os_str().to_os_string();
    status.push(".ay-status");
    PathBuf::from(status)
}

pub(super) fn dimacs_proof_status_lock_path(path: &Path) -> PathBuf {
    let mut lock = path.as_os_str().to_os_string();
    lock.push(".lock");
    PathBuf::from(lock)
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn dimacs_proof_digest_hex(digest: Sha256Digest) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(digest.len() * 2);
    for byte in digest {
        encoded.push(HEX[(byte >> 4) as usize] as char);
        encoded.push(HEX[(byte & 0x0f) as usize] as char);
    }
    encoded
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn dimacs_proof_status_content(status: &str, sha256: Option<Sha256Digest>) -> String {
    let mut content = format!(
        "ay-dimacs-proof-status-v1\nstatus={status}\nproducer_pid={}\n",
        std::process::id()
    );
    if let Some(sha256) = sha256 {
        content.push_str("sha256=");
        content.push_str(&dimacs_proof_digest_hex(sha256));
        content.push('\n');
    }
    content
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn status_transaction_error(
    operation_error: io::Error,
    cleanup: io::Result<bool>,
    label: &str,
) -> io::Error {
    match cleanup {
        Ok(_) => operation_error,
        Err(cleanup_error) => io::Error::other(format!(
            "{operation_error}; failed to clean the owned {label}: {cleanup_error}"
        )),
    }
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn reserve_dimacs_proof_status(proof_path: &str) -> io::Result<DimacsProofStatusReservation> {
    reserve_dimacs_proof_status_body(proof_path)
}

#[cfg(not(any(target_os = "linux", target_os = "macos", windows)))]
fn reserve_dimacs_proof_status(_proof_path: &str) -> io::Result<DimacsProofStatusReservation> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "transactional DIMACS proof status publication is unavailable on this platform",
    ))
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn rewrite_reserved_dimacs_proof_status(
    descriptor: &File,
    path: &Path,
    identity: ProofFileIdentity,
    content: &[u8],
) -> io::Result<()> {
    let visible = open_dimacs_regular_file(path)?;
    if regular_single_link_identity(&visible, path)? != identity {
        return Err(io::Error::other(format!(
            "DIMACS proof status path '{}' was replaced",
            path.display()
        )));
    }
    let mut writer = descriptor;
    writer.set_len(0)?;
    writer.seek(SeekFrom::Start(0))?;
    writer.write_all(content)?;
    writer.sync_all()?;
    if regular_single_link_identity(descriptor, path)? != identity {
        return Err(io::Error::other(format!(
            "DIMACS proof status path '{}' changed during update",
            path.display()
        )));
    }
    Ok(())
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn publish_reserved_dimacs_proof_status(
    reservation: DimacsProofStatusReservation,
    status: &str,
    sha256: Option<Sha256Digest>,
) -> io::Result<RetainedDimacsPublication> {
    let content = dimacs_proof_status_content(status, sha256);
    if let Err(error) = rewrite_reserved_dimacs_proof_status(
        &reservation.lock_descriptor,
        &reservation.lock_path,
        reservation.lock_identity,
        content.as_bytes(),
    ) {
        return Err(dimacs_invalidation_error(
            error,
            invalidate_dimacs_descriptor(
                &reservation.lock_descriptor,
                DimacsPublicationInvalidation::Empty,
            ),
            "DIMACS proof status transaction lock",
        ));
    }
    if let Err(error) = rename_dimacs_noreplace(&reservation.lock_path, &reservation.status_path) {
        return Err(dimacs_invalidation_error(
            error,
            invalidate_dimacs_descriptor(
                &reservation.lock_descriptor,
                DimacsPublicationInvalidation::Empty,
            ),
            "DIMACS proof status transaction lock",
        ));
    }
    let publication = RetainedDimacsPublication::capture(
        reservation.lock_descriptor,
        reservation.status_path.clone(),
        "DIMACS proof status marker",
        None,
        DimacsPublicationInvalidation::Empty,
    )?;
    // Directory fsync is the POSIX idiom for making a rename durable, and is
    // gated to unix exactly as the other two sites are: on Windows `File::open`
    // of a DIRECTORY fails with ERROR_ACCESS_DENIED unless it is opened with
    // FILE_FLAG_BACKUP_SEMANTICS, and a directory handle cannot be flushed
    // anyway. NTFS orders the rename's metadata itself, so there is nothing to
    // force here.
    #[cfg(unix)]
    if let Some(parent) = reservation.status_path.parent() {
        if let Err(error) = File::open(parent).and_then(|directory| directory.sync_all()) {
            return Err(dimacs_invalidation_error(
                error,
                publication.invalidate_exact(),
                "DIMACS proof status marker",
            ));
        }
    }
    Ok(publication)
}

#[cfg(not(any(target_os = "linux", target_os = "macos", windows)))]
fn publish_reserved_dimacs_proof_status(
    _reservation: DimacsProofStatusReservation,
    _status: &str,
    _sha256: Option<Sha256Digest>,
) -> io::Result<RetainedDimacsPublication> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "transactional DIMACS proof status publication is unavailable on this platform",
    ))
}

fn take_owned_dimacs_proof_status_reservation(
    proof_path: &str,
) -> io::Result<Option<DimacsProofStatusReservation>> {
    let resolved = resolved_dimacs_proof_path(proof_path)?;
    Ok(owned_dimacs_proofs()
        .lock()
        .map_err(|_| dimacs_proof_registry_error())?
        .get_mut(&resolved)
        .and_then(|state| state.status_reservation.take()))
}

fn mark_synthesized_default_dimacs_proof_stale(proof: &ProofConfig) {
    debug_assert!(proof.synthesized_default);
    let reservation =
        take_owned_dimacs_proof_status_reservation(&proof.path).and_then(|reservation| {
            match reservation {
                Some(reservation) => Ok(reservation),
                None => reserve_dimacs_proof_status(&proof.path),
            }
        });
    match reservation.and_then(|reservation| {
        publish_reserved_dimacs_proof_status(reservation, "stale-not-current", None)
    }) {
        Ok(status_publication) => safe_eprintln!(
            "c proof-status: stale-not-current ({}; marker {})",
            proof.path,
            status_publication.path.display()
        ),
        Err(error) => safe_eprintln!(
            "c proof-status: stale-not-current ({}; status marker unavailable: {error})",
            proof.path
        ),
    }
}

fn mark_synthesized_default_dimacs_proof_current(
    proof: &ProofConfig,
    published: PublishedDimacsProof,
    publication: &mut DimacsUnsatPublicationTransaction,
) -> io::Result<()> {
    if validate_published_dimacs_proof(&proof.path)? != published {
        return Err(io::Error::other(
            "synthesized-default proof publication changed before status commit",
        ));
    }
    publication.proof.validate()?;
    let reservation =
        take_owned_dimacs_proof_status_reservation(&proof.path)?.ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::NotFound,
                "synthesized-default proof status transaction is not owned by this run",
            )
        })?;
    let status_publication = publish_reserved_dimacs_proof_status(
        reservation,
        "current-same-run",
        Some(published.sha256),
    )?;
    let status_path = status_publication.path.clone();
    publication.status = Some(status_publication);

    // The current marker was the last participant to become public. Re-check
    // the exact proof only after that publication so no status can authorize a
    // proof generation replaced in the marker-commit window.
    if validate_published_dimacs_proof(&proof.path)? != published {
        return Err(io::Error::other(
            "synthesized-default proof publication changed during status commit",
        ));
    }
    publication.proof.validate()?;
    safe_eprintln!(
        "c proof-status: current-same-run ({}; marker {})",
        proof.path,
        status_path.display()
    );
    Ok(())
}

fn warn_optional_dimacs_proof_failure(proof: &ProofConfig, reason: &str) {
    mark_synthesized_default_dimacs_proof_stale(proof);
    safe_eprintln!(
        "c Warning: optional synthesized DIMACS proof {} was not published: {reason}; solver verdict remains authoritative",
        proof.path
    );
}

fn handle_dimacs_proof_io_failure(proof: &ProofConfig, operation: &str, error: &io::Error) {
    let mut reason = format!("failed to {operation} DIMACS proof {}: {error}", proof.path);
    if synthesized_default_dimacs_proof_is_optional(proof) {
        warn_optional_dimacs_proof_failure(proof, &reason);
        if let Err(cleanup_error) = remove_owned_dimacs_proof(&proof.path) {
            safe_eprintln!(
                "c Warning: failed to discard unpublished optional DIMACS proof {}: {cleanup_error}",
                proof.path
            );
        }
        return;
    }
    if proof.synthesized_default {
        if let Err(cleanup_error) = invalidate_synthesized_default_dimacs_proof(proof) {
            reason.push_str(&format!(
                "; failed to remove only AY's authenticated proof generation: {cleanup_error}"
            ));
        }
    }
    if let Some(gate) = required_dimacs_proof_gate_name() {
        if proof.synthesized_default || proof.is_temp {
            fail_closed_satcomp_proof_setup(&format!(
                "{gate} rejected UNSAT because required proof I/O failed: {reason}"
            ));
        }
    }
    safe_eprintln!("Error: {reason}");
    std::process::exit(1);
}

fn handle_failed_proof_create(proof: &ProofConfig, error: &io::Error) {
    if synthesized_default_dimacs_proof_is_optional(proof) {
        handle_dimacs_proof_io_failure(proof, "create", error);
        return;
    }
    if official_sat_main_regular_route_from_env() {
        let mut reason = format!(
            "proof output unavailable: failed to create proof file {}: {error}",
            proof.path
        );
        if proof.synthesized_default {
            if let Err(cleanup_error) = invalidate_synthesized_default_dimacs_proof(proof) {
                reason.push_str(&format!(
                    "; failed to remove only AY's authenticated proof generation: {cleanup_error}"
                ));
            }
        }
        fail_closed_satcomp_proof_setup(&reason);
    }
    handle_dimacs_proof_io_failure(proof, "create", error);
}

fn sink_proof_output_after_optional_create_failure(
    proof: &ProofConfig,
    num_original_clauses: u64,
    error: &io::Error,
) -> ProofOutput {
    handle_failed_proof_create(proof, error);
    debug_assert!(synthesized_default_dimacs_proof_is_optional(proof));
    match (proof.format, proof.binary) {
        (ProofFormat::Veripb, _) => ProofOutput::veripb(io::sink()),
        (ProofFormat::Drat, false) => ProofOutput::drat_text(io::sink()),
        (ProofFormat::Drat, true) => ProofOutput::drat_binary(io::sink()),
        (ProofFormat::Lrat, false) => ProofOutput::lrat_text(io::sink(), num_original_clauses),
        (ProofFormat::Lrat, true) => ProofOutput::lrat_binary(io::sink(), num_original_clauses),
        (ProofFormat::Alethe | ProofFormat::Lean4, _) => {
            unreachable!("Alethe/Lean4 do not create a pre-solve DIMACS proof file")
        }
    }
}
