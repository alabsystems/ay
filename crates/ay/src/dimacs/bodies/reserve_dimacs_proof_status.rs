// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn create_dimacs_status_reservation(
    proof_path: &str,
    label: Option<&ay::proof_store::ProofSubject>,
) -> io::Result<DimacsProofStatusReservation> {
    // An exit waits for this reservation until its custody is registered
    // (status_custody.rs), and the process-exit sweep exists before the lock.
    let _reserving = DimacsStatusReserving::enter();
    // The exit claims the run before it reads the in-flight count, and this
    // reservation counts itself before it reads the claim (both SeqCst): so
    // either the exit waits for this reservation, or no lock is created.
    if crate::run_claimed_unanswered() {
        return Err(io::Error::other(
            "the run ended unanswered; no DIMACS proof status transaction was reserved",
        ));
    }
    arm_abandoned_dimacs_proof_sweep();
    let proof_path = resolved_dimacs_proof_path(proof_path)?;
    let status_path = dimacs_proof_status_path_from_path(&proof_path);
    let lock_path = dimacs_proof_status_lock_path(&status_path);
    let mut lock_descriptor = if label
        .is_some_and(|subject| subject.placement == ay::proof_store::ProofPlacement::Store)
    {
        // The checker must see a live locked descriptor or an abandoned name,
        // never a newly created name whose writer has not acquired its lock yet.
        let directory = lock_path
            .parent()
            .ok_or_else(|| io::Error::other("missing proof slot"))?;
        let _directory = ay::proof_store::lock_slot_directory(directory)?;
        open_dimacs_status_lock(&lock_path)?
    } else {
        open_dimacs_status_lock(&lock_path)?
    };
    let lock_identity = regular_file_identity(&lock_descriptor, &lock_path).map_err(|error| {
        dimacs_invalidation_error(
            error,
            invalidate_dimacs_descriptor(&lock_descriptor, DimacsPublicationInvalidation::Empty),
            "DIMACS proof status transaction lock",
        )
    })?;
    #[cfg(test)]
    let validation = if take_injected_dimacs_status_lock_identity_failure() {
        Err(io::Error::other(
            "injected DIMACS proof status lock identity failure",
        ))
    } else {
        regular_single_link_identity(&lock_descriptor, &lock_path)
    };
    #[cfg(not(test))]
    let validation = regular_single_link_identity(&lock_descriptor, &lock_path);
    // The lock, which becomes the published marker, says what it is from its
    // creation on, as its proof does (DC-77).
    let validation = validation.and_then(|identity| match label {
        Some(subject) => {
            ay::proof_store::label_at_creation(&lock_descriptor, subject).map(|()| identity)
        }
        None => Ok(identity),
    });
    if let Err(error) = validation {
        return Err(status_transaction_error(
            error,
            remove_authenticated_visible_file(
                &lock_path,
                &lock_descriptor,
                lock_identity,
                "DIMACS proof status transaction lock",
                DimacsPublicationInvalidation::Empty,
            ),
            "DIMACS proof status transaction lock",
        ));
    }
    let content = format!(
        "ay-dimacs-proof-status-transaction-v1\nproducer_pid={}\n",
        std::process::id()
    );
    if let Err(error) = lock_descriptor
        .write_all(content.as_bytes())
        .and_then(|()| lock_descriptor.sync_all())
    {
        return Err(status_transaction_error(
            error,
            remove_authenticated_visible_file(
                &lock_path,
                &lock_descriptor,
                lock_identity,
                "DIMACS proof status transaction lock",
                DimacsPublicationInvalidation::Empty,
            ),
            "DIMACS proof status transaction lock",
        ));
    }
    let custody = register_reserved_dimacs_status_custody(
        &lock_path,
        &status_path,
        &lock_descriptor,
        lock_identity,
    )?;
    Ok(DimacsProofStatusReservation {
        proof_path,
        status_path,
        lock_path,
        lock_descriptor,
        lock_identity,
        custody,
    })
}

/// Create the status transaction lock `lock_path` exclusively: never through
/// a symlink, never over an existing object.
#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn open_dimacs_status_lock(lock_path: &Path) -> io::Result<File> {
    let mut options = OpenOptions::new();
    options.read(true).write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options
            .mode(0o600)
            .custom_flags(nix::libc::O_NOFOLLOW | nix::libc::O_NONBLOCK);
    }
    #[cfg(windows)]
    {
        use std::os::windows::fs::OpenOptionsExt as _;
        options.share_mode(ay_sys::windows_fs::SHARE_READ_WRITE_DELETE);
    }
    let lock = options.open(lock_path).map_err(|error| {
        if error.kind() == io::ErrorKind::AlreadyExists {
            io::Error::new(
                io::ErrorKind::AlreadyExists,
                format!(
                    "synthesized-default proof status transaction '{}' is already active",
                    lock_path.display()
                ),
            )
        } else {
            error
        }
    })?;
    // Held for the run's life, on this descriptor and every clone of it, and
    // still held once the lock is renamed onto the marker: a lock or marker
    // whose lock another process can take belongs to no live run, whatever
    // process id it records (`ay::proof_store`'s check again). It is taken
    // before the header is written, so a free lock with a header is one its
    // run left. The wait is only for a check again's momentary hold.
    lock.lock()?;
    Ok(lock)
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn reject_preexisting_dimacs_status(
    reservation: DimacsProofStatusReservation,
) -> io::Result<DimacsProofStatusReservation> {
    match std::fs::symlink_metadata(&reservation.status_path) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(reservation),
        status => {
            let error = match status {
                Ok(_) => io::Error::new(
                    io::ErrorKind::AlreadyExists,
                    format!(
                        "refusing to overwrite pre-existing DIMACS proof status output '{}'",
                        reservation.status_path.display()
                    ),
                ),
                Err(error) => error,
            };
            // An exit that already settled the lock owns it now.
            let cleanup = {
                let claim = reservation.custody.claim_settling()?;
                let removed = remove_authenticated_visible_file(
                    &reservation.lock_path,
                    &reservation.lock_descriptor,
                    reservation.lock_identity,
                    "DIMACS proof status transaction lock",
                    DimacsPublicationInvalidation::Empty,
                );
                claim.finish(removed.is_ok());
                removed
            };
            Err(status_transaction_error(
                error,
                cleanup,
                "DIMACS proof status transaction lock",
            ))
        }
    }
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn reserve_dimacs_proof_status_body(
    proof_path: &str,
    label: Option<&ay::proof_store::ProofSubject>,
) -> io::Result<DimacsProofStatusReservation> {
    reject_preexisting_dimacs_status(create_dimacs_status_reservation(proof_path, label)?)
}
