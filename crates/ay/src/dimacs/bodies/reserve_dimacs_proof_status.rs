// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn create_dimacs_status_reservation(proof_path: &str) -> io::Result<DimacsProofStatusReservation> {
    let proof_path = resolved_dimacs_proof_path(proof_path)?;
    let status_path = dimacs_proof_status_path_from_path(&proof_path);
    let lock_path = dimacs_proof_status_lock_path(&status_path);
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
    let mut lock_descriptor = options.open(&lock_path).map_err(|error| {
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
    Ok(DimacsProofStatusReservation {
        proof_path,
        status_path,
        lock_path,
        lock_descriptor,
        lock_identity,
    })
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
            let cleanup = remove_authenticated_visible_file(
                &reservation.lock_path,
                &reservation.lock_descriptor,
                reservation.lock_identity,
                "DIMACS proof status transaction lock",
                DimacsPublicationInvalidation::Empty,
            );
            Err(status_transaction_error(
                error,
                cleanup,
                "DIMACS proof status transaction lock",
            ))
        }
    }
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn reserve_dimacs_proof_status_body(proof_path: &str) -> io::Result<DimacsProofStatusReservation> {
    reject_preexisting_dimacs_status(create_dimacs_status_reservation(proof_path)?)
}
