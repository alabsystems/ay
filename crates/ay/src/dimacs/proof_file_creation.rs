// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn regular_single_link_identity(file: &File, path: &Path) -> io::Result<ProofFileIdentity> {
    let metadata = file.metadata()?;
    if !metadata.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!(
                "DIMACS proof output '{}' is not a regular file",
                path.display()
            ),
        ));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        if metadata.nlink() != 1 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!(
                    "DIMACS proof output '{}' has {} hard links; exactly one is required",
                    path.display(),
                    metadata.nlink()
                ),
            ));
        }
    }
    #[cfg(windows)]
    {
        let links = ay_sys::windows_fs::file_info(file)?.number_of_links;
        if links != 1 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!(
                    "DIMACS proof output '{}' has {links} hard links; exactly one is required",
                    path.display()
                ),
            ));
        }
    }
    ProofFileIdentity::from_file(file)
}

fn open_dimacs_regular_file(path: &Path) -> io::Result<File> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        OpenOptions::new()
            .read(true)
            .custom_flags(nix::libc::O_NOFOLLOW | nix::libc::O_NONBLOCK)
            .open(path)
    }
    #[cfg(not(unix))]
    {
        let metadata = std::fs::symlink_metadata(path)?;
        if !metadata.file_type().is_file() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("'{}' is not a regular file", path.display()),
            ));
        }
        #[cfg(windows)]
        {
            use std::os::windows::fs::OpenOptionsExt as _;
            // See create_named_dimacs_staging_file: a reader holding this file
            // open must not block the quarantine rename that fail-closed
            // cleanup performs on the same path.
            OpenOptions::new()
                .read(true)
                .share_mode(ay_sys::windows_fs::SHARE_READ_WRITE_DELETE)
                .open(path)
        }
        #[cfg(not(windows))]
        File::open(path)
    }
}

fn regular_file_identity(file: &File, path: &Path) -> io::Result<ProofFileIdentity> {
    let metadata = file.metadata()?;
    if !metadata.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!(
                "DIMACS proof output '{}' is not a regular file",
                path.display()
            ),
        ));
    }
    ProofFileIdentity::from_file(file)
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn create_private_dimacs_staging_directory(target: &Path) -> io::Result<(PathBuf, PathBuf)> {
    let parent = target.parent().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "DIMACS proof target has no parent directory",
        )
    })?;
    let first =
        DIMACS_PROOF_STAGING_NONCE.fetch_add(DIMACS_PROOF_STAGING_ATTEMPTS, Ordering::Relaxed);
    for offset in 0..DIMACS_PROOF_STAGING_ATTEMPTS {
        let directory = parent.join(format!(
            "{DIMACS_PROOF_STAGING_PREFIX}{}-{}",
            std::process::id(),
            first.wrapping_add(offset)
        ));
        let mut builder = std::fs::DirBuilder::new();
        #[cfg(unix)]
        {
            use std::os::unix::fs::DirBuilderExt as _;
            builder.mode(0o700);
        }
        match builder.create(&directory) {
            Ok(()) => return Ok((directory.clone(), directory.join("proof"))),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(error),
        }
    }
    Err(io::Error::new(
        io::ErrorKind::AlreadyExists,
        format!(
            "could not reserve a private DIMACS proof staging directory after {DIMACS_PROOF_STAGING_ATTEMPTS} attempts"
        ),
    ))
}

#[cfg(target_os = "linux")]
fn create_anonymous_dimacs_staging_file(target: &Path) -> io::Result<File> {
    use std::os::unix::fs::OpenOptionsExt as _;

    #[cfg(test)]
    if let Some(raw_os_error) = take_injected_anonymous_dimacs_staging_error() {
        return Err(io::Error::from_raw_os_error(raw_os_error));
    }

    let parent = target.parent().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "DIMACS proof target has no parent directory",
        )
    })?;
    let mut options = OpenOptions::new();
    options
        .read(true)
        .write(true)
        .mode(0o600)
        .custom_flags(nix::libc::O_TMPFILE | nix::libc::O_NOFOLLOW | nix::libc::O_NONBLOCK);
    options.open(parent)
}

#[cfg(target_os = "linux")]
fn anonymous_dimacs_staging_is_unsupported(error: &io::Error) -> bool {
    matches!(
        error.raw_os_error(),
        // EOPNOTSUPP is the documented filesystem rejection. EINVAL is
        // returned by filesystems which reject the O_TMPFILE flag combination.
        // EISDIR can identify a pre-O_TMPFILE kernel, which also lacks the
        // renameat2 primitive required to publish and quarantine a named stage;
        // it must therefore remain fail closed. Permission, quota, I/O, and
        // exhaustion failures likewise retain their precise result.
        Some(nix::libc::EOPNOTSUPP | nix::libc::EINVAL)
    )
}

#[cfg(target_os = "macos")]
fn create_anonymous_dimacs_staging_file(_target: &Path) -> io::Result<File> {
    // macOS has no O_TMPFILE-style anonymous inode. Report the documented
    // "filesystem cannot stage anonymously" rejection so the caller falls
    // back to the named single-link stage, which macOS publishes atomically
    // with no-replace semantics via renamex_np(RENAME_EXCL).
    Err(io::Error::from_raw_os_error(nix::libc::EOPNOTSUPP))
}

#[cfg(target_os = "macos")]
fn anonymous_dimacs_staging_is_unsupported(error: &io::Error) -> bool {
    matches!(error.raw_os_error(), Some(nix::libc::EOPNOTSUPP))
}

#[cfg(windows)]
fn create_anonymous_dimacs_staging_file(_target: &Path) -> io::Result<File> {
    // Windows has no O_TMPFILE-style anonymous inode either. Take the same
    // route macOS takes: report "cannot stage anonymously" so the caller falls
    // back to the named single-link stage, which Windows publishes with
    // no-replace semantics via MoveFileExW without MOVEFILE_REPLACE_EXISTING
    // (`ay_sys::fs::rename_noreplace`).
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "anonymous DIMACS proof staging is unavailable on this platform",
    ))
}

#[cfg(windows)]
fn anonymous_dimacs_staging_is_unsupported(error: &io::Error) -> bool {
    error.kind() == io::ErrorKind::Unsupported
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn create_named_dimacs_staging_file(target: &Path) -> io::Result<(PathBuf, File)> {
    let parent = target.parent().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "DIMACS proof target has no parent directory",
        )
    })?;
    let first =
        DIMACS_PROOF_STAGING_NONCE.fetch_add(DIMACS_PROOF_STAGING_ATTEMPTS, Ordering::Relaxed);
    for offset in 0..DIMACS_PROOF_STAGING_ATTEMPTS {
        let staging_path = parent.join(format!(
            "{DIMACS_PROOF_STAGING_PREFIX}{}-{}.stage",
            std::process::id(),
            first.wrapping_add(offset)
        ));
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
            // Windows refuses MoveFileExW/DeleteFile on a path whose file still
            // has an open handle unless EVERY handle permits deletion. The
            // staged publication path renames the staging file while its
            // descriptor is still held (that descriptor is the authentication
            // root and cannot be closed first), so FILE_SHARE_DELETE is
            // mandatory here; without it publication fails with ERROR_ACCESS_DENIED.
            options.share_mode(ay_sys::windows_fs::SHARE_READ_WRITE_DELETE);
        }
        match options.open(&staging_path) {
            Ok(file) => return Ok((staging_path, file)),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(error),
        }
    }
    Err(io::Error::new(
        io::ErrorKind::AlreadyExists,
        format!(
            "could not reserve a named DIMACS proof staging file after {DIMACS_PROOF_STAGING_ATTEMPTS} attempts"
        ),
    ))
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn cleanup_unregistered_dimacs_staging(
    descriptor: &File,
    staging_path: &Path,
    invalidation: DimacsPublicationInvalidation,
) -> io::Result<()> {
    let descriptor_identity = regular_file_identity(descriptor, staging_path)?;
    if !remove_authenticated_visible_file(
        staging_path,
        descriptor,
        descriptor_identity,
        "private DIMACS staging file",
        invalidation,
    )? {
        match std::fs::symlink_metadata(staging_path) {
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Ok(_) => {
                return Err(io::Error::other(format!(
                    "private DIMACS proof staging path '{}' was replaced during failed setup; it was preserved",
                    staging_path.display()
                )));
            }
            Err(error) => return Err(error),
        }
    }
    Ok(())
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn dimacs_proof_setup_error(
    error: io::Error,
    cleanup: io::Result<()>,
    staging_path: &Path,
) -> io::Error {
    match cleanup {
        Ok(()) => error,
        Err(cleanup_error) => io::Error::other(format!(
            "{error}; failed to clean descriptor-owned private DIMACS staging file '{}': {cleanup_error}",
            staging_path.display()
        )),
    }
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn preexisting_dimacs_proof_error(path: &Path, error: Option<&io::Error>) -> io::Error {
    let detail = error.map_or_else(String::new, |error| format!(": {error}"));
    io::Error::new(
        io::ErrorKind::AlreadyExists,
        format!(
            "refusing to overwrite pre-existing DIMACS proof output '{}'{detail}",
            path.display()
        ),
    )
}

/// The two duplicates of a new generation's descriptor: the registry's, and
/// the custody's own for exits that cannot take the registry's lock
/// (proof_custody.rs).
#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn clone_owned_dimacs_proof_descriptors(file: &File) -> io::Result<(File, File)> {
    #[cfg(test)]
    if take_injected_dimacs_proof_create_failure(InjectedDimacsProofCreateFailure::Clone) {
        return Err(io::Error::other("injected DIMACS proof clone failure"));
    }
    Ok((file.try_clone()?, file.try_clone()?))
}

/// Reserve a proof target for this process without following or truncating an
/// existing object. Linux prefers an anonymous descriptor and falls back to a
/// randomized mode-0600 sibling stage when the filesystem lacks `O_TMPFILE`.
/// Sealing publishes the authenticated generation with no-clobber semantics.
/// Unsupported platforms fail before reserving any proof/status pathname. The
/// registry retains a descriptor for every later seal, verification, artifact
/// scan, and cleanup.
fn create_owned_dimacs_proof_file_with_status(
    path: &str,
    status_reservation: &mut Option<DimacsProofStatusReservation>,
    invalidation: DimacsPublicationInvalidation,
    fast_publication: bool,
) -> io::Result<File> {
    create_labelled_dimacs_proof_file_with_status(
        path,
        status_reservation,
        invalidation,
        fast_publication,
        None,
    )
}

/// As [`create_owned_dimacs_proof_file_with_status`], labelling the staged
/// file at its creation with what the proof is derived from
/// (`ay::proof_store`), before it is registered: a label that cannot be
/// written fails the creation, and the unregistered stage is cleaned up the
/// way an identity failure is. The label stays on the inode through the
/// rename or link that publishes it, and a run killed mid-write leaves a stage
/// that says what it is.
#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn create_labelled_dimacs_proof_file_with_status(
    path: &str,
    status_reservation: &mut Option<DimacsProofStatusReservation>,
    invalidation: DimacsPublicationInvalidation,
    fast_publication: bool,
    label: Option<&ay::proof_store::ProofSubject>,
) -> io::Result<File> {
    let resolved = match status_reservation.as_ref() {
        Some(reservation) => reservation.proof_path.clone(),
        None => resolved_dimacs_proof_path(path)?,
    };
    let mut owned = owned_dimacs_proofs()
        .lock()
        .map_err(|_| dimacs_proof_registry_error())?;
    if owned.contains_key(&resolved) {
        return Err(io::Error::new(
            io::ErrorKind::AlreadyExists,
            format!(
                "DIMACS proof output '{}' is already active",
                resolved.display()
            ),
        ));
    }

    match std::fs::symlink_metadata(&resolved) {
        Ok(_) => return Err(preexisting_dimacs_proof_error(&resolved, None)),
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(error) => return Err(error),
    }

    let (file, staging_path, location) = match create_anonymous_dimacs_staging_file(&resolved) {
        Ok(file) => (file, None, OwnedDimacsProofLocation::Anonymous),
        Err(error) if anonymous_dimacs_staging_is_unsupported(&error) => {
            let (staging, file) = create_named_dimacs_staging_file(&resolved)?;
            (file, Some(staging), OwnedDimacsProofLocation::Staged)
        }
        Err(error) => return Err(error),
    };
    let staging_label = staging_path.as_deref().unwrap_or(&resolved);
    #[cfg(test)]
    let identity_result =
        if take_injected_dimacs_proof_create_failure(InjectedDimacsProofCreateFailure::Identity) {
            Err(io::Error::other("injected DIMACS proof identity failure"))
        } else {
            match location {
                OwnedDimacsProofLocation::Anonymous => regular_file_identity(&file, staging_label),
                _ => regular_single_link_identity(&file, staging_label),
            }
        };
    #[cfg(not(test))]
    let identity_result = match location {
        OwnedDimacsProofLocation::Anonymous => regular_file_identity(&file, staging_label),
        _ => regular_single_link_identity(&file, staging_label),
    };
    let identity_result = identity_result.and_then(|identity| match label {
        Some(subject) => ay::proof_store::label_at_creation(&file, subject).map(|()| identity),
        None => Ok(identity),
    });
    let identity = match identity_result {
        Ok(identity) => identity,
        Err(error) => {
            let cleanup = staging_path
                .as_deref()
                .map(|staging| cleanup_unregistered_dimacs_staging(&file, staging, invalidation))
                .unwrap_or(Ok(()));
            return Err(dimacs_proof_setup_error(error, cleanup, staging_label));
        }
    };
    let (descriptor, custody_descriptor) = match clone_owned_dimacs_proof_descriptors(&file) {
        Ok(descriptors) => descriptors,
        Err(error) => {
            let cleanup = staging_path
                .as_deref()
                .map(|staging| cleanup_unregistered_dimacs_staging(&file, staging, invalidation))
                .unwrap_or(Ok(()));
            return Err(dimacs_proof_setup_error(error, cleanup, staging_label));
        }
    };
    // Armed BEFORE the registry publishes this generation, so no window exists
    // in which an abandoned staging file or status lock has no owner.
    arm_abandoned_dimacs_proof_sweep();
    let custody = register_dimacs_proof_custody(
        resolved.clone(),
        staging_path.clone(),
        identity,
        custody_descriptor,
        fast_publication,
    );
    let write_failed = Arc::new(AtomicBool::new(false));
    owned.insert(
        resolved,
        OwnedDimacsProof {
            descriptor,
            identity,
            staging_path,
            location,
            write_failed,
            published: None,
            status_reservation: status_reservation.take(),
            invalidation,
            custody,
        },
    );
    Ok(file)
}

#[cfg(not(any(target_os = "linux", target_os = "macos", windows)))]
fn create_labelled_dimacs_proof_file_with_status(
    _path: &str,
    _status_reservation: &mut Option<DimacsProofStatusReservation>,
    _invalidation: DimacsPublicationInvalidation,
    _fast_publication: bool,
    _label: Option<&ay::proof_store::ProofSubject>,
) -> io::Result<File> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "transactional DIMACS proof publication is unavailable on this platform",
    ))
}

fn create_owned_dimacs_proof_file(path: &str) -> io::Result<File> {
    let mut status_reservation = None;
    create_owned_dimacs_proof_file_with_status(
        path,
        &mut status_reservation,
        DimacsPublicationInvalidation::Proof { binary: false },
        false,
    )
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn create_configured_dimacs_proof_file(proof: &ProofConfig) -> io::Result<File> {
    if !proof.synthesized_default {
        let mut status_reservation = None;
        return create_labelled_dimacs_proof_file_with_status(
            &proof.path,
            &mut status_reservation,
            DimacsPublicationInvalidation::Proof {
                binary: proof.binary,
            },
            dimacs_fast_publication(proof),
            proof.label.as_ref(),
        );
    }

    let mut status_reservation = Some(reserve_dimacs_proof_status(
        &proof.path,
        proof.label.as_ref(),
    )?);
    match create_labelled_dimacs_proof_file_with_status(
        &proof.path,
        &mut status_reservation,
        DimacsPublicationInvalidation::Proof {
            binary: proof.binary,
        },
        false,
        proof.label.as_ref(),
    ) {
        Ok(file) => Ok(file),
        Err(proof_error) => {
            let Some(reservation) = status_reservation.take() else {
                return Err(proof_error);
            };
            match publish_reserved_dimacs_proof_status(reservation, "stale-not-current", None) {
                Ok(_) => Err(proof_error),
                Err(status_error) => Err(io::Error::other(format!(
                    "{proof_error}; failed to publish the synthesized-default stale status: {status_error}"
                ))),
            }
        }
    }
}

#[cfg(not(any(target_os = "linux", target_os = "macos", windows)))]
fn create_configured_dimacs_proof_file(_proof: &ProofConfig) -> io::Result<File> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "transactional DIMACS proof publication is unavailable on this platform",
    ))
}
