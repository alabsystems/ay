// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

struct AuthenticatedRemoval<'a> {
    path: &'a Path,
    descriptor: &'a File,
    identity: ProofFileIdentity,
    label: &'a str,
    invalidation: DimacsPublicationInvalidation,
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn quarantine_inspection_failure(
    removal: &AuthenticatedRemoval<'_>,
    quarantine_path: &Path,
    inspect_error: io::Error,
) -> io::Error {
    let operation_error = match rename_dimacs_noreplace(quarantine_path, removal.path) {
        Ok(()) => io::Error::other(format!(
            "could not authenticate quarantined {}; it was restored to '{}': {inspect_error}",
            removal.label,
            removal.path.display()
        )),
        Err(restore_error) => io::Error::other(format!(
            "could not authenticate quarantined {} at '{}': {inspect_error}; restoration to '{}' also failed: {restore_error}; the quarantined object was preserved",
            removal.label,
            quarantine_path.display(),
            removal.path.display()
        )),
    };
    dimacs_invalidation_error(
        operation_error,
        invalidate_dimacs_descriptor(removal.descriptor, removal.invalidation),
        removal.label,
    )
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn quarantine_authenticated_file(
    removal: &AuthenticatedRemoval<'_>,
) -> io::Result<Option<(PathBuf, File, ProofFileIdentity)>> {
    let (private_directory, _) =
        create_private_dimacs_staging_directory(removal.path).map_err(|error| {
            dimacs_invalidation_error(
                error,
                invalidate_dimacs_descriptor(removal.descriptor, removal.invalidation),
                removal.label,
            )
        })?;
    let quarantine_path = private_directory.join("discard");
    match move_dimacs_proof_to_private_quarantine(removal.path, &quarantine_path) {
        Ok(()) => {}
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            invalidate_dimacs_descriptor(removal.descriptor, removal.invalidation)?;
            return Ok(None);
        }
        Err(error) => {
            return Err(dimacs_invalidation_error(
                error,
                invalidate_dimacs_descriptor(removal.descriptor, removal.invalidation),
                removal.label,
            ));
        }
    }
    #[cfg(test)]
    if take_injected_dimacs_proof_cleanup_replacement() {
        std::fs::write(removal.path, b"raced replacement\n")?;
    }
    #[cfg(test)]
    if take_injected_dimacs_proof_cleanup_failure() {
        return Err(dimacs_invalidation_error(
            io::Error::other("injected DIMACS proof cleanup failure after quarantine"),
            invalidate_dimacs_descriptor(removal.descriptor, removal.invalidation),
            removal.label,
        ));
    }
    let quarantined = open_dimacs_regular_file(&quarantine_path)
        .map_err(|error| quarantine_inspection_failure(removal, &quarantine_path, error))?;
    let identity = match regular_file_identity(&quarantined, &quarantine_path) {
        Ok(identity) => identity,
        Err(error) => {
            drop(quarantined);
            return Err(quarantine_inspection_failure(
                removal,
                &quarantine_path,
                error,
            ));
        }
    };
    Ok(Some((quarantine_path, quarantined, identity)))
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn finish_authenticated_quarantine(removal: AuthenticatedRemoval<'_>) -> io::Result<bool> {
    let Some((quarantine_path, quarantined, identity)) = quarantine_authenticated_file(&removal)?
    else {
        return Ok(false);
    };
    if identity != removal.identity {
        drop(quarantined);
        let restore = rename_dimacs_noreplace(&quarantine_path, removal.path).map_err(|error| {
            io::Error::other(format!(
                "{} cleanup quarantined a replacement at '{}', then could not restore it to '{}': {error}; the replacement was preserved",
                removal.label,
                quarantine_path.display(),
                removal.path.display()
            ))
        });
        let invalidation = invalidate_dimacs_descriptor(removal.descriptor, removal.invalidation);
        return match (restore, invalidation) {
            (Ok(()), Ok(())) => Ok(false),
            (Err(error), invalidation) => Err(dimacs_invalidation_error(
                error,
                invalidation,
                removal.label,
            )),
            (Ok(()), Err(error)) => Err(error),
        };
    }
    invalidate_dimacs_descriptor(removal.descriptor, removal.invalidation)?;
    #[cfg(unix)]
    if let Some(parent) = removal.path.parent() {
        File::open(parent)?.sync_all()?;
    }
    drop(quarantined);
    Ok(true)
}

fn remove_authenticated_visible_file_body(removal: AuthenticatedRemoval<'_>) -> io::Result<bool> {
    if regular_file_identity(removal.descriptor, removal.path)? != removal.identity {
        return Err(io::Error::other(format!(
            "owned {} descriptor identity changed before cleanup",
            removal.label
        )));
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos", windows)))]
    {
        let path_matches = match open_dimacs_regular_file(removal.path) {
            Ok(visible) => regular_single_link_identity(&visible, removal.path)
                .map(|found| found == removal.identity),
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(false),
            Err(error) => Err(error),
        };
        let invalidation = invalidate_dimacs_descriptor(removal.descriptor, removal.invalidation);
        return match (path_matches, invalidation) {
            (Ok(matches), Ok(())) => Ok(matches),
            (Err(error), invalidation) => Err(dimacs_invalidation_error(
                error,
                invalidation,
                removal.label,
            )),
            (Ok(_), Err(error)) => Err(error),
        };
    }
    #[cfg(any(target_os = "linux", target_os = "macos", windows))]
    finish_authenticated_quarantine(removal)
}
