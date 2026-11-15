// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

struct AuthenticatedRemoval<'a> {
    path: &'a Path,
    descriptor: &'a File,
    identity: ProofFileIdentity,
    label: &'a str,
    invalidation: DimacsPublicationInvalidation,
}

#[cfg(all(test, any(target_os = "linux", target_os = "macos", windows)))]
std::thread_local! {
    static INJECTED_DIMACS_QUARANTINE_SWAP: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
    static INJECTED_DIMACS_QUARANTINE_SIBLING: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
}

/// Before the quarantine is discarded, move the owned inode aside to
/// `displaced` in the same private directory and put a stranger at `discard`.
#[cfg(all(test, target_os = "linux"))]
fn inject_dimacs_quarantine_swap_once() {
    INJECTED_DIMACS_QUARANTINE_SWAP.with(|swap| swap.set(true));
}

/// Before the quarantine is discarded, put a foreign entry, `sibling`, beside
/// `discard` in the same private directory. It is a copy of what `discard`
/// holds at that moment, so a test also sees whether the owned inode was
/// invalidated before its discard began.
#[cfg(all(test, target_os = "linux"))]
fn inject_dimacs_quarantine_sibling_once() {
    INJECTED_DIMACS_QUARANTINE_SIBLING.with(|sibling| sibling.set(true));
}

#[cfg(all(test, any(target_os = "linux", target_os = "macos", windows)))]
fn take_injected_dimacs_quarantine_swap() -> bool {
    INJECTED_DIMACS_QUARANTINE_SWAP.with(|swap| swap.replace(false))
}

#[cfg(all(test, any(target_os = "linux", target_os = "macos", windows)))]
fn take_injected_dimacs_quarantine_sibling() -> bool {
    INJECTED_DIMACS_QUARANTINE_SIBLING.with(|sibling| sibling.replace(false))
}

/// Remove the private directory [`quarantine_authenticated_file`] created for
/// `quarantine_path` once nothing of the removal is left in it. `remove_dir`
/// removes only an empty directory, so whatever another process put there is
/// preserved with it.
#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn remove_empty_private_quarantine(quarantine_path: &Path) -> io::Result<()> {
    quarantine_path.parent().map_or(Ok(()), std::fs::remove_dir)
}

/// Discard the quarantine of a completed authenticated removal: the owned
/// inode, already invalidated, then its private directory, so nothing of the
/// removal is left beside the target.
///
/// Both names belong to this call: `create_private_dimacs_staging_directory`
/// creates the directory exclusively (mode 0700 on Unix), under this PID and a
/// nonce that is never reused. So, as for a private staging name
/// ([`remove_private_dimacs_custody_name`]), re-authenticating the inode
/// immediately before the unlink is the whole guarantee. Only a process acting
/// inside this run's private directory can put anything there, and whatever it
/// put is preserved: a foreign inode fails the identity check, and `remove_dir`
/// cannot remove a directory that is not empty.
#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn discard_authenticated_quarantine(
    quarantine_path: &Path,
    identity: ProofFileIdentity,
) -> io::Result<()> {
    #[cfg(test)]
    if take_injected_dimacs_quarantine_swap() {
        std::fs::rename(quarantine_path, quarantine_path.with_file_name("displaced"))?;
        std::fs::write(quarantine_path, b"raced quarantine replacement\n")?;
    }
    #[cfg(test)]
    if take_injected_dimacs_quarantine_sibling() {
        std::fs::copy(quarantine_path, quarantine_path.with_file_name("sibling"))?;
    }
    remove_private_dimacs_custody_name(quarantine_path, identity)?;
    remove_empty_private_quarantine(quarantine_path)
}

#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn quarantine_inspection_failure(
    removal: &AuthenticatedRemoval<'_>,
    quarantine_path: &Path,
    inspect_error: io::Error,
) -> io::Error {
    let operation_error = match rename_dimacs_noreplace(quarantine_path, removal.path) {
        Ok(()) => {
            // Restored: the private directory is empty again. This path
            // already reports an error, so the directory goes best-effort.
            let _ = remove_empty_private_quarantine(quarantine_path);
            io::Error::other(format!(
                "could not authenticate quarantined {}; it was restored to '{}': {inspect_error}",
                removal.label,
                removal.path.display()
            ))
        }
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
            // Nothing was moved: the private directory is empty and ours.
            let _ = std::fs::remove_dir(&private_directory);
            invalidate_dimacs_descriptor(removal.descriptor, removal.invalidation)?;
            return Ok(None);
        }
        Err(error) => {
            // Nothing was moved either: the private directory is empty and
            // ours, and `remove_dir` cannot take anything else with it.
            let _ = std::fs::remove_dir(&private_directory);
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

/// Move the visible file into a fresh private quarantine and settle it there:
/// this run's inode is invalidated and discarded with its private directory
/// (`Ok(true)`), anything else is restored to the visible path (`Ok(false)`),
/// and an object that cannot be authenticated or restored is preserved.
#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn finish_authenticated_quarantine(removal: AuthenticatedRemoval<'_>) -> io::Result<bool> {
    let Some((quarantine_path, quarantined, identity)) = quarantine_authenticated_file(&removal)?
    else {
        return Ok(false);
    };
    if identity != removal.identity {
        drop(quarantined);
        let restore = rename_dimacs_noreplace(&quarantine_path, removal.path)
            .map_err(|error| {
                io::Error::other(format!(
                    "{} cleanup quarantined a replacement at '{}', then could not restore it to '{}': {error}; the replacement was preserved",
                    removal.label,
                    quarantine_path.display(),
                    removal.path.display()
                ))
            })
            .and_then(|()| {
                remove_empty_private_quarantine(&quarantine_path).map_err(|error| {
                    io::Error::other(format!(
                        "{} cleanup restored a replacement to '{}', then could not remove its private quarantine directory: {error}",
                        removal.label,
                        removal.path.display()
                    ))
                })
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
    drop(quarantined);
    let discarded = discard_authenticated_quarantine(&quarantine_path, removal.identity);
    #[cfg(unix)]
    if let Some(parent) = removal.path.parent() {
        File::open(parent)?.sync_all()?;
    }
    discarded.map_err(|error| {
        io::Error::other(format!(
            "owned {} was removed from '{}' and invalidated, but its private quarantine at '{}' could not be discarded: {error}",
            removal.label,
            removal.path.display(),
            quarantine_path.display()
        ))
    })?;
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
