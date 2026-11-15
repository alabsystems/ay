// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Removing the names of a proof generation or a status transaction that an
// exit settles (proof_custody.rs, status_custody.rs).

/// Remove this run's private staging name. The name is reserved with `O_EXCL`
/// under this PID and a nonce that is never reused, so authenticating the
/// visible inode is the whole guarantee, as in the exit sweep.
#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn remove_private_dimacs_custody_name(stage: &Path, identity: ProofFileIdentity) -> io::Result<()> {
    let visible = match open_dimacs_regular_file(stage) {
        Ok(visible) => visible,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(error),
    };
    let visible_identity = regular_file_identity(&visible, stage)?;
    drop(visible);
    if visible_identity != identity {
        return Err(io::Error::other(format!(
            "DIMACS proof staging path '{}' no longer names this run's generation; it was preserved",
            stage.display()
        )));
    }
    match std::fs::remove_file(stage) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
        removed => removed,
    }
}

/// Remove this run's proof from its public target, where another process may
/// have put an object of its own. The inode is first moved into a private
/// directory, where nothing else can replace it, and only removed if it is
/// still this run's; anything else is put back. Nothing of this run is left,
/// the private directory included.
#[cfg(any(target_os = "linux", target_os = "macos", windows))]
fn remove_public_dimacs_custody_name(target: &Path, identity: ProofFileIdentity) -> io::Result<()> {
    // Most unanswered runs never published: settle that without a quarantine.
    let names_this_run = match open_dimacs_regular_file(target) {
        Ok(visible) => regular_file_identity(&visible, target).ok() == Some(identity),
        Err(error) if error.kind() == io::ErrorKind::NotFound => false,
        // A symlink, a directory or an unreadable object is not this run's.
        Err(_) => false,
    };
    if !names_this_run {
        return Ok(());
    }
    let (directory, _) = create_private_dimacs_staging_directory(target)?;
    let quarantined = directory.join("discard");
    let moved = (|| -> io::Result<()> {
        match rename_dimacs_noreplace(target, &quarantined) {
            Ok(()) => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(()),
            Err(error) => return Err(error),
        }
        let still_this_run = open_dimacs_regular_file(&quarantined)
            .and_then(|moved| regular_file_identity(&moved, &quarantined))
            .ok()
            == Some(identity);
        if still_this_run {
            std::fs::remove_file(&quarantined)
        } else {
            // Replaced between the check and the move: restore the stranger.
            rename_dimacs_noreplace(&quarantined, target)
        }
    })();
    moved.and(std::fs::remove_dir(&directory))
}
