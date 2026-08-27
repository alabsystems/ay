// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

fn publish_owned_dimacs_proof_state(
    state: &mut OwnedDimacsProof,
    resolved: &Path,
) -> io::Result<()> {
    state.descriptor.sync_all()?;
    let descriptor_label = state.staging_path.as_deref().unwrap_or(resolved);
    let descriptor_identity = match state.location {
        OwnedDimacsProofLocation::Anonymous => {
            regular_file_identity(&state.descriptor, descriptor_label)?
        }
        _ => regular_single_link_identity(&state.descriptor, descriptor_label)?,
    };
    if descriptor_identity != state.identity {
        return Err(io::Error::other(
            "DIMACS proof descriptor identity changed before publication",
        ));
    }
    match state.location {
        OwnedDimacsProofLocation::Anonymous => {
            #[cfg(target_os = "linux")]
            {
                if let Err(error) = publish_dimacs_descriptor_noreplace(&state.descriptor, resolved)
                {
                    return Err(if error.kind() == io::ErrorKind::AlreadyExists {
                        preexisting_dimacs_proof_error(resolved, Some(&error))
                    } else {
                        error
                    });
                }
                state.location = OwnedDimacsProofLocation::Public;
            }
            #[cfg(not(target_os = "linux"))]
            return Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "anonymous DIMACS proof publication is not supported on this platform",
            ));
        }
        OwnedDimacsProofLocation::Staged => {
            let staging_path = state
                .staging_path
                .clone()
                .ok_or_else(|| io::Error::other("named DIMACS proof staging path is missing"))?;
            #[cfg(any(target_os = "linux", target_os = "macos", windows))]
            if let Err(error) = rename_dimacs_noreplace(&staging_path, resolved) {
                return Err(if error.kind() == io::ErrorKind::AlreadyExists {
                    preexisting_dimacs_proof_error(resolved, Some(&error))
                } else {
                    error
                });
            }
            #[cfg(not(any(target_os = "linux", target_os = "macos", windows)))]
            return Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "descriptor-authenticated DIMACS proof publication is not supported on this platform",
            ));
            state.location = OwnedDimacsProofLocation::Public;
            state.staging_path = None;
        }
        OwnedDimacsProofLocation::Public => {}
        OwnedDimacsProofLocation::Removed => {
            return Err(io::Error::other(
                "DIMACS proof generation was removed before publication",
            ));
        }
    }
    Ok(())
}

fn authenticate_published_dimacs_proof(
    state: &OwnedDimacsProof,
    resolved: &Path,
) -> io::Result<PublishedDimacsProof> {
    let mut visible = open_dimacs_regular_file(resolved)?;
    if regular_single_link_identity(&visible, resolved)? != state.identity {
        return Err(io::Error::other(format!(
            "DIMACS proof path '{}' was replaced before publication",
            resolved.display()
        )));
    }
    let before_len = visible.metadata()?.len();
    let (len, sha256) = hash_file(&mut visible)?;
    let after_metadata = visible.metadata()?;
    if ProofFileIdentity::from_file(&visible)? != state.identity
        || before_len != len
        || after_metadata.len() != len
    {
        return Err(io::Error::other(format!(
            "DIMACS proof output '{}' changed while it was sealed",
            resolved.display()
        )));
    }
    Ok(PublishedDimacsProof {
        identity: state.identity,
        len,
        sha256,
    })
}

fn seal_owned_dimacs_proof_body(path: &str) -> io::Result<PublishedDimacsProof> {
    let resolved = resolved_dimacs_proof_path(path)?;
    let mut owned = owned_dimacs_proofs()
        .lock()
        .map_err(|_| dimacs_proof_registry_error())?;
    let state = owned.get_mut(&resolved).ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::NotFound,
            format!(
                "no proof output owned by this run exists at '{}'",
                resolved.display()
            ),
        )
    })?;
    if state.write_failed.load(Ordering::Acquire) {
        return Err(io::Error::new(
            io::ErrorKind::WriteZero,
            format!(
                "DIMACS proof output '{}' had an earlier optional writer failure",
                resolved.display()
            ),
        ));
    }
    if let Some(published) = state.published {
        return Ok(published);
    }
    publish_owned_dimacs_proof_state(state, &resolved)?;
    let published = authenticate_published_dimacs_proof(state, &resolved)?;
    #[cfg(unix)]
    if let Some(parent) = resolved.parent() {
        File::open(parent)?.sync_all()?;
    }
    state.published = Some(published);
    Ok(published)
}
