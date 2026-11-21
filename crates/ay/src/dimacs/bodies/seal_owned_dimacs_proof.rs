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
    // A fast-publication proof is published under its writer's digest, so
    // nothing may have grown or shrunk it since: fail before the name exists.
    if let Some(streamed) = state.custody.streamed_digest() {
        let len = state.descriptor.metadata()?.len();
        if len != streamed.len {
            return Err(io::Error::other(format!(
                "DIMACS proof output '{}' holds {len} bytes but its writer wrote {}; it is not published",
                resolved.display(),
                streamed.len
            )));
        }
    }
    match state.location {
        OwnedDimacsProofLocation::Anonymous => {
            #[cfg(target_os = "linux")]
            {
                state.custody.begin_publication()?;
                let linked = publish_dimacs_descriptor_noreplace(&state.descriptor, resolved);
                state.custody.end_publication(linked.is_ok());
                if let Err(error) = linked {
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
            {
                state.custody.begin_publication()?;
                let renamed = rename_dimacs_noreplace(&staging_path, resolved);
                state.custody.end_publication(renamed.is_ok());
                if let Err(error) = renamed {
                    return Err(if error.kind() == io::ErrorKind::AlreadyExists {
                        preexisting_dimacs_proof_error(resolved, Some(&error))
                    } else {
                        error
                    });
                }
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
    // The fast path: the writer hashed every byte as it wrote it, so the name
    // is bound to that digest without reading 2.73 GB back (166e1e5a).
    if let Some(streamed) = state.custody.streamed_digest() {
        if visible.metadata()?.len() != streamed.len {
            return Err(io::Error::other(format!(
                "DIMACS proof output '{}' changed while it was sealed",
                resolved.display()
            )));
        }
        return Ok(PublishedDimacsProof {
            identity: state.identity,
            len: streamed.len,
            sha256: streamed.sha256,
        });
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
    // Fail fast, before the fsync: the authoritative check is the custody
    // compare-and-swap immediately before the rename or link.
    if state.custody.is_abandoned() {
        return Err(io::Error::other(format!(
            "DIMACS proof output '{}' was abandoned by an unanswered exit and is not published",
            resolved.display()
        )));
    }
    publish_owned_dimacs_proof_state(state, &resolved)?;
    let published = authenticate_published_dimacs_proof(state, &resolved)?;
    // The label written at creation now records the published bytes' sha256,
    // which is what lets a proof store count it again later. A proof whose
    // label cannot be completed is still this run's proof; it just never
    // counts for a later one.
    if let Err(error) =
        ay::proof_store::seal_label(&state.descriptor, &ay::proof_store::hex(&published.sha256))
    {
        safe_eprintln!(
            "c warning: the label of {} records no proof sha256: {error}",
            resolved.display()
        );
    }
    #[cfg(unix)]
    if let Some(parent) = resolved.parent() {
        File::open(parent)?.sync_all()?;
    }
    state.published = Some(published);
    Ok(published)
}
