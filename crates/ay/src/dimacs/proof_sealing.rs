// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn seal_owned_dimacs_proof(path: &str) -> io::Result<PublishedDimacsProof> {
    seal_owned_dimacs_proof_body(path)
}

fn published_dimacs_proof(path: &str) -> io::Result<PublishedDimacsProof> {
    let resolved = resolved_dimacs_proof_path(path)?;
    let owned = owned_dimacs_proofs()
        .lock()
        .map_err(|_| dimacs_proof_registry_error())?;
    owned
        .get(&resolved)
        .and_then(|state| state.published)
        .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::NotFound,
                format!(
                    "proof output '{}' was not emitted and sealed by this run",
                    resolved.display()
                ),
            )
        })
}

fn validate_published_dimacs_proof(path: &str) -> io::Result<PublishedDimacsProof> {
    let resolved = resolved_dimacs_proof_path(path)?;
    let published = published_dimacs_proof(path)?;
    let mut file = open_dimacs_regular_file(&resolved)?;
    if regular_single_link_identity(&file, &resolved)? != published.identity {
        return Err(io::Error::other(format!(
            "DIMACS proof path '{}' was replaced after publication",
            resolved.display()
        )));
    }
    let before_len = file.metadata()?.len();
    let (len, sha256) = hash_file(&mut file)?;
    let after = file.metadata()?;
    if ProofFileIdentity::from_file(&file)? != published.identity
        || before_len != published.len
        || len != published.len
        || after.len() != published.len
        || sha256 != published.sha256
    {
        return Err(io::Error::other(format!(
            "DIMACS proof output '{}' changed after publication",
            resolved.display()
        )));
    }
    Ok(published)
}

fn retain_published_dimacs_proof(
    path: &str,
    published: PublishedDimacsProof,
    binary: bool,
) -> io::Result<RetainedDimacsPublication> {
    let resolved = resolved_dimacs_proof_path(path)?;
    let descriptor = {
        let owned = owned_dimacs_proofs()
            .lock()
            .map_err(|_| dimacs_proof_registry_error())?;
        let state = owned.get(&resolved).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::NotFound,
                "same-run DIMACS proof ownership disappeared before authorization",
            )
        })?;
        if state.published != Some(published) {
            return Err(io::Error::other(
                "same-run DIMACS proof seal changed before authorization",
            ));
        }
        state.descriptor.try_clone()?
    };
    RetainedDimacsPublication::capture(
        descriptor,
        resolved,
        "DIMACS proof",
        Some(published),
        DimacsPublicationInvalidation::Proof { binary },
    )
}

/// Descriptor-backed publications that must remain authoritative until UNSAT
/// is visible.
///
/// The transaction retains the exact proof, status marker, and artifact
/// descriptors together with the policy that decides whether late validation
/// failure is fatal. Unless `commit` settles the transaction after verdict
/// output, `Drop` invalidates those retained publications through their exact
/// descriptors so a replaced pathname is never removed.
struct DimacsUnsatPublicationTransaction {
    proof: RetainedDimacsPublication,
    status: Option<RetainedDimacsPublication>,
    artifact: Option<RetainedDimacsPublication>,
    requirement: DimacsProofRequirement,
    invalidate_on_drop: bool,
}

impl DimacsUnsatPublicationTransaction {
    fn new(
        proof: RetainedDimacsPublication,
        artifact: Option<RetainedDimacsPublication>,
        requirement: DimacsProofRequirement,
    ) -> Self {
        Self {
            proof,
            status: None,
            artifact,
            requirement,
            invalidate_on_drop: true,
        }
    }

    fn validate(&mut self) -> io::Result<()> {
        self.proof.validate()?;
        if let Some(status) = &mut self.status {
            status.validate()?;
        }
        if let Some(artifact) = &mut self.artifact {
            artifact.validate()?;
        }
        Ok(())
    }

    fn invalidate_exact(&mut self) -> String {
        let mut errors = Vec::new();
        if let Some(status) = &self.status {
            if let Err(error) = status.invalidate_exact() {
                errors.push(format!("status marker: {error}"));
            }
        }
        if let Some(artifact) = &self.artifact {
            if let Err(error) = artifact.invalidate_exact() {
                errors.push(format!("proof artifact: {error}"));
            }
        }
        if let Err(error) = self.proof.invalidate_exact() {
            errors.push(format!("proof: {error}"));
        }
        self.invalidate_on_drop = false;
        if errors.is_empty() {
            "; exact same-run DIMACS publications were descriptor-invalidated".to_string()
        } else {
            format!(
                "; WARNING: retained DIMACS publication invalidation also failed ({})",
                errors.join("; ")
            )
        }
    }

    /// Settle the transaction after the verdict becomes visible.
    ///
    /// Durable publications may then outlive the retained descriptors instead
    /// of being invalidated by `Drop`.
    fn commit(&mut self) {
        self.invalidate_on_drop = false;
    }
}

impl Drop for DimacsUnsatPublicationTransaction {
    fn drop(&mut self) {
        // Any path that loses the authorization token before verdict commit
        // must invalidate the exact publications still held by this run.
        if self.invalidate_on_drop {
            let _ = self.invalidate_exact();
        }
    }
}

/// Authorization to expose a DIMACS UNSAT verdict after its mandatory gates.
///
/// A populated transaction retains descriptor authority over every published
/// sidecar until the verdict is committed. An empty transaction is also a
/// settled authorization: all mandatory verdict checks completed, but either
/// no artifacts were requested or an optional publication was already
/// invalidated and abandoned.
struct AuthorizedDimacsUnsatPublication {
    publication: Option<DimacsUnsatPublicationTransaction>,
    temp_proof_path: Option<String>,
}

/// A late publication failure together with the policy needed to resolve it.
#[derive(Debug)]
struct DimacsUnsatPublicationValidationError {
    requirement: DimacsProofRequirement,
    reason: String,
}

impl AuthorizedDimacsUnsatPublication {
    /// Authorize the verdict with no live publication obligation remaining.
    ///
    /// Callers may still publish UNSAT: every proof/publication obligation
    /// required by the current policy is settled, and any optional failed
    /// artifacts were invalidated before construction.
    fn without_artifacts() -> Self {
        Self {
            publication: None,
            temp_proof_path: None,
        }
    }

    /// Revalidate every retained descriptor immediately before verdict output.
    ///
    /// Failure exact-invalidates and consumes the transaction, then reports
    /// both the publication requirement and the reason to the output gate.
    fn validate_before_verdict(&mut self) -> Result<(), DimacsUnsatPublicationValidationError> {
        let Some(publication) = &mut self.publication else {
            return Ok(());
        };
        if let Err(error) = publication.validate() {
            let requirement = publication.requirement;
            let invalidation = publication.invalidate_exact();
            let failure = Err(DimacsUnsatPublicationValidationError {
                requirement,
                reason: format!(
                    "same-run DIMACS publication lost namespace authority before UNSAT: {error}{invalidation}"
                ),
            });
            // A failed publication no longer participates in later output
            // gates. Its exact members have already been invalidated; an
            // optional failure would otherwise repeat the same warning, while
            // a required failure causes the caller to exit.
            self.publication = None;
            return failure;
        }
        Ok(())
    }

    /// Settle publication ownership immediately after the verdict is visible.
    ///
    /// Temporary proofs are removed and exact-invalidated while their retained
    /// descriptor is still available. Durable artifacts are committed so
    /// dropping the token preserves them.
    fn commit_after_verdict(&mut self) {
        if let Some(path) = self.temp_proof_path.take() {
            let cleanup = remove_owned_dimacs_proof(&path);
            let proof_invalidation = self
                .publication
                .as_ref()
                .map(|publication| publication.proof.invalidate_exact())
                .transpose();
            if let Err(error) = cleanup {
                safe_eprintln!(
                    "c Warning: failed to settle verified temporary DIMACS proof {path} after verdict output: {error}"
                );
            }
            if let Err(error) = proof_invalidation {
                let fallback = self.publication.as_mut().map_or_else(
                    String::new,
                    DimacsUnsatPublicationTransaction::invalidate_exact,
                );
                safe_eprintln!(
                    "c Warning: failed to exact-invalidate verified temporary DIMACS proof {path} after verdict output: {error}{fallback}"
                );
            }
        }
        if let Some(publication) = &mut self.publication {
            publication.commit();
        }
    }
}

fn validate_dimacs_unsat_publication_before_verdict(
    authority: &mut AuthorizedDimacsUnsatPublication,
) {
    match authority.validate_before_verdict() {
        Ok(()) => {}
        Err(DimacsUnsatPublicationValidationError {
            requirement: DimacsProofRequirement::Optional,
            reason,
        }) => safe_eprintln!(
            "c Warning: optional synthesized DIMACS publication changed before verdict ({reason}); UNSAT verdict remains authoritative"
        ),
        Err(DimacsUnsatPublicationValidationError {
            requirement: DimacsProofRequirement::Required,
            reason,
        }) => fail_dimacs_certification_or_exit(&reason),
    }
}

pub(crate) fn read_published_dimacs_proof(
    path: &str,
    expected_sha256: Sha256Digest,
) -> io::Result<Vec<u8>> {
    let resolved = resolved_dimacs_proof_path(path)?;
    let published = validate_published_dimacs_proof(path)?;
    if published.sha256 != expected_sha256 {
        return Err(io::Error::other("DIMACS proof seal digest mismatch"));
    }
    let mut file = open_dimacs_regular_file(&resolved)?;
    if regular_single_link_identity(&file, &resolved)? != published.identity {
        return Err(io::Error::other(
            "DIMACS proof changed before verifier read",
        ));
    }
    let capacity = usize::try_from(published.len)
        .map_err(|_| io::Error::other("DIMACS proof is too large to verify in memory"))?;
    let mut bytes = Vec::with_capacity(capacity);
    file.read_to_end(&mut bytes)?;
    let after = file.metadata()?;
    if ProofFileIdentity::from_file(&file)? != published.identity
        || after.len() != published.len
        || bytes.len() as u64 != published.len
        || sha256_digest(&bytes) != expected_sha256
    {
        return Err(io::Error::other(format!(
            "DIMACS proof output '{}' changed after publication",
            resolved.display()
        )));
    }
    Ok(bytes)
}
