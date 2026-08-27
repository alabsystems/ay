// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

enum SynthesizedProofStatus {
    MarkStale,
    Preserve,
}

/// Whether publication loss may leave the already-solved verdict authoritative.
///
/// This policy stays attached to the retained-descriptor transaction so a late
/// validation failure cannot lose the required-versus-optional distinction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DimacsProofRequirement {
    Optional,
    Required,
}

impl DimacsProofRequirement {
    fn from_proof(proof: &ProofConfig) -> Self {
        if synthesized_default_dimacs_proof_is_optional(proof) {
            Self::Optional
        } else {
            Self::Required
        }
    }

    fn is_optional(self) -> bool {
        matches!(self, Self::Optional)
    }
}

fn abandon_dimacs_authorization(
    proof: &ProofConfig,
    requirement: DimacsProofRequirement,
    mut reason: String,
    status: SynthesizedProofStatus,
) -> AuthorizedDimacsUnsatPublication {
    if proof.synthesized_default && matches!(status, SynthesizedProofStatus::MarkStale) {
        mark_synthesized_default_dimacs_proof_stale(proof);
    }
    if let Err(cleanup_error) = remove_owned_dimacs_proof(&proof.path) {
        reason.push_str(&format!(
            "; failed to settle only AY's authenticated proof generation: {cleanup_error}"
        ));
    }
    if requirement.is_optional() {
        safe_eprintln!(
            "c Warning: optional synthesized DIMACS proof {} was not published: {reason}; solver verdict remains authoritative",
            proof.path
        );
        AuthorizedDimacsUnsatPublication::without_artifacts()
    } else {
        fail_dimacs_certification_or_exit(&reason)
    }
}

fn retain_authorized_dimacs_proof(
    proof: &ProofConfig,
    requirement: DimacsProofRequirement,
) -> Result<(PublishedDimacsProof, RetainedDimacsPublication), Box<AuthorizedDimacsUnsatPublication>>
{
    let published = published_dimacs_proof(&proof.path).map_err(|error| {
        Box::new(abandon_dimacs_authorization(
            proof,
            requirement,
            format!("same-run proof publication failed: {error}"),
            SynthesizedProofStatus::MarkStale,
        ))
    })?;
    let retained =
        retain_published_dimacs_proof(&proof.path, published, proof.binary).map_err(|error| {
            Box::new(abandon_dimacs_authorization(
                proof,
                requirement,
                format!(
                    "same-run proof publication could not retain descriptor authority: {error}"
                ),
                SynthesizedProofStatus::MarkStale,
            ))
        })?;
    Ok((published, retained))
}

fn verify_authorized_dimacs_proof(
    source: DimacsInputSource<'_>,
    proof: &ProofConfig,
    requirement: DimacsProofRequirement,
    publication: &mut DimacsUnsatPublicationTransaction,
) -> Result<(), Box<AuthorizedDimacsUnsatPublication>> {
    if !verify_unsat_proof_from_source(source, Some(proof)) {
        let mut reason = "independent DIMACS proof re-check did not accept".to_string();
        reason.push_str(&publication.invalidate_exact());
        return Err(Box::new(abandon_dimacs_authorization(
            proof,
            requirement,
            reason,
            SynthesizedProofStatus::MarkStale,
        )));
    }
    if !verify_lean_proof(Some(proof)) {
        let invalidation = publication.invalidate_exact();
        safe_eprintln!("c Error: Lean-rejected DIMACS publications were invalidated{invalidation}");
        if proof.synthesized_default {
            mark_synthesized_default_dimacs_proof_stale(proof);
        }
        if let Err(cleanup_error) = remove_owned_dimacs_proof(&proof.path) {
            safe_eprintln!(
                "c Error: failed to settle Lean-rejected DIMACS proof generation {}: {cleanup_error}",
                proof.path
            );
        }
        std::process::exit(2);
    }
    Ok(())
}

fn retain_dimacs_artifact(
    source: DimacsInputSource<'_>,
    proof: &ProofConfig,
    theory: ProofArtifactTheoryMetadata,
    published: PublishedDimacsProof,
) -> io::Result<Option<RetainedDimacsPublication>> {
    write_sealed_proof_artifact(
        source.proof_artifact_problem(),
        proof,
        theory,
        published.sha256,
    )
    .and_then(|artifact| {
        artifact
            .map(|(descriptor, path)| {
                RetainedDimacsPublication::capture(
                    descriptor,
                    path,
                    "DIMACS proof artifact",
                    None,
                    DimacsPublicationInvalidation::Empty,
                )
            })
            .transpose()
    })
}

fn complete_dimacs_authorization(
    proof: &ProofConfig,
    requirement: DimacsProofRequirement,
    published: PublishedDimacsProof,
    publication: &mut DimacsUnsatPublicationTransaction,
) -> Result<(), Box<AuthorizedDimacsUnsatPublication>> {
    if proof.synthesized_default {
        if let Err(error) =
            mark_synthesized_default_dimacs_proof_current(proof, published, publication)
        {
            let mut reason = format!(
                "same-run proof status could not retain authority for {}: {error}",
                proof.path
            );
            reason.push_str(&publication.invalidate_exact());
            return Err(Box::new(abandon_dimacs_authorization(
                proof,
                requirement,
                reason,
                SynthesizedProofStatus::Preserve,
            )));
        }
    }
    if let Err(error) = publication.validate() {
        let mut reason =
            format!("same-run DIMACS publication changed before authorization completed: {error}");
        reason.push_str(&publication.invalidate_exact());
        return Err(Box::new(abandon_dimacs_authorization(
            proof,
            requirement,
            reason,
            SynthesizedProofStatus::Preserve,
        )));
    }
    Ok(())
}

fn authorize_dimacs_unsat_artifacts_body(
    source: DimacsInputSource<'_>,
    proof_config: Option<&ProofConfig>,
    theory: ProofArtifactTheoryMetadata,
) -> AuthorizedDimacsUnsatPublication {
    enforce_required_dimacs_proof_gate(proof_config);
    let Some(proof) = proof_config else {
        if !verify_unsat_proof_from_source(source, None) {
            fail_dimacs_certification_or_exit("independent DIMACS proof re-check did not accept");
        }
        if !verify_lean_proof(None) {
            std::process::exit(2);
        }
        return AuthorizedDimacsUnsatPublication::without_artifacts();
    };
    let requirement = DimacsProofRequirement::from_proof(proof);
    let (published, retained) = match retain_authorized_dimacs_proof(proof, requirement) {
        Ok(retained) => retained,
        Err(without_artifacts) => return *without_artifacts,
    };
    let mut publication = DimacsUnsatPublicationTransaction::new(retained, None, requirement);
    if let Err(without_artifacts) =
        verify_authorized_dimacs_proof(source, proof, requirement, &mut publication)
    {
        return *without_artifacts;
    }
    match retain_dimacs_artifact(source, proof, theory, published) {
        Ok(artifact) => publication.artifact = artifact,
        Err(error) => {
            let mut reason = format!(
                "proof artifact could not retain same-run authority for {}: {error}",
                proof.path
            );
            reason.push_str(&publication.invalidate_exact());
            return abandon_dimacs_authorization(
                proof,
                requirement,
                reason,
                SynthesizedProofStatus::MarkStale,
            );
        }
    }
    if let Err(without_artifacts) =
        complete_dimacs_authorization(proof, requirement, published, &mut publication)
    {
        return *without_artifacts;
    }
    AuthorizedDimacsUnsatPublication {
        publication: Some(publication),
        temp_proof_path: proof.is_temp.then(|| proof.path.clone()),
    }
}
