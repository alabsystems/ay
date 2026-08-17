// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Final binding of authenticated theorem sources to publication scopes.

use super::*;

/// Fully authenticated theorem selected by the common UNSAT mint.
pub(super) enum CertificationSource {
    StrictProof,
    CheckedSatRefutation,
    PendingNestedArray(PendingNestedArrayBoolBvUnsat),
    CheckedBoolBv {
        evidence: AuthenticatedBoolBvUnsatQuery,
        exact_roots: Box<[TermId]>,
    },
    CheckedBvLia {
        evidence: AuthenticatedBvLiaUnsatQuery,
        exact_roots: Box<[TermId]>,
    },
    DischargedTrust,
}

pub(super) enum StrictProofPresentationFailure {
    Missing,
    Rejected(ay_proof::ProofCheckError),
}

impl Executor {
    pub(super) fn check_strict_unsat_presentation(
        &self,
    ) -> Result<(), StrictProofPresentationFailure> {
        self.last_proof.as_ref().map_or_else(
            || Err(StrictProofPresentationFailure::Missing),
            |proof| {
                self.check_proof_strict_with_datatypes(proof)
                    .map(|_| ())
                    .map_err(StrictProofPresentationFailure::Rejected)
            },
        )
    }

    /// Bind a selected theorem to the freshly authenticated publication scope.
    pub(super) fn bind_unsat_certification_source(
        &mut self,
        source: CertificationSource,
        scope: AuthenticatedUnsatScope,
    ) -> Result<UnsatCertificate, UnsatCertificationError> {
        let kind = match source {
            CertificationSource::StrictProof => UnsatCertificateKind::StrictProof(scope),
            CertificationSource::CheckedSatRefutation => {
                let checked = self.last_checked_sat_refutation.take().ok_or_else(|| {
                    UnsatCertificationError::StrictProofRejected {
                        reason: "checked SAT-refutation authority disappeared before token mint"
                            .to_string(),
                    }
                })?;
                UnsatCertificateKind::CheckedSatRefutation { checked, scope }
            }
            CertificationSource::PendingNestedArray(pending) => {
                let checked = pending.bind(scope, self).ok_or_else(|| {
                    UnsatCertificationError::StrictProofRejected {
                        reason: "pending nested finite-array Bool/BV authority became stale before token mint"
                            .to_string(),
                    }
                })?;
                UnsatCertificateKind::CheckedBoolBv(checked)
            }
            CertificationSource::CheckedBoolBv {
                evidence,
                exact_roots,
            } => {
                let checked =
                    CheckedBoolBvUnsat::bind(scope, evidence, &self.ctx.terms, &exact_roots)
                        .ok_or_else(|| UnsatCertificationError::StrictProofRejected {
                            reason: "source-level Bool/BV authority became stale before token mint"
                                .to_string(),
                        })?;
                UnsatCertificateKind::CheckedBoolBv(checked)
            }
            CertificationSource::CheckedBvLia {
                evidence,
                exact_roots,
            } => {
                let checked =
                    CheckedBvLiaUnsat::bind(scope, evidence, &self.ctx.terms, &exact_roots)
                        .ok_or_else(|| UnsatCertificationError::StrictProofRejected {
                            reason: "source-level BV/LIA authority became stale before token mint"
                                .to_string(),
                        })?;
                UnsatCertificateKind::CheckedBvLia(checked)
            }
            CertificationSource::DischargedTrust => UnsatCertificateKind::DischargedTrust(scope),
        };
        Ok(UnsatCertificate(kind))
    }
}
