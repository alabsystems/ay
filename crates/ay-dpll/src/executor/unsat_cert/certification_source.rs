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
    /// #bitblast-original-clause-authority — an abstraction-backed but fully
    /// re-checked refutation. Kept distinct from `CheckedBoolBv` so the exact
    /// class never carries an abstracted theorem.
    CheckedUfLeafBoolBv {
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
    /// # Measured: do NOT merge this with the collecting replay (#cert-accounting)
    ///
    /// The obvious refactor is to fold this strict replay and the *collecting*
    /// replay in `discharge_trust_steps_for_certification`
    /// (`ay_proof::check_proof_collecting_trust_with_typed_context`) into one
    /// pass over `last_proof`, since on the trust-rejection path both walk the
    /// same proof with the same datatype/selector/premise context. Two reasons
    /// not to, recorded here so the idea is re-litigated with the evidence:
    ///
    /// 1. IT IS NOT A PURE DE-DUPLICATION. The two calls enter `ay_proof` by
    ///    different doors with different acceptance semantics — this one
    ///    REJECTS trust steps, the other DEFERS them — and this one has a
    ///    finite-enum branch (`check_bounded_finite_enum_proof`) the collecting
    ///    checker has no counterpart for. Replacing "strict rejected it" with
    ///    "the collecting checker deferred something" changes what a MANDATORY
    ///    UNSAT gate accepts, which is the one direction that must not be
    ///    traded for latency.
    /// 2. IT IS WORTH AT MOST ~1.6% OF THE BUDGET IT WAS PROPOSED TO SAVE.
    ///    On the #4751 benchmark, `ay_dpll::CertificationAccounting` measures
    ///    5.59 s of certificate minting across 1019 mints — of which 5.26 s
    ///    (94.1%) is 94 fresh-`Executor` whole-problem corroboration re-solves.
    ///    Everything else in every mint, both replays included, is the
    ///    remaining 0.33 s of a 20 s budget. A controlled A/B has separately
    ///    refuted minting as the critical path at all: removing all of it left
    ///    the benchmark failing at 27.9 s.
    ///
    /// Re-run the attribution before revisiting:
    /// `cargo test --release -p ay-chc --test cert_accounting_dillig12_m_4751
    /// -- --ignored --nocapture`.
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
            CertificationSource::CheckedUfLeafBoolBv {
                evidence,
                exact_roots,
            } => {
                let checked =
                    CheckedUfLeafBoolBvUnsat::bind(scope, evidence, &self.ctx.terms, &exact_roots)
                        .ok_or_else(|| UnsatCertificationError::StrictProofRejected {
                            reason: "source-level Bool/BV+UF-leaf authority became stale before \
                                     token mint"
                                .to_string(),
                        })?;
                UnsatCertificateKind::CheckedUfLeafBoolBv(checked)
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
