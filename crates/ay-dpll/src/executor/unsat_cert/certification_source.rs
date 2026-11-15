// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Final binding of authenticated theorem sources to publication scopes.

use super::*;

/// Fully authenticated theorem selected by the common UNSAT mint.
pub(super) enum CertificationSource {
    StrictProof,
    StrictNativeBvLiaBundle(PreparedStrictNativeBvLiaBundle),
    StrictNativeNraSosBundle(PreparedStrictNativeNraSosBundle),
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
    DischargedTrust(crate::executor::UnsatCorroboration),
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
        // The reconstruction pipeline sets this bit only after deciding that
        // the retained native proof has no authenticated authored-scope
        // presentation. Replaying that hidden proof can still establish
        // internal truth for best-effort and bare self-check solves, but it
        // must not mint the `StrictProof` presentation token when the caller
        // explicitly promised an artifact or proof checking. Keep this guard
        // aligned with the independent-sidecar presentation policy: retention
        // is a memory knob and must not change a no-artifact verdict merely
        // because the internally strict proof cannot be rendered.
        if self.last_unsat_proof_reconstruction_suppressed
            && self.independent_sidecar_blocked_by_presentation()
        {
            return Err(StrictProofPresentationFailure::Missing);
        }
        self.last_proof.as_ref().map_or_else(
            || Err(StrictProofPresentationFailure::Missing),
            |proof| {
                self.check_proof_strict_with_datatypes(proof)
                    .map(|_| ())
                    .map_err(StrictProofPresentationFailure::Rejected)
            },
        )
    }

    /// #certify-before-presentation fallback. When the proof the funnel is
    /// about to certify is a derivation kept behind a presentation bound
    /// (`last_proof_surface_withheld`) and that derivation cannot be certified
    /// — the strict checker rejects it outright (an `assume` outside the
    /// obligation), or the trust discharge rejects one of its non-trust steps
    /// (no empty clause) — revert it to the one-line `(cl)` poison the bound
    /// used to install, with the document un-withheld, i.e. to exactly the
    /// state that route produced before. The verdict is then admitted, or
    /// not, by the same discharge it always was, under the same
    /// `discharged-trust` label; nothing stronger is ever claimed for it.
    ///
    /// Measured on the D7 list (2026-10-02): 2 of the 62 rewrite-site files
    /// carry a kept derivation rejected this way — AUFDTLIRA spark
    /// `N624-020 perm_rem sort.adb_72_52` and UFDTNIRA spark `R509-011
    /// higher_order`, each with a reachable `assume` of a term outside the
    /// supplied problem obligation. Without the revert both correct `unsat`s
    /// published `unknown`, here and again in the step-(4) twin screen; the
    /// poison had been hiding the defective derivation in BOTH places, which
    /// is a producer defect this records rather than repairs. The probe line
    /// names it.
    ///
    /// Returns whether a revert happened.
    pub(super) fn revert_withheld_derivation_to_poison(
        &mut self,
        why: &dyn std::fmt::Display,
    ) -> bool {
        if self.last_proof_surface_withheld.is_none() {
            return false;
        }
        probe_cert_reject(|| {
            format!(
                "withheld-surface derivation REJECTED ({why}); reverted to the (cl) poison \
                 the presentation bound installed before #certify-before-presentation"
            )
        });
        let mut poisoned = ay_core::Proof::new();
        poisoned.add_rule_step(
            ay_core::AletheRule::Trust,
            Vec::new(),
            Vec::new(),
            Vec::new(),
        );
        self.last_proof = Some(poisoned);
        self.last_unsat_proof_reconstruction_suppressed = false;
        self.last_proof_surface_withheld = None;
        self.last_proof_term_overrides = None;
        self.last_proof_quality = None;
        self.proof_check_result = None;
        self.clear_finite_enum_proof_state();
        true
    }

    /// Bind a selected theorem to the freshly authenticated publication scope.
    pub(super) fn bind_unsat_certification_source(
        &mut self,
        source: CertificationSource,
        scope: AuthenticatedUnsatScope,
    ) -> Result<UnsatCertificate, UnsatCertificationError> {
        let kind = match source {
            CertificationSource::StrictProof => UnsatCertificateKind::StrictProof(scope),
            CertificationSource::StrictNativeNraSosBundle(prepared) => {
                let checked = prepared.bind(scope, self).ok_or_else(|| {
                    UnsatCertificationError::StrictProofRejected {
                        reason:
                            "strict native SOS bundle became stale or stopped before token mint"
                                .to_string(),
                    }
                })?;
                UnsatCertificateKind::StrictNativeNraSosBundle(checked)
            }
            CertificationSource::StrictNativeBvLiaBundle(prepared) => {
                let checked = prepared.bind(scope, self).ok_or_else(|| {
                    UnsatCertificationError::StrictProofRejected {
                        reason: "strict native BV/LIA bundle became stale before token mint"
                            .to_string(),
                    }
                })?;
                UnsatCertificateKind::StrictNativeBvLiaBundle(checked)
            }
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
            CertificationSource::DischargedTrust(corroboration) => {
                UnsatCertificateKind::DischargedTrust(scope, corroboration)
            }
        };
        Ok(UnsatCertificate(kind))
    }
}
