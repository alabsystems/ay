// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact-query handoff for strict native Bool/BV/LIA proof bundles.

use ay_core::{Proof, TermId, TheoryLemmaKind};
use ay_proof::{
    authenticate_bv_lia_unsat_query, re_check_bundle_strict, AuthenticatedBvLiaUnsatQuery,
    SerializableProofBundle,
};

use super::*;

mod canonical;
mod resources;
use canonical::{bundle_matches_live_proof, bundle_matches_proof};

/// Move-only route identity minted by the bounded source decision lane.
///
/// The source checker initially authenticates the complete ordered public
/// query. Proof reconstruction may append terms before the common UNSAT mint,
/// so this token deliberately records an immutable-prefix stamp rather than
/// pretending that the checker's whole-arena snapshot remains current. The
/// final native bundle path re-runs the checker after constructing every proof
/// term and stores that fresh whole-snapshot evidence in the certificate.
#[derive(Debug)]
pub(in crate::executor) struct PendingBoundedBvLiaUnsat {
    authority_epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    exact_roots: Box<[TermId]>,
    source_term_prefix: TermStoreSnapshotStamp,
}

/// Strict native bundle built from a current pending exact-source theorem.
/// Binding to the common publication scope is intentionally deferred until
/// [`Executor::bind_unsat_certification_source`].
pub(in crate::executor) struct PreparedStrictNativeBvLiaBundle {
    exact_roots: Box<[TermId]>,
    proof_roots: Box<[TermId]>,
    final_evidence: AuthenticatedBvLiaUnsatQuery,
    bundle: SerializableProofBundle,
    candidate: Proof,
    quality: ay_proof::ProofQuality,
}

/// Exact-query certificate class for a native proof whose sole unsupported
/// Alethe step is the honestly rendered `BvLiaTautology` hole.
#[derive(Debug)]
pub(in crate::executor) struct StrictNativeBvLiaBundleUnsat {
    scope: AuthenticatedUnsatScope,
    exact_roots: Box<[TermId]>,
    proof_roots: Box<[TermId]>,
    final_evidence: AuthenticatedBvLiaUnsatQuery,
    bundle: SerializableProofBundle,
}

/// Persistent export identity retained after the one-shot public certificate
/// is consumed by either the native or SMT-LIB result boundary.
#[derive(Debug)]
pub(in crate::executor) struct StrictNativeBvLiaBundleState {
    authority_epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    solver_assumptions: Option<Box<[TermId]>>,
    solver_assumption_entries: Option<Box<[TermEntryStamp]>>,
    exact_roots: Box<[TermId]>,
    proof_roots: Box<[TermId]>,
    term_snapshot: TermStoreSnapshotStamp,
    bundle: SerializableProofBundle,
}

fn exact_roots_match_epoch(
    roots: &[TermId],
    epoch: &UnsatQueryEpoch,
    assumptions: &[TermId],
) -> bool {
    roots
        .iter()
        .copied()
        .eq(epoch.assertions.iter().chain(assumptions.iter()).copied())
}

fn plain_epoch_is_current(
    executor: &Executor,
    epoch: &UnsatQueryEpoch,
    assumptions: &[TermId],
) -> bool {
    epoch.is_current(executor)
        && epoch.assumptions.as_deref() == Some(assumptions)
        && epoch.declared_extension.is_empty()
        && epoch.declared_extension_entries.is_empty()
        && epoch.declared_extension_objectives.is_none()
        && epoch.declared_extension_objective_entries.is_none()
        && executor.ctx.objectives().is_empty()
        && executor
            .proof_problem_assertion_provenance
            .as_ref()
            .is_some_and(|provenance| provenance.original_problem_assertions == epoch.assertions)
}

impl PendingBoundedBvLiaUnsat {
    fn is_current_for(
        &self,
        executor: &Executor,
        epoch: &UnsatQueryEpoch,
        assumptions: &[TermId],
    ) -> bool {
        self.authority_epoch
            .is_same_epoch(&executor.query_authority_epoch)
            && self.authority_epoch.is_same_epoch(&epoch.authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && self.source_context_stamp == epoch.source_context_stamp
            && self
                .source_term_prefix
                .is_append_only_prefix_of(&executor.ctx.terms)
            && plain_epoch_is_current(executor, epoch, assumptions)
            && exact_roots_match_epoch(&self.exact_roots, epoch, assumptions)
    }
}

impl StrictNativeBvLiaBundleUnsat {
    pub(super) fn is_current(&self, executor: &Executor) -> bool {
        self.scope.is_current(executor)
            && self.scope.declared_extension.is_empty()
            && self.scope.declared_extension_objectives.is_none()
            && self.exact_roots.iter().copied().eq(self
                .scope
                .assertions
                .iter()
                .chain(self.scope.assumptions.iter())
                .copied())
            && self
                .final_evidence
                .is_current_for(&executor.ctx.terms, &self.exact_roots)
            && bundle_matches_live_proof(
                executor,
                &self.exact_roots,
                &self.proof_roots,
                &self.bundle,
            )
    }

    fn export_state(&self, executor: &Executor) -> StrictNativeBvLiaBundleState {
        StrictNativeBvLiaBundleState {
            authority_epoch: self.scope.authority_epoch.clone(),
            source_context_stamp: self.scope.source_context_stamp.clone(),
            solver_assumptions: self.scope.solver_assumptions.clone(),
            solver_assumption_entries: self.scope.solver_assumption_entries.clone(),
            exact_roots: self.exact_roots.clone(),
            proof_roots: self.proof_roots.clone(),
            term_snapshot: executor.ctx.terms.snapshot_stamp(),
            bundle: self.bundle.clone(),
        }
    }
}

impl PreparedStrictNativeBvLiaBundle {
    pub(super) fn bind(
        self,
        scope: AuthenticatedUnsatScope,
        executor: &mut Executor,
    ) -> Option<StrictNativeBvLiaBundleUnsat> {
        if !scope.is_current(executor)
            || !scope.declared_extension.is_empty()
            || scope.declared_extension_objectives.is_some()
            || !self.exact_roots.iter().copied().eq(scope
                .assertions
                .iter()
                .chain(scope.assumptions.iter())
                .copied())
            || !self
                .final_evidence
                .is_current_for(&executor.ctx.terms, &self.exact_roots)
            || !bundle_matches_proof(
                executor,
                &self.exact_roots,
                &self.proof_roots,
                &self.candidate,
                &self.bundle,
            )
        {
            return None;
        }
        let PreparedStrictNativeBvLiaBundle {
            exact_roots,
            proof_roots,
            final_evidence,
            bundle,
            candidate,
            quality,
        } = self;
        let certificate = StrictNativeBvLiaBundleUnsat {
            scope,
            exact_roots,
            proof_roots,
            final_evidence,
            bundle,
        };
        executor.commit_authenticated_plain_refutation(candidate, quality);
        if !certificate.is_current(executor) {
            executor.last_proof = None;
            executor.last_proof_quality = None;
            executor.clear_strict_native_bundle_states();
            return None;
        }
        executor.last_strict_native_bv_lia_bundle = Some(certificate.export_state(executor));
        Some(certificate)
    }
}

impl StrictNativeBvLiaBundleState {
    fn is_current_for(&self, executor: &Executor, proof: &Proof) -> bool {
        let Some(epoch) = executor.unsat_query_epoch.as_ref() else {
            return false;
        };
        let Some(assumptions) = epoch.assumptions.as_deref() else {
            return false;
        };
        self.authority_epoch
            .is_same_epoch(&executor.query_authority_epoch)
            && self.authority_epoch.is_same_epoch(&epoch.authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && self.source_context_stamp == epoch.source_context_stamp
            && self.term_snapshot == executor.ctx.terms.snapshot_stamp()
            && plain_epoch_is_current(executor, epoch, assumptions)
            && self.solver_assumptions.as_deref() == executor.last_assumptions.as_deref()
            && match (
                self.solver_assumptions.as_deref(),
                self.solver_assumption_entries.as_deref(),
            ) {
                (Some(roots), Some(entries)) => {
                    entries.len() == roots.len()
                        && entries.iter().copied().map(Some).eq(roots
                            .iter()
                            .map(|&root| executor.ctx.terms.entry_stamp(root)))
                }
                (None, None) => true,
                _ => false,
            }
            && exact_roots_match_epoch(&self.exact_roots, epoch, assumptions)
            && proof.named_steps.is_empty()
            && proof.steps == self.bundle.steps
            && bundle_matches_live_proof(
                executor,
                &self.exact_roots,
                &self.proof_roots,
                &self.bundle,
            )
    }
}

impl Executor {
    /// Re-authenticate the immutable public epoch after the bounded decision
    /// route succeeds. The route may have solved a transient working set;
    /// only this exact epoch-derived check is allowed to mint the pending
    /// strict-native handoff.
    pub(in crate::executor) fn authenticate_and_prepare_pending_bounded_bv_lia_unsat(
        &mut self,
        assumptions: &[TermId],
    ) -> Result<bool, UnsatCertificationError> {
        self.pending_bounded_bv_lia_unsat = None;
        let exact_roots = {
            let Some(epoch) = self.unsat_query_epoch.as_ref() else {
                return Ok(false);
            };
            if !plain_epoch_is_current(self, epoch, assumptions) {
                return Ok(false);
            }
            let Some(root_count) = epoch.assertions.len().checked_add(assumptions.len()) else {
                return Ok(false);
            };
            if root_count > ay_proof::MAX_BV_LIA_QUERY_ROOTS {
                return Ok(false);
            }
            let mut roots = Vec::new();
            if roots.try_reserve_exact(root_count).is_err() {
                return Ok(false);
            }
            roots.extend_from_slice(&epoch.assertions);
            roots.extend_from_slice(assumptions);
            roots
        };
        if self.exact_roots_hold_unauthored_false(&exact_roots) {
            return Ok(false);
        }
        if self.should_abort_theory_loop() {
            return Ok(false);
        }
        let evidence = match authenticate_bv_lia_unsat_query(
            &self.ctx.terms,
            &exact_roots,
            self.current_solve_deadline(),
        ) {
            Ok(evidence) => evidence,
            Err(error) if error.is_capability_decline() => return Ok(false),
            Err(error) => {
                return Err(UnsatCertificationError::StrictProofRejected {
                    reason: format!(
                        "exact public BV/LIA source rejected a working-set refutation: {error}"
                    ),
                });
            }
        };
        if self.should_abort_theory_loop() {
            return Ok(false);
        }
        if !self.prepare_pending_bounded_bv_lia_unsat(exact_roots, evidence, assumptions) {
            return Err(UnsatCertificationError::StrictProofRejected {
                reason:
                    "exact public BV/LIA source authority changed while sealing its route token"
                        .to_string(),
            });
        }
        Ok(true)
    }

    /// Seal a move-only route token immediately after the bounded source lane
    /// authenticates the full exact ordered public query.
    pub(in crate::executor) fn prepare_pending_bounded_bv_lia_unsat(
        &mut self,
        exact_roots: Vec<TermId>,
        evidence: AuthenticatedBvLiaUnsatQuery,
        assumptions: &[TermId],
    ) -> bool {
        self.pending_bounded_bv_lia_unsat = None;
        let Some(epoch) = self.unsat_query_epoch.as_ref() else {
            return false;
        };
        if !plain_epoch_is_current(self, epoch, assumptions)
            || !exact_roots_match_epoch(&exact_roots, epoch, assumptions)
            || !evidence.is_current_for(&self.ctx.terms, &exact_roots)
        {
            return false;
        }
        let pending = PendingBoundedBvLiaUnsat {
            authority_epoch: epoch.authority_epoch.clone(),
            source_context_stamp: epoch.source_context_stamp.clone(),
            exact_roots: exact_roots.into_boxed_slice(),
            source_term_prefix: self.ctx.terms.snapshot_stamp(),
        };
        if !pending.is_current_for(self, epoch, assumptions) {
            return false;
        }
        self.pending_bounded_bv_lia_unsat = Some(pending);
        true
    }

    pub(super) fn pending_bounded_bv_lia_unsat_is_current(
        &self,
        pending: &PendingBoundedBvLiaUnsat,
        assumptions: &[TermId],
    ) -> bool {
        self.unsat_query_epoch
            .as_ref()
            .is_some_and(|epoch| pending.is_current_for(self, epoch, assumptions))
    }

    pub(in crate::executor) fn pending_bounded_bv_lia_unsat_matches_bound_epoch(
        &self,
        pending: &PendingBoundedBvLiaUnsat,
    ) -> bool {
        self.unsat_query_epoch.as_ref().is_some_and(|epoch| {
            epoch
                .assumptions
                .as_deref()
                .is_some_and(|assumptions| pending.is_current_for(self, epoch, assumptions))
        })
    }

    pub(super) fn require_current_pending_bounded_bv_lia_for_mint(
        &self,
        pending: Option<PendingBoundedBvLiaUnsat>,
        assumptions: &[TermId],
    ) -> Result<Option<PendingBoundedBvLiaUnsat>, UnsatCertificationError> {
        if pending.as_ref().is_some_and(|candidate| {
            !self.pending_bounded_bv_lia_unsat_is_current(candidate, assumptions)
        }) {
            return Err(UnsatCertificationError::StrictProofRejected {
                reason: "pending bounded BV/LIA authority is stale or does not match the exact public query"
                    .to_string(),
            });
        }
        Ok(pending)
    }

    /// Build the canonical native proof, re-authenticate the full exact source
    /// query after every possible term-store mutation, and offline-replay the
    /// serialized bundle before exposing it to the common certificate binder.
    pub(super) fn prepare_strict_native_bv_lia_bundle(
        &mut self,
        pending: PendingBoundedBvLiaUnsat,
        assumptions: &[TermId],
    ) -> Result<Option<PreparedStrictNativeBvLiaBundle>, UnsatCertificationError> {
        if !self.pending_bounded_bv_lia_unsat_is_current(&pending, assumptions) {
            return Err(UnsatCertificationError::StrictProofRejected {
                reason: "bounded BV/LIA authority became stale before native proof construction"
                    .to_string(),
            });
        }
        let exact_roots = pending.exact_roots.clone();
        let Some(selected) = super::super::proof_original_rebuild::collect_bounded_bv_lia_roots(
            &self.ctx.terms,
            &exact_roots,
        ) else {
            return Ok(None);
        };
        if selected.is_empty() {
            return Ok(None);
        }
        let Some(candidate) = self.build_authenticated_bv_lia_refutation(
            &selected,
            TheoryLemmaKind::BvLiaTautology,
            &exact_roots,
        ) else {
            return Ok(None);
        };
        let quality = self
            .check_proof_strict_with_datatypes(&candidate)
            .map_err(|error| UnsatCertificationError::StrictProofRejected {
                reason: format!("native bounded BV/LIA proof replay failed: {error}"),
            })?;
        if !quality.is_complete() || !Self::proof_derives_empty_clause(&candidate) {
            return Err(UnsatCertificationError::StrictProofRejected {
                reason:
                    "native bounded BV/LIA proof was incomplete or lacked an empty terminal clause"
                        .to_string(),
            });
        }

        // Candidate construction interns explicit raw negations. Authenticate
        // again only after that mutation so the retained evidence seals the
        // exact term universe serialized below.
        let final_evidence = match authenticate_bv_lia_unsat_query(
            &self.ctx.terms,
            &exact_roots,
            self.current_solve_deadline(),
        ) {
            Ok(evidence) => evidence,
            Err(error) if error.is_capability_decline() => return Ok(None),
            Err(error) => {
                return Err(UnsatCertificationError::StrictProofRejected {
                    reason: format!(
                        "final exact-source BV/LIA authentication rejected native bundle: {error}"
                    ),
                });
            }
        };
        let bundle =
            SerializableProofBundle::from_proof(&candidate, &self.ctx.terms, exact_roots.to_vec());
        let checked = re_check_bundle_strict(&bundle).map_err(|error| {
            UnsatCertificationError::StrictProofRejected {
                reason: format!("offline native BV/LIA bundle replay failed: {error}"),
            }
        })?;
        if !checked.quality.is_complete() || checked.assume_terms != selected {
            return Err(UnsatCertificationError::StrictProofRejected {
                reason:
                    "offline native BV/LIA bundle did not retain its complete load-bearing root set"
                        .to_string(),
            });
        }
        if !final_evidence.is_current_for(&self.ctx.terms, &exact_roots)
            || !self.pending_bounded_bv_lia_unsat_is_current(&pending, assumptions)
        {
            return Err(UnsatCertificationError::StrictProofRejected {
                reason: "bounded BV/LIA source or term snapshot changed during bundle replay"
                    .to_string(),
            });
        }

        Ok(Some(PreparedStrictNativeBvLiaBundle {
            exact_roots,
            proof_roots: selected.into_boxed_slice(),
            final_evidence,
            bundle,
            candidate,
            quality,
        }))
    }

    pub(in crate::executor) fn clear_strict_native_bundle_states(&mut self) {
        self.last_strict_native_bv_lia_bundle = None;
        self.last_strict_native_nra_sos_bundle = None;
    }

    pub(crate) fn has_strict_native_bv_lia_bundle_state(&self) -> bool {
        self.last_strict_native_bv_lia_bundle.is_some()
    }

    pub(crate) fn strict_native_bv_lia_bundle_for_proof(
        &self,
        proof: &Proof,
    ) -> Option<&SerializableProofBundle> {
        let state = self.last_strict_native_bv_lia_bundle.as_ref()?;
        state.is_current_for(self, proof).then_some(&state.bundle)
    }
}

#[cfg(test)]
mod tests;
