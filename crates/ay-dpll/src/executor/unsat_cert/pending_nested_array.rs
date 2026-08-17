// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Affine authority for exact nested finite-array UNSAT results.

use super::*;

/// Affine transport from the final nested-array quarantine to UNSAT minting.
///
/// This is deliberately not an [`UnsatCertificate`].  The quarantine can
/// authenticate the exact finite Bool/BV/array theorem only after every
/// same-executor proof, rescue, and core-minimization operation has finished
/// growing the term store, but the public-query scope is minted later by the
/// common certification funnel.  Keeping those two stages separate prevents
/// both a duplicate bit-blast authentication and a pre-bound scope from being
/// retargeted by wrapper code.
///
/// No `Clone` implementation is provided: the evidence is moved exactly once
/// into [`CheckedBoolBvUnsat`] or discarded at another terminal boundary.
#[derive(Debug)]
pub(in crate::executor) struct PendingNestedArrayBoolBvUnsat {
    authority_epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    exact_roots: Box<[TermId]>,
    evidence: AuthenticatedBoolBvUnsatQuery,
}

impl PendingNestedArrayBoolBvUnsat {
    /// Recheck every part of the sealed theorem against the live public query.
    ///
    /// The full term-snapshot check is load-bearing: append-only term growth
    /// preserves the epoch's per-root entry stamps, but invalidates the proof
    /// checker's whole-arena authentication.
    fn is_current_for(
        &self,
        executor: &Executor,
        epoch: &UnsatQueryEpoch,
        assumptions: &[TermId],
    ) -> bool {
        self.evidence.used_exact_finite_arrays()
            && self
                .authority_epoch
                .is_same_epoch(&executor.query_authority_epoch)
            && self.authority_epoch.is_same_epoch(&epoch.authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && self.source_context_stamp == epoch.source_context_stamp
            && executor.ctx.objectives().is_empty()
            && epoch.declared_extension.is_empty()
            && epoch.declared_extension_entries.is_empty()
            && epoch.declared_extension_objectives.is_none()
            && epoch.declared_extension_objective_entries.is_none()
            && epoch.assumptions.as_deref() == Some(assumptions)
            && epoch.is_current(executor)
            && self.exact_roots.iter().copied().eq(epoch
                .assertions
                .iter()
                .chain(assumptions.iter())
                .copied())
            && self
                .evidence
                .is_current_for(&executor.ctx.terms, &self.exact_roots)
    }

    /// Bind this already-authenticated theorem to the freshly captured common
    /// publication scope.  `CheckedBoolBvUnsat::bind` independently repeats
    /// the exact-root/snapshot join before constructing the certificate kind.
    pub(super) fn bind(
        self,
        scope: AuthenticatedUnsatScope,
        executor: &Executor,
    ) -> Option<CheckedBoolBvUnsat> {
        if !self.evidence.used_exact_finite_arrays() {
            return None;
        }
        CheckedBoolBvUnsat::bind(scope, self.evidence, &executor.ctx.terms, &self.exact_roots)
    }
}

impl Executor {
    /// Whether the final nested-array quarantine can already rely on a
    /// complete proof authority for this exact public query.
    ///
    /// An explicit proof/strict-check request may be satisfied only by the
    /// translated proof itself.  Otherwise the opaque checked SAT sidecar is
    /// consulted first; unlike a cached Boolean, it rechecks its query binding
    /// at every use.  A strict proof remains a valid fallback, but its success
    /// is deliberately not cached here -- final minting checks the artifact
    /// again against the freshly authenticated publication scope.
    pub(in crate::executor) fn nested_array_unsat_proof_authority_is_current(&self) -> bool {
        let Some(epoch) = self.unsat_query_epoch.as_ref() else {
            return false;
        };
        let Some(assumptions) = epoch.assumptions.as_deref() else {
            return false;
        };

        if !self.strict_unsat_presentation_required()
            && self.checked_sat_refutation_authorizes(epoch, assumptions)
        {
            return true;
        }

        let proof_scope_is_current = epoch.is_current(self)
            && self
                .proof_problem_assertion_provenance
                .as_ref()
                .is_some_and(|provenance| {
                    provenance.original_problem_assertions == epoch.assertions
                })
            && self.last_assumptions.iter().flatten().all(|&term| {
                self.query_authorizes_assumption(term, &epoch.assertions, assumptions)
            });
        proof_scope_is_current
            && self
                .last_proof
                .as_ref()
                .is_some_and(|proof| self.check_proof_strict_with_datatypes(proof).is_ok())
    }

    /// Produce the move-only exact finite-array theorem consumed later by the
    /// common UNSAT mint.
    ///
    /// This method is called only by the final public nested-array quarantine,
    /// after proof reconstruction, checked-sidecar construction, named-core
    /// rescue, and core minimization.  Those operations may intern terms; the
    /// proof checker's evidence seals the complete term-store snapshot and
    /// would become stale if it were produced any earlier.
    pub(in crate::executor) fn prepare_pending_nested_array_bool_bv_unsat(
        &mut self,
    ) -> Result<bool, UnsatCertificationError> {
        debug_assert!(
            self.pending_nested_array_bool_bv_unsat.is_none(),
            "the final quarantine must retire earlier pending authority before rebuilding it"
        );

        // Semantic evidence cannot satisfy an explicitly requested proof
        // artifact.  Avoid paying for a theorem the mandatory mint must reject.
        if self.strict_unsat_presentation_required() || !self.ctx.objectives().is_empty() {
            return Ok(false);
        }

        let (authority_epoch, source_context_stamp, assumptions) = {
            let Some(epoch) = self.unsat_query_epoch.as_ref() else {
                // Internal/raw probes carry no public epoch and retain the
                // historical fail-closed quarantine behavior.
                return Ok(false);
            };
            if !epoch
                .authority_epoch
                .is_same_epoch(&self.query_authority_epoch)
            {
                return Err(UnsatCertificationError::StaleEpoch);
            }
            if epoch.source_context_stamp != self.ctx.source_context_stamp() {
                return Err(UnsatCertificationError::StaleSourceContext);
            }
            if !epoch.term_entries_are_current(self) {
                return Err(UnsatCertificationError::StaleTermEntry);
            }
            if !epoch.declared_extension.is_empty()
                || !epoch.declared_extension_entries.is_empty()
                || epoch.declared_extension_objectives.is_some()
                || epoch.declared_extension_objective_entries.is_some()
            {
                return Ok(false);
            }
            let assumptions = epoch
                .assumptions
                .clone()
                .ok_or(UnsatCertificationError::UnboundAssumptions)?;
            (
                epoch.authority_epoch.clone(),
                epoch.source_context_stamp.clone(),
                assumptions,
            )
        };

        let Some((evidence, exact_roots)) = self.authenticate_bool_bv_query(
            self.unsat_query_epoch
                .as_ref()
                .ok_or(UnsatCertificationError::MissingEpoch)?,
            &assumptions,
        )?
        else {
            return Ok(false);
        };
        if !evidence.used_exact_finite_arrays() {
            // The quarantine is specifically authority for the guarded array
            // structure.  Plain Bool/BV evidence remains available at normal
            // mint time, but cannot open this gate.
            return Ok(false);
        }

        let pending = PendingNestedArrayBoolBvUnsat {
            authority_epoch,
            source_context_stamp,
            exact_roots,
            evidence,
        };
        let Some(epoch) = self.unsat_query_epoch.as_ref() else {
            return Err(UnsatCertificationError::MissingEpoch);
        };
        if !pending.is_current_for(self, epoch, &assumptions) {
            return Err(UnsatCertificationError::StrictProofRejected {
                reason: "nested finite-array Bool/BV authority became stale while sealing"
                    .to_string(),
            });
        }
        self.pending_nested_array_bool_bv_unsat = Some(pending);
        Ok(true)
    }

    pub(super) fn pending_nested_array_bool_bv_unsat_is_current(
        &self,
        pending: &PendingNestedArrayBoolBvUnsat,
        assumptions: &[TermId],
    ) -> bool {
        self.unsat_query_epoch
            .as_ref()
            .is_some_and(|epoch| pending.is_current_for(self, epoch, assumptions))
    }

    /// Treat a present stale affine token as a lifecycle failure, not a normal
    /// semantic-lane decline that could silently fall through to another mint.
    pub(super) fn require_current_pending_nested_array_for_mint(
        &self,
        pending: Option<PendingNestedArrayBoolBvUnsat>,
        epoch: &UnsatQueryEpoch,
        assumptions: &[TermId],
    ) -> Result<Option<PendingNestedArrayBoolBvUnsat>, UnsatCertificationError> {
        if pending
            .as_ref()
            .is_some_and(|candidate| !candidate.is_current_for(self, epoch, assumptions))
        {
            return Err(UnsatCertificationError::StrictProofRejected {
                reason: "pending nested finite-array Bool/BV authority is stale or does not match the exact public query"
                    .to_string(),
            });
        }
        Ok(pending)
    }
}
