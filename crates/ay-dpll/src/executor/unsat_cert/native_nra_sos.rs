// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact-source native polynomial evidence, never Alethe-hole authority.

use std::sync::Arc;

use ay_core::Proof;
use ay_proof::{CheckedNraSosQuery, SerializableProofBundle};

use super::*;

mod build;
mod control;
mod resources;
use build::BuiltSosProof;
use control::{Control, Stop};

/// Construction is private and follows authentication of the original query.
/// The same terminal control survives construction until final publication.
pub(in crate::executor) struct PreparedStrictNativeNraSosBundle {
    authority_epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    assertions: Box<[TermId]>,
    assumptions: Box<[TermId]>,
    built: BuiltSosProof,
    control: Control<'static>,
}

/// Immutable native artifact shared without another whole-bundle copy between
/// the one-shot certificate and its persistent, independently guarded exporter.
#[derive(Debug)]
pub(in crate::executor) struct StrictNativeNraSosBundleState {
    scope: AuthenticatedUnsatScope,
    evidence: CheckedNraSosQuery,
    bundle: SerializableProofBundle,
}

#[derive(Debug)]
pub(in crate::executor) struct StrictNativeNraSosBundleUnsat {
    state: Arc<StrictNativeNraSosBundleState>,
}

fn plain_epoch_is_current(executor: &Executor, assumptions: &[TermId]) -> bool {
    executor.unsat_query_epoch.as_ref().is_some_and(|epoch| {
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
                .is_some_and(|source| source.original_problem_assertions == epoch.assertions)
    })
}

/// The AST checker interprets named arithmetic as builtins. An ordinary
/// declaration must not own either their spelling or their canonical identity,
/// even when frontend overload renaming made the other name look harmless.
fn operators_are_unshadowed(executor: &Executor, control: &mut Control<'_>) -> bool {
    const OPERATORS: &[&str] = &["+", "-", "*", "=", "<", "<=", ">", ">=", "not"];
    for (surface, info) in executor.ctx.symbol_iter() {
        let identity = executor.ctx.symbol_identity_name(surface, info);
        let Some(work) = surface
            .len()
            .checked_add(identity.len())
            .and_then(|n| n.checked_add(1))
        else {
            return false;
        };
        if !control.poll(work, 0)
            || OPERATORS.contains(&surface.as_str())
            || OPERATORS.contains(&identity)
        {
            return false;
        }
    }
    true
}

fn stopped_error() -> UnsatCertificationError {
    UnsatCertificationError::StrictProofRejected {
        reason: "exact-source native SOS publication stopped by its resource/deadline control"
            .to_string(),
    }
}

/// What a stopped preparation hands back to the common mint.
///
/// This lane is an optional upgrade of a presentation the mint has already
/// checked strictly: it is only consulted when the retained Alethe proof
/// carries a known wire gap, and the mint falls back to that proof whenever
/// this lane has no evidence (`Ok(None)`). A spent search allowance is no
/// evidence, not a rejection, so it must take that same fall-through; a
/// bounded DSOS search that finds no witness within its own caps already
/// does. Every terminal stop keeps retiring the whole attempt: the executor's
/// deadline, interrupt or memory ceiling is not this lane's to outlive.
fn refusal(
    control: &Control<'_>,
) -> Result<Option<PreparedStrictNativeNraSosBundle>, UnsatCertificationError> {
    match control.stop() {
        Some(Stop::Allowance) => Ok(None),
        Some(Stop::Terminal) | None => Err(stopped_error()),
    }
}

impl StrictNativeNraSosBundleState {
    fn is_current_for(&self, executor: &Executor, proof: &Proof) -> bool {
        // The bundle is immutable after independent replay. Equality with its
        // complete step vector covers unreachable steps too, so inserting a
        // second unsupported theory rule cannot inherit this narrow exception.
        self.scope.is_current(executor)
            && plain_epoch_is_current(executor, &self.scope.assumptions)
            && self
                .evidence
                .is_current_for_with_progress(
                    &executor.ctx.terms,
                    &self.scope.assertions,
                    &self.scope.assumptions,
                    &mut |_, _| true,
                )
                .unwrap_or(false)
            && proof.named_steps.is_empty()
            && proof.steps == self.bundle.steps
    }
}

impl StrictNativeNraSosBundleUnsat {
    pub(super) fn is_current(&self, executor: &Executor) -> bool {
        executor
            .last_proof
            .as_ref()
            .is_some_and(|proof| self.state.is_current_for(executor, proof))
    }
}

impl PreparedStrictNativeNraSosBundle {
    pub(super) fn bind(
        mut self,
        scope: AuthenticatedUnsatScope,
        executor: &mut Executor,
    ) -> Option<StrictNativeNraSosBundleUnsat> {
        if !self.control.poll_terms(&executor.ctx.terms, 1, 0)
            || !self.authority_epoch.is_same_epoch(&scope.authority_epoch)
            || self.source_context_stamp != scope.source_context_stamp
            || self.assertions != scope.assertions
            || self.assumptions != scope.assumptions
            || !scope.is_current(executor)
            || !plain_epoch_is_current(executor, &scope.assumptions)
            || !self.built.candidate.named_steps.is_empty()
            || self.built.candidate.steps != self.built.bundle.steps
            || !self.built.quality.is_complete()
            || !self
                .built
                .evidence
                .is_current_for_with_progress(
                    &executor.ctx.terms,
                    &scope.assertions,
                    &scope.assumptions,
                    &mut |work, bytes| self.control.poll(work, bytes),
                )
                .ok()?
        {
            return None;
        }
        let BuiltSosProof {
            candidate,
            bundle,
            evidence,
            quality,
        } = self.built;
        let state = Arc::new(StrictNativeNraSosBundleState {
            scope,
            evidence,
            bundle,
        });
        executor.commit_authenticated_plain_refutation(candidate, quality);
        // The shared installer retires the displaced proof's surface overrides
        // with every other sidecar. This proof's `assume`s are the exact source
        // roots, so rebuild their authored channel from the immutable source
        // rows, exactly as the ordinary assembly's final pass does. Without it
        // `(get-proof)` printed the canonical `(<= 1 x)` for an authored
        // `(>= x 1)`, and pinned carcara matched that `assume` against no
        // premise of the problem (QF_NIA/simple_product_unsat.smt2).
        let installed = executor.last_proof.take();
        if let Some(proof) = installed.as_ref() {
            executor.restore_reachable_authored_assume_surface_overrides(proof);
        }
        executor.last_proof = installed;
        let checked = StrictNativeNraSosBundleUnsat {
            state: Arc::clone(&state),
        };
        executor.last_strict_native_nra_sos_bundle = Some(state);
        drop(self.assertions);
        drop(self.assumptions);
        // Old proof/state destruction and assembly happen before this final
        // poll. No candidate or alternate certificate survives a terminal stop.
        if !checked.is_current(executor) || !self.control.poll_terms(&executor.ctx.terms, 0, 0) {
            executor.last_proof = None;
            executor.last_proof_quality = None;
            executor.clear_strict_native_bundle_states();
            return None;
        }
        Some(checked)
    }
}

impl Executor {
    /// Only the common UNSAT mint calls this: a provisional verdict is not
    /// evidence, and no transformed SAT trail or cached NIA witness is reused.
    pub(super) fn prepare_strict_native_nra_sos_bundle(
        &mut self,
        assumptions: &[TermId],
    ) -> Result<Option<PreparedStrictNativeNraSosBundle>, UnsatCertificationError> {
        let mut control = Control::new(self);
        if !control.poll_terms(&self.ctx.terms, 1, 0) {
            return refusal(&control);
        }
        if !plain_epoch_is_current(self, assumptions) {
            return Ok(None);
        }
        let epoch = self
            .unsat_query_epoch
            .as_ref()
            .ok_or(UnsatCertificationError::MissingEpoch)?;
        match build::supports_source(
            &self.ctx.terms,
            &epoch.assertions,
            assumptions,
            &mut |work, bytes| control.poll(work, bytes),
        ) {
            Ok(true) => {}
            Ok(false) => return Ok(None),
            Err(_) => return refusal(&control),
        }
        if !operators_are_unshadowed(self, &mut control) {
            return if control.stopped() {
                refusal(&control)
            } else {
                Ok(None)
            };
        }
        let epoch = self
            .unsat_query_epoch
            .as_ref()
            .ok_or(UnsatCertificationError::MissingEpoch)?;
        let Some(count) = epoch.assertions.len().checked_add(assumptions.len()) else {
            return Ok(None);
        };
        // Match the existing source fragment's cap; never filter slots to fit.
        if count == 0 || count > ay_core::NraSosCertificate::MAX_CLAUSE_SLOTS {
            return Ok(None);
        }
        if !control.poll(count, count * std::mem::size_of::<TermId>()) {
            return refusal(&control);
        }
        let assertions = epoch.assertions.clone().into_boxed_slice();
        let assumptions: Box<[TermId]> = assumptions.into();
        let authority_epoch = epoch.authority_epoch.clone();
        let source_context_stamp = epoch.source_context_stamp.clone();
        let built = build::build(
            &mut self.ctx.terms,
            &assertions,
            &assumptions,
            &mut |work, bytes| control.poll(work, bytes),
        );
        if !control.poll_terms(&self.ctx.terms, 0, 0) {
            return refusal(&control);
        }
        let Some(built) = built.map_err(|error| UnsatCertificationError::StrictProofRejected {
            reason: format!("exact-source native SOS proof construction rejected: {error}"),
        })?
        else {
            return Ok(None);
        };
        if !plain_epoch_is_current(self, &assumptions) {
            return Err(UnsatCertificationError::StaleTermEntry);
        }
        Ok(Some(PreparedStrictNativeNraSosBundle {
            authority_epoch,
            source_context_stamp,
            assertions,
            assumptions,
            built,
            control,
        }))
    }

    pub(crate) fn has_strict_native_nra_sos_bundle_state(&self) -> bool {
        self.last_strict_native_nra_sos_bundle.is_some()
    }

    pub(crate) fn strict_native_nra_sos_bundle_for_proof(
        &self,
        proof: &Proof,
    ) -> Option<&SerializableProofBundle> {
        let state = self.last_strict_native_nra_sos_bundle.as_ref()?;
        state.is_current_for(self, proof).then_some(&state.bundle)
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
impl Executor {
    /// Test only: inject the decision fact, never its proof or certificate.
    /// This pins the missing-presentation route without depending on which
    /// stronger proof an unrelated SMT search might construct first.
    pub(crate) fn certify_native_sos_provisional_for_test(&mut self) -> SolveResult {
        self.begin_public_solve(false);
        self.bind_unsat_query_assumptions(&[]);
        self.last_result = Some(SolveResult::unsat());
        let published = self.certify_unsat_for_publication(SolveResult::unsat(), &[]);
        self.last_result = Some(published.clone());
        published
    }
}
