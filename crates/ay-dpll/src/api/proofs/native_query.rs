// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Diagnostic native proof source ownership, separate from public admission.

use std::sync::Arc;

use crate::api::{NativeReplayExportBudget, Solver, SolverCacheToken};
use crate::executor::NativeProofSourceScope;
use ay_core::time::Instant;
use ay_proof::ProofCheckError;
use ay_proof::{
    capture_strict_retained_bundle_with_resource_control, BundleReCheck, RetainedProofBundle,
};

use super::exact_query::resources::{construction, control::Control};

mod document;
#[cfg(test)]
mod tests;
mod transaction;
pub use document::NativeQueryDiagnosticDocument;

/// Two immutable observations inside the same public check transaction. The
/// input hook runs after epoch rotation and before any preprocessing; the proof
/// hook sees the actual completed native proof before publication can revoke it.
pub(in crate::api) trait NativeQueryObservation {
    fn deadline(&self) -> Instant;
    fn input(&mut self, solver: &Solver);
    fn proof(&mut self, executor: &crate::executor::Executor);
}

/// Opaque ownership of the actual native input captured at one audited public
/// decision entry, after its query epoch was rotated and before preprocessing.
///
/// This is not an UNSAT verdict or an external-checker permit. It has no public
/// constructor, deserializer or serialized-id rebinding operation. Every use
/// must validate the same live solver arena, attempt and complete source.
#[must_use = "native query ownership must be consumed by checked diagnostic export"]
pub struct NativeQueryBinding {
    solver: SolverCacheToken,
    source: Arc<NativeProofSourceScope>,
}

/// Owning diagnostic native evidence after two independent strict checks.
/// This is deliberately separate from public solver result admission and
/// says nothing about the pinned external checker's grammar or acceptance.
/// The retained v4 document cannot be detached as a mutable raw-v3 snapshot.
pub struct NativeQueryProofEnvelope {
    binding: NativeQueryBinding,
    proof: RetainedProofBundle,
    // Present only when captured at this actual check entry. A post-solve
    // export cannot reconstruct and claim custody of an earlier input.
    input_json: Option<String>,
}

/// Ordinary public solve details paired with separately checked native-only
/// diagnostic evidence. An envelope never strengthens `solve.result`.
pub struct NativeDiagnosticSolve {
    solve: crate::api::SolveDetails,
    proof: Option<NativeQueryProofEnvelope>,
}

impl NativeDiagnosticSolve {
    pub fn solve(&self) -> &crate::api::SolveDetails {
        &self.solve
    }

    pub fn proof(&self) -> Option<&NativeQueryProofEnvelope> {
        self.proof.as_ref()
    }

    pub fn into_parts(self) -> (crate::api::SolveDetails, Option<NativeQueryProofEnvelope>) {
        (self.solve, self.proof)
    }
}

impl std::fmt::Debug for NativeQueryProofEnvelope {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("NativeQueryProofEnvelope")
            .finish_non_exhaustive()
    }
}

impl NativeQueryProofEnvelope {
    /// Actual retained-proof schema; it is not a source or UNSAT permit.
    pub fn proof_schema(&self) -> &str {
        self.proof.schema()
    }

    /// Original query occurrences before proof-support narrowing.
    pub fn original_assertion_count(&self) -> usize {
        self.binding.original_assertion_count()
    }

    /// Complete native INPUT captured before this proof's actual solve. The
    /// document is diagnostic data, not a deserializable source authority.
    /// A separately requested post-solve envelope has no issued input document.
    pub fn issued_input_json(&self) -> Option<&str> {
        self.input_json.as_deref()
    }

    /// Independently replay the retained document against its still-live exact
    /// source. A foreign/stale solver or query declines before replay. This
    /// operation neither solves nor changes any public publication verdict.
    pub fn recheck_against_live_query_with_resource_control(
        &self,
        solver: &Solver,
        deadline: Instant,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Option<BundleReCheck>, ProofCheckError> {
        let mut original = |work, bytes| {
            Instant::now() < deadline && progress(work, bytes) && Instant::now() < deadline
        };
        Control::new(&mut original).run_retained(|control| {
            if !self.binding.is_current(solver, control)? {
                return Ok(None);
            }
            let checked = self.proof.with_checked_source_view_with_resource_control(
                deadline,
                &mut |w, b| control.charge(w, b).is_ok(),
                |view, checked, progress| {
                    if !checked.quality.is_complete() || checked.assume_terms.is_empty() {
                        return Ok(None);
                    }
                    // The immutable source owner, not the serialized ids or
                    // digest, supplies every expected original typed node.
                    if !self.binding.source.matches_retained_source_with_progress(
                        &solver.executor,
                        &view,
                        progress,
                    )? {
                        return Ok(None);
                    }
                    Ok(Some(checked))
                },
            )?;
            let Some(checked) = checked else {
                return Ok(None);
            };
            if !control.all_ids_in(&checked.assume_terms, self.binding.source.roots())? {
                return Ok(None);
            }
            if !self.binding.is_current(solver, control)? {
                return Ok(None);
            }
            Ok(Some(checked))
        })
    }
}

impl std::fmt::Debug for NativeQueryBinding {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("NativeQueryBinding")
            .finish_non_exhaustive()
    }
}

impl NativeQueryBinding {
    /// Full original assertion occurrences, including duplicates. This count
    /// is disclosure, not source or result authority.
    #[must_use]
    pub fn original_assertion_count(&self) -> usize {
        self.source.roots().len()
    }

    fn is_current(
        &self,
        solver: &Solver,
        control: &mut Control<'_>,
    ) -> Result<bool, ProofCheckError> {
        control.charge(1, 0)?;
        if !self.solver.is_current() || self.solver != solver.cache_token {
            return Ok(false);
        }
        self.source
            .is_current_with_progress(&solver.executor, &mut |w, b| control.charge(w, b).is_ok())
            .ok_or(ProofCheckError::ResourceLimit)
    }
}

impl Solver {
    /// Run the unchanged public solve/publication path while retaining a
    /// bounded independently checked native proof before publication may
    /// revoke it. Explicit proof production must already be requested.
    ///
    /// The observer receives only a borrowed executor and cannot affect a
    /// verdict or bypass a gate. Native evidence has two independent strict
    /// passes and exact original-premise binding. A wire refusal still returns
    /// the ordinary Unknown, with any native envelope labelled diagnostic.
    /// The original deadline only tightens the configured solve timeout; the
    /// same caller-owned ledger covers all diagnostic phases. The reusable
    /// input budget is debited as well and is never reset internally. Resource or
    /// checker failure returns no diagnostic owner and changes no stored
    /// public verdict.
    pub fn check_sat_with_native_query_diagnostic(
        &mut self,
        deadline: Instant,
        input_budget: &mut NativeReplayExportBudget,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<NativeDiagnosticSolve, ProofCheckError> {
        let started = Instant::now();
        let deadline = self
            .timeout
            .and_then(|timeout| started.checked_add(timeout))
            .map_or(deadline, |configured| deadline.min(configured));
        let mut original = |work, bytes| {
            Instant::now() < deadline && progress(work, bytes) && Instant::now() < deadline
        };
        Control::new(&mut original).run_retained(|control| {
            control.charge(1, std::mem::size_of::<NativeDiagnosticSolve>())?;
            let mut observer = transaction::Transaction::new(
                self.cache_token.clone(),
                deadline,
                input_budget,
                control,
            );
            let verified = self.check_sat_with_native_query_observer(&mut observer);
            let proof = observer.finish()?;
            let mut solve = self.build_solve_details(verified);
            solve.resource_usage.wall_time = started.elapsed();
            Ok(NativeDiagnosticSolve { solve, proof })
        })
    }

    /// Retain the source ownership that the ordinary authored native entry
    /// minted before its last solve. It cannot predict or authorize a future
    /// query. Missing capture returns `None`; later mutation may leave an
    /// owning stale binding whose checked export must decline.
    ///
    /// The caller keeps this same cumulative resource callback for source
    /// authentication, both independent retained checks and later transport.
    /// This fixed-size operation copies only opaque ownership handles.
    pub fn native_query_binding_with_resource_control(
        &self,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Option<NativeQueryBinding>, ProofCheckError> {
        if !progress(1, std::mem::size_of::<NativeQueryBinding>()) {
            return Err(ProofCheckError::ResourceLimit);
        }
        let binding = self
            .executor
            .native_proof_source_scope
            .as_ref()
            .map(|source| NativeQueryBinding {
                solver: self.cache_token.clone(),
                source: Arc::clone(source),
            });
        if !progress(0, 0) {
            return Err(ProofCheckError::ResourceLimit);
        }
        Ok(binding)
    }

    /// Consume the actual issued native binding and construct diagnostic
    /// retained evidence under the original deadline and cumulative owner.
    /// All first-check assumptions must be exact frozen original roots;
    /// preprocessing facts require explicit derivation, never adoption.
    /// Missing proof, foreign/stale source or unsupported evidence declines.
    /// A public Unknown remains Unknown regardless of this diagnostic path.
    pub fn export_native_query_retained_envelope_with_resource_control(
        &self,
        binding: NativeQueryBinding,
        deadline: Instant,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Option<NativeQueryProofEnvelope>, ProofCheckError> {
        let mut original = |work, bytes| {
            Instant::now() < deadline && progress(work, bytes) && Instant::now() < deadline
        };
        Control::new(&mut original).run_retained(move |control| {
            if !binding.is_current(self, control)? || binding.source.roots().is_empty() {
                return Ok(None);
            }
            if !binding
                .source
                .diagnostic_applications_are_declared_with_progress(&self.executor, &mut |w, b| {
                    control.charge(w, b).is_ok()
                })
                .ok_or(ProofCheckError::ResourceLimit)?
            {
                return Ok(None);
            }
            let Some(proof) = self.executor.last_proof() else {
                return Ok(None);
            };
            control.charge(0, self.terms().true_memory_bytes())?;
            let Some(snapshot) = construction::bundle(
                self,
                proof,
                |progress| {
                    let source = binding.source.roots();
                    let bytes = source
                        .len()
                        .checked_mul(std::mem::size_of::<ay_core::TermId>())
                        .ok_or(ProofCheckError::ResourceLimit)?;
                    if !progress(source.len(), bytes) {
                        return Err(ProofCheckError::ResourceLimit);
                    }
                    let mut roots = Vec::new();
                    roots
                        .try_reserve_exact(source.len())
                        .map_err(|_| ProofCheckError::ResourceLimit)?;
                    roots.extend_from_slice(source);
                    Ok(roots)
                },
                &mut |w, b| control.charge(w, b).is_ok(),
            )?
            else {
                return Ok(None);
            };
            let capture = capture_strict_retained_bundle_with_resource_control(
                snapshot,
                deadline,
                &mut |w, b| control.charge(w, b).is_ok(),
            )?;
            let first = capture.first_check();
            if !first.quality.is_complete()
                || first.assume_terms.is_empty()
                || !control.all_ids_in(&first.assume_terms, binding.source.roots())?
                || !binding.is_current(self, control)?
            {
                return Ok(None);
            }
            let (proof, checked) = capture
                .finish_exact_with_resource_control(&mut |w, b| control.charge(w, b).is_ok())?;
            if !checked.quality.is_complete()
                || checked.assume_terms.is_empty()
                || !control.all_ids_in(&checked.assume_terms, proof.obligation_assertions())?
                || !control.all_ids_in(proof.obligation_assertions(), &checked.assume_terms)?
                || !binding.is_current(self, control)?
            {
                return Ok(None);
            }
            Ok(Some(NativeQueryProofEnvelope {
                binding,
                proof,
                input_json: None,
            }))
        })
    }
}
