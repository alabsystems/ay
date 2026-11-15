// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cooperative cancellation of the existing independent offline reader.

use super::*;

mod resources;
pub use resources::re_check_bundle_strict_with_resource_control;

#[cfg(test)]
mod tests;

type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;

/// Independently re-check an in-memory bundle with cooperative cancellation.
///
/// The borrowed callback runs on the calling thread throughout structural
/// preflight, snapshot/proof copying, datatype and Skolem authentication, and
/// the strict checker's existing inner traversal checkpoints. Returning false
/// is sticky for this attempt and returns [`ProofCheckError::ResourceLimit`].
/// No unchecked fallback or partial result is returned. The callback is not
/// consulted after the strict checker's final step: a re-check that validated
/// every step is returned even if the caller's stop arrives afterwards.
/// Panics are not caught here; a callback panic also latches refusal in case a
/// lower-level guard catches it before control returns to this reader, and a
/// latched refusal still fails the attempt.
///
/// This is cancellation, NOT a complete work/allocation budget or a hard
/// latency guarantee. JSON decoding is outside this in-memory API. Individual
/// clone/hash/equality/arithmetic operations and destruction remain opaque;
/// the strict checker's semantic BV checks, empty-set demand census,
/// and some rule validators still have uninterrupted
/// intervals. Existing local checker limits remain unchanged.
///
/// As with [`re_check_bundle_strict`], success authenticates only the bundle's
/// internal proof/context pairing. The caller must still bind its assertions
/// and complete declarations to the intended external source problem.
pub fn re_check_bundle_strict_with_cancellation(
    bundle: &SerializableProofBundle,
    progress: &mut dyn FnMut() -> bool,
) -> Result<BundleReCheck, ProofCheckError> {
    Cancellation {
        progress,
        refused: false,
    }
    .run(|progress| reconstruct_and_check(bundle, progress))
}

struct Cancellation<'a> {
    progress: &'a mut dyn FnMut() -> bool,
    refused: bool,
}

impl Cancellation<'_> {
    fn poll(&mut self) -> Result<(), ProofCheckError> {
        if self.refused {
            return Err(ProofCheckError::ResourceLimit);
        }
        // Latch BEFORE user code: even a callback panic caught by an inner
        // validation guard must not permit a subsequent retry or publication.
        self.refused = true;
        if (self.progress)() {
            self.refused = false;
            Ok(())
        } else {
            Err(ProofCheckError::ResourceLimit)
        }
    }

    fn run<T>(
        &mut self,
        operation: impl FnOnce(Progress<'_>) -> Result<T, ProofCheckError>,
    ) -> Result<T, ProofCheckError> {
        self.poll()?;
        // The same sticky control reaches every existing progress walker.
        // Charges are deliberately ignored: this API makes no byte/work claim.
        let result = operation(&mut |_, _| self.poll().is_ok());
        // #completed-check-accepted: consult the LATCH, not the caller. A
        // refusal the operation observed stays final even if a lower-level
        // guard swallowed it, but a stop that arrives after the operation's
        // last callback cannot turn a completed check into a refusal. (A
        // fresh poll here used to do exactly that, and also replaced a
        // genuine validation error with `ResourceLimit`.)
        if self.refused {
            return Err(ProofCheckError::ResourceLimit);
        }
        result
    }
}

fn charge(progress: Progress<'_>, work: usize, bytes: usize) -> Result<(), ProofCheckError> {
    if progress(work, bytes) {
        Ok(())
    } else {
        Err(ProofCheckError::ResourceLimit)
    }
}

fn reconstruct_and_check(
    bundle: &SerializableProofBundle,
    progress: Progress<'_>,
) -> Result<BundleReCheck, ProofCheckError> {
    reconstruct_and_check_with_retained(bundle, None, progress).map(|(checked, _)| checked)
}

/// Shared reconstruction for the private retained lane. This remains an
/// in-memory v5 snapshot plus separately supplied untrusted bytes, not a v6
/// serde reader or an authentication shortcut.
pub(super) fn reconstruct_and_check_with_retained(
    bundle: &SerializableProofBundle,
    retained: Option<crate::quality::retained::Request<'_>>,
    progress: Progress<'_>,
) -> Result<
    (
        BundleReCheck,
        Vec<crate::checker::bv_bitblast::retained_session::RetainedStepPayload>,
    ),
    ProofCheckError,
> {
    let schema_bytes = bundle
        .schema
        .len()
        .checked_add(PROOF_BUNDLE_SCHEMA.len())
        .ok_or(ProofCheckError::ResourceLimit)?;
    charge(progress, schema_bytes, 0)?;
    let schema_matches = bundle.schema == PROOF_BUNDLE_SCHEMA;
    // Reuse the existing post-comparison checkpoint so cancellation callers
    // retain their exact callback sequence, including malformed schemas.
    let copied_bytes = if schema_matches { 0 } else { schema_bytes };
    charge(progress, copied_bytes, copied_bytes)?;
    if !schema_matches {
        return Err(ProofCheckError::BundleSchemaMismatch {
            expected: PROOF_BUNDLE_SCHEMA.to_owned(),
            found: bundle.schema.clone(),
        });
    }
    reconstruct_checked_schema(bundle, retained, progress)
}

/// Only the private owning v6 envelope may enter this lane. The mandatory
/// inventory is always replayed: this entry cannot capture replacement evidence
/// or select the legacy checker. Its caller supplies original-clock control.
pub(super) fn reconstruct_and_replay_versioned(
    envelope: &retained::RetainedBundle,
    wire_limits: Option<crate::bv_blast_solver::retained::wire::WireLimits>,
    deadline: ay_core::time::Instant,
    progress: Progress<'_>,
) -> Result<BundleReCheck, ProofCheckError> {
    let (bundle, payloads) = envelope.parts();
    let schema_bytes = bundle
        .schema
        .len()
        .checked_add(retained::RETAINED_SCHEMA.len())
        .ok_or(ProofCheckError::ResourceLimit)?;
    charge(progress, schema_bytes, 0)?;
    // The envelope constructor establishes shape, not proof authority. Keep
    // this local schema check before any snapshot reconstruction too.
    if bundle.schema != retained::RETAINED_SCHEMA {
        charge(progress, schema_bytes, schema_bytes)?;
        return Err(ProofCheckError::BundleSchemaMismatch {
            expected: retained::RETAINED_SCHEMA.to_owned(),
            found: bundle.schema.clone(),
        });
    }
    charge(progress, 0, 0)?;
    let (checked, output) = reconstruct_checked_schema(
        bundle,
        Some(crate::quality::retained::Request {
            operation: crate::checker::bv_bitblast::retained_session::RetainedOperation::Replay(
                payloads,
            ),
            wire_limits,
            deadline,
        }),
        progress,
    )?;
    // Replay never manufactures inventory. Refuse even in release builds if a
    // future implementation accidentally violates this private boundary.
    if !output.is_empty() {
        let reason = "retained replay produced replacement evidence";
        charge(progress, reason.len(), reason.len())?;
        return Err(malformed_bundle(reason));
    }
    Ok(checked)
}

/// Both callers authenticate their schema before entering this shared body.
/// Only v5 admits optional retained mode; the v6 caller above forces Replay.
fn reconstruct_checked_schema(
    bundle: &SerializableProofBundle,
    retained: Option<crate::quality::retained::Request<'_>>,
    progress: Progress<'_>,
) -> Result<
    (
        BundleReCheck,
        Vec<crate::checker::bv_bitblast::retained_session::RetainedStepPayload>,
    ),
    ProofCheckError,
> {
    let mut declaration_term_symbols = preflight::preflight_bundle_with_progress(bundle, progress)?;
    let mut terms = TermStore::from_entries_with_progress(
        &bundle.term_entries,
        bundle.true_term,
        bundle.false_term,
        bundle.var_counter,
        progress,
    )
    .map_err(|_| ProofCheckError::ResourceLimit)?;
    // Restore namespace DATA before any strict checker can interpret a head.
    // Pay the source scan, hash and owning registry entry under this same
    // request. Registration can only remove builtin interpretation.
    for identity in &bundle.declared_function_identities {
        let bytes = identity
            .len()
            .checked_mul(2)
            .and_then(|bytes| {
                bytes.checked_add(
                    16 * (std::mem::size_of::<String>() + std::mem::size_of::<usize>()),
                )
            })
            .ok_or(ProofCheckError::ResourceLimit)?;
        let work = identity
            .len()
            .checked_mul(2)
            .and_then(|work| work.checked_add(1))
            .ok_or(ProofCheckError::ResourceLimit)?;
        if !progress(work, bytes) {
            return Err(ProofCheckError::ResourceLimit);
        }
        if declaration_term_symbols.contains_key(identity) {
            return Err(malformed_bundle(
                "duplicate or datatype-owned user-function identity",
            ));
        }
        terms.register_declared_function(identity);
        declaration_term_symbols.insert(identity.clone(), "declared user function");
    }
    let datatype_declarations = (!bundle.datatype_declarations.is_empty())
        .then_some(bundle.datatype_declarations.as_slice());
    let constructor_selectors = (!bundle.constructor_selectors.is_empty())
        .then_some(bundle.constructor_selectors.as_slice());
    // Authenticate the exact typed namespace BEFORE introducing certificate-
    // derived names into even this private checker-only term store.
    crate::checker::validate_datatype_signature_context_with_progress(
        &terms,
        datatype_declarations,
        constructor_selectors,
        &bundle.datatype_member_signatures,
        progress,
    )?;
    let proof = Proof::from_steps(construction::copy_steps(&bundle.steps, progress)?);
    let names = crate::checker::quantifier::authenticate_bundle_skolems_with_progress(
        &proof,
        &terms,
        &bundle.obligation_assertions,
        &declaration_term_symbols,
        progress,
    )?;
    let terms = terms
        .with_skolem_symbols_with_progress(names, progress)
        .map_err(|_| ProofCheckError::ResourceLimit)?;
    // A structural scan of the copied steps, so it is paid BEFORE the strict
    // check: the check's final step is then the last work that consults the
    // caller (#completed-check-accepted).
    let assume_terms = collect_assumptions(&proof, progress)?;
    let (quality, retained_output) = match retained {
        None => (
            crate::check_proof_strict_with_typed_context_and_progress(
                &proof,
                &terms,
                datatype_declarations,
                constructor_selectors,
                &bundle.datatype_member_signatures,
                Some(&bundle.obligation_assertions),
                progress,
            )?,
            Vec::new(),
        ),
        Some(request) => crate::quality::retained::check(
            &proof,
            crate::quality::retained::Context {
                terms: &terms,
                dt_decls: datatype_declarations,
                ctor_selectors: constructor_selectors,
                datatype_member_signatures: &bundle.datatype_member_signatures,
                problem_assertions: &bundle.obligation_assertions,
            },
            request,
            progress,
        )?,
    };
    Ok((
        BundleReCheck {
            quality,
            assume_terms,
        },
        retained_output,
    ))
}

fn collect_assumptions(
    proof: &Proof,
    progress: Progress<'_>,
) -> Result<Vec<TermId>, ProofCheckError> {
    let mut count = 0usize;
    for step in &proof.steps {
        charge(progress, 1, 0)?;
        if matches!(step, ProofStep::Assume(_)) {
            count = count.checked_add(1).ok_or(ProofCheckError::ResourceLimit)?;
        }
    }
    let bytes = count
        .checked_mul(std::mem::size_of::<TermId>())
        .ok_or(ProofCheckError::ResourceLimit)?;
    charge(progress, count, bytes)?;
    let mut assumptions = Vec::new();
    assumptions
        .try_reserve_exact(count)
        .map_err(|_| ProofCheckError::ResourceLimit)?;
    for step in &proof.steps {
        charge(progress, 1, 0)?;
        if let ProofStep::Assume(term) = step {
            // Preserve exact order and duplicate slots, not a deduplicated set.
            assumptions.push(*term);
        }
    }
    Ok(assumptions)
}
