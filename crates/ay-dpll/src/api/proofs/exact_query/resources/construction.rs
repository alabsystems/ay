// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Construction only: neither source authentication nor a strict proof check.

use super::{ProofCheckError, SerializableProofBundle, Solver};
use ay_core::{Proof, TermId};

type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;

/// Preserve the legacy route order and callback sequence. A selected sealed
/// state that declines is terminal: it never authorizes generic reconstruction.
/// The complete problem collector is lazy so sealed/finite routes do not add a
/// source walk. No route performs an independent proof check here.
pub(super) fn bundle(
    solver: &Solver,
    proof: &Proof,
    complete_problem: impl FnOnce(Progress<'_>) -> Result<Vec<TermId>, ProofCheckError>,
    progress: Progress<'_>,
) -> Result<Option<SerializableProofBundle>, ProofCheckError> {
    if solver.executor.has_strict_native_nra_sos_bundle_state() {
        return solver
            .executor
            .export_strict_native_nra_sos_bundle_for_proof_with_progress(proof, progress);
    }
    if solver.executor.has_strict_native_bv_lia_bundle_state() {
        return solver
            .executor
            .export_strict_native_bv_lia_bundle_for_proof_with_progress(proof, progress);
    }
    let finite = solver.executor.last_proof_has_finite_enum_sidecar();
    let (problem, declarations, selectors, signatures) = if finite {
        let Some((declarations, selectors, signatures)) = solver
            .executor
            .checked_finite_enum_export_declarations_with_progress(proof, progress)?
        else {
            return Ok(None);
        };
        let Some(problem) = solver
            .executor
            .finite_enum_scope_for_proof_with_progress(proof, progress)?
        else {
            return Ok(None);
        };
        (problem, declarations, selectors, signatures)
    } else {
        let problem = complete_problem(progress)?;
        let declarations = solver
            .executor
            .datatype_decls_for_strict_proof_with_progress(progress)?;
        let selectors = solver
            .executor
            .ctor_selector_decls_for_strict_proof_with_progress(progress)?;
        let Some(signatures) = solver
            .executor
            .datatype_member_signatures_for_strict_proof_with_progress(progress)?
        else {
            return Ok(None);
        };
        (problem, declarations, selectors, signatures)
    };
    Ok(Some(
        SerializableProofBundle::from_proof_with_typed_context_and_progress(
            proof,
            solver.executor.terms(),
            &problem,
            &declarations,
            &selectors,
            &signatures,
            progress,
        )?,
    ))
}
