// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Final capability construction and optional bounded proof retention.

use super::*;

pub(super) fn finish_capability(
    authority: SealedAuthority,
    authored: AuthoredTerms,
    re_derived_premises: usize,
    replay: &mut ReplayValidation,
) -> Result<CheckedSatRefutation, CheckedSatRefutationError> {
    let boxed_root_bytes = checked_resource_mul(
        authored.ordered_roots.len(),
        size_of::<TermId>(),
        ResolutionValidationResource::Bytes,
    )?;
    replay
        .meter
        .charge(authored.ordered_roots.len(), boxed_root_bytes)?;
    let ordered_authored_roots = authored.ordered_roots.into_boxed_slice();
    let boxed_assumption_bytes = checked_resource_mul(
        authored.ordered_assumptions.len(),
        size_of::<TermId>(),
        ResolutionValidationResource::Bytes,
    )?;
    replay
        .meter
        .charge(authored.ordered_assumptions.len(), boxed_assumption_bytes)?;
    let ordered_assumptions = authored.ordered_assumptions.into_boxed_slice();
    replay.meter.charge(0, 0)?;
    let original_clause_count = checked_resource_add(
        replay.validated.original_mappings().len(),
        ordered_assumptions.len(),
        ResolutionValidationResource::OriginalClauses,
    )?;
    Ok(CheckedSatRefutation {
        query_epoch: authority.query_epoch,
        source_context_stamp: authority.source_context_stamp,
        ordered_authored_roots,
        ordered_assumptions,
        original_clause_count,
        derived_step_count: replay.validated.dag().derived.len(),
        re_derived_premises,
        native_proof: None,
    })
}

pub(super) fn native_candidate(
    executor: &mut Executor,
    fragment: ExactOriginalProofFragment,
    replay: &mut ReplayValidation,
    strict: &StrictContext,
    checked: &CheckedSatRefutation,
) -> Option<Proof> {
    if !checked.ordered_assumptions.is_empty() {
        return None;
    }
    let candidate = materialize::materialize(
        fragment,
        &replay.validated,
        executor.last_var_to_term.as_ref()?,
        &mut executor.ctx.terms,
        &mut replay.meter,
    );
    crate::executor::probe_cert_reject_raw(|| {
        format!(
            "native SAT materialization: retained={}, fixed-premises={}",
            candidate.is_some(),
            replay.validated.unit_premises().len(),
        )
    });
    let proof = candidate?;
    let bytes = strict_authentication_bytes(&proof, &mut replay.meter).ok()?;
    replay.meter.charge(proof.steps.len(), bytes).ok()?;
    let quality = ay_proof::check_proof_strict_with_typed_context_and_progress(
        &proof,
        &executor.ctx.terms,
        (!strict.datatype_decls.is_empty()).then_some(strict.datatype_decls.as_slice()),
        (!strict.selector_decls.is_empty()).then_some(strict.selector_decls.as_slice()),
        &strict.member_signatures,
        Some(&checked.ordered_authored_roots),
        &mut |work, bytes| replay.meter.charge(work, bytes).is_ok(),
    )
    .ok()?;
    crate::executor::probe_cert_reject_raw(|| {
        format!(
            "native SAT materialization: strict-complete={}",
            quality.is_complete(),
        )
    });
    quality.is_complete().then_some(proof)
}
