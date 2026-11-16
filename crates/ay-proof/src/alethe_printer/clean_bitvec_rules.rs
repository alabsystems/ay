// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Dialect-scoped emission for Clean's checked bit-vector rules.
//!
//! Pinned Carcara receives `hole` before any Clean-only surface claim is made.
//! Keeping the two literal spellings in this module makes that confinement
//! visible to the wire-rule inventory instead of relying on a nearby branch in
//! the dialect-independent printer.

use super::{dialect, AlethePrintError, AlethePrinter};
use ay_core::{ProofId, TermId};

pub(super) fn format_bv_reconstruct(
    printer: &AlethePrinter<'_>,
    id: ProofId,
    clause: &[TermId],
    premises: &[ProofId],
    args: &[TermId],
) -> Result<String, AlethePrintError> {
    crate::checker::bv_reconstruct::validate(
        printer.terms,
        id,
        clause,
        premises.len(),
        args.len(),
        &mut |_, _| true,
    )
    .map_err(|error| AlethePrintError::InvalidSurfaceStep {
        id,
        reason: error.to_string(),
    })?;
    let clause_str = printer.format_clause(clause);
    if dialect::current() == dialect::AletheDialect::PinnedCarcara {
        return Ok(format!("(step {id} {clause_str} :rule hole)"));
    }
    let wire_overrides = printer.judgement_overrides();
    if !crate::bv_reconstruct_step_lowering_supported(
        dialect::current(),
        printer.terms,
        clause,
        premises.len(),
        args.len(),
        wire_overrides.as_ref(),
    ) {
        return Err(AlethePrintError::InvalidSurfaceStep {
            id,
            reason: "BV reconstruction equality changed under surface rewriting".to_string(),
        });
    }
    dialect::note_clean_only(dialect::CleanOnlySpelling::BvReconstructV1);
    Ok(format!("(step {id} {clause_str} :rule bv_reconstruct_v1)"))
}

pub(super) fn format_bv_offset_spines(
    printer: &AlethePrinter<'_>,
    id: ProofId,
    clause: &[TermId],
    premises: &[ProofId],
    args: &[TermId],
) -> Result<String, AlethePrintError> {
    crate::checker::bv_offset_spines::validate(
        printer.terms,
        id,
        clause,
        premises.len(),
        args.len(),
        &mut |_, _| true,
    )
    .map_err(|error| AlethePrintError::InvalidSurfaceStep {
        id,
        reason: error.to_string(),
    })?;
    let clause_str = printer.format_clause(clause);
    if dialect::current() == dialect::AletheDialect::PinnedCarcara {
        return Ok(format!("(step {id} {clause_str} :rule hole)"));
    }
    let wire_overrides = printer.judgement_overrides();
    if !crate::bv_offset_spines_step_lowering_supported(
        dialect::current(),
        printer.terms,
        clause,
        premises.len(),
        args.len(),
        wire_overrides.as_ref(),
    ) {
        return Err(AlethePrintError::InvalidSurfaceStep {
            id,
            reason: "BV offset spine equality changed under surface rewriting".to_string(),
        });
    }
    dialect::note_clean_only(dialect::CleanOnlySpelling::BvOffsetSpinesV1);
    Ok(format!(
        "(step {id} {clause_str} :rule eq_simplify_bv_offset_spines)"
    ))
}
