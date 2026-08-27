// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rule dispatch for the two fresh-definition rules.
//!
//! `fresh_def_bound` and `fresh_def_eq` share ONE whole-proof registry (see
//! [`super::fresh_def`] for why that sharing is a soundness requirement) but
//! NOT a shape: each owns its own recognizer, its own error enum, and its own
//! local guards (`<=` vs `=`, and the bound's `side`). This module is the
//! single point where the rule chooses between them, so no `match` on the rule
//! has to live inside a recognizer.

use ay_core::proof_validation::{recognize_fresh_def_bound, recognize_fresh_def_eq};
use ay_core::{AletheRule, ProofId, TermId, TermStore};

use super::ProofCheckError;

/// Dispatch to the rule's own local shape recognizer.
///
/// Any rule other than the two fresh-definition rules is a caller bug and is
/// refused rather than defaulted, so a future third rule cannot silently
/// inherit the bound recognizer.
pub(super) fn recognize_fresh_definition(
    terms: &TermStore,
    rule: &AletheRule,
    clause: &[TermId],
    premise_count: usize,
    args: &[TermId],
) -> Result<(TermId, TermId), String> {
    match rule {
        AletheRule::FreshDefBound => recognize_fresh_def_bound(terms, clause, premise_count, args)
            .map(|shape| (shape.definiendum, shape.definiens))
            .map_err(|error| error.to_string()),
        AletheRule::FreshDefEq => recognize_fresh_def_eq(terms, clause, premise_count, args)
            .map(|shape| (shape.definiendum, shape.definiens))
            .map_err(|error| error.to_string()),
        other => Err(format!(
            "`{}` is not a fresh-definition rule and has no definitional provenance",
            other.name()
        )),
    }
}

/// Printer-side shape gate for a fresh-definition step.
///
/// The printer emits this step's CLAUSE, so a malformed step must decline
/// rather than reach the wire. Only the local shape is decided here; the
/// whole-proof provenance is the strict checker's job and is not re-run for
/// printing (the printer never claims the step is proved — it prints `hole`).
///
/// # Errors
///
/// Returns [`ProofCheckError::InvalidTheoryLemma`] when the step is malformed.
pub(crate) fn validate_fresh_definition_for_printer(
    terms: &TermStore,
    rule: &AletheRule,
    step_id: ProofId,
    clause: &[TermId],
    premises: &[ProofId],
    args: &[TermId],
) -> Result<(), ProofCheckError> {
    recognize_fresh_definition(terms, rule, clause, premises.len(), args)
        .map(|_| ())
        .map_err(|reason| ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason,
        })
}
