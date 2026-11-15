// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Account the complete native SOS payload before cloning or semantic replay.

use ay_core::{NraSosCertificate, NraSosRational, NraSosShapeError, NraSosTerm};

use super::*;

#[allow(clippy::ptr_arg)] // Allocated clause capacity is part of the payload charge.
pub(super) fn meter(
    terms: &TermStore,
    step: ProofId,
    clause: &Vec<TermId>,
    certificate: &NraSosCertificate,
    pending: &mut Vec<TermId>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    charge_progress(progress, 1, 0)?;
    if clause.len() > NraSosCertificate::MAX_CLAUSE_SLOTS {
        return Err(ProofCheckError::ResourceLimit);
    }
    certificate.validate_shape().map_err(|error| match error {
        NraSosShapeError::Limit => ProofCheckError::ResourceLimit,
        NraSosShapeError::Malformed => ProofCheckError::InvalidTheoryLemma {
            step,
            reason: "malformed native NRA SOS payload".into(),
        },
    })?;
    validate_roots(terms, step, clause, certificate, progress)?;
    charge_progress(
        progress,
        clause.len(),
        checked_mul_usize(clause.capacity(), size_of::<TermId>())?,
    )?;
    push_term_slice(pending, clause, progress)?;
    charge_progress(
        progress,
        certificate.basis.len(),
        checked_mul_usize(certificate.basis.capacity(), size_of::<Vec<TermId>>())?,
    )?;
    for monomial in &certificate.basis {
        charge_progress(
            progress,
            1,
            checked_mul_usize(monomial.capacity(), size_of::<TermId>())?,
        )?;
        push_term_slice(pending, monomial, progress)?;
    }
    charge_progress(
        progress,
        certificate.gram.len(),
        checked_mul_usize(
            certificate.gram.capacity(),
            size_of::<Vec<NraSosRational>>(),
        )?,
    )?;
    for row in &certificate.gram {
        charge_progress(
            progress,
            row.len(),
            checked_mul_usize(row.capacity(), size_of::<NraSosRational>())?,
        )?;
        for value in row {
            meter_rational(value, progress)?;
        }
    }
    charge_progress(
        progress,
        certificate.terms.len(),
        checked_mul_usize(certificate.terms.capacity(), size_of::<NraSosTerm>())?,
    )?;
    for term in &certificate.terms {
        // The origin is inline in NraSosTerm; its positional slots carry no
        // separate TermIds. Its multiplier still owns two dynamic integers.
        meter_rational(&term.multiplier, progress)?;
    }
    meter_rational(&certificate.rhs, progress)
}

fn meter_rational(
    value: &NraSosRational,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    meter_bigint(&value.numerator, progress)?;
    meter_bigint(&value.denominator, progress)
}

fn validate_roots(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    certificate: &NraSosCertificate,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let invalid = || ProofCheckError::InvalidTheoryLemma {
        step,
        reason: "NRA SOS payload contains an invalid or mistyped term root".into(),
    };
    for literal in clause {
        charge_progress(progress, 1, 0)?;
        if literal.index() >= terms.len() || terms.sort(*literal) != &Sort::Bool {
            return Err(invalid());
        }
    }
    for variable in certificate.basis.iter().flatten() {
        charge_progress(progress, 1, 0)?;
        if variable.index() >= terms.len()
            || !matches!(terms.sort(*variable), Sort::Int | Sort::Real)
            || !matches!(terms.get(*variable), TermData::Var(..))
        {
            return Err(invalid());
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests;
