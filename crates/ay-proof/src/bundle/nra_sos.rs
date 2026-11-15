// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Borrowed preflight for every term and positional source slot in an SOS step.

use ay_core::{NraSosCertificate, NraSosOrigin, NraSosShapeError};

use super::*;

pub(super) fn validate(
    entries: &[(TermData, Sort)],
    step_index: usize,
    clause: &[TermId],
    certificate: &NraSosCertificate,
) -> Result<(), ProofCheckError> {
    if clause.len() > NraSosCertificate::MAX_CLAUSE_SLOTS {
        return Err(ProofCheckError::ResourceLimit);
    }
    certificate.validate_shape().map_err(|error| match error {
        NraSosShapeError::Limit => ProofCheckError::ResourceLimit,
        NraSosShapeError::Malformed => malformed_bundle(format!(
            "proof step t{step_index} has malformed NRA SOS payload"
        )),
    })?;
    for &literal in clause {
        bundle_bool_term(entries, literal, "NRA SOS clause")?;
    }
    for &variable in certificate.basis.iter().flatten() {
        let (data, sort) = bundle_term(entries, variable, "NRA SOS basis")?;
        if !matches!(data, TermData::Var(..)) || !matches!(sort, Sort::Int | Sort::Real) {
            return Err(malformed_bundle(format!(
                "proof step t{step_index} NRA SOS basis references a non-arithmetic variable"
            )));
        }
    }
    for term in &certificate.terms {
        let valid = match term.origin {
            NraSosOrigin::ClauseLiteral { position } => (position as usize) < clause.len(),
            NraSosOrigin::Product { left, right } => {
                (left as usize) < clause.len() && (right as usize) < clause.len()
            }
        };
        if !valid {
            return Err(malformed_bundle(format!(
                "proof step t{step_index} NRA SOS origin references a missing clause slot"
            )));
        }
    }
    Ok(())
}
