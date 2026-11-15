// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Same shape/root/slot policy as the portable DTO, with per-operation charges.
//! No arithmetic, source normalization, Gram checking or proof authority here.

use ay_core::{NraSosCertificate, NraSosOrigin, NraSosRational, NraSosShapeError};

use super::*;

pub(super) fn validate(
    entries: &[(TermData, Sort)],
    step: usize,
    clause: &[TermId],
    certificate: &NraSosCertificate,
    meter: &mut ProofMeter<'_>,
) -> Result<(), ProofCheckError> {
    meter.charge(1, 0)?;
    if clause.len() > NraSosCertificate::MAX_CLAUSE_SLOTS {
        return Err(ProofCheckError::ResourceLimit);
    }
    shape(certificate, step, meter)?;
    meter.clause(entries, clause, step, "NRA SOS clause")?;
    for monomial in &certificate.basis {
        meter.charge(1, 0)?;
        for &variable in monomial {
            let (data, sort) = meter.term(entries, variable, step, "NRA SOS basis")?;
            if !matches!(data, TermData::Var(..)) || !matches!(sort, Sort::Int | Sort::Real) {
                return meter.invalid(step, "NRA SOS basis references a non-arithmetic variable");
            }
        }
    }
    for term in &certificate.terms {
        meter.charge(1, 0)?;
        let (left, right) = positions(term.origin);
        if left >= clause.len() || right >= clause.len() {
            return meter.invalid(step, "NRA SOS origin references a missing clause slot");
        }
    }
    Ok(())
}

fn shape(
    certificate: &NraSosCertificate,
    step: usize,
    meter: &mut ProofMeter<'_>,
) -> Result<(), ProofCheckError> {
    meter.charge(1, 0)?;
    let n = certificate.basis.len();
    if n > NraSosCertificate::MAX_BASIS
        || certificate.gram.len() > NraSosCertificate::MAX_BASIS
        || certificate.terms.len() > NraSosCertificate::MAX_TERMS
    {
        return Err(ProofCheckError::ResourceLimit);
    }
    if n == 0 || !certificate.basis[0].is_empty() || certificate.gram.len() != n {
        return meter.invalid(step, "has malformed NRA SOS payload");
    }
    for (index, monomial) in certificate.basis.iter().enumerate() {
        meter.charge(1, 0)?;
        if monomial.len() > 2 {
            return Err(ProofCheckError::ResourceLimit);
        }
        if monomial.windows(2).any(|pair| pair[0] > pair[1]) {
            return meter.invalid(step, "has malformed NRA SOS payload");
        }
        for prior in &certificate.basis[..index] {
            // Each previously validated monomial has <=2 TermIds; there is no
            // recursive comparison or allocation hidden in this equality.
            meter.charge(meter::add(monomial.len(), 1)?, 0)?;
            if prior == monomial {
                return meter.invalid(step, "has malformed NRA SOS payload");
            }
        }
    }
    for row in &certificate.gram {
        meter.charge(1, 0)?;
        if row.len() > NraSosCertificate::MAX_BASIS {
            return Err(ProofCheckError::ResourceLimit);
        }
        if row.len() != n {
            return meter.invalid(step, "has malformed NRA SOS payload");
        }
        for coefficient in row {
            rational(coefficient, step, meter)?;
        }
    }
    for term in &certificate.terms {
        meter.charge(1, 0)?;
        let (left, right) = positions(term.origin);
        if left >= NraSosCertificate::MAX_CLAUSE_SLOTS
            || right >= NraSosCertificate::MAX_CLAUSE_SLOTS
        {
            return Err(ProofCheckError::ResourceLimit);
        }
        rational(&term.multiplier, step, meter)?;
    }
    rational(&certificate.rhs, step, meter)
}

fn positions(origin: NraSosOrigin) -> (usize, usize) {
    match origin {
        NraSosOrigin::ClauseLiteral { position } => (position as usize, position as usize),
        NraSosOrigin::Product { left, right } => (left as usize, right as usize),
    }
}

fn rational(
    value: &NraSosRational,
    step: usize,
    meter: &mut ProofMeter<'_>,
) -> Result<(), ProofCheckError> {
    // bits() reads the length and top limb; sign() is a scalar read. This does
    // not hash/clone, construct Ratio, normalize, or scan arbitrary limbs.
    meter.charge(3, 0)?;
    match value.validate_shape() {
        Ok(()) => Ok(()),
        Err(NraSosShapeError::Limit) => Err(ProofCheckError::ResourceLimit),
        Err(NraSosShapeError::Malformed) => meter.invalid(step, "has malformed NRA SOS payload"),
    }
}
