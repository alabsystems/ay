// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independent source-bound rational SOS replay. No search, floating point,
//! solver import or implicit source factors participate in proof authority.

use super::nra_poly::{
    extract_sos_clause_sources, Constraint, MPoly, Rel, WorkMeter, WORK_METER_RESOURCE_LIMIT,
};
use super::ProofCheckError;
use ay_core::{
    NraSosCertificate, NraSosOrigin, NraSosRational, NraSosShapeError, ProofId, TermId, TermStore,
};
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::collections::{BTreeMap, BTreeSet};

mod gram;
mod rational;
#[cfg(test)]
mod tests;

pub(crate) fn validate_nra_sos_with_progress(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    certificate: &NraSosCertificate,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let mut meter = WorkMeter::with_progress(progress);
    check(terms, clause, certificate, &mut meter).map_err(|reason| {
        if reason == WORK_METER_RESOURCE_LIMIT
            || reason.starts_with("nra work budget exceeded:")
            || reason.starts_with("nra polynomial coefficient exceeds cap ")
            || reason.starts_with("nra polynomial degree exceeds cap ")
            || reason == "nra term nesting exceeds depth cap"
        {
            ProofCheckError::ResourceLimit
        } else {
            ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: format!("nra_sos: {reason}"),
            }
        }
    })
}

fn check(
    terms: &TermStore,
    clause: &[TermId],
    cert: &NraSosCertificate,
    meter: &mut WorkMeter<'_>,
) -> Result<(), String> {
    meter.poll()?;
    cert.validate_shape().map_err(|error| match error {
        NraSosShapeError::Limit => WORK_METER_RESOURCE_LIMIT.to_string(),
        NraSosShapeError::Malformed => "malformed certificate shape".to_string(),
    })?;
    let sources = extract_sos_clause_sources(terms, clause, meter)?;
    validate_basis(terms, cert, &sources, meter)?;
    let rhs = rational::decode(&cert.rhs, meter)?;
    if rhs.is_positive() {
        return Err("positive right-hand side".to_string());
    }
    let gram = gram::decode_and_check(&cert.gram, meter)?;
    meter.poll()?;
    let mut sum = sigma(cert, &gram, meter)?;
    let mut strict_positive = false;
    for term in &cert.terms {
        meter.poll()?;
        let coefficient = rational::decode(&term.multiplier, meter)?;
        let (poly, kind) = derive_factor(term.origin, &sources, meter)?;
        if kind != Rel::Eq && coefficient.is_negative() {
            return Err("negative inequality multiplier".to_string());
        }
        strict_positive |= kind == Rel::Gt && coefficient.is_positive();
        let scaled = poly.scale(&coefficient, meter)?;
        checked_poly(&scaled)?;
        sum.add_assign_from(&scaled, meter)?;
        checked_poly(&sum)?;
    }
    if rhs.is_zero() && !strict_positive {
        return Err("zero right-hand side has no strict-positive term".to_string());
    }
    if sum.as_constant(meter)? != Some(rhs) {
        return Err("polynomial identity mismatch".to_string());
    }
    // Cancellation arriving during the last exact operation must dominate success.
    meter.poll()
}

fn checked_poly(poly: &MPoly) -> Result<(), String> {
    if poly.terms.len() > 256 || poly.max_total_degree() > 4 {
        return Err(WORK_METER_RESOURCE_LIMIT.to_string());
    }
    for coefficient in poly.terms.values() {
        rational::fits(coefficient)?;
    }
    Ok(())
}

fn validate_basis(
    terms: &TermStore,
    cert: &NraSosCertificate,
    sources: &[Constraint],
    meter: &mut WorkMeter<'_>,
) -> Result<(), String> {
    let mut variables = BTreeSet::new();
    for source in sources {
        for monomial in source.poly.terms.keys() {
            for &(variable, _) in monomial {
                meter.charge_container_slot::<TermId>()?;
                if !variables.contains(&variable) && variables.len() == NraSosCertificate::MAX_VARS
                {
                    return Err(WORK_METER_RESOURCE_LIMIT.to_string());
                }
                variables.insert(variable);
            }
        }
    }
    for monomial in &cert.basis {
        for variable in monomial {
            meter.charge_ops(1)?;
            if variable.index() >= terms.len() || !variables.contains(variable) {
                return Err("basis variable is not bound to the source".to_string());
            }
        }
    }
    Ok(())
}

fn orient(source: &Constraint, meter: &mut WorkMeter<'_>) -> Result<(MPoly, Rel), String> {
    let (sign, kind) = match source.rel {
        Rel::Ge => (1, Rel::Ge),
        Rel::Gt => (1, Rel::Gt),
        Rel::Eq => (1, Rel::Eq),
        Rel::Le => (-1, Rel::Ge),
        Rel::Lt => (-1, Rel::Gt),
        Rel::Ne => return Err("disequality is not an SOS factor".to_string()),
    };
    Ok((
        source
            .poly
            .scale(&BigRational::from_integer(sign.into()), meter)?,
        kind,
    ))
}

fn derive_factor(
    origin: NraSosOrigin,
    sources: &[Constraint],
    meter: &mut WorkMeter<'_>,
) -> Result<(MPoly, Rel), String> {
    let source = |position: u32| {
        sources
            .get(position as usize)
            .ok_or_else(|| "factor clause position is out of range".to_string())
    };
    match origin {
        NraSosOrigin::ClauseLiteral { position } => orient(source(position)?, meter),
        NraSosOrigin::Product { left, right } => {
            let (left, left_kind) = orient(source(left)?, meter)?;
            let (right, right_kind) = orient(source(right)?, meter)?;
            if left_kind == Rel::Eq || right_kind == Rel::Eq {
                return Err("product factor must be an inequality".to_string());
            }
            if left.max_total_degree() + right.max_total_degree() > 4 {
                return Err(WORK_METER_RESOURCE_LIMIT.to_string());
            }
            let kind = if left_kind == Rel::Gt && right_kind == Rel::Gt {
                Rel::Gt
            } else {
                Rel::Ge
            };
            let product = left.mul(&right, meter)?;
            checked_poly(&product)?;
            Ok((product, kind))
        }
    }
}

fn sigma(
    cert: &NraSosCertificate,
    gram: &[Vec<BigRational>],
    meter: &mut WorkMeter<'_>,
) -> Result<MPoly, String> {
    let mut result = MPoly::zero();
    for (row, left) in cert.basis.iter().enumerate() {
        for (column, right) in cert.basis.iter().enumerate() {
            meter.poll()?;
            let coefficient = &gram[row][column];
            if coefficient.is_zero() {
                continue;
            }
            meter.charge_monomials(1)?;
            let mut factors = Vec::with_capacity(left.len() + right.len());
            factors.extend_from_slice(left);
            factors.extend_from_slice(right);
            factors.sort_unstable();
            let mut monomial: super::nra_poly::Monomial = Vec::with_capacity(factors.len());
            for variable in factors {
                match monomial.last_mut() {
                    Some((last, exponent)) if *last == variable => *exponent += 1,
                    _ => monomial.push((variable, 1)),
                }
            }
            meter.charge_rational_scratch(super::nra_poly::rat_bits(coefficient))?;
            let poly = MPoly {
                terms: BTreeMap::from([(monomial, coefficient.clone())]),
            };
            result.add_assign_from(&poly, meter)?;
            checked_poly(&result)?;
        }
    }
    Ok(result)
}
