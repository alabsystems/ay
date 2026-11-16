// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One source slot per exact clause literal, with no Boolean flattening,
//! constant filtering or entailed-bound insertion. Independent of AY's solver.

use super::*;
use ay_core::NraSosCertificate;

/// Parse the conjunction of the NEGATIONS of direct comparison literals.
/// Constants remain real constraint slots; even a true comparison is retained.
pub(crate) fn extract_sos_clause_sources(
    terms: &TermStore,
    clause: &[TermId],
    meter: &mut WorkMeter<'_>,
) -> Result<Vec<Constraint>, String> {
    if clause.is_empty() {
        return Err("empty SOS clause has no source constraints".to_string());
    }
    if clause.len() > NraSosCertificate::MAX_CLAUSE_SLOTS {
        return Err(WORK_METER_RESOURCE_LIMIT.to_string());
    }
    meter.charge_private_allocation(clause.len(), clause.len() * size_of::<Constraint>())?;
    let mut output = Vec::new();
    output
        .try_reserve_exact(clause.len())
        .map_err(|_| WORK_METER_RESOURCE_LIMIT.to_string())?;
    let mut memo = BTreeMap::new();
    let mut total_terms = 0usize;
    for &literal in clause {
        let (mut atom, mut asserted) = (literal, false);
        loop {
            meter.charge_node()?;
            if atom.index() >= terms.len() || terms.sort(atom) != &Sort::Bool {
                return Err("SOS source literal is missing or non-Boolean".to_string());
            }
            match terms.get(atom) {
                TermData::Not(inner) => {
                    atom = *inner;
                    asserted = !asserted;
                }
                _ => break,
            }
        }
        let TermData::App(Symbol::Named(name), args) = terms.get(atom) else {
            return Err("SOS requires direct arithmetic comparison literals".to_string());
        };
        if declared_application(terms, atom, meter)? {
            return Err("SOS comparison is a declared application".to_string());
        }
        if args.len() != 2 || !matches!(name.as_str(), "=" | "<" | "<=" | ">" | ">=") {
            return Err("SOS rejects Boolean packing and unsupported comparisons".to_string());
        }
        for &arg in args {
            preflight_arithmetic(terms, arg, meter)?;
        }
        if !matches!(terms.sort(args[0]), Sort::Int | Sort::Real)
            || terms.sort(args[0]) != terms.sort(args[1])
        {
            return Err("SOS comparison sorts do not agree".to_string());
        }
        let left = parse_poly(terms, args[0], &mut memo, meter, 0)?;
        let right = parse_poly(terms, args[1], &mut memo, meter, 0)?;
        check_source_poly(&left)?;
        check_source_poly(&right)?;
        let poly = left.sub(&right, meter)?;
        check_source_poly(&poly)?;
        total_terms += poly.terms.len();
        if total_terms > 8_192 {
            return Err(WORK_METER_RESOURCE_LIMIT.to_string());
        }
        let rel = match (name.as_str(), asserted) {
            ("=", true) => Rel::Eq,
            ("=", false) => Rel::Ne,
            ("<", true) | (">=", false) => Rel::Lt,
            ("<=", true) | (">", false) => Rel::Le,
            (">", true) | ("<=", false) => Rel::Gt,
            (">=", true) | ("<", false) => Rel::Ge,
            _ => return Err("SOS unsupported source relation".to_string()),
        };
        output.push(Constraint { poly, rel });
    }
    meter.poll()?;
    Ok(output)
}

fn check_source_poly(poly: &MPoly) -> Result<(), String> {
    if poly.terms.len() > 256
        || poly.max_total_degree() > 4
        || poly.terms.values().any(|coefficient| {
            coefficient.numer().bits() > 1_024
                || coefficient.denom().bits() > 1_024
                || !coefficient.denom().is_positive()
        })
    {
        return Err(WORK_METER_RESOURCE_LIMIT.to_string());
    }
    Ok(())
}

/// Admit only the producer's homogeneous numeric grammar before invoking the
/// shared parser. In particular, do not inherit its opaque applications,
/// divisions, coercions or bitvector folds as new SOS source authority. The
/// unfolded walk is bounded before enqueuing children and imposes depth 256
/// before the generic recursive parser.
fn preflight_arithmetic(
    terms: &TermStore,
    root: TermId,
    meter: &mut WorkMeter<'_>,
) -> Result<(), String> {
    meter.charge_node()?;
    if root.index() >= terms.len() {
        return Err("SOS missing source term".to_string());
    }
    let source_sort = terms.sort(root);
    if !matches!(source_sort, Sort::Int | Sort::Real) {
        return Err("SOS requires numeric source terms".to_string());
    }
    let mut pending = vec![(root, 0usize)];
    while let Some((term, depth)) = pending.pop() {
        meter.poll()?;
        if depth > 256 {
            return Err(WORK_METER_RESOURCE_LIMIT.to_string());
        }
        if term.index() >= terms.len() {
            return Err("SOS missing source term".to_string());
        }
        if terms.sort(term) != source_sort {
            return Err("SOS arithmetic child sorts do not agree".to_string());
        }
        if declared_application(terms, term, meter)? {
            return Err("SOS source has an opaque declared application".to_string());
        }
        match terms.get(term) {
            TermData::Const(Constant::Rational(value)) if source_sort == &Sort::Real => {
                if !value.0.denom().is_positive() {
                    return Err("SOS malformed source rational".to_string());
                }
                if value.0.numer().bits() > 1_024 || value.0.denom().bits() > 1_024 {
                    return Err(WORK_METER_RESOURCE_LIMIT.to_string());
                }
            }
            TermData::Const(Constant::Int(value)) if source_sort == &Sort::Int => {
                if value.bits() > 1_024 {
                    return Err(WORK_METER_RESOURCE_LIMIT.to_string());
                }
            }
            TermData::Var(..) => {}
            TermData::App(Symbol::Named(name), args)
                if !args.is_empty() && matches!(name.as_str(), "+" | "-" | "*") =>
            {
                meter.charge_nodes(args.len())?;
                pending
                    .try_reserve(args.len())
                    .map_err(|_| WORK_METER_RESOURCE_LIMIT.to_string())?;
                pending.extend(args.iter().rev().map(|&arg| (arg, depth + 1)));
            }
            _ => return Err("SOS unsupported or ill-typed numeric source".to_string()),
        }
    }
    Ok(())
}
