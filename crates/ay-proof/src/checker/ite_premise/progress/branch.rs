// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn flatten(
    term: TermId,
    out: &mut Vec<TermId>,
    depth: usize,
    meter: &mut Meter<'_, '_>,
) -> Result<(), ProofCheckError> {
    let data = meter.term(term)?;
    if depth < 8 {
        if let TermData::App(Symbol::Named(name), args) = data {
            if meter.named(name, "or")? {
                // Repeated edges are intentionally unfolded, not visited-set
                // deduplicated. Each visit/push is independently metered.
                for &arg in args {
                    flatten(arg, out, depth + 1, meter)?;
                }
                return Ok(());
            }
        }
    }
    meter.push(out, term)
}

pub(super) fn matches(
    literals: &[TermId],
    conjuncts: &[TermId],
    positive: Option<TermId>,
    branch: TermId,
    meter: &mut Meter<'_, '_>,
) -> Result<bool, ProofCheckError> {
    let mut expected = Vec::new();
    if let Some(positive) = positive {
        meter.push(&mut expected, positive)?;
    }
    flatten(branch, &mut expected, 0, meter)?;
    let mut expected_used = meter.flags(expected.len())?;
    let mut conjunct_used = meter.flags(conjuncts.len())?;
    for &literal in literals {
        meter.charge(1, 0)?;
        if consume(literal, &expected, &mut expected_used, meter)? {
            continue;
        }
        if let TermData::Not(inner) = meter.term(literal)? {
            meter.root(*inner)?;
            if consume(*inner, conjuncts, &mut conjunct_used, meter)? {
                continue;
            }
        }
        return Ok(false);
    }
    covered(
        literals,
        &expected,
        &expected_used,
        conjuncts,
        &conjunct_used,
        meter,
    )
}

fn consume(
    literal: TermId,
    expected: &[TermId],
    used: &mut [bool],
    meter: &mut Meter<'_, '_>,
) -> Result<bool, ProofCheckError> {
    for (&candidate, slot) in expected.iter().zip(used.iter_mut()) {
        meter.charge(1, 0)?;
        if !*slot && candidate == literal {
            *slot = true;
            return Ok(true);
        }
    }
    Ok(false)
}

fn covered(
    literals: &[TermId],
    expected: &[TermId],
    expected_used: &[bool],
    conjuncts: &[TermId],
    conjunct_used: &[bool],
    meter: &mut Meter<'_, '_>,
) -> Result<bool, ProofCheckError> {
    // Preserve legacy set coverage AFTER slot-by-slot consumption. In
    // particular, duplicated expected slots may be represented once; surplus
    // duplicated assumed literals need not be accepted.
    for (&candidate, &used) in expected.iter().zip(expected_used) {
        meter.charge(1, 0)?;
        if !used && !contains(literals, candidate, meter)? {
            return Ok(false);
        }
    }
    for (&conjunct, &used) in conjuncts.iter().zip(conjunct_used) {
        meter.charge(1, 0)?;
        if !used && !contains_negation(literals, conjunct, meter)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn contains(
    literals: &[TermId],
    candidate: TermId,
    meter: &mut Meter<'_, '_>,
) -> Result<bool, ProofCheckError> {
    for &literal in literals {
        meter.charge(1, 0)?;
        if literal == candidate {
            return Ok(true);
        }
    }
    Ok(false)
}

fn contains_negation(
    literals: &[TermId],
    conjunct: TermId,
    meter: &mut Meter<'_, '_>,
) -> Result<bool, ProofCheckError> {
    for &literal in literals {
        if let TermData::Not(inner) = meter.term(literal)? {
            meter.root(*inner)?;
            meter.charge(1, 0)?;
            if *inner == conjunct {
                return Ok(true);
            }
        }
    }
    Ok(false)
}
