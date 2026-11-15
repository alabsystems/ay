// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Positive RUP to binary resolution by reverse unit propagation.

use super::*;

fn copy(source: &[Literal], meter: &mut CheckedRefutationMeter) -> Option<Vec<Literal>> {
    let mut result = reserve(source.len(), meter)?;
    result.extend_from_slice(source);
    Some(result)
}

pub(super) fn propagate(
    target: &[Literal],
    hints: &[u64],
    clauses: &[&[Literal]],
    num_vars: usize,
    meter: &mut CheckedRefutationMeter,
) -> Option<(Vec<Option<Literal>>, usize)> {
    let mut values = reserve(num_vars, meter)?;
    values.resize(num_vars, None);
    for &lit in target {
        meter.charge(1, 0).ok()?;
        let slot = values.get_mut(lit.variable().index())?;
        let value = !lit.is_positive();
        if slot.is_some_and(|old| old != value) {
            return None;
        }
        *slot = Some(value);
    }
    let mut units = reserve(hints.len(), meter)?;
    for &hint in hints {
        meter.charge(1, 0).ok()?;
        let clause = clauses.get(usize::try_from(hint).ok()?)?;
        let mut unit = None;
        let mut multiple = false;
        let mut satisfied = false;
        for &lit in *clause {
            meter.charge(1, 0).ok()?;
            match values.get(lit.variable().index())? {
                Some(value) if *value == lit.is_positive() => {
                    satisfied = true;
                    break;
                }
                Some(_) => {}
                None => {
                    if unit.is_some_and(|old| old != lit) {
                        multiple = true;
                    }
                    unit = Some(lit);
                }
            }
        }
        if satisfied {
            units.push(None);
        } else if multiple {
            return None;
        } else if let Some(lit) = unit {
            *values.get_mut(lit.variable().index())? = Some(lit.is_positive());
            units.push(Some(lit));
        } else {
            let conflict = units.len();
            units.push(None);
            return Some((units, conflict));
        }
    }
    None
}

fn resolve(
    left: &[Literal],
    right: &[Literal],
    unit: Literal,
    meter: &mut CheckedRefutationMeter,
) -> Option<Vec<Literal>> {
    meter
        .charge(left.len().checked_add(right.len())?.checked_mul(2)?, 0)
        .ok()?;
    if !left.contains(&unit.negated())
        || !right.contains(&unit)
        || left.contains(&unit)
        || right.contains(&unit.negated())
    {
        return None;
    }
    let size = left.len().checked_add(right.len())?;
    let mut result = reserve(size, meter)?;
    for &lit in left.iter().chain(right) {
        meter
            .charge(result.len().checked_mul(2)?.checked_add(1)?, 0)
            .ok()?;
        if lit.variable() == unit.variable() {
            continue;
        }
        if result.contains(&lit.negated()) {
            return None;
        }
        if !result.contains(&lit) {
            if result.len() >= MAX_LITERALS {
                return None;
            }
            result.push(lit);
        }
    }
    Some(result)
}

pub(super) fn expand(
    row: &ay_sat::RupStep,
    clauses: &[&[Literal]],
    ids: &[Option<ProofId>],
    num_vars: usize,
    proof: &mut Proof,
    var_to_term: &HashMap<u32, TermId>,
    terms: &mut TermStore,
    meter: &mut CheckedRefutationMeter,
) -> Option<ProofId> {
    let target = *clauses.get(usize::try_from(row.id).ok()?)?;
    let (units, conflict) = propagate(target, &row.rup_hints, clauses, num_vars, meter)?;
    let conflicting_id = usize::try_from(*row.rup_hints.get(conflict)?).ok()?;
    let mut current = ids.get(conflicting_id).copied().flatten()?;
    let mut resolvent = copy(clauses.get(conflicting_id)?, meter)?;
    for index in (0..conflict).rev() {
        meter.charge(1, 0).ok()?;
        let Some(unit) = units[index] else { continue };
        meter.charge(resolvent.len(), 0).ok()?;
        if !resolvent.contains(&unit.negated()) {
            continue;
        }
        let hint = usize::try_from(row.rup_hints[index]).ok()?;
        let right = ids.get(hint).copied().flatten()?;
        resolvent = resolve(&resolvent, clauses.get(hint)?, unit, meter)?;
        let clause =
            translate_sat_clause(row.id, &resolvent, var_to_term, &[], terms, meter).ok()?;
        let pivot = *var_to_term.get(&(unit.variable().index() as u32))?;
        if proof.steps.len() >= MAX_STEPS || proof.steps.len() == proof.steps.capacity() {
            return None;
        }
        meter.charge(1, 0).ok()?;
        current = proof.add_resolution(clause, pivot, current, right);
    }
    // Subsuming RUP chains need a separately checked weakening. Until that is
    // supported, require set equality; never claim the wider target by fiat.
    meter
        .charge(
            resolvent.len().checked_mul(target.len())?.checked_mul(2)?,
            0,
        )
        .ok()?;
    if !resolvent.iter().all(|lit| target.contains(lit))
        || !target.iter().all(|lit| resolvent.contains(lit))
    {
        return None;
    }
    Some(current)
}
