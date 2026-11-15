// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn collect(
    literals: &[Lit],
    budget: &mut ReplayBudget<'_, '_>,
) -> Result<BTreeSet<Lit>, BvBlastValidateError> {
    let mut result = BTreeSet::new();
    for &literal in literals {
        budget.poll()?;
        result.insert(literal);
    }
    Ok(result)
}

pub(super) fn equal(
    left: &BTreeSet<Lit>,
    right: &BTreeSet<Lit>,
    budget: &mut ReplayBudget<'_, '_>,
) -> Result<bool, BvBlastValidateError> {
    budget.poll()?;
    if left.len() != right.len() {
        return Ok(false);
    }
    for (left, right) in left.iter().zip(right) {
        budget.poll()?;
        if left != right {
            return Ok(false);
        }
    }
    Ok(true)
}

pub(super) fn clause_eq(
    left: &[Lit],
    right: &[Lit],
    budget: &mut ReplayBudget<'_, '_>,
) -> Result<bool, BvBlastValidateError> {
    let left = collect(left, budget)?;
    let right = collect(right, budget)?;
    equal(&left, &right, budget)
}

fn contains(
    literals: &[Lit],
    literal: Lit,
    budget: &mut ReplayBudget<'_, '_>,
) -> Result<bool, BvBlastValidateError> {
    for &candidate in literals {
        budget.poll()?;
        if candidate == literal {
            return Ok(true);
        }
    }
    Ok(false)
}

/// The same pivot policy and first-occurrence output order as the old replay.
/// Individual BTree operations remain opaque; every input edge is polled.
pub(super) fn resolve(
    a: &[Lit],
    b: &[Lit],
    pivot: u32,
    budget: &mut ReplayBudget<'_, '_>,
) -> Result<Option<Vec<Lit>>, BvBlastValidateError> {
    let a_has_pos = contains(a, Lit::pos(pivot), budget)?;
    let a_has_neg = contains(a, Lit::neg(pivot), budget)?;
    let b_has_pos = contains(b, Lit::pos(pivot), budget)?;
    let b_has_neg = contains(b, Lit::neg(pivot), budget)?;
    let valid = (a_has_pos && b_has_neg && !a_has_neg && !b_has_pos)
        || (a_has_neg && b_has_pos && !a_has_pos && !b_has_neg);
    if !valid {
        return Ok(None);
    }
    let mut out = Vec::new();
    let mut seen = BTreeSet::new();
    for &literal in a.iter().chain(b) {
        budget.poll()?;
        if literal.var == pivot {
            continue;
        }
        if seen.contains(&literal.negated()) {
            return Ok(None);
        }
        if seen.insert(literal) {
            out.push(literal);
        }
    }
    Ok(Some(out))
}
