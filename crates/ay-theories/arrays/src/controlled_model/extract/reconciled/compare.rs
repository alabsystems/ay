// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn maps(
    left: &HashMap<TermId, ArrayInterpretation>,
    right: &HashMap<TermId, ArrayInterpretation>,
    work: &mut WorkBudget<'_>,
) -> Result<bool, QueryError> {
    work.charge(16)?;
    if left.len() != right.len() {
        return Ok(false);
    }
    owned::scan_table::<(TermId, ArrayInterpretation)>(left.allocation_size(), work)?;
    for (&term, left) in left {
        let Some(right) = scan::lookup(right, term, work)? else {
            return Ok(false);
        };
        if !interpretations(left, right, work)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn interpretations(
    left: &ArrayInterpretation,
    right: &ArrayInterpretation,
    work: &mut WorkBudget<'_>,
) -> Result<bool, QueryError> {
    work.charge(32)?;
    if left.stores.len() != right.stores.len()
        || !sorts(left.index_sort.as_ref(), right.index_sort.as_ref(), work)?
        || !sorts(
            left.element_sort.as_ref(),
            right.element_sort.as_ref(),
            work,
        )?
        || !texts(left.default.as_deref(), right.default.as_deref(), work)?
    {
        return Ok(false);
    }
    for ((lk, lv), (rk, rv)) in left.stores.iter().zip(&right.stores) {
        work.charge(16)?;
        if !storage::equal(lk, rk, work)? || !storage::equal(lv, rv, work)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn texts(
    left: Option<&str>,
    right: Option<&str>,
    work: &mut WorkBudget<'_>,
) -> Result<bool, QueryError> {
    work.charge(16)?;
    match (left, right) {
        (None, None) => Ok(true),
        (Some(left), Some(right)) => storage::equal(left, right, work),
        _ => Ok(false),
    }
}

fn sorts(
    left: Option<&Sort>,
    right: Option<&Sort>,
    work: &mut WorkBudget<'_>,
) -> Result<bool, QueryError> {
    work.charge(16)?;
    match (left, right) {
        (None, None) | (Some(Sort::Bool), Some(Sort::Bool)) => Ok(true),
        (Some(Sort::BitVec(left)), Some(Sort::BitVec(right))) => Ok(left.width == right.width),
        (None, Some(_))
        | (Some(_), None)
        | (Some(Sort::Bool), Some(Sort::BitVec(_)))
        | (Some(Sort::BitVec(_)), Some(Sort::Bool)) => Ok(false),
        _ => Err(work.refuse_exhaustion()),
    }
}
