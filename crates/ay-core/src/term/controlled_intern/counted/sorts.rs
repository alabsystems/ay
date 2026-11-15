// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

// Same native owned-Sort copy safety as term/snapshot.rs, not a query cap.
const MAX_COPY_DEPTH: usize = 256;

pub(super) fn visit(
    sort: &Sort,
    owner: &dyn TermConstructionAdmission,
    usage: PayloadUse,
) -> Result<bool> {
    owner.admit(1, 0)?;
    match sort {
        Sort::Bool => return Ok(false),
        Sort::FiniteField(_) => return Ok(true),
        Sort::BitVec(width) => {
            return if width.width > 0 {
                Ok(false)
            } else {
                Err(CountedTermError::InvalidInput)
            }
        }
        Sort::FloatingPoint(eb, sb) => return field_sort(*eb, *sb).map(|()| false),
        Sort::Array(_) => {}
        _ => return Err(CountedTermError::Unsupported),
    }
    let mut stack = Vec::new();
    let mut has_field = false;
    storage::reserve(&mut stack, 1, owner)?;
    stack.push((sort, 0usize));
    while let Some((sort, depth)) = stack.pop() {
        owner.admit(1, 0)?;
        if depth > MAX_COPY_DEPTH {
            return Err(CountedTermError::Unsupported);
        }
        match sort {
            Sort::Bool => {}
            Sort::FiniteField(_) => has_field = true,
            Sort::BitVec(width) if width.width > 0 => {}
            Sort::BitVec(_) => return Err(CountedTermError::InvalidInput),
            Sort::FloatingPoint(eb, sb) => field_sort(*eb, *sb)?,
            Sort::Array(array) => {
                owner.admit(1, usage.bytes(size_of::<crate::sort::ArraySort>()))?;
                storage::reserve(&mut stack, 2, owner)?;
                stack.push((&array.index_sort, depth + 1));
                stack.push((&array.element_sort, depth + 1));
            }
            _ => return Err(CountedTermError::Unsupported),
        }
    }
    Ok(has_field)
}

pub(super) fn copy(sort: &Sort, owner: &dyn TermConstructionAdmission) -> Result<Sort> {
    copy_with_presence(sort, owner).map(|(sort, _)| sort)
}

pub(super) fn copy_with_presence(
    sort: &Sort,
    owner: &dyn TermConstructionAdmission,
) -> Result<(Sort, bool)> {
    let presence = visit(sort, owner, PayloadUse::Copy)?;
    Ok((sort.clone(), presence))
}

pub(super) fn equal(
    left: &Sort,
    right: &Sort,
    owner: &dyn TermConstructionAdmission,
) -> Result<bool> {
    visit(left, owner, PayloadUse::Inspect)?;
    visit(right, owner, PayloadUse::Inspect)?;
    Ok(left == right)
}

// Representation checks only. Solver source namespaces remain caller-owned.
fn field_sort(eb: u32, sb: u32) -> Result<()> {
    if eb < 2 || sb < 2 || eb.checked_add(sb).is_none() {
        Err(CountedTermError::InvalidInput)
    } else {
        Ok(())
    }
}
