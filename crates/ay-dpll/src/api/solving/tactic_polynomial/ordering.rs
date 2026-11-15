// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! In-place heapsort: no hidden sort allocation or uninterruptible comparator.
use super::*;
pub(super) fn sort<T>(
    values: &mut [T],
    owner: &dyn TermConstructionAdmission,
    compare: &mut impl FnMut(&T, &T) -> Result<Ordering, TacticFailure>,
) -> Result<(), TacticFailure> {
    fn sift<T>(
        values: &mut [T],
        mut root: usize,
        end: usize,
        owner: &dyn TermConstructionAdmission,
        compare: &mut impl FnMut(&T, &T) -> Result<Ordering, TacticFailure>,
    ) -> Result<(), TacticFailure> {
        loop {
            pay(owner, 1)?;
            let Some(left) = root
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .filter(|n| *n < end)
            else {
                return Ok(());
            };
            let mut largest = left;
            if left + 1 < end && compare(&values[left], &values[left + 1])? == Ordering::Less {
                largest = left + 1
            }
            if compare(&values[root], &values[largest])? != Ordering::Less {
                return Ok(());
            }
            pay(
                owner,
                std::mem::size_of::<T>().checked_mul(2).ok_or_else(fail)?,
            )?;
            values.swap(root, largest);
            root = largest;
        }
    }
    for root in (0..values.len() / 2).rev() {
        sift(values, root, values.len(), owner, compare)?;
    }
    for end in (1..values.len()).rev() {
        pay(
            owner,
            std::mem::size_of::<T>().checked_mul(2).ok_or_else(fail)?,
        )?;
        values.swap(0, end);
        sift(values, 0, end, owner, compare)?;
    }
    owner.check().map_err(|_| fail())
}
