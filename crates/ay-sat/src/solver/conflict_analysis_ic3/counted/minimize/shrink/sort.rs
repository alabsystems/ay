// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Williams' in-place heapsort, CACM 1964 Algorithm 232. Unique real trail
//! positions give the same total order as ordinary (level desc, trail desc).

use super::*;

type Entry = (u32, usize, usize);

pub(super) fn by_block(entries: &mut [Entry], owner: &CountedAdmission) -> AdmissionResult<()> {
    owner.admit(1, 0)?;
    let len = entries.len();
    for root in (0..len / 2).rev() {
        sift(entries, root, len, owner)?;
    }
    for end in (1..len).rev() {
        owner.admit(1, 0)?;
        entries.swap(0, end);
        sift(entries, 0, end, owner)?;
    }
    Ok(())
}

fn less(a: Entry, b: Entry) -> bool {
    (a.0, a.1) > (b.0, b.1)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::counted_storage::test_owner;

    #[test]
    fn block_order_matches_ordinary_for_small_and_large_sorts_and_every_work_cut() {
        for len in [0, 1, 2, 7, 33, 65] {
            let input: Vec<_> = (0..len)
                .map(|index| ((index % 5) as u32, (index * 7) % 67, index))
                .collect();
            let mut expected = input.clone();
            expected.sort_unstable_by(|a, b| b.0.cmp(&a.0).then_with(|| b.1.cmp(&a.1)));
            let owner = test_owner(1_000_000, 0);
            let mut actual = input.clone();
            by_block(&mut actual, &owner).unwrap();
            assert_eq!(actual, expected);
            let total = owner.usage().unwrap().work_admitted;
            for work in 0..total {
                let owner = test_owner(work, 0);
                assert_eq!(
                    by_block(&mut input.clone(), &owner),
                    Err(CountedAdmissionError::WorkExhausted)
                );
            }
        }
    }
}

fn sift(
    entries: &mut [Entry],
    mut root: usize,
    end: usize,
    owner: &CountedAdmission,
) -> AdmissionResult<()> {
    loop {
        owner.admit(1, 0)?;
        let Some(mut child) = root
            .checked_mul(2)
            .and_then(|n| n.checked_add(1))
            .filter(|child| *child < end)
        else {
            return Ok(());
        };
        if child + 1 < end {
            owner.admit(1, 0)?;
            if less(entries[child], entries[child + 1]) {
                child += 1;
            }
        }
        owner.admit(1, 0)?;
        if !less(entries[root], entries[child]) {
            return Ok(());
        }
        owner.admit(1, 0)?;
        entries.swap(root, child);
        root = child;
    }
}
