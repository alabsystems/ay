// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Williams' in-place heapsort (CACM 1964, Algorithm 232), admitting actual
//! comparisons and swaps. Valid trail positions uniquely order learned vars,
//! so the result equals the ordinary unstable-by-trail ordering exactly.

use super::*;

pub(super) fn by_trail(
    values: &mut [Literal],
    data: &[VarData],
    owner: &CountedAdmission,
) -> AdmissionResult<()> {
    owner.admit(1, 0)?;
    let len = values.len();
    for root in (0..len / 2).rev() {
        sift(values, data, root, len, owner)?;
    }
    for end in (1..len).rev() {
        owner.admit(1, 0)?;
        values.swap(0, end);
        sift(values, data, 0, end, owner)?;
    }
    Ok(())
}

fn sift(
    values: &mut [Literal],
    data: &[VarData],
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
            if data[values[child].variable().index()].trail_pos
                < data[values[child + 1].variable().index()].trail_pos
            {
                child += 1;
            }
        }
        owner.admit(1, 0)?;
        if data[values[root].variable().index()].trail_pos
            >= data[values[child].variable().index()].trail_pos
        {
            return Ok(());
        }
        owner.admit(1, 0)?;
        values.swap(root, child);
        root = child;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::counted_storage::test_owner;

    #[test]
    fn real_heapsort_matches_std_order_and_each_short_work_cut_is_terminal() {
        let data: Vec<_> = (0..19)
            .map(|index| VarData {
                trail_pos: ((index * 7) % 19) as u32,
                ..VarData::UNASSIGNED
            })
            .collect();
        for len in [0, 1, 2, 7, 19] {
            let input: Vec<_> = (0..len)
                .rev()
                .map(|index| Literal::positive(Variable::new(index)))
                .collect();
            let mut expected = input.clone();
            expected.sort_unstable_by_key(|lit| data[lit.variable().index()].trail_pos);
            let owner = test_owner(10_000_000, 0);
            let mut actual = input.clone();
            by_trail(&mut actual, &data, &owner).unwrap();
            assert_eq!(actual, expected);
            let total = owner.usage().unwrap().work_admitted;
            for work in 0..=total {
                let owner = test_owner(work, 0);
                let mut actual = input.clone();
                let result = by_trail(&mut actual, &data, &owner);
                if work == total {
                    assert_eq!(result, Ok(()));
                    assert_eq!(actual, expected);
                } else {
                    assert_eq!(result, Err(CountedAdmissionError::WorkExhausted));
                    assert_eq!(owner.check(), Err(CountedAdmissionError::WorkExhausted));
                }
            }
        }
    }
}
