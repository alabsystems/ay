// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{Sort, TermStore};

fn input(polarities: &[i8]) -> (TseitinResult, Vec<i8>, Vec<Application>, [usize; 3]) {
    let mut terms = TermStore::new();
    let mut cnf = TseitinResult::new(
        Vec::new(),
        Default::default(),
        Default::default(),
        0,
        polarities.len() as u32,
    );
    let mut values = vec![0];
    let mut counts = [0; 3];
    let mut group = Vec::new();
    for (index, &value) in polarities.iter().enumerate() {
        let term = terms.mk_var(&format!("g{index}"), Sort::Bool);
        cnf.term_to_var.insert(term, index as u32 + 1);
        cnf.var_to_term.insert(index as u32 + 1, term);
        values.push(value);
        counts[(value + 1) as usize] += 1;
        group.push((term, Vec::new()));
    }
    (cnf, values, group, counts)
}

#[test]
fn residual_count_and_order_match_independent_all_pairs_including_unknowns() {
    for signs in [&[1, 1, -1, 0, 0][..], &[-1, -1, 1, 0, -1], &[0, 0]] {
        let (cnf, values, group, counts) = input(signs);
        let expected: Vec<_> = (0..signs.len())
            .flat_map(|i| {
                ((i + 1)..signs.len()).filter_map(move |j| {
                    (!(signs[i] != 0 && signs[i] == signs[j])).then_some((i, j))
                })
            })
            .collect();
        assert_eq!(count(counts), Some(expected.len()));
        let actual = pairs(&cnf, &values, &group, counts, &mut Work(4096), &mut || {
            Ok::<_, ()>(())
        })
        .unwrap()
        .unwrap();
        assert_eq!(actual, expected);
    }
    assert_eq!(count([0, 65, 0]), Some(2080));
    assert!(count([usize::MAX, 1, 1]).is_none());
    assert!(count([0, usize::MAX, 0]).is_none());
}

#[test]
fn residual_exact_work_shared_exhaustion_and_zero_pair_fastpath() {
    let mut signs = vec![1; 65];
    signs[64] = -1;
    let (cnf, values, group, counts) = input(&signs);
    // Independent scan count plus actual retained capacity, not an assumption
    // that the allocator returns exactly the requested 64 pair slots.
    let mut baseline = Work(4096);
    let admitted = pairs(&cnf, &values, &group, counts, &mut baseline, &mut || {
        Ok::<_, ()>(())
    })
    .unwrap()
    .unwrap();
    let cost = 65 * 64 / 2 + 2 * admitted.capacity();
    assert_eq!(4096 - baseline.0, cost);
    let mut work = Work(cost);
    assert_eq!(
        pairs(
            &cnf,
            &values,
            &group,
            counts,
            &mut work,
            &mut || Ok::<_, ()>(())
        )
        .unwrap()
        .unwrap()
        .len(),
        64
    );
    assert_eq!(work.0, 0);
    assert!(pairs(
        &cnf,
        &values,
        &group,
        counts,
        &mut work,
        &mut || Ok::<_, ()>(())
    )
    .unwrap()
    .is_none());
    assert!(pairs(
        &cnf,
        &values,
        &group,
        counts,
        &mut Work(cost - 1),
        &mut || Ok::<_, ()>(())
    )
    .unwrap()
    .is_none());

    let (cnf, values, group, counts) = input(&vec![1; 256]);
    let mut polls = 0;
    assert!(pairs(&cnf, &values, &group, counts, &mut Work(0), &mut || {
        polls += 1;
        Ok::<_, ()>(())
    })
    .unwrap()
    .unwrap()
    .is_empty());
    assert_eq!(
        polls, 0,
        "parent retains entry/final controls; uniform pair phase does no work"
    );

    let (cnf, values, group, counts) = input(&vec![0; 65]);
    assert!(pairs(
        &cnf,
        &values,
        &group,
        counts,
        &mut Work(4096),
        &mut || Ok::<_, ()>(())
    )
    .unwrap()
    .is_none());
    // An admissible residual count alone is insufficient: enumeration is metered.
    let mut signs = vec![1; 256];
    signs[255] = -1;
    let (cnf, values, group, counts) = input(&signs);
    assert_eq!(count(counts), Some(255));
    assert!(pairs(
        &cnf,
        &values,
        &group,
        counts,
        &mut Work(4096),
        &mut || Ok::<_, ()>(())
    )
    .unwrap()
    .is_none());
}

#[test]
fn every_residual_stop_returns_error_without_a_partial_pair_plan_or_repoll() {
    let (cnf, values, group, counts) = input(&[1, 1, -1, 0, 0]);
    let mut total = 0;
    assert!(
        pairs(&cnf, &values, &group, counts, &mut Work(4096), &mut || {
            total += 1;
            Ok::<_, ()>(())
        })
        .unwrap()
        .is_some()
    );
    for cutoff in 1..=total {
        let mut polls = 0;
        let result = pairs(&cnf, &values, &group, counts, &mut Work(4096), &mut || {
            polls += 1;
            if polls == cutoff {
                Err(())
            } else {
                Ok(())
            }
        });
        assert!(result.is_err(), "stop{cutoff}");
        assert_eq!(
            polls, cutoff,
            "transient stop cannot recover within this attempt"
        );
    }
}
