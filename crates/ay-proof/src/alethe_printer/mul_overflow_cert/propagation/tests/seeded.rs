// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;

#[test]
fn monotone_children_skip_unchanged_rows_but_keep_exact_models_and_reasons() {
    let groups = 64u32;
    let db: Vec<_> = (0..groups)
        .flat_map(|group| {
            let a = 2 * group + 1;
            [vec![(a, true), (a, false)], vec![(a, false), (a + 1, true)]]
        })
        .collect();
    let fixed = HashMap::default();
    let old_calls = Cell::new(0usize);
    let mut old_callback = || {
        old_calls.set(old_calls.get() + 1);
        true
    };
    let old_owner = EmissionProgress::with_caller(&mut old_callback);
    let (old, old_trace) =
        measured(|| legacy_localsat::solve(&db, &fixed, &mut 10_000_000, &old_owner).unwrap());
    let new_calls = Cell::new(0usize);
    let mut new_callback = || {
        new_calls.set(new_calls.get() + 1);
        true
    };
    let new_owner = EmissionProgress::with_caller(&mut new_callback);
    let (new, new_trace) =
        measured(|| localsat::solve(&db, &fixed, &mut 10_000_000, &new_owner).unwrap());
    assert_eq!(new, old);
    assert_eq!(new.as_ref().unwrap().len(), 2 * groups as usize);
    assert!(new.as_ref().unwrap().values().all(|&value| value));
    assert_eq!(new_trace.assignments, old_trace.assignments);
    assert_eq!(new_trace.assignments.len(), groups as usize);
    assert_eq!(
        old_trace.visits,
        (2 * groups + 4 * groups * groups) as usize
    );
    assert_eq!(new_trace.visits, 5 * groups as usize);
    assert!(
        new_calls.get() < old_calls.get(),
        "actual observed work must fall"
    );
    assert!(
        new_calls.get() > new_trace.visits,
        "visited work remains observed"
    );
}

fn next(state: &mut u64) -> u64 {
    *state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
    *state >> 17
}

#[test]
fn seeded_branch_trees_keep_frozen_legacy_models_and_reason_order_on_generated_cnf() {
    let mut random = 0x9485_137d_e471_30abu64;
    for sample in 0..768 {
        let atoms = 3 + next(&mut random) % 6;
        let count = 3 + next(&mut random) % 18;
        let mut db: Vec<localsat::Clause> = (0..count)
            .map(|_| {
                let width = 1 + next(&mut random) % 5;
                (0..width)
                    .map(|_| {
                        let atom = 1 + next(&mut random) % atoms;
                        (atom as T, next(&mut random) & 1 != 0)
                    })
                    .collect()
            })
            .collect();
        // Keep repeated/opposite occurrences as authored, including a branch
        // forced by a tautology whose open occurrences are not deduplicated.
        db.insert(0, vec![(1, true), (1, false), (1, true)]);
        let mut fixed = HashMap::default();
        for atom in 1..=atoms {
            if next(&mut random) % 5 == 0 {
                fixed.insert(atom as T, next(&mut random) & 1 != 0);
            }
        }
        compare_localsat(&db, &fixed);
        db.reverse();
        compare_localsat(&db, &fixed);
        if sample % 7 == 0 {
            db.insert(db.len() / 2, vec![]);
            compare_localsat(&db, &fixed);
        }
    }
}

#[test]
fn ternary_cube_searches_and_duplicate_rows_keep_legacy_branch_conflicts() {
    for excluded in 0..=8 {
        let mut db: Vec<localsat::Clause> = (0..8)
            .filter(|&mask| mask != excluded)
            .map(|mask| (1..=3).map(|a| (a, mask & (1 << (a - 1)) != 0)).collect())
            .collect();
        db.insert(1, vec![(1, true), (1, false), (1, false)]);
        db.insert(3, vec![(2, false), (2, false), (3, true), (3, true)]);
        for shift in 0..db.len() {
            let mut ordered = db.clone();
            ordered.rotate_left(shift);
            compare_localsat(&ordered, &HashMap::default());
            for atom in 1..=3 {
                for value in [false, true] {
                    compare_localsat(&ordered, &HashMap::from_iter([(atom, value)]));
                }
            }
        }
    }
}
