// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;

mod resources;

type Model = HashMap<T, bool>;

fn all_models(db: &[Clause], fixed: &Model, projection: &[T], atoms: T) -> HashSet<Vec<bool>> {
    (0..1usize << atoms)
        .filter(|bits| {
            fixed
                .iter()
                .all(|(&a, &v)| ((bits >> (a - 1)) & 1 != 0) == v)
                && db.iter().all(|clause| {
                    clause
                        .iter()
                        .any(|&(a, v)| ((bits >> (a - 1)) & 1 != 0) == v)
                })
        })
        .map(|bits| {
            projection
                .iter()
                .map(|&a| (bits >> (a - 1)) & 1 != 0)
                .collect()
        })
        .collect()
}

fn old_project(
    db: &[Clause],
    fixed: &Model,
    projection: &[T],
    budget: &mut u64,
    owner: &EmissionProgress<'_>,
) -> Option<HashSet<Vec<bool>>> {
    let mut db = db.to_vec();
    let mut solver = Projection::new(&mut db, fixed, budget, owner)?;
    let mut found = HashSet::default();
    for &atom in projection {
        solver.append([(atom, true), (atom, false)].into_iter())?;
    }
    while let Some(model) = solver.solve()? {
        let state: Vec<_> = projection
            .iter()
            .map(|atom| model.get(atom).copied().unwrap_or(false))
            .collect();
        if projection.is_empty() {
            found.insert(state);
            break;
        }
        solver.append(projection.iter().zip(&state).map(|(&a, &v)| (a, !v)))?;
        found.insert(state);
    }
    drop(solver);
    owner.poll().then_some(found)
}

fn compare(db: &[Clause], fixed: &Model, projection: &[T], atoms: T) {
    let owner = EmissionProgress::default();
    let expected = all_models(db, fixed, projection, atoms);
    assert_eq!(
        project(db, fixed, projection, &mut 1_000_000, &owner),
        Some(expected.clone()),
        "db={db:?}, fixed={fixed:?}, projection={projection:?}"
    );
    assert_eq!(
        old_project(db, fixed, projection, &mut 1_000_000, &owner),
        Some(expected)
    );
}

#[test]
fn projection_tree_matches_independent_truth_tables_exhaustively() {
    let literals = [(1, false), (1, true), (2, false), (2, true)];
    let mut clauses = vec![vec![]];
    for a in literals {
        clauses.push(vec![a]);
        for b in literals {
            clauses.push(vec![a, b]);
        }
    }
    for a in &clauses {
        for b in &clauses {
            let db = [a.clone(), b.clone()];
            for fixed_value in [None, Some(false), Some(true)] {
                let fixed = fixed_value.map(|v| (1, v)).into_iter().collect();
                for projection in [&[][..], &[1][..], &[2, 1][..], &[2, 2, 3][..]] {
                    compare(&db, &fixed, projection, 3);
                }
            }
        }
    }
}

fn random(state: &mut u64) -> u64 {
    *state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
    *state >> 17
}

#[test]
fn hidden_atoms_and_projected_duplicates_match_generated_cnf_truth_tables() {
    let mut seed = 0x4356_271a_8824_febdu64;
    for sample in 0..512 {
        let mut db: Vec<Clause> = (0..1 + random(&mut seed) % 12)
            .map(|_| {
                (0..1 + random(&mut seed) % 4)
                    .map(|_| ((1 + random(&mut seed) % 5) as T, random(&mut seed) & 1 != 0))
                    .collect()
            })
            .collect();
        if sample % 7 == 0 {
            db.push(Vec::new());
        }
        let fixed = [(1, sample % 2 == 0), (6, sample % 3 == 0)]
            .into_iter()
            .collect();
        compare(&db, &fixed, &[6, 2, 2, 4], 6);
        compare(&db, &Model::default(), &[], 6);
    }
}

#[test]
fn a_complete_projected_assignment_still_needs_a_real_existential_model() {
    // No root unit or empty clause. The existential search must branch to
    // establish that the hidden three-atom cube has no satisfying extension.
    let impossible: Vec<Clause> = (0..8)
        .map(|mask| (1..=3).map(|a| (a, mask & (1 << (a - 1)) != 0)).collect())
        .collect();
    for projection in [&[][..], &[4][..], &[4, 4][..]] {
        compare(&impossible, &Model::default(), projection, 4);
        compare(&impossible, &Model::from_iter([(4, true)]), projection, 4);
    }
    let mut possible = impossible;
    possible.pop();
    compare(&possible, &Model::default(), &[4, 4], 4);
}

#[test]
fn one_tree_has_no_blocking_rows_or_cross_attempt_assignment_cache() {
    let owner = EmissionProgress::default();
    let mut db = vec![vec![(1, true), (2, true)]];
    let original = db.clone();
    let first = project(&db, &Model::default(), &[1, 2, 3], &mut 1_000_000, &owner).unwrap();
    assert_eq!(first.len(), 6);
    assert_eq!(db, original);
    assert_eq!(
        project(
            &db,
            &Model::from_iter([(1, false)]),
            &[1, 2],
            &mut 1_000_000,
            &owner
        ),
        Some(HashSet::from_iter([vec![false, true]]))
    );
    db.push(Vec::new());
    assert_eq!(
        project(&db, &Model::default(), &[1, 2], &mut 1_000_000, &owner),
        Some(HashSet::default())
    );
    let empty = Vec::new();
    assert_eq!(
        project(&empty, &Model::default(), &[], &mut 1_000_000, &owner),
        Some(HashSet::from_iter([vec![]]))
    );
}

#[test]
fn dense_projection_removes_restarts_and_reduces_observed_actual_work() {
    let db = vec![vec![(7, true)]];
    let fixed = Model::default();
    let projection: Vec<T> = (1..=6).collect();
    let old_calls = Cell::new(0usize);
    let mut old_callback = || {
        old_calls.set(old_calls.get() + 1);
        true
    };
    let mut old_budget = 10_000_000;
    let old = old_project(
        &db,
        &fixed,
        &projection,
        &mut old_budget,
        &EmissionProgress::with_caller(&mut old_callback),
    )
    .unwrap();
    let new_calls = Cell::new(0usize);
    let mut new_callback = || {
        new_calls.set(new_calls.get() + 1);
        true
    };
    let mut new_budget = 10_000_000;
    let new = project(
        &db,
        &fixed,
        &projection,
        &mut new_budget,
        &EmissionProgress::with_caller(&mut new_callback),
    )
    .unwrap();
    assert_eq!(new, old);
    assert_eq!(new.len(), 64);
    assert!(new_calls.get() < old_calls.get());
    assert!(
        new_budget > old_budget,
        "less actual work, not a larger grant"
    );
}

#[test]
fn a_completed_state_cannot_be_reused_with_an_equal_but_foreign_index() {
    let db = vec![vec![(1, true)]];
    let owner = EmissionProgress::default();
    let index = Occurrences::new(&db, &mut 100_000, &owner).unwrap();
    let foreign = Occurrences::new(&db, &mut 100_000, &owner).unwrap();
    let parent = propagate(
        &db,
        &index,
        Pending::Fresh(Model::default()),
        &mut 100_000,
        &owner,
    )
    .unwrap()
    .unwrap();
    let mut remaining = 100_000;
    assert!(solve_pending(
        &db,
        &foreign,
        Pending::Ready(parent),
        &mut remaining,
        &owner
    )
    .is_none());
    assert_eq!(remaining, 0);
}
