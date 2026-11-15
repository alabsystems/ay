// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;

fn fixture() -> Vec<Clause> {
    vec![
        vec![(2, false), (3, true)],
        vec![(1, false), (2, true)],
        vec![(1, true), (1, false), (1, true)],
        vec![(3, false), (4, true)],
    ]
}

fn child(budget: &mut u64, progress: &EmissionProgress<'_>) -> Option<Option<HashMap<T, bool>>> {
    let db = fixture();
    let index = Occurrences::new(&db, budget, progress)?;
    let parent = propagate(
        &db,
        &index,
        Pending::Fresh(HashMap::default()),
        budget,
        progress,
    )??;
    let result = propagate(
        &db,
        &index,
        Pending::Child {
            parent,
            decision: (1, true),
        },
        budget,
        progress,
    )?;
    progress.poll().then_some(())?;
    Some(result.map(|fixed| fixed.assignment))
}

#[test]
fn sparse_child_keeps_exact_work_and_each_smaller_allowance_refuses() {
    let owner = EmissionProgress::default();
    let mut budget = 100_000;
    let expected = child(&mut budget, &owner).unwrap().unwrap();
    assert_eq!(expected, HashMap::from_iter((1..=4).map(|a| (a, true))));
    let used = 100_000 - budget;
    let mut exact = used;
    assert_eq!(child(&mut exact, &owner), Some(Some(expected)));
    assert_eq!(exact, 0);
    for allowance in 0..used {
        let mut remaining = allowance;
        assert_eq!(child(&mut remaining, &owner), None, "allowance={allowance}");
        assert_eq!(remaining, 0);
    }
}

#[test]
fn each_sparse_seed_and_propagation_observation_can_refuse_without_revival() {
    let calls = Cell::new(0usize);
    let mut accepting = || {
        calls.set(calls.get() + 1);
        true
    };
    assert!(child(&mut 100_000, &EmissionProgress::with_caller(&mut accepting)).is_some());
    for stop in 1..=calls.get() {
        let seen = Cell::new(0usize);
        let mut callback = || {
            seen.set(seen.get() + 1);
            seen.get() != stop
        };
        let owner = EmissionProgress::with_caller(&mut callback);
        let mut budget = 100_000;
        assert_eq!(child(&mut budget, &owner), None, "poll={stop}");
        assert!(owner.refused());
        let remaining = budget;
        assert_eq!(child(&mut budget, &owner), None);
        assert_eq!(budget, remaining);
        assert_eq!(seen.get(), stop);
    }
}

#[test]
fn every_sparse_seed_observer_unwind_is_terminal_for_the_original_owner() {
    let calls = Cell::new(0usize);
    let mut accepting = || {
        calls.set(calls.get() + 1);
        true
    };
    assert!(child(&mut 100_000, &EmissionProgress::with_caller(&mut accepting)).is_some());
    for stop in 1..=calls.get() {
        let seen = Cell::new(0usize);
        let mut callback = || {
            seen.set(seen.get() + 1);
            assert_ne!(seen.get(), stop, "original seed observer unwound");
            true
        };
        let owner = EmissionProgress::with_caller(&mut callback);
        let mut budget = 100_000;
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            child(&mut budget, &owner)
        }))
        .is_err());
        assert!(owner.refused());
        let remaining = budget;
        assert_eq!(child(&mut budget, &owner), None);
        assert_eq!(budget, remaining);
        assert_eq!(seen.get(), stop);
    }
}

#[test]
fn a_seed_cannot_authorize_an_equal_but_different_occurrence_index() {
    let db = fixture();
    let owner = EmissionProgress::default();
    let index = Occurrences::new(&db, &mut 100_000, &owner).unwrap();
    let other = Occurrences::new(&db, &mut 100_000, &owner).unwrap();
    let parent = propagate(
        &db,
        &index,
        Pending::Fresh(HashMap::default()),
        &mut 100_000,
        &owner,
    )
    .unwrap()
    .unwrap();
    let seed = ChildSeed {
        index: parent.index,
        atom: 1,
    };
    let mut budget = 100_000;
    assert!(other
        .sweep_after_decision(&seed, &mut budget, &owner)
        .is_none());
    assert_eq!(budget, 0);
}

#[test]
fn a_child_must_extend_its_parent_not_overwrite_an_existing_assignment() {
    let db = vec![vec![(1, true)]];
    let owner = EmissionProgress::default();
    let mut budget = 100_000;
    let index = Occurrences::new(&db, &mut budget, &owner).unwrap();
    let parent = propagate(
        &db,
        &index,
        Pending::Fresh(HashMap::default()),
        &mut budget,
        &owner,
    )
    .unwrap()
    .unwrap();
    assert!(propagate(
        &db,
        &index,
        Pending::Child {
            parent,
            decision: (1, false),
        },
        &mut budget,
        &owner,
    )
    .is_none());
    assert_eq!(budget, 0);
}

#[test]
fn arbitrary_roots_and_projection_appends_always_receive_a_full_sweep() {
    let owner = EmissionProgress::default();
    for db in [
        vec![vec![(8, true)]],
        vec![vec![(8, true)], vec![]],
        vec![vec![], vec![(8, true)]],
    ] {
        let result = solve(&db, &HashMap::default(), &mut 100_000, &owner).unwrap();
        if db.len() == 1 {
            assert_eq!(result, Some(HashMap::from_iter([(8, true)])));
        } else {
            assert_eq!(result, None);
        }
    }
    let mut db = vec![vec![(1, true), (1, false)]];
    let original = db.clone();
    let fixed = HashMap::default();
    let mut budget = 100_000;
    let mut projection = Projection::new(&mut db, &fixed, &mut budget, &owner).unwrap();
    assert!(projection.solve().unwrap().is_some());
    projection.append([(100, true)].into_iter()).unwrap();
    assert_eq!(projection.solve().unwrap().unwrap().get(&100), Some(&true));
    projection.append(std::iter::empty()).unwrap();
    assert_eq!(projection.solve(), Some(None));
    drop(projection);
    assert_eq!(db, original);
}
