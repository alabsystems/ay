// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Legacy engines are frozen copies of the pre-change implementations, with
//! imports and observational visit/reason hooks only. No shared new scheduler.
#![cfg(test)]

use super::super::{cdcl, localsat};
use super::{EmissionProgress, Occurrences, T};
use ay_core::kani_compat::DetHashMap as HashMap;
use std::cell::{Cell, RefCell};

#[path = "tests/initial_notice.rs"]
mod initial_notice;
#[path = "legacy_cdcl.rs"]
mod legacy_cdcl;
#[path = "legacy_localsat.rs"]
mod legacy_localsat;
#[path = "tests/order.rs"]
mod order;
#[path = "tests/resources.rs"]
mod resources;
#[path = "tests/seeded.rs"]
mod seeded;

#[derive(Default, Debug)]
struct Trace {
    visits: usize,
    assignments: Vec<(T, usize)>,
}

thread_local! {
    static TRACE: RefCell<Option<Trace>> = const { RefCell::new(None) };
}

pub(super) fn visited() {
    TRACE.with(|trace| {
        if let Some(trace) = &mut *trace.borrow_mut() {
            trace.visits += 1;
        }
    });
}

pub(super) fn assigned(atom: T, reason: usize) {
    TRACE.with(|trace| {
        if let Some(trace) = &mut *trace.borrow_mut() {
            trace.assignments.push((atom, reason));
        }
    });
}

fn measured<R>(operation: impl FnOnce() -> R) -> (R, Trace) {
    TRACE.with(|trace| *trace.borrow_mut() = Some(Trace::default()));
    let result = operation();
    let trace = TRACE.with(|trace| trace.borrow_mut().take().unwrap());
    (result, trace)
}

fn clauses() -> Vec<localsat::Clause> {
    let literals = [(1, true), (1, false), (2, true), (2, false)];
    let mut clauses = vec![vec![]];
    for literal in literals {
        clauses.push(vec![literal]);
        for other in literals {
            clauses.push(vec![literal, other]);
        }
    }
    clauses
}

fn fixed(code: usize) -> HashMap<T, bool> {
    [(1, code % 3), (2, code / 3)]
        .into_iter()
        .filter_map(|(atom, value)| match value {
            0 => None,
            1 => Some((atom, false)),
            _ => Some((atom, true)),
        })
        .collect()
}

fn compare_localsat(db: &[localsat::Clause], fixed: &HashMap<T, bool>) {
    let progress = EmissionProgress::default();
    let (old, old_trace) = measured(|| {
        legacy_localsat::solve(db, fixed, &mut 1_000_000, &progress).expect("legacy completes")
    });
    let (new, new_trace) =
        measured(|| localsat::solve(db, fixed, &mut 1_000_000, &progress).expect("new completes"));
    assert_eq!(new, old, "db={db:?}, fixed={fixed:?}");
    assert_eq!(new_trace.assignments, old_trace.assignments, "db={db:?}");
}

#[test]
fn every_small_clause_pair_and_partial_assignment_matches_legacy() {
    for left in clauses() {
        for right in clauses() {
            let db = vec![left.clone(), right];
            for code in 0..9 {
                compare_localsat(&db, &fixed(code));
            }
        }
    }
    for code in 0..9 {
        compare_localsat(&[], &fixed(code));
    }
}

fn compare_cdcl(db: &[localsat::Clause], target: &[(T, bool)], decide: &[T]) {
    let progress = EmissionProgress::default();
    let (old, old_trace) = measured(|| {
        legacy_cdcl::refute(db, target, decide, &mut 1_000_000, &progress)
            .map(|proof| (proof.learned, proof.used))
    });
    let (new, new_trace) = measured(|| {
        cdcl::refute(db, target, decide, &mut 1_000_000, &progress)
            .map(|proof| (proof.learned, proof.used))
    });
    assert_eq!(new, old, "db={db:?}, target={target:?}, decide={decide:?}");
    assert_eq!(new_trace.assignments, old_trace.assignments, "db={db:?}");
}

#[test]
fn small_cdcl_databases_preserve_every_propagation_reason() {
    let targets = [
        vec![],
        vec![(1, true)],
        vec![(2, false)],
        vec![(1, false), (2, true)],
    ];
    for left in clauses() {
        for right in clauses() {
            let db = vec![left.clone(), right];
            for target in &targets {
                compare_cdcl(&db, target, &[]);
                compare_cdcl(&db, target, &[2, 1]);
            }
        }
    }
}

fn unsat() -> Vec<localsat::Clause> {
    vec![
        vec![(1, true), (2, true)],
        vec![(1, true), (2, false)],
        vec![(1, false), (2, true)],
        vec![(1, false), (2, false)],
    ]
}

#[test]
fn learned_clause_is_indexed_and_backjump_keeps_legacy_reasons() {
    let db = unsat();
    compare_cdcl(&db, &[], &[1, 2]);
    compare_cdcl(&db, &[], &[2, 1]);
    let (proof, trace) = measured(|| {
        cdcl::refute(&db, &[], &[], &mut 10_000, &EmissionProgress::default()).unwrap()
    });
    assert_eq!(proof.learned, vec![vec![(1, false)]]);
    assert_eq!(proof.used, vec![0, 1, 2, 3]);
    assert!(trace
        .assignments
        .iter()
        .any(|&(_, reason)| reason >= db.len()));
}

#[test]
fn ternary_unsat_cubes_and_duplicate_tautologies_keep_the_same_proof() {
    let mut db: Vec<_> = (0..8)
        .map(|mask| {
            (1..=3)
                .map(|atom| (atom, mask & (1 << (atom - 1)) != 0))
                .collect()
        })
        .collect();
    db.insert(2, vec![(1, true), (1, false), (1, true)]);
    db.insert(5, vec![(2, false), (2, false), (3, true), (3, true)]);
    for decide in [vec![], vec![1, 2, 3], vec![3, 2, 1]] {
        compare_cdcl(&db, &[], &decide);
    }
}

fn reverse_chain(length: T) -> Vec<localsat::Clause> {
    let mut db: Vec<_> = (1..=length)
        .rev()
        .map(|atom| vec![(atom, false), (atom + 1, true)])
        .collect();
    db.push(vec![(1, true)]);
    db
}

#[test]
fn reverse_chain_removes_quadratic_clause_visits_not_owner_checks() {
    let db = reverse_chain(256);
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
    assert_eq!(new_trace.assignments, old_trace.assignments);
    assert_eq!(old_trace.visits, 257 * 258);
    assert!(new_trace.visits <= 4 * 256, "{}", new_trace.visits);
    assert!(
        new_calls.get() < old_calls.get(),
        "{} >= {}",
        new_calls.get(),
        old_calls.get()
    );
    assert!(new_calls.get() > new_trace.visits);
}
