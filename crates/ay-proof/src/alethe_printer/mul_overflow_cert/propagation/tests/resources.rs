// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;

#[derive(Clone, Copy)]
enum Engine {
    Models,
    Refutation,
}

fn run(
    engine: Engine,
    db: &[localsat::Clause],
    budget: &mut u64,
    owner: &EmissionProgress<'_>,
) -> Option<bool> {
    match engine {
        Engine::Models => {
            localsat::solve(db, &HashMap::default(), budget, owner).map(|m| m.is_some())
        }
        Engine::Refutation => cdcl::refute(db, &[], &[], budget, owner).map(|_| true),
    }
}

#[test]
fn zero_exact_and_short_allowances_cover_index_queue_and_search() {
    for engine in [Engine::Models, Engine::Refutation] {
        let db = unsat();
        let owner = EmissionProgress::default();
        let mut remaining = 100_000;
        let expected = run(engine, &db, &mut remaining, &owner).unwrap();
        let used = 100_000 - remaining;
        assert!(used > 0);
        let mut exact = used;
        assert_eq!(run(engine, &db, &mut exact, &owner), Some(expected));
        assert_eq!(exact, 0);
        let mut short = used - 1;
        assert_eq!(run(engine, &db, &mut short, &owner), None);
        assert_eq!(short, 0);
        assert_eq!(run(engine, &db, &mut short, &owner), None);
        assert_eq!(short, 0);
        assert_eq!(run(engine, &db, &mut 0, &owner), None);
    }
    // Even the empty database and an already empty clause must enter the owner.
    for db in [vec![], vec![vec![]], vec![vec![(1, true)]]] {
        assert_eq!(
            run(Engine::Models, &db, &mut 0, &EmissionProgress::default()),
            None
        );
    }
}

fn every_refusal(engine: Engine, db: &[localsat::Clause]) {
    let calls = Cell::new(0usize);
    let mut accepting = || {
        calls.set(calls.get() + 1);
        true
    };
    let owner = EmissionProgress::with_caller(&mut accepting);
    assert!(run(engine, db, &mut 100_000, &owner).is_some());
    for stop in 1..=calls.get() {
        let seen = Cell::new(0usize);
        let mut callback = || {
            seen.set(seen.get() + 1);
            seen.get() != stop
        };
        let owner = EmissionProgress::with_caller(&mut callback);
        let nested = owner.clone();
        let mut budget = 100_000;
        assert_eq!(run(engine, db, &mut budget, &nested), None, "poll {stop}");
        assert_eq!(seen.get(), stop);
        assert!(owner.refused());
        let remaining = budget;
        assert_eq!(run(engine, db, &mut budget, &owner), None);
        assert_eq!(budget, remaining);
        assert_eq!(seen.get(), stop);
    }
}

#[test]
fn every_observed_index_queue_and_search_refusal_stays_terminal() {
    every_refusal(Engine::Models, &reverse_chain(3));
    every_refusal(Engine::Models, &unsat());
    every_refusal(Engine::Refutation, &unsat());
}

#[test]
fn callback_unwind_cannot_resume_after_partial_queue_or_index_mutation() {
    for engine in [Engine::Models, Engine::Refutation] {
        let db = unsat();
        let calls = Cell::new(0usize);
        let mut accepting = || {
            calls.set(calls.get() + 1);
            true
        };
        let owner = EmissionProgress::with_caller(&mut accepting);
        assert!(run(engine, &db, &mut 100_000, &owner).is_some());
        for stop in [1, calls.get() / 2, calls.get()] {
            let seen = Cell::new(0usize);
            let mut callback = || {
                seen.set(seen.get() + 1);
                assert_ne!(seen.get(), stop, "original observer unwound");
                true
            };
            let owner = EmissionProgress::with_caller(&mut callback);
            let mut budget = 100_000;
            assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                run(engine, &db, &mut budget, &owner)
            }))
            .is_err());
            assert!(owner.refused());
            let remaining = budget;
            assert_eq!(run(engine, &db, &mut budget, &owner), None);
            assert_eq!(remaining, budget);
            assert_eq!(seen.get(), stop);
        }
    }
}

#[test]
fn separate_searches_consume_the_same_remaining_local_allowance() {
    let db = reverse_chain(4);
    let owner = EmissionProgress::default();
    let mut remaining = 100_000;
    assert_eq!(run(Engine::Models, &db, &mut remaining, &owner), Some(true));
    let used = 100_000 - remaining;
    let mut budget = used * 2 - 1;
    assert_eq!(run(Engine::Models, &db, &mut budget, &owner), Some(true));
    assert_eq!(run(Engine::Models, &db, &mut budget, &owner), None);
    assert_eq!(budget, 0);
    assert_eq!(run(Engine::Models, &db, &mut budget, &owner), None);
}
