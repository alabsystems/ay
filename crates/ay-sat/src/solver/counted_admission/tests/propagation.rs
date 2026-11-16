// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod callers;

fn lit(index: usize) -> Literal {
    Literal::positive(Variable::new(index as u32))
}

fn granted(work: u64, storage: usize) -> CountedAdmission {
    CountedAdmission::new(
        FiniteAdmissionGrant::new(work, storage),
        None,
        Arc::new(|| false),
    )
    .unwrap()
}

fn chain(length: usize, unsat: bool) -> Solver {
    let mut solver = Solver::new(length);
    for index in 1..length {
        assert!(solver.add_clause(vec![lit(index - 1).negated(), lit(index)]));
    }
    assert!(solver.add_clause(vec![lit(0)]));
    if unsat {
        assert!(solver.add_clause(vec![lit(length - 1).negated()]));
    }
    solver
}

fn watch_fanout(count: usize, root_unit: bool) -> Solver {
    let mut solver = Solver::new(1 + count * 3);
    for index in 0..count {
        let first = 1 + index * 3;
        assert!(solver.add_clause(vec![
            lit(0).negated(),
            lit(first),
            lit(first + 1),
            lit(first + 2)
        ]));
    }
    if root_unit {
        assert!(solver.add_clause(vec![lit(0)]));
    }
    solver
}

fn prepare(mut solver: Solver) -> Solver {
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    solver
}

#[derive(Debug, PartialEq, Eq)]
struct PropagationState {
    qhead: usize,
    trail: Vec<Literal>,
    values: Vec<i8>,
    watches: Vec<Vec<u64>>,
    clauses: Vec<Vec<Literal>>,
}

fn state(solver: &Solver) -> PropagationState {
    let watches = (0..solver.num_vars * 2)
        .map(|index| {
            let literal = Literal(index as u32);
            (0..solver.watches.len_of(literal))
                .map(|watch| solver.watches.entry_raw(literal, watch))
                .collect()
        })
        .collect();
    PropagationState {
        qhead: solver.qhead,
        trail: solver.trail.clone(),
        values: solver.vals.clone(),
        watches,
        clauses: solver
            .arena
            .indices()
            .map(|offset| solver.arena.literals(offset).to_vec())
            .collect(),
    }
}

#[test]
fn long_binary_chain_has_exact_and_short_cumulative_admission() {
    for unsat in [false, true] {
        let mut baseline = prepare(chain(128, unsat));
        let original = granted(1_000_000, 1 << 20);
        attach(&mut baseline, &original);
        assert_eq!(
            baseline.search_propagate_counted().unwrap().is_some(),
            unsat
        );
        let used = original.usage().unwrap();
        assert!(used.work_admitted > 128);
        assert!(used.storage_admitted > 0);
        for work in [used.work_admitted - 1, used.work_admitted] {
            let mut solver = prepare(chain(128, unsat));
            let owner = granted(work, used.storage_admitted);
            attach(&mut solver, &owner);
            let result = solver.search_propagate_counted();
            if work == used.work_admitted {
                assert_eq!(result.unwrap().is_some(), unsat);
                assert_eq!(state(&solver), state(&baseline));
                assert_eq!(owner.usage().unwrap().work_remaining, 0);
            } else {
                assert_eq!(result, Err(SatUnknownReason::ResourceBudget));
                assert_eq!(owner.check(), Err(CountedAdmissionError::WorkExhausted));
                assert_eq!(solver.search_propagate_counted(), result);
            }
        }
    }
}

#[test]
fn whole_long_watch_transaction_is_admitted_before_any_mutation() {
    for (work, storage, expected) in [
        (64, 1 << 20, CountedAdmissionError::WorkExhausted),
        (1_000_000, 1, CountedAdmissionError::StorageExhausted),
    ] {
        let mut solver = prepare(watch_fanout(64, true));
        let before = state(&solver);
        let original = granted(work, storage);
        attach(&mut solver, &original);
        assert_eq!(
            solver.search_propagate_counted(),
            Err(SatUnknownReason::ResourceBudget)
        );
        assert_eq!(state(&solver), before);
        assert_eq!(solver.deferred_replacement_watches.len(), 0);
        assert_eq!(original.check(), Err(expected));
    }
}

#[test]
fn completed_watch_moves_match_legacy_and_exact_storage_is_sufficient() {
    let mut legacy = prepare(watch_fanout(64, true));
    assert!(legacy.search_propagate().is_none());
    let mut baseline = prepare(watch_fanout(64, true));
    let original = granted(1_000_000, 1 << 20);
    attach(&mut baseline, &original);
    assert_eq!(baseline.search_propagate_counted(), Ok(None));
    assert_eq!(state(&baseline), state(&legacy));
    let used = original.usage().unwrap();
    for storage in [used.storage_admitted - 1, used.storage_admitted] {
        let mut solver = prepare(watch_fanout(64, true));
        let before = state(&solver);
        attach(&mut solver, &granted(used.work_admitted, storage));
        let result = solver.search_propagate_counted();
        if storage == used.storage_admitted {
            assert_eq!(result, Ok(None));
            assert_eq!(state(&solver), state(&legacy));
        } else {
            assert_eq!(result, Err(SatUnknownReason::ResourceBudget));
            assert_eq!(state(&solver), before);
        }
    }
}

#[test]
fn destination_region_and_unified_buffer_growth_are_pre_admitted_once() {
    let make = || {
        let moves = 64;
        let existing = 512;
        let target = 1 + moves;
        let mut solver = Solver::new(target + 1 + existing);
        for index in 1..=moves {
            assert!(solver.add_clause(vec![lit(0).negated(), lit(index), lit(target)]));
        }
        for index in 0..existing {
            assert!(solver.add_clause(vec![lit(target), lit(target + 1 + index)]));
        }
        assert!(solver.add_clause(vec![lit(0)]));
        prepare(solver)
    };
    let mut legacy = make();
    assert!(legacy.search_propagate().is_none());
    let mut baseline = make();
    let original = granted(1_000_000, 1 << 20);
    attach(&mut baseline, &original);
    assert_eq!(baseline.search_propagate_counted(), Ok(None));
    assert_eq!(state(&baseline), state(&legacy));
    let used = original.usage().unwrap();
    assert!(used.storage_admitted > 512 * size_of::<u64>());
    assert!(used.work_admitted > 512);
    for storage in [used.storage_admitted - 1, used.storage_admitted] {
        let mut solver = make();
        let before = state(&solver);
        let original = granted(used.work_admitted, storage);
        attach(&mut solver, &original);
        let result = solver.search_propagate_counted();
        if storage == used.storage_admitted {
            assert_eq!(result, Ok(None));
            assert_eq!(state(&solver), state(&legacy));
        } else {
            assert_eq!(result, Err(SatUnknownReason::ResourceBudget));
            assert_eq!(state(&solver), before);
        }
    }
}

#[test]
fn one_shot_refusal_inside_watch_bound_scan_is_terminal_and_transactional() {
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let original = CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1 << 20),
        None,
        Arc::new(move || observed.fetch_add(1, Ordering::SeqCst) == 12),
    )
    .unwrap();
    let mut solver = prepare(watch_fanout(64, true));
    let before = state(&solver);
    attach(&mut solver, &original);
    assert_eq!(
        solver.search_propagate_counted(),
        Err(SatUnknownReason::Interrupted)
    );
    assert!(calls.load(Ordering::SeqCst) >= 13);
    assert_eq!(state(&solver), before);
    assert_eq!(
        solver.search_propagate_counted(),
        Err(SatUnknownReason::Interrupted)
    );
    assert_eq!(state(&solver), before);
}

#[test]
fn final_poll_cannot_publish_a_completed_conflict_or_fixpoint_after_stop() {
    for unsat in [false, true] {
        let calls = Arc::new(AtomicUsize::new(0));
        let observed = Arc::clone(&calls);
        let original = CountedAdmission::new(
            FiniteAdmissionGrant::new(1_000_000, 1 << 20),
            None,
            Arc::new(move || {
                observed.fetch_add(1, Ordering::SeqCst);
                false
            }),
        )
        .unwrap();
        let mut healthy = prepare(chain(32, unsat));
        attach(&mut healthy, &original);
        assert_eq!(healthy.search_propagate_counted().unwrap().is_some(), unsat);
        let last_poll = calls.load(Ordering::SeqCst) - 1;
        let calls = Arc::new(AtomicUsize::new(0));
        let observed = Arc::clone(&calls);
        let original = CountedAdmission::new(
            FiniteAdmissionGrant::new(1_000_000, 1 << 20),
            None,
            Arc::new(move || observed.fetch_add(1, Ordering::SeqCst) == last_poll),
        )
        .unwrap();
        let mut stopped = prepare(chain(32, unsat));
        attach(&mut stopped, &original);
        assert_eq!(
            stopped.search_propagate_counted(),
            Err(SatUnknownReason::Interrupted)
        );
        assert_eq!(state(&stopped), state(&healthy));
        assert_eq!(
            stopped.search_propagate_counted(),
            Err(SatUnknownReason::Interrupted)
        );
    }
}

#[test]
fn later_chain_refusal_preserves_each_completed_watch_transaction() {
    let mut solver = prepare(chain(64, false));
    let original = granted(100, 1 << 20);
    attach(&mut solver, &original);
    assert_eq!(
        solver.search_propagate_counted(),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert!(solver.qhead > 0 && solver.qhead < solver.trail.len());
    assert_eq!(solver.deferred_replacement_watches.len(), 0);
    for offset in solver.arena.indices() {
        let clause = solver.arena.literals(offset);
        if clause.len() >= 2 {
            for literal in &clause[..2] {
                assert!((0..solver.watches.len_of(*literal)).any(|index| {
                    crate::watched::entry_clause_off(solver.watches.entry_raw(*literal, index))
                        == offset as u32
                }));
            }
        }
    }
}

#[test]
fn domain_is_restored_on_refusal_and_healthy_ic3_and_normal_paths_agree() {
    for ic3 in [false, true] {
        let make = || {
            let mut solver = watch_fanout(16, false);
            if ic3 {
                solver.set_ic3_mode();
            }
            solver.set_domain_bcp_min_vars(0);
            let mut solver = prepare(solver);
            solver.active_domain = Some(vec![true; solver.num_vars]);
            solver.decide(lit(0));
            solver
        };
        let mut legacy = make();
        assert!(legacy.search_propagate().is_none());
        let mut healthy = make();
        attach(&mut healthy, &granted(1_000_000, 1 << 20));
        assert_eq!(healthy.search_propagate_counted(), Ok(None));
        assert_eq!(state(&healthy), state(&legacy));
        for work in [1, 64] {
            let mut stopped = make();
            let before = state(&stopped);
            let domain = stopped.active_domain.clone();
            attach(&mut stopped, &granted(work, 1 << 20));
            assert_eq!(
                stopped.search_propagate_counted(),
                Err(SatUnknownReason::ResourceBudget)
            );
            assert_eq!(stopped.active_domain, domain);
            assert_eq!(state(&stopped), before);
        }
    }
}
