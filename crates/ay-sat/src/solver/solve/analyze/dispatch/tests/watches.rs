// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::solver::conflict_analysis_level::admitted::Counted;

fn fixture(detached: bool) -> (Solver, ClauseRef) {
    let mut s = configured(4);
    s.initialize_watches();
    for var in 0..4 {
        s.decide(pos(var));
        assert!(s.search_propagate().is_none());
        assert_eq!(s.qhead, s.trail.len());
    }
    // Attach the delayed conflicting clause only after every real decision
    // has reached a BCP fixpoint. Installing it earlier would force neg(3),
    // so deciding pos(3) would fabricate an impossible live search state.
    assert!(s.add_clause(vec![neg(0), neg(1), neg(2), neg(3)]));
    let reference = ClauseRef(s.arena.indices().next().unwrap() as u32);
    s.attach_clause_watches(reference, (neg(0), neg(1)), false);
    if detached {
        s.watches.get_watches_mut(neg(0)).clear();
        s.watches.get_watches_mut(neg(1)).clear();
    }
    assert_eq!(s.decision_level, 4);
    assert!(s
        .arena
        .literals(reference.index())
        .iter()
        .all(|&lit| s.lit_val(lit) < 0));
    assert_eq!(
        s.arena.literals(reference.index()),
        &[neg(0), neg(1), neg(2), neg(3)]
    );
    (s, reference)
}

fn watch_invariant(s: &Solver, reference: ClauseRef) {
    let lits = s.arena.literals(reference.index());
    let mut matched = Vec::new();
    for var in 0..s.num_vars {
        for lit in [pos(var as u32), neg(var as u32)] {
            let watches = s.watches.get_watches(lit);
            for index in 0..watches.len() {
                if watches.clause_ref(index) == reference {
                    matched.push(lit);
                }
            }
        }
    }
    let mut expected = lits[..2].to_vec();
    expected.sort();
    matched.sort();
    assert_eq!(
        matched, expected,
        "each actual watched literal has exactly one watch"
    );
}

#[test]
fn actual_conflict_relocation_matches_order_capacity_and_does_not_change_formula_epoch() {
    let (mut expected, reference) = fixture(false);
    let answer = expected.find_conflict_level(reference);
    let (mut s, reference) = fixture(false);
    let epoch = s.arena.formula_epoch();
    let owner = generous();
    assert_eq!(
        s.find_conflict_level_admitted(reference, &Counted(&owner))
            .unwrap(),
        answer
    );
    assert_eq!(answer, (4, Some(neg(3))));
    assert_eq!(&s.arena.literals(reference.index())[..2], &[neg(3), neg(2)]);
    assert_eq!(s.arena.formula_epoch(), epoch);
    assert!(owner.usage().unwrap().storage_admitted > 0);
    watch_invariant(&s, reference);
    parity(&s, &expected);
}

#[test]
fn detached_jit_watches_stay_detached_and_do_not_allocate_orphans() {
    let (mut expected, reference) = fixture(true);
    let answer = expected.find_conflict_level(reference);
    let (mut s, reference) = fixture(true);
    let owner = generous();
    assert_eq!(
        s.find_conflict_level_admitted(reference, &Counted(&owner))
            .unwrap(),
        answer
    );
    assert_eq!(owner.usage().unwrap().storage_admitted, 0);
    for var in 0..4 {
        assert_eq!(s.watches.get_watches(neg(var)).len(), 0);
    }
    parity(&s, &expected);
}

#[test]
fn ghost_levels_are_ignored_for_conflict_level_but_keep_original_watch_ordering() {
    let (mut expected, reference) = fixture(false);
    expected.backtrack(2);
    expected.var_data[3].level = 99;
    let answer = expected.find_conflict_level(reference);
    let (mut s, reference) = fixture(false);
    s.backtrack(2);
    s.var_data[3].level = 99;
    assert_eq!(s.lit_val(neg(3)), 0);
    assert_eq!(
        s.find_conflict_level_admitted(reference, &Counted(&generous()))
            .unwrap(),
        answer
    );
    assert_eq!(answer, (2, Some(neg(1))));
    parity(&s, &expected);
}

#[test]
fn every_short_watch_work_and_storage_grant_preserves_complete_relocation_transactions() {
    let (mut baseline, reference) = fixture(false);
    let owner = generous();
    baseline
        .find_conflict_level_admitted(reference, &Counted(&owner))
        .unwrap();
    let used = owner.usage().unwrap();
    assert!(used.work_admitted > 20 && used.storage_admitted > 0);
    for work in 0..used.work_admitted {
        let (mut s, reference) = fixture(false);
        let owner = test_owner(work, 100_000_000);
        assert!(s
            .find_conflict_level_admitted(reference, &Counted(&owner))
            .is_err());
        assert_eq!(owner.check(), Err(CountedAdmissionError::WorkExhausted));
        watch_invariant(&s, reference);
    }
    for storage in 0..used.storage_admitted {
        let (mut s, reference) = fixture(false);
        let owner = test_owner(100_000_000, storage);
        assert!(s
            .find_conflict_level_admitted(reference, &Counted(&owner))
            .is_err());
        assert_eq!(owner.check(), Err(CountedAdmissionError::StorageExhausted));
        watch_invariant(&s, reference);
    }
}
