// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

fn leaf(count: u32) -> (Solver, Literal) {
    let mut s = Solver::new((count + 1) as usize);
    let mut clause = vec![pos(count)];
    clause.extend((0..count).map(neg));
    assert!(s.add_clause(clause));
    let reference = ClauseRef(s.arena.indices().next().unwrap() as u32);
    s.initialize_watches();
    for var in 0..count {
        s.decide(pos(var));
        assert!(s.search_propagate().is_none());
    }
    assert_eq!(s.qhead, s.trail.len());
    assert_eq!(s.lit_val(pos(count)), 1);
    assert!(matches!(
        s.var_reason_kind(count as usize),
        ReasonKind::Clause(actual) if actual == reference
    ));
    (s, pos(count))
}

#[test]
fn real_leaf_reason_marks_entire_clause_even_when_limit_is_crossed() {
    let (mut actual, lit) = leaf(5);
    let (mut expected, other) = leaf(5);
    let mut expected_added = 0;
    expected.add_reason_literals_to_analyzed(other, 1, &mut expected_added, 1);
    let mut actual_added = 0;
    let owner = test_owner(1_000_000, 1_000_000);
    actual
        .add_reason_literals_admitted(lit, 1, &mut actual_added, 1, &Counted(&owner))
        .unwrap();
    assert_eq!(actual_added, 5);
    assert_eq!(actual_added, expected_added);
    assert_eq!(actual.var_data, expected.var_data);
    assert_eq!(
        actual.conflict.analyzed_vars(),
        expected.conflict.analyzed_vars()
    );
    assert_eq!(actual.search_ticks, expected.search_ticks);
}

#[test]
fn real_over_limit_reason_bump_rolls_back_seen_and_keeps_ordinary_hysteresis() {
    let (mut actual, lit) = leaf(16);
    let (mut expected, other) = leaf(16);
    for (s, uip) in [(&mut actual, lit), (&mut expected, other)] {
        s.conflict.set_asserting_literal(uip.negated());
        s.conflict
            .mark_seen(uip.variable().index(), &mut s.var_data);
        s.stable_mode = false;
    }
    expected.bump_reason_literals();
    let owner = test_owner(1_000_000, 1_000_000);
    actual
        .bump_reason_literals_admitted(&Counted(&owner))
        .unwrap();
    assert_eq!(actual.var_data, expected.var_data);
    assert_eq!(actual.conflict.analyzed_vars(), &[16]);
    assert_eq!(
        actual.cold.bumpreason_delay_interval,
        expected.cold.bumpreason_delay_interval
    );
    assert_eq!(
        actual.cold.bumpreason_delay_remaining,
        expected.cold.bumpreason_delay_remaining
    );
    assert_eq!(actual.cold.bumpreason_delay_interval[0], 1);
}

#[test]
fn chrono_ghost_is_skipped_before_invalid_stale_reason_pointer() {
    let (mut s, lit) = leaf(3);
    s.vals[lit.index()] = 0;
    s.vals[lit.negated().index()] = 0;
    s.var_data[lit.variable().index()].reason = 0x7fff_ffff;
    let owner = test_owner(1_000_000, 1_000_000);
    let mut added = 0;
    s.add_reason_literals_admitted(lit, 2, &mut added, 10, &Counted(&owner))
        .unwrap();
    assert_eq!(added, 0);
    assert_eq!(s.conflict.analyzed_vars().len(), 0);
    assert!(owner.usage().unwrap().work_admitted > 0);
}

#[test]
fn ordinary_minimize_ghost_short_circuit_precedes_reason_validation() {
    let (mut s, lit) = leaf(3);
    s.vals[lit.index()] = 0;
    s.vals[lit.negated().index()] = 0;
    s.var_data[lit.variable().index()].reason = 0x7fff_ffff;
    let owner = test_owner(1_000_000, 1_000_000);
    assert!(!s
        .redundant_admitted(lit.negated(), 0, &Counted(&owner))
        .unwrap());
    assert!(!s.redundant_admitted(lit.negated(), 0, &Ordinary).unwrap());
}
