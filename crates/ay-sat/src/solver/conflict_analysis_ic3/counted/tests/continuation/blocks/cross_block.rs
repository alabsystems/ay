// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn two_blocks(walked: bool) -> (Solver, ClauseRef) {
    let mut s = Solver::new(12);
    s.set_ic3_mode();
    s.cold.jump_reasons_enabled = false;
    s.cold.shrink_removable_kissat = walked;
    for (var, antecedents) in [
        (1, vec![0]),
        (2, vec![1]),
        (3, vec![1]),
        (4, vec![2]),
        (5, vec![1]),
        (7, vec![6, 2]),
        (8, vec![6, 3]),
        (10, vec![9]),
        (11, vec![9]),
    ] {
        let mut clause = vec![pos(var)];
        clause.extend(antecedents.into_iter().map(neg));
        assert!(s.add_clause(clause));
    }
    assert!(s.add_clause(vec![neg(10), neg(11), neg(4), neg(5), neg(7), neg(8)]));
    s.initialize_watches();
    for decision in [0, 6] {
        s.decide(pos(decision));
        assert!(s.search_propagate().is_none());
    }
    s.decide(pos(9));
    let conflict = s.search_propagate().unwrap();
    (s, conflict)
}

#[test]
fn actual_lower_block_cache_promotion_enables_later_block_only_when_selected() {
    for walked in [false, true] {
        let (mut ordinary, conflict) = two_blocks(walked);
        let expected = ordinary_minimize(&mut ordinary, conflict);
        if walked {
            assert_eq!(expected.lower, [neg(1), neg(6)]);
            assert_eq!(ordinary.stats.shrink_block_successes, 2);
        } else {
            assert_eq!(expected.lower, [neg(1), neg(8), neg(7)]);
            assert_eq!(ordinary.stats.shrink_block_successes, 1);
            assert_eq!(ordinary.stats.shrink_fail_lower, 1);
        }
        let (mut actual, conflict) = two_blocks(walked);
        attach(&mut actual, &test_owner(10_000_000, 10_000_000));
        assert_eq!(minimize(&mut actual, conflict), Ok(expected));
        assert_eq!(counters(&actual), counters(&ordinary));
        assert_eq!(actual.cold.shrink_removable_kissat, walked);
        fully_retired(&mut actual);
    }
}

#[test]
fn every_promoting_cross_block_storage_cut_is_sticky_and_fully_retired() {
    let (mut baseline, conflict) = two_blocks(true);
    let owner = test_owner(10_000_000, 10_000_000);
    attach(&mut baseline, &owner);
    let scope = baseline
        .begin_counted_ic3_resolution(conflict)
        .unwrap()
        .unwrap();
    let prefix = owner.usage().unwrap().storage_admitted;
    scope.minimize_selected().unwrap().finish().unwrap();
    let total = owner.usage().unwrap().storage_admitted;
    assert!(total > prefix);
    assert_eq!(baseline.stats.shrink_block_successes, 2);
    for storage in prefix..total {
        let (mut actual, conflict) = two_blocks(true);
        let before = state(&actual);
        let owner = test_owner(10_000_000, storage);
        attach(&mut actual, &owner);
        assert_eq!(
            minimize(&mut actual, conflict),
            Err(SatUnknownReason::ResourceBudget)
        );
        assert_eq!(owner.check(), Err(CountedAdmissionError::StorageExhausted));
        assert_eq!(state(&actual), before);
        fully_retired(&mut actual);
    }
}
