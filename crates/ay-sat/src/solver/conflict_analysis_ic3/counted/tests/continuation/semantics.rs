// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn satisfies(clause: &[Literal], bits: usize) -> bool {
    clause
        .iter()
        .any(|lit| ((bits >> lit.variable().index()) & 1 == 1) == lit.is_positive())
}

#[test]
fn actual_recursive_minimizer_removes_real_lower_clause_literals_like_ordinary() {
    for kind in [Reasons::Binary, Reasons::Long] {
        for length in [1, 2, 4, 16] {
            for kissat_ticks in [false, true] {
                let (mut expected, conflict, _) = removable(length, kind);
                expected.cold.analysis_ticks_kissat = kissat_ticks;
                let expected = (
                    ordinary_minimize(&mut expected, conflict),
                    expected.search_ticks,
                );
                assert_eq!(
                    expected.0,
                    Resolved {
                        uip: neg(length + 2),
                        lower: vec![neg(1)],
                        lbd: 1
                    }
                );
                let (mut actual, conflict, _) = removable(length, kind);
                actual.cold.analysis_ticks_kissat = kissat_ticks;
                let before = state(&actual);
                attach(&mut actual, &test_owner(10_000_000, 10_000_000));
                assert_eq!(minimize(&mut actual, conflict), Ok(expected.0));
                assert_eq!(actual.search_ticks, expected.1);
                assert_eq!(state(&actual), before);
                retired(&mut actual);
            }
        }
    }
}

#[test]
fn minimized_clause_is_entailed_by_all_models_of_the_real_original_cnf() {
    for length in 1..=3 {
        for kind in [Reasons::Binary, Reasons::Long] {
            let (mut s, conflict, clauses) = removable(length, kind);
            attach(&mut s, &test_owner(10_000_000, 10_000_000));
            let result = minimize(&mut s, conflict).unwrap();
            assert_eq!(result.lower.len(), 1);
            let learned = [result.uip, result.lower[0]];
            let mut models = 0;
            for bits in 0..(1usize << s.num_vars) {
                if clauses.iter().all(|clause| satisfies(clause, bits)) {
                    models += 1;
                    assert!(satisfies(&learned, bits));
                }
            }
            assert!(models > 0);
        }
    }
}

#[test]
fn depth_abort_and_lower_lazy_or_decision_reason_conservatively_keep_literals() {
    for mutate in [
        (|s: &mut Solver| s.min.minimize_depth_limit = 0) as fn(&mut Solver),
        |s| {
            s.var_data[5].reason = NO_REASON;
        },
        |s| {
            s.var_data[5].set_lazy_theory_reason(true);
        },
    ] {
        let (mut expected, conflict, _) = removable(4, Reasons::Long);
        mutate(&mut expected);
        let expected = ordinary_minimize(&mut expected, conflict);
        assert_eq!(expected.lower.len(), 2);
        let (mut s, conflict, _) = removable(4, Reasons::Long);
        mutate(&mut s);
        attach(&mut s, &test_owner(10_000_000, 10_000_000));
        assert_eq!(minimize(&mut s, conflict), Ok(expected));
        retired(&mut s);
    }
}

#[test]
fn default_singleton_and_distinct_level_routes_preserve_real_shrink_state() {
    for distinct in [false, true] {
        let (mut s, conflict) = if distinct {
            distinct_levels()
        } else {
            let (s, conflict, _) = fixture(2, Reasons::Long);
            (s, conflict)
        };
        let (mut expected, same) = if distinct {
            distinct_levels()
        } else {
            let (s, conflict, _) = fixture(2, Reasons::Long);
            (s, conflict)
        };
        // Exercise the real stamp-clear rollover, not a detached prescan.
        s.glue_stamp_counter = u32::MAX;
        expected.glue_stamp_counter = u32::MAX;
        let expected_result = ordinary_minimize(&mut expected, same);
        attach(&mut s, &test_owner(10_000_000, 10_000_000));
        assert_eq!(minimize(&mut s, conflict), Ok(expected_result));
        assert_eq!(s.glue_stamp, expected.glue_stamp);
        assert_eq!(s.glue_stamp_counter, expected.glue_stamp_counter);
        assert_eq!(
            s.stats.shrink_lits_deduced,
            expected.stats.shrink_lits_deduced
        );
        assert_eq!(
            s.stats.shrink_singleton_fast_path_skips,
            expected.stats.shrink_singleton_fast_path_skips
        );
        assert!(s.shrink_enabled);
        retired(&mut s);
    }
}

#[test]
fn selected_repeated_level_block_shrinking_is_not_silently_replaced_or_disabled() {
    let (mut s, conflict, _) = removable(3, Reasons::Long);
    s.set_shrink_enabled(true);
    let before = state(&s);
    let (mut ordinary, other, _) = removable(3, Reasons::Long);
    ordinary.set_shrink_enabled(true);
    let expected = ordinary_minimize(&mut ordinary, other);
    let owner = test_owner(10_000_000, 10_000_000);
    attach(&mut s, &owner);
    assert_eq!(minimize(&mut s, conflict), Ok(expected));
    assert!(s.stats.shrink_block_successes > 0);
    assert!(owner.usage().unwrap().refusal.is_none());
    assert!(s.shrink_enabled);
    assert_eq!(state(&s), before);
    retired(&mut s);
}

#[test]
fn intact_garbage_keep_data_lower_reason_remains_usable_like_ordinary() {
    let (mut s, conflict, _) = removable(3, Reasons::Long);
    let reason = s.var_reason(4).unwrap();
    s.arena.mark_garbage_keep_data(reason.0 as usize);
    let (mut expected, same, _) = removable(3, Reasons::Long);
    let reason = expected.var_reason(4).unwrap();
    expected.arena.mark_garbage_keep_data(reason.0 as usize);
    let expected = ordinary_minimize(&mut expected, same);
    attach(&mut s, &test_owner(10_000_000, 10_000_000));
    assert_eq!(minimize(&mut s, conflict), Ok(expected));
    retired(&mut s);
}

#[test]
fn large_real_learned_clause_sort_and_cache_reuse_match_ordinary_compaction() {
    for length in [2, 3, 7, 32, 65] {
        let (mut expected, conflict) = dense_removable(length);
        let expected = ordinary_minimize(&mut expected, conflict);
        assert_eq!(expected.lower, vec![neg(0)]);
        let (mut s, conflict) = dense_removable(length);
        let before = state(&s);
        attach(&mut s, &test_owner(10_000_000, 10_000_000));
        assert_eq!(minimize(&mut s, conflict), Ok(expected));
        assert_eq!(state(&s), before);
        retired(&mut s);
    }
}

#[test]
fn default_unit_learned_clause_has_empty_lower_buffer_and_preminimize_lbd_zero() {
    let mut s = Solver::new(3);
    s.set_ic3_mode();
    for clause in [
        vec![neg(0), pos(1)],
        vec![neg(0), pos(2)],
        vec![neg(1), neg(2)],
    ] {
        assert!(s.add_clause(clause));
    }
    s.initialize_watches();
    s.decide(pos(0));
    let conflict = s.search_propagate().unwrap();
    attach(&mut s, &test_owner(10_000_000, 10_000_000));
    assert_eq!(
        minimize(&mut s, conflict),
        Ok(Resolved {
            uip: neg(0),
            lower: vec![],
            lbd: 0
        })
    );
    assert!(s.shrink_enabled);
    retired(&mut s);
}
