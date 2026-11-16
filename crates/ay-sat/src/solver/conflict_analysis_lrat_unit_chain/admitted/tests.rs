// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]
use super::*;
use crate::counted_storage::test_owner;
use crate::kani_compat::det_hash_set_new;

fn pos(v: u32) -> Literal {
    Literal::positive(Variable(v))
}

fn units() -> Solver {
    let mut s = Solver::new(8);
    s.enable_clause_trace();
    s.set_unsat_certificate_enabled(false);
    for var in 0..8 {
        assert!(s.add_clause(vec![pos(var)]));
    }
    s.initialize_watches();
    assert!(s.process_initial_clauses().is_none());
    assert!(s.search_propagate().is_none());
    assert_eq!(s.trail.len(), 8);
    assert_eq!(s.qhead, s.trail.len());
    assert!(s.unit_proof_id.iter().all(|&id| id != 0));
    s
}

fn chain(s: &mut Solver) -> Vec<u64> {
    s.conflict.set_asserting_literal(pos(7));
    s.conflict.get_result(0, 0).resolution_chain
}

#[test]
fn fast_and_stale_position_paths_keep_exact_reverse_order_and_filtering() {
    for stale in [false, true] {
        for filtered in [false, true] {
            let mut expected = units();
            let mut actual = units();
            if stale {
                expected.var_data[7].trail_pos = 0;
                actual.var_data[7].trail_pos = 0;
            }
            let wanted = if filtered {
                vec![actual.unit_proof_id[5]]
            } else {
                vec![actual.unit_proof_id[7], actual.unit_proof_id[5]]
            };
            let mut filter = det_hash_set_new();
            if filtered {
                filter.insert(pos(7));
            }
            expected.append_lrat_unit_chain(&[5, 7, 5], &filter);
            let owner = test_owner(1_000_000, 1_000_000);
            actual
                .append_lrat_unit_chain_admitted(&[5, 7, 5], &filter, &root::Counted(&owner))
                .unwrap();
            assert_eq!(chain(&mut actual), wanted);
            assert_eq!(chain(&mut expected), wanted);
            assert_eq!(
                actual.lrat_materialization_stats(),
                expected.lrat_materialization_stats()
            );
            assert_eq!(
                actual.stats.lrat_unit_chain_root_trail_entries,
                if stale { 8 } else { 0 }
            );
            assert_eq!(actual.min.lrat_to_clear.len(), 0);
            assert!(actual.min.minimize_flags.iter().all(|&value| value == 0));
            assert!(owner.usage().unwrap().work_admitted > 0);
        }
    }
}

#[test]
fn actual_bfs_missing_unit_fallback_keeps_ordinary_chain_without_minting_ids() {
    let fixture = || {
        let mut s = Solver::new(3);
        s.enable_clause_trace();
        s.set_unsat_certificate_enabled(false);
        for clause in [
            vec![pos(0)],
            vec![pos(0).negated(), pos(1)],
            vec![pos(1).negated(), pos(2)],
        ] {
            assert!(s.add_clause(clause));
        }
        s.initialize_watches();
        assert!(s.process_initial_clauses().is_none());
        assert!(s.search_propagate().is_none());
        assert_eq!(s.trail, vec![pos(0), pos(1), pos(2)]);
        assert_eq!(s.qhead, s.trail.len());
        assert_eq!(&s.unit_proof_id[1..], &[0, 0]);
        s
    };
    let mut expected = fixture();
    let mut actual = fixture();
    let unit = actual.unit_proof_id[0];
    assert_ne!(unit, 0);
    let filter = det_hash_set_new();
    expected.append_lrat_unit_chain(&[2], &filter);
    let owner = test_owner(1_000_000, 1_000_000);
    actual
        .append_lrat_unit_chain_admitted(&[2], &filter, &root::Counted(&owner))
        .unwrap();
    expected.conflict.set_asserting_literal(pos(2));
    actual.conflict.set_asserting_literal(pos(2));
    assert_eq!(actual.conflict.get_result(0, 0).resolution_chain, [unit]);
    assert_eq!(expected.conflict.get_result(0, 0).resolution_chain, [unit]);
    assert_eq!(actual.stats.lrat_unit_chain_missing_hints, 2);
    assert_eq!(
        actual.lrat_materialization_stats(),
        expected.lrat_materialization_stats()
    );
    assert_eq!(actual.unit_proof_id, expected.unit_proof_id);
    assert_eq!(actual.min.lrat_to_clear.len(), 0);
}

#[test]
fn hash_filter_actual_layout_matches_ordinary_at_all_growth_boundaries() {
    for len in [1, 3, 4, 7, 8, 14, 15, 16, 31, 32, 63, 64, 127, 128] {
        let owner = test_owner(1_000_000, 1_000_000);
        let mut actual = filter::new(len, &owner).unwrap();
        let mut expected = crate::kani_compat::det_hash_set_with_capacity(len);
        assert_eq!(actual.capacity(), expected.capacity());
        assert_eq!(actual.allocation_size(), expected.allocation_size());
        for var in 0..len as u32 {
            filter::probe(&actual, &owner).unwrap();
            assert_eq!(actual.insert(pos(var)), expected.insert(pos(var)));
        }
        for var in 0..=len as u32 {
            filter::probe(&actual, &owner).unwrap();
            assert_eq!(actual.contains(&pos(var)), expected.contains(&pos(var)));
        }
        assert_eq!(actual.capacity(), expected.capacity());
        assert!(owner.usage().unwrap().storage_admitted >= actual.allocation_size());
    }
}

#[test]
fn invalid_root_and_counter_overflow_refuse_before_dirty_registration() {
    for overflow in [false, true] {
        let mut s = units();
        if overflow {
            s.stats.lrat_unit_chain_calls = u64::MAX;
        }
        let roots = if overflow { vec![0] } else { vec![8] };
        let owner = test_owner(1_000_000, 1_000_000);
        assert!(s
            .append_lrat_unit_chain_admitted(&roots, &det_hash_set_new(), &root::Counted(&owner))
            .is_err());
        assert_eq!(s.min.lrat_to_clear.len(), 0);
        assert!(s.min.minimize_flags.iter().all(|&v| v == 0));
        assert_eq!(s.conflict.resolution_chain_len(), 0);
        assert!(owner.check().is_err());
    }
}
