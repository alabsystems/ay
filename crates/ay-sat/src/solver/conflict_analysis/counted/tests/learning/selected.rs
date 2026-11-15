// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn selected_real_reduction_refuses_after_learning_without_reusable_trace() {
    let (mut s, reference, _) = fork(0, 0);
    s.cold.next_reduce_db = 0;
    let before = trace_rows(&s);
    let owner = test_owner(100_000_000, 100_000_000);
    attach(&mut s, &owner);
    assert_eq!(
        learn(&mut s, reference),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert!(owner.usage().unwrap().refusal.is_some());
    assert!(
        trace_rows(&s).len() > before.len(),
        "must reach actual insertion"
    );
    assert!(s.clause_trace().unwrap().proof_work_exhausted());
    assert_eq!(
        s.cold.next_reduce_db, 0,
        "do not disable or run the selected reduction"
    );
    clean(&s);
}

#[test]
fn selected_dip_hook_refuses_before_backtrack_instead_of_disabling_it() {
    let (mut s, reference, _) = fork(3, 0);
    s.dip.enabled = true;
    let trail = s.trail.clone();
    let before = trace_rows(&s);
    attach(&mut s, &test_owner(100_000_000, 100_000_000));
    assert_eq!(
        learn(&mut s, reference),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert!(s.dip.enabled);
    assert_eq!(s.trail, trail);
    assert_eq!(trace_rows(&s), before);
    clean(&s);
}

#[test]
fn derived_insertion_rejects_original_id_alias_without_minting_or_publishing() {
    let (mut s, reference, _) = fork(0, 0);
    let original = s.cold.clause_ids[reference.index()];
    assert!(s.is_original_clause_id(original));
    s.cold.next_clause_id = original;
    let before = trace_rows(&s);
    attach(&mut s, &test_owner(100_000_000, 100_000_000));
    assert_eq!(
        learn(&mut s, reference),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert_eq!(trace_rows(&s), before);
    assert_eq!(s.cold.next_clause_id, original);
    assert!(s.clause_trace().unwrap().proof_work_exhausted());
    clean(&s);
}

fn add_subsumed_candidate(s: &mut Solver, duplicate: bool) -> ClauseRef {
    let lits = if duplicate {
        vec![neg(1), neg(0)]
    } else {
        vec![neg(1), neg(0), pos(2)]
    };
    // Both are genuine consequences of the original fork formula. This
    // candidate precedes the actual learned row in the ordinary eager window.
    s.add_learned_clause(lits, 2, &[1, 2, 3])
}

#[test]
fn actual_eager_window_preserves_long_garbage_dirty_watches_and_duplicate_binaries() {
    for duplicate in [false, true] {
        let (mut expected, reference, _) = fork(1, 0);
        let expected_candidate = add_subsumed_candidate(&mut expected, duplicate);
        expected.analyze_and_backtrack(reference, "eager parity", |_, _| {});
        assert!(expected.arena.is_garbage(expected_candidate.index()));
        let (mut s, reference, _) = fork(1, 0);
        let candidate = add_subsumed_candidate(&mut s, duplicate);
        attach(&mut s, &test_owner(100_000_000, 100_000_000));
        learn(&mut s, reference).unwrap();
        assert!(s.arena.is_garbage(candidate.index()));
        assert!(s.cold.num_eager_subsumptions > 0);
        if duplicate {
            assert!(s.cold.num_eager_subsumed_duplicate_binaries > 0);
        } else {
            assert!(!s.dirty_watch_list.is_empty());
        }
        parity(&s, &expected);
        clean(&s);
    }
}
