// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod controls;
mod cross_block;
mod unwind;

fn selected(length: u32, kind: Reasons) -> (Solver, ClauseRef, Vec<Vec<Literal>>) {
    let (mut s, conflict, clauses) = removable(length, kind);
    s.set_shrink_enabled(true);
    (s, conflict, clauses)
}

/// The level-2 block depends on an unkept level-1 decision. Block resolution
/// must fail and run recursive fallback, not drop the required dependency.
fn failed_block() -> (Solver, ClauseRef, Vec<Vec<Literal>>) {
    let clauses = vec![
        vec![neg(0), pos(1)],
        vec![neg(2), neg(0), pos(3)],
        vec![neg(2), neg(1), pos(4)],
        vec![neg(5), pos(6)],
        vec![neg(5), pos(7)],
        vec![neg(6), neg(7), neg(3), neg(4)],
    ];
    let mut s = Solver::new(8);
    s.set_ic3_mode();
    s.cold.jump_reasons_enabled = false;
    for clause in &clauses {
        assert!(s.add_clause(clause.clone()));
    }
    s.initialize_watches();
    for decision in [0, 2] {
        s.decide(pos(decision));
        assert!(s.search_propagate().is_none());
    }
    s.decide(pos(5));
    let conflict = s.search_propagate().unwrap();
    (s, conflict, clauses)
}

fn fully_retired(s: &mut Solver) {
    retired(s);
    assert!(s.ws_shrink_entries.is_empty());
    assert!(s.ws_shrink_result.is_empty());
    assert!(s.ws_shrink_block_lits.is_empty());
    assert!(s.ws_shrink_chain.is_empty());
    assert!(s.min.shrink_walked.is_empty());
    assert!(s.reap.is_empty());
}

fn counters(s: &Solver) -> [u64; 7] {
    [
        s.stats.shrink_block_attempts,
        s.stats.shrink_block_successes,
        s.stats.shrink_lits_block_removed,
        s.stats.shrink_lits_fallback_removed,
        s.stats.shrink_fail_lower,
        s.stats.shrink_fail_decision,
        s.search_ticks[usize::from(s.stable_mode)],
    ]
}

#[test]
fn real_clause_and_binary_blocks_shrink_with_ordinary_order_and_counters() {
    for kind in [Reasons::Long, Reasons::Binary] {
        for length in [2, 5, 17] {
            let (mut actual, conflict, _) = selected(length, kind);
            let (mut ordinary, other, _) = selected(length, kind);
            let expected = ordinary_minimize(&mut ordinary, other);
            let before = state(&actual);
            attach(&mut actual, &test_owner(10_000_000, 10_000_000));
            assert_eq!(minimize(&mut actual, conflict), Ok(expected));
            assert!(actual.stats.shrink_block_successes > 0);
            assert_eq!(counters(&actual), counters(&ordinary));
            assert_eq!(state(&actual), before);
            fully_retired(&mut actual);
        }
    }
}

#[test]
fn real_lower_dependency_forces_failed_block_fallback_with_exact_ordinary_literals() {
    let (mut actual, conflict, _) = failed_block();
    let (mut ordinary, other, _) = failed_block();
    let expected = ordinary_minimize(&mut ordinary, other);
    assert!(ordinary.stats.shrink_fail_lower > 0);
    assert_eq!(ordinary.stats.shrink_block_successes, 0);
    attach(&mut actual, &test_owner(10_000_000, 10_000_000));
    assert_eq!(minimize(&mut actual, conflict), Ok(expected));
    assert_eq!(counters(&actual), counters(&ordinary));
    fully_retired(&mut actual);
}

#[test]
fn shrunken_and_fallback_clauses_hold_in_every_original_cnf_model() {
    for (mut actual, conflict, clauses) in [
        selected(2, Reasons::Long),
        selected(2, Reasons::Binary),
        failed_block(),
    ] {
        let variables = actual.num_vars;
        attach(&mut actual, &test_owner(10_000_000, 10_000_000));
        let result = minimize(&mut actual, conflict).unwrap();
        let learned: Vec<_> = std::iter::once(result.uip).chain(result.lower).collect();
        let satisfies = |clause: &[Literal], bits: usize| {
            clause
                .iter()
                .any(|lit| ((bits >> lit.variable().index()) & 1 != 0) == lit.is_positive())
        };
        let mut models = 0;
        for bits in 0..(1usize << variables) {
            if clauses.iter().all(|clause| satisfies(clause, bits)) {
                models += 1;
                assert!(satisfies(&learned, bits), "model {bits}");
            }
        }
        assert!(models > 0);
    }
}

#[test]
fn selected_walked_promotion_uip_bump_and_stamp_wrap_match_ordinary() {
    for walked in [false, true] {
        for bump in [false, true] {
            let configure = |s: &mut Solver| {
                s.cold.shrink_removable_kissat = walked;
                s.cold.shrink_bump_uip_kissat = bump;
                s.shrink_stamp_counter = u32::MAX;
                s.shrink_stamp.fill(99);
            };
            let (mut actual, conflict, _) = selected(5, Reasons::Long);
            let (mut ordinary, other, _) = selected(5, Reasons::Long);
            configure(&mut actual);
            configure(&mut ordinary);
            let expected = ordinary_minimize(&mut ordinary, other);
            attach(&mut actual, &test_owner(10_000_000, 10_000_000));
            assert_eq!(minimize(&mut actual, conflict), Ok(expected));
            assert_eq!(actual.shrink_stamp, ordinary.shrink_stamp);
            assert_eq!(actual.shrink_stamp_counter, ordinary.shrink_stamp_counter);
            assert_eq!(counters(&actual), counters(&ordinary));
            fully_retired(&mut actual);
        }
    }
}

#[test]
fn ordinary_lrat_block_route_retains_exact_removed_literals_and_reason_ids() {
    let (mut s, conflict, _) = selected(3, Reasons::Long);
    ordinary(&mut s, conflict).unwrap();
    // This is an ordinary shared-kernel control, not a counted proof claim.
    // IDs are the real registered original-clause IDs already in the arena.
    s.cold.lrat_enabled = true;
    let mut expected = Vec::new();
    for var in (2..=4).rev() {
        expected.push(s.clause_id(s.var_reason(var).unwrap()));
    }
    assert!(expected.iter().all(|id| *id != 0));
    let mut removed = Vec::new();
    let count = s.conflict.learned_count();
    assert_eq!(count, 2);
    s.shrink_and_minimize_repeated_level_learned_clause_collect_removed(count, Some(&mut removed));
    assert_eq!(s.conflict.counted_ic3_lower_literals(), &[neg(1)]);
    assert_eq!(removed, [neg(4)]);
    assert_eq!(s.ws_shrink_chain, expected);
    assert_eq!(s.conflict.resolution_chain_len(), expected.len());
    assert_eq!(s.stats.shrink_block_successes, 1);
    assert!(s.min.minimize_to_clear.is_empty());
}

#[test]
fn ordinary_standard_analysis_uses_shared_repeated_block_engine() {
    let (_, _, clauses) = selected(3, Reasons::Long);
    let mut s = Solver::new(8);
    // Same trace/preprocessing posture as SmtContext::build_cnf, no IC3 switch.
    s.enable_clause_trace();
    s.set_unsat_certificate_enabled(false);
    s.set_preprocess_enabled(false);
    for clause in clauses {
        assert!(s.add_clause(clause));
    }
    s.initialize_watches();
    assert!(s.process_initial_clauses().is_none());
    assert!(s.search_propagate().is_none());
    s.decide(pos(1));
    assert!(s.search_propagate().is_none());
    s.decide(pos(5));
    let conflict = s.search_propagate().unwrap();
    let result = s.analyze_conflict(conflict).unwrap();
    assert!(!s.is_ic3_mode());
    assert!(s.shrink_enabled);
    assert_eq!(result.learned_clause, [neg(5), neg(1)]);
    assert!(s.stats.shrink_block_successes > 0);
}
