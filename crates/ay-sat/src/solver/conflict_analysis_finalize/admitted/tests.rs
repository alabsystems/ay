// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::counted_storage::test_owner;
use ay_core::original_query::FiniteAdmissionGrant;
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};

mod controls;
mod reason;

fn pos(var: u32) -> Literal {
    Literal::positive(Variable::new(var))
}
fn neg(var: u32) -> Literal {
    pos(var).negated()
}

/// Default ordinary BCP: x0 implies both lower literals; the high fork has
/// different guards, preventing OTFS without disabling it. Finalization must
/// really collapse the repeated lower block to its common UIP.
fn fixture(shrink: bool, heuristic: BranchHeuristic) -> (Solver, ClauseRef, Vec<Vec<Literal>>) {
    fixture_tracking(shrink, heuristic, Tracking::Untraced)
}

enum Tracking {
    Untraced,
    Traced,
}

fn fixture_tracking(
    shrink: bool,
    heuristic: BranchHeuristic,
    tracking: Tracking,
) -> (Solver, ClauseRef, Vec<Vec<Literal>>) {
    let clauses = vec![
        vec![neg(0), pos(1)],
        vec![neg(0), pos(2)],
        vec![neg(4), pos(5), neg(1)],
        vec![neg(4), pos(6), neg(2)],
        vec![neg(5), neg(6), neg(3)],
    ];
    let mut s = Solver::new(7);
    assert!(s.shrink_enabled && !s.cold.ic3_mode);
    if matches!(tracking, Tracking::Traced) {
        s.enable_clause_trace();
    }
    s.set_shrink_enabled(shrink);
    s.set_branch_heuristic(heuristic);
    for clause in &clauses {
        assert!(s.add_clause(clause.clone()));
    }
    s.initialize_watches();
    for var in [0, 3] {
        s.decide(pos(var));
        assert!(s.search_propagate().is_none());
    }
    s.decide(pos(4));
    let conflict = s
        .search_propagate()
        .expect("actual guarded fork must conflict");
    (s, conflict, clauses)
}

#[derive(Debug, PartialEq, Eq)]
struct Learned {
    clause: Vec<Literal>,
    backtrack: u32,
    lbd: u32,
}

fn run(s: &mut Solver, conflict: ClauseRef) -> Result<Learned, SatUnknownReason> {
    let scope = s
        .begin_counted_standard_analysis(conflict)?
        .expect("nonroot conflict");
    let result = Learned {
        clause: scope.learned_clause().to_vec(),
        backtrack: scope.backtrack_level(),
        lbd: scope.lbd(),
    };
    scope.finish()?;
    Ok(result)
}

fn ordinary(s: &mut Solver, conflict: ClauseRef) -> Learned {
    let result = s
        .analyze_conflict(conflict)
        .expect("ordinary guarded conflict");
    Learned {
        clause: result.learned_clause,
        backtrack: result.backtrack_level,
        lbd: result.lbd,
    }
}

fn attach(s: &mut Solver, owner: &CountedAdmission) {
    assert!(s.attach_counted_admission(owner.clone()).is_ok());
}

fn counters(s: &Solver) -> [u64; 8] {
    [
        s.stats.shrink_lits_deduced,
        s.stats.shrink_block_attempts,
        s.stats.shrink_block_successes,
        s.stats.shrink_lits_block_removed,
        s.stats.shrink_lits_fallback_removed,
        s.stats.shrink_singleton_fast_path_skips,
        s.search_ticks[0],
        s.search_ticks[1],
    ]
}

fn clean(s: &mut Solver) {
    assert!(s.var_data.iter().all(|vd| !vd.is_seen()));
    assert!(s.min.minimize_to_clear.is_empty());
    assert!(s.min.minimize_flags.iter().all(|&flags| flags == 0));
    assert!(s.min.minimize_levels_to_clear.is_empty());
    assert!(s.conflict.clause_buf_mut().is_empty());
    assert!(s.conflict.analyzed_vars().is_empty());
    assert_eq!(s.conflict.learned_count(), 0);
    assert!(s.ws_shrink_entries.is_empty() && s.ws_shrink_result.is_empty());
    assert!(s.ws_shrink_block_lits.is_empty() && s.ws_shrink_chain.is_empty());
    assert!(s.min.shrink_walked.is_empty() && s.reap.is_empty());
    assert!(s.bump_order_sort_buf.is_empty());
}

#[test]
fn real_standard_block_shrink_and_plain_minimize_match_all_activity_modes() {
    for shrink in [true, false] {
        for heuristic in [
            BranchHeuristic::Evsids,
            BranchHeuristic::Chb,
            BranchHeuristic::Vmtf,
        ] {
            let (mut actual, conflict, _) = fixture(shrink, heuristic);
            let (mut expected, other, _) = fixture(shrink, heuristic);
            let learned = ordinary(&mut expected, other);
            let owner = test_owner(10_000_000, 10_000_000);
            attach(&mut actual, &owner);
            assert_eq!(run(&mut actual, conflict).unwrap(), learned);
            assert_eq!(counters(&actual), counters(&expected));
            assert_eq!(
                format!("{:?}", actual.vsids),
                format!("{:?}", expected.vsids)
            );
            if shrink {
                assert!(actual.stats.shrink_block_successes > 0);
                assert!(actual.stats.shrink_lits_block_removed > 0);
            }
            assert!(!actual.cold.ic3_mode);
            assert!(owner.usage().unwrap().work_admitted > 0);
            clean(&mut actual);
        }
    }
}

#[test]
fn actual_learned_clause_is_entailed_by_every_original_cnf_model() {
    let (mut s, conflict, clauses) = fixture(true, BranchHeuristic::Evsids);
    attach(&mut s, &test_owner(10_000_000, 10_000_000));
    let result = run(&mut s, conflict).unwrap();
    let mut models = 0;
    for bits in 0..128 {
        let holds = |lit: Literal| ((bits >> lit.variable().index()) & 1 != 0) == lit.is_positive();
        if clauses
            .iter()
            .all(|clause| clause.iter().copied().any(&holds))
        {
            models += 1;
            assert!(result.clause.iter().copied().any(&holds));
        }
    }
    assert!(models > 0);
    assert_eq!(result.backtrack, 2);
    assert_eq!(result.clause[0], neg(4));
}

#[test]
fn kissat_stable_level_order_preserves_equal_level_analysis_order_at_every_cut() {
    let data: Vec<_> = (0..17)
        .map(|i| VarData {
            level: (i % 4) as u32,
            ..VarData::UNASSIGNED
        })
        .collect();
    let input: Vec<_> = (0..17).rev().map(pos).collect();
    let mut expected = input.clone();
    expected.sort_by_key(|lit| std::cmp::Reverse(data[lit.variable().index()].level));
    let owner = test_owner(1_000_000, 1_000_000);
    let mut actual = input.clone();
    sort::stable_by_level(&mut actual, &data, &owner).unwrap();
    assert_eq!(actual, expected);
    for work in 0..owner.usage().unwrap().work_admitted {
        let owner = test_owner(work, 1_000_000);
        assert_eq!(
            sort::stable_by_level(&mut input.clone(), &data, &owner),
            Err(CountedAdmissionError::WorkExhausted)
        );
    }
}

#[test]
fn ordinary_unstable_sort_ties_match_including_stale_ghost_positions() {
    use crate::solver::conflict_analysis_minimize::admitted::Policy as Minimize;
    let data: Vec<_> = (0..65)
        .map(|i| VarData {
            trail_pos: (i % 3) as u32,
            ..VarData::UNASSIGNED
        })
        .collect();
    let mut actual: Vec<_> = (0..65).rev().map(pos).collect();
    let mut expected = actual.clone();
    Minimize::sort(&Ordinary, &mut expected, &data).unwrap();
    Minimize::sort(
        &Counted(&test_owner(10_000_000, 10_000_000)),
        &mut actual,
        &data,
    )
    .unwrap();
    assert_eq!(actual, expected);
}
