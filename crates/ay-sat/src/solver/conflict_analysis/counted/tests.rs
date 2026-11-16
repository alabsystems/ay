// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::counted_storage::test_owner;
use ay_core::original_query::FiniteAdmissionGrant;
use std::sync::{
    atomic::{AtomicBool, AtomicUsize, Ordering},
    Arc,
};

mod controls;
mod learning;
mod selected;
mod semantics;
mod unwind;

#[derive(Clone, Copy)]
enum Reasons {
    Binary,
    Long,
}
fn pos(var: u32) -> Literal {
    Literal::positive(Variable::new(var))
}
fn neg(var: u32) -> Literal {
    pos(var).negated()
}

/// Actual default-mode BCP, two distinct lower decision guards, and two
/// implication chains meeting at a conflict. Distinct guards prevent OTFS
/// selection without disabling the algorithm.
fn fork_formula(length: u32, reasons: Reasons) -> (Solver, Vec<Vec<Literal>>) {
    let mut s = Solver::new((3 + 2 * length) as usize);
    s.cold.jump_reasons_enabled = matches!(reasons, Reasons::Binary);
    if matches!(reasons, Reasons::Long) {
        s.enable_clause_trace();
    }
    s.set_unsat_certificate_enabled(false);
    s.set_preprocess_enabled(false);
    let mut clauses = Vec::new();
    for (guard, start) in [(0, 3), (1, 3 + length)] {
        let mut previous = 2;
        for next in start..start + length {
            let mut clause = vec![neg(previous), pos(next)];
            if matches!(reasons, Reasons::Long) {
                clause.push(neg(guard));
            }
            clauses.push(clause);
            previous = next;
        }
    }
    let mut conflict = vec![neg(2 + length), neg(2 + 2 * length)];
    if matches!(reasons, Reasons::Binary) {
        conflict.extend([neg(0), neg(1)]);
    }
    clauses.push(conflict);
    (s, clauses)
}

fn fixture(length: u32, reasons: Reasons) -> (Solver, ClauseRef, Vec<Vec<Literal>>) {
    let (mut s, clauses) = fork_formula(length, reasons);
    for clause in &clauses {
        assert!(s.add_clause(clause.clone()));
    }
    s.initialize_watches();
    for var in [0, 1] {
        s.decide(pos(var));
        assert!(s.search_propagate().is_none());
    }
    s.decide(pos(2));
    let conflict = s.search_propagate().expect("actual forked BCP conflict");
    assert!(!s.cold.ic3_mode);
    assert!(s.chrono_enabled);
    (s, conflict, clauses)
}

fn attach(s: &mut Solver, owner: &CountedAdmission) {
    assert!(s.attach_counted_admission(owner.clone()).is_ok());
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Learned {
    clause: Vec<Literal>,
    backtrack: u32,
    lbd: u32,
    chain: Vec<u64>,
}

fn run(s: &mut Solver, conflict: ClauseRef) -> Result<Option<Learned>, SatUnknownReason> {
    let Some(scope) = s.begin_counted_standard_analysis(conflict)? else {
        return Ok(None);
    };
    let result = Learned {
        clause: scope.learned_clause().to_vec(),
        backtrack: scope.backtrack_level(),
        lbd: scope.lbd(),
        chain: scope.resolution_chain().to_vec(),
    };
    scope.finish()?;
    Ok(Some(result))
}

fn ordinary(s: &mut Solver, conflict: ClauseRef) -> Option<Learned> {
    s.analyze_conflict(conflict).map(|result| Learned {
        clause: result.learned_clause,
        backtrack: result.backtrack_level,
        lbd: result.lbd,
        chain: result.resolution_chain,
    })
}

fn clean(s: &Solver) {
    assert!(s.var_data.iter().all(|data| !data.is_seen()));
    assert_eq!(s.conflict.analyzed_vars().len(), 0);
    assert_eq!(s.conflict.learned_count(), 0);
    assert_eq!(s.min.level_seen_to_clear.len(), 0);
    assert!(s
        .min
        .level_seen
        .iter()
        .all(|level| *level == minimization_state::LevelSeen::EMPTY));
    assert_eq!(s.min.minimize_to_clear.len(), 0);
    assert!(s.min.minimize_flags.iter().all(|flags| *flags == 0));
    assert_eq!(s.min.minimize_levels_to_clear.len(), 0);
    assert!(s
        .min
        .minimize_level_seen
        .iter()
        .all(|level| *level == minimization_state::LevelSeen::EMPTY));
    assert_eq!(s.ws_shrink_entries.len(), 0);
    assert_eq!(s.ws_shrink_result.len(), 0);
    assert_eq!(s.ws_shrink_block_lits.len(), 0);
}

fn clauses(s: &Solver) -> Vec<Vec<Literal>> {
    s.arena
        .indices()
        .map(|offset| s.arena.literals(offset).to_vec())
        .collect()
}

fn observing_owner(stop: usize, calls: &Arc<AtomicUsize>) -> CountedAdmission {
    let calls = Arc::clone(calls);
    CountedAdmission::new(
        FiniteAdmissionGrant::new(100_000_000, 100_000_000),
        None,
        Arc::new(move || calls.fetch_add(1, Ordering::SeqCst) == stop),
    )
    .unwrap()
}
