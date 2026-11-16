// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::test_owner;
use ay_core::original_query::FiniteAdmissionGrant;
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};

mod controls;
mod semantics;

fn lit(index: u32) -> Literal {
    Literal::positive(Variable::new(index))
}

fn sync_frontier(s: &mut Solver) {
    let mut frontier = std::mem::take(&mut s.relevancy_frontier);
    frontier.sync(s);
    s.relevancy_frontier = frontier;
}

fn fixture(chrono: bool, ic3: bool) -> Solver {
    let mut s = Solver::new(8);
    if ic3 {
        s.set_ic3_mode();
    } else {
        s.set_chrono_enabled(chrono);
    }
    for clause in [
        vec![lit(0).negated(), lit(1)],
        vec![lit(1).negated(), lit(2)],
        vec![lit(3).negated(), lit(4), lit(5)],
        vec![lit(6)],
    ] {
        assert!(s.add_clause(clause));
    }
    s.initialize_watches();
    assert!(s.process_initial_clauses().is_none());
    assert!(s.search_propagate().is_none());
    for decision in [lit(0), lit(3), lit(4).negated()] {
        s.decide(decision);
        assert!(s.search_propagate().is_none());
    }
    assert_eq!(s.trail.len(), 7);
    assert_ne!(s.var_data[1].reason, s.var_data[0].reason);
    s.stable_mode = true;
    s.no_conflict_until = s.trail.len();
    s.target_trail_len = 0;
    s.best_trail_len = 0;
    s.cold.lrat_level0_unit_materialize_cursor = 1;
    s.cold.lrat_level0_unit_materialize_pinned = vec![0];
    // Exercise lazy membership/stack growth, not just an already-full queue.
    s.bucket_queue_active = true;
    s.active_domain = Some(vec![true; 8]);
    for &assigned in &s.trail {
        s.vsids.remove_from_heap(assigned.variable());
    }
    sync_frontier(&mut s);
    s
}

fn attach(s: &mut Solver, owner: &CountedAdmission) {
    assert!(s.attach_counted_admission(owner.clone()).is_ok());
}

fn run(s: &mut Solver, target: u32, ic3: bool) -> Result<(), SatUnknownReason> {
    if ic3 {
        s.backtrack_ic3_counted(target)
    } else {
        s.backtrack_counted(target)
    }
}

fn ordinary(s: &mut Solver, target: u32, ic3: bool) {
    if ic3 {
        s.backtrack_ic3(target);
    } else {
        s.backtrack(target);
    }
}

#[derive(Debug, PartialEq, Eq)]
struct State {
    trail: Vec<Literal>,
    limits: Vec<usize>,
    values: Vec<i8>,
    data: Vec<VarData>,
    phase: Vec<i8>,
    target: Vec<i8>,
    best: Vec<i8>,
    lambda: Vec<Option<ClauseRef>>,
    marks: Vec<u32>,
    invalidated: bool,
    counters: (u32, usize, usize, usize, usize, u64, u64, u32),
    lrat: (usize, Vec<usize>),
    vsids: String,
    frontier: String,
    ids: Vec<u64>,
}

fn state(s: &Solver) -> State {
    State {
        trail: s.trail.clone(),
        limits: s.trail_lim.clone(),
        values: s.vals.clone(),
        data: s.var_data.clone(),
        phase: s.phase.clone(),
        target: s.target_phase.clone(),
        best: s.best_phase.clone(),
        lambda: s.lambda.clone(),
        marks: s.reason_clause_marks.clone(),
        invalidated: s.reason_marks_invalidated,
        counters: (
            s.decision_level,
            s.qhead,
            s.no_conflict_until,
            s.target_trail_len,
            s.best_trail_len,
            s.stats.mli_reimplied,
            s.cold.last_target_improve_conflicts,
            s.reason_clause_epoch,
        ),
        lrat: (
            s.cold.lrat_level0_unit_materialize_cursor,
            s.cold.lrat_level0_unit_materialize_pinned.clone(),
        ),
        vsids: format!("{:?}", s.vsids),
        frontier: s.relevancy_frontier.backtrack_test_snapshot(),
        ids: s.cold.original_ledger.clause_ids().to_vec(),
    }
}

#[test]
fn real_trail_binary_reasons_phases_and_ic3_match_ordinary_backtracks() {
    for (chrono, ic3) in [(false, false), (true, false), (false, true)] {
        for target in [0, 1, 2, 3] {
            let mut expected = fixture(chrono, ic3);
            ordinary(&mut expected, target, ic3);
            let mut actual = fixture(chrono, ic3);
            let owner = test_owner(10_000_000, 10_000_000);
            attach(&mut actual, &owner);
            assert_eq!(run(&mut actual, target, ic3), Ok(()));
            assert_eq!(state(&actual), state(&expected));
            assert_eq!(
                actual.search_propagate_counted().unwrap(),
                expected.search_propagate()
            );
            assert_eq!(state(&actual), state(&expected));
        }
    }
}

fn lambda_fixture() -> Solver {
    let mut s = fixture(true, false);
    let offset = s
        .arena
        .add(&[lit(3), lit(0).negated(), lit(1).negated()], true);
    s.lambda[3] = Some(ClauseRef(offset as u32));
    // The successful reimplication must traverse its real clause, then grow
    // the reason-mark array before its final invalidation at backtrack exit.
    s.reason_marks_invalidated = false;
    s.reason_clause_marks.clear();
    s.reason_clause_marks.shrink_to_fit();
    s
}

#[test]
fn chrono_lambda_reimplication_grows_real_reason_marks_and_compacts_in_order() {
    let mut expected = lambda_fixture();
    expected.backtrack(1);
    assert_eq!(expected.var_data[3].level, 1);
    assert_eq!(expected.stats.mli_reimplied, 1);
    assert!(expected.trail.contains(&lit(3)));
    let mut actual = lambda_fixture();
    attach(&mut actual, &test_owner(10_000_000, 10_000_000));
    assert_eq!(actual.backtrack_counted(1), Ok(()));
    assert_eq!(state(&actual), state(&expected));
    assert_ne!(actual.reason_clause_marks.len(), 0);
}

#[test]
fn root_restart_keeps_out_of_order_root_literal_and_lrat_retry_cursor() {
    let make = || {
        let mut s = fixture(true, false);
        let root = s.arena.add(&[lit(7)], true);
        s.enqueue(lit(7), Some(ClauseRef(root as u32)));
        assert_eq!(s.var_data[7].level, 0);
        s
    };
    let mut expected = make();
    expected.backtrack(0);
    assert_eq!(expected.trail, vec![lit(6), lit(7)]);
    assert_eq!(expected.cold.lrat_level0_unit_materialize_cursor, 1);
    let mut actual = make();
    attach(&mut actual, &test_owner(10_000_000, 10_000_000));
    assert_eq!(actual.backtrack_counted(0), Ok(()));
    assert_eq!(state(&actual), state(&expected));
}

#[test]
fn without_phase_saving_uses_same_paid_kernel_without_touching_saved_phases() {
    let mut expected = fixture(true, false);
    expected.backtrack_without_phase_saving(1);
    let mut actual = fixture(true, false);
    attach(&mut actual, &test_owner(10_000_000, 10_000_000));
    assert_eq!(
        actual.backtrack_with_owner(1, Lane::Standard { save_phases: false }),
        Ok(())
    );
    assert_eq!(state(&actual), state(&expected));
}
