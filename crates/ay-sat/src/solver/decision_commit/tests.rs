// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::test_owner;
use ay_core::original_query::FiniteAdmissionGrant;
use std::sync::atomic::AtomicUsize;

mod controls;
mod trace;

fn lit(index: u32) -> Literal {
    Literal::positive(Variable::new(index))
}

fn fixture() -> Solver {
    let mut s = Solver::new(8);
    assert!(s.add_clause(vec![lit(0).negated(), lit(1)]));
    assert!(s.add_clause(vec![lit(1).negated(), lit(2)]));
    assert!(s.add_clause(vec![lit(3).negated(), lit(4)]));
    s.initialize_watches();
    s.decide(lit(0));
    assert!(s.search_propagate().is_none());
    assert_eq!(s.trail.len(), 3);
    s.var_data[3].flags = VarData::FLAG_SEEN_PUB | VarData::FLAG_BINARY_REASON_PUB;
    s.reason_marks_invalidated = false;
    s.trail.shrink_to_fit();
    s.trail_lim.shrink_to_fit();
    s
}

fn attach(s: &mut Solver, owner: &CountedAdmission) {
    assert!(s.attach_counted_admission(owner.clone()).is_ok());
}

#[derive(Debug, PartialEq, Eq)]
struct State {
    trail: Vec<Literal>,
    limits: Vec<usize>,
    vals: Vec<i8>,
    data: Vec<VarData>,
    phase: Vec<i8>,
    marks: (Vec<u32>, bool),
    counters: (u32, usize, u64, u64, u64, u32, u64, u64),
    ids: Vec<u64>,
}

fn state(s: &Solver) -> State {
    State {
        trail: s.trail.clone(),
        limits: s.trail_lim.clone(),
        vals: s.vals.clone(),
        data: s.var_data.clone(),
        phase: s.phase.clone(),
        marks: (s.reason_clause_marks.clone(), s.reason_marks_invalidated),
        counters: (
            s.decision_level,
            s.qhead,
            s.num_decisions,
            s.stats.stable_decisions,
            s.stats.focused_decisions,
            s.stats.peak_decision_level,
            s.stats.decision_level_sum,
            s.stats.decision_level_count,
        ),
        ids: s.cold.original_ledger.clause_ids().to_vec(),
    }
}

fn legacy_general_enqueue_decision(s: &mut Solver, lit: Literal) {
    // The old decide sequence, independently using GENERAL enqueue(None).
    s.decision_level += 1;
    s.trail_lim.push(s.trail.len());
    s.num_decisions += 1;
    s.stats.record_decision_level(s.decision_level);
    if s.stable_mode {
        s.stats.stable_decisions += 1;
    } else {
        s.stats.focused_decisions += 1;
    }
    s.trace_decide(lit);
    s.enqueue(lit, None);
    s.log_decision(lit);
}

#[test]
fn real_decision_matches_general_enqueue_for_modes_phases_flags_and_chrono() {
    for chrono in [false, true] {
        for stable in [false, true] {
            for suppress in [false, true] {
                let make = || {
                    let mut s = fixture();
                    s.chrono_enabled = chrono;
                    s.stable_mode = stable;
                    s.suppress_phase_saving = suppress;
                    s.phase[3] = -1;
                    s
                };
                let mut expected = make();
                legacy_general_enqueue_decision(&mut expected, lit(3));
                let mut ordinary = make();
                ordinary.decide(lit(3));
                assert_eq!(state(&ordinary), state(&expected));
                let mut actual = make();
                attach(&mut actual, &test_owner(10_000_000, 10_000_000));
                assert_eq!(actual.decide_counted(lit(3)), Ok(()));
                assert_eq!(state(&actual), state(&expected));
                assert_eq!(actual.var_data[3].flags, VarData::FLAG_SEEN_PUB);
                assert!(!actual.reason_marks_invalidated);
                assert_eq!(
                    actual.search_propagate_counted().unwrap(),
                    expected.search_propagate()
                );
                assert_eq!(state(&actual), state(&expected));
            }
        }
    }
}

#[test]
fn ownerless_decision_uses_the_same_real_ordinary_kernel() {
    let mut expected = fixture();
    expected.decide(lit(3).negated());
    let mut actual = fixture();
    assert_eq!(actual.decide_counted(lit(3).negated()), Ok(()));
    assert_eq!(state(&actual), state(&expected));
}

#[test]
fn selected_literal_can_feed_paid_decide_and_actual_paid_search_bcp() {
    let mut expected = fixture();
    let var = expected.pick_next_decision_variable().unwrap();
    let selected = expected.pick_phase(var);
    expected.decide(selected);
    let conflict = expected.search_propagate();
    let mut actual = fixture();
    attach(&mut actual, &test_owner(10_000_000, 10_000_000));
    let selected = actual
        .pick_next_decision_literal_counted()
        .unwrap()
        .unwrap();
    assert_eq!(actual.decide_counted(selected), Ok(()));
    assert_eq!(actual.search_propagate_counted().unwrap(), conflict);
    assert_eq!(state(&actual), state(&expected));
}
