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

fn fixture(heuristic: BranchHeuristic) -> Solver {
    let mut s = Solver::new(12);
    s.active_branch_heuristic = heuristic;
    s.stable_mode = true;
    s.cold.random_var_freq = 0.0;
    for clause in [
        vec![lit(0).negated(), lit(1)],
        vec![lit(1).negated(), lit(2)],
        vec![lit(3), lit(4), lit(5)],
        vec![lit(6), lit(7)],
    ] {
        assert!(s.add_clause(clause));
    }
    s.initialize_watches();
    assert!(s.process_initial_clauses().is_none());
    s.decide(lit(0));
    assert!(s.search_propagate().is_none());
    assert_eq!(s.trail.len(), 3);
    assert_ne!(s.var_data[0].reason, s.var_data[1].reason);
    for i in 0..12 {
        s.vsids.set_activity(Variable::new(i), (12 - i) as f64);
    }
    s.var_lifecycle.mark_eliminated(8);
    s
}

fn domain_fixture() -> Solver {
    let mut s = fixture(BranchHeuristic::Evsids);
    s.active_domain = Some(vec![true; 12]);
    let mut domain = vec![false; 12];
    domain[6] = true;
    s.decision_domain = Some(domain);
    s
}

fn frontier_fixture() -> Solver {
    let mut s = fixture(BranchHeuristic::Evsids);
    s.set_relevancy_branching(true);
    s.set_relevancy_hard(true);
    s
}

fn attach(s: &mut Solver, owner: &CountedAdmission) {
    assert!(s.attach_counted_admission(owner.clone()).is_ok());
}

fn ordinary(s: &mut Solver) -> Option<Literal> {
    s.pick_next_decision_variable().map(|var| s.pick_phase(var))
}

#[derive(Debug, PartialEq, Eq)]
struct State {
    trail: Vec<Literal>,
    limits: Vec<usize>,
    values: Vec<i8>,
    data: Vec<VarData>,
    domains: (Option<Vec<bool>>, Option<Vec<bool>>),
    support: Vec<u32>,
    phases: (Vec<i8>, Vec<i8>, Vec<i8>),
    counters: (u32, usize, u64, u64, u64, u64, u64, u64),
    random: (u64, u64, u64),
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
        domains: (s.active_domain.clone(), s.decision_domain.clone()),
        support: s.indep_support.clone(),
        phases: (
            s.phase.clone(),
            s.target_phase.clone(),
            s.cold.forced_phase.clone(),
        ),
        counters: (
            s.decision_level,
            s.qhead,
            s.num_decisions,
            s.num_conflicts,
            s.stats.indep_support_decisions,
            s.stats.indep_support_fallback_decisions,
            s.stats.random_decisions,
            s.relevancy_decisions,
        ),
        random: (
            s.cold.random_decision_phases,
            s.cold.randomized_deciding,
            s.cold.next_random_decision,
        ),
        vsids: format!("{:?}", s.vsids),
        frontier: s.relevancy_frontier.backtrack_test_snapshot(),
        ids: s.cold.original_ledger.clause_ids().to_vec(),
    }
}

fn assert_parity(make: impl Fn() -> Solver) {
    let mut expected = make();
    let result = ordinary(&mut expected);
    let mut actual = make();
    let owner = test_owner(10_000_000, 10_000_000);
    attach(&mut actual, &owner);
    assert_eq!(actual.pick_next_decision_literal_counted(), Ok(result));
    assert_eq!(state(&actual), state(&expected));
    assert!(owner.usage().unwrap().work_admitted > 0);
    // Selection itself must not assign, change BCP reasons, or issue an ID.
    let initial = make();
    assert_eq!(actual.trail, initial.trail);
    assert_eq!(actual.var_data, initial.var_data);
    assert_eq!(
        actual.cold.original_ledger.clause_ids(),
        initial.cold.original_ledger.clause_ids()
    );
}

#[test]
fn real_bcp_reason_heap_domain_and_vmtf_selection_match_ordinary() {
    for heuristic in [
        BranchHeuristic::Evsids,
        BranchHeuristic::Chb,
        BranchHeuristic::Vmtf,
    ] {
        assert_parity(|| fixture(heuristic));
        assert_parity(|| {
            let mut s = domain_fixture();
            s.active_branch_heuristic = heuristic;
            s
        });
    }
}

#[test]
fn relevancy_first_rebuild_and_selected_phase_match_ordinary() {
    assert_parity(frontier_fixture);
}

#[test]
fn ordinary_ownerless_entry_retains_existing_selection() {
    let mut expected = domain_fixture();
    let result = ordinary(&mut expected);
    let mut actual = domain_fixture();
    assert_eq!(actual.pick_next_decision_literal_counted(), Ok(result));
    assert_eq!(state(&actual), state(&expected));
}
