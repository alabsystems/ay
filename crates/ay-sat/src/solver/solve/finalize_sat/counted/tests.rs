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

mod legacy_sweep;
mod models;
mod resources;
mod unwind;

fn pos(v: u32) -> Literal {
    Literal::positive(Variable(v))
}
fn neg(v: u32) -> Literal {
    pos(v).negated()
}
fn owner() -> CountedAdmission {
    test_owner(1_000_000, 1_000_000)
}
fn attach(s: &mut Solver, owner: &CountedAdmission) {
    assert!(s.attach_counted_admission(owner.clone()).is_ok());
}

fn assigned() -> Solver {
    let mut s = Solver::new(3);
    s.enable_clause_trace();
    s.set_unsat_certificate_enabled(false);
    assert!(s.add_clause(vec![pos(0), pos(1)]));
    s.initialize_watches();
    assert!(s.process_initial_clauses().is_none());
    s.decide(pos(0));
    assert!(s.propagate().is_none());
    s.decide(neg(1));
    assert!(s.propagate().is_none());
    s.decide(pos(2));
    assert!(s.propagate().is_none());
    assert_eq!(s.trail.len(), 3);
    s
}

fn reconstructed() -> Solver {
    let mut s = Solver::new(3);
    s.enable_clause_trace();
    s.set_unsat_certificate_enabled(false);
    let first = vec![pos(0), pos(1)];
    let second = vec![neg(0), pos(2)];
    assert!(s.add_clause(first.clone()));
    assert!(s.add_clause(second.clone()));
    let indices: Vec<_> = s.arena.indices().collect();
    for index in indices {
        s.arena.mark_garbage_keep_data(index);
    }
    s.var_lifecycle.mark_eliminated(0);
    s.inproc
        .reconstruction
        .push_witness_clause(vec![pos(0)], first);
    s.inproc
        .reconstruction
        .push_witness_clause(vec![neg(0)], second);
    s.initialize_watches();
    assert!(s.process_initial_clauses().is_none());
    s.decide(neg(1));
    assert!(s.propagate().is_none());
    s.decide(pos(2));
    assert!(s.propagate().is_none());
    assert_eq!(s.get_model(), vec![false, false, true]);
    s
}

fn refused(s: &Solver, owner: &CountedAdmission) {
    assert!(owner.usage().unwrap().refusal.is_some());
    assert!(s.clause_trace().unwrap().proof_work_exhausted());
    assert!(s.cold.decision_trace.is_none());
}

fn observed(cut: usize, calls: &Arc<AtomicUsize>) -> CountedAdmission {
    let seen = Arc::clone(calls);
    CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1_000_000),
        None,
        Arc::new(move || seen.fetch_add(1, Ordering::SeqCst) == cut),
    )
    .unwrap()
}
