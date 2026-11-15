// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use crate::counted_storage::test_owner;
use ay_core::original_query::{
    CountedAdmission, CountedAdmissionError, FiniteAdmissionGrant, OriginalAdmissionError,
};
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};

mod controls;
mod semantics;
mod unwind;

fn pos(v: u32) -> Literal {
    Literal::positive(Variable(v))
}
fn neg(v: u32) -> Literal {
    pos(v).negated()
}

fn unsat() -> Solver {
    let mut s = Solver::new(2);
    s.enable_clause_trace();
    s.set_unsat_certificate_enabled(false);
    // Retain actual default retention; SmtContext sets only the option above.
    assert!(s.cold.retain_unsat_certificate);
    for a in [pos(0), neg(0)] {
        for b in [pos(1), neg(1)] {
            assert!(s.add_clause(vec![a, b]));
        }
    }
    s.initialize_watches();
    assert!(s.process_initial_clauses().is_none());
    assert!(s.trail.is_empty());
    assert!(!s.cold.ic3_mode && s.chrono_enabled);
    s
}
fn sat() -> Solver {
    let mut s = Solver::new(3);
    s.enable_clause_trace();
    s.set_unsat_certificate_enabled(false);
    assert!(s.add_clause(vec![pos(0), pos(1)]));
    s.initialize_watches();
    assert!(s.process_initial_clauses().is_none());
    s
}
fn attach(s: &mut Solver, owner: &CountedAdmission) {
    assert!(s.attach_counted_admission(owner.clone()).is_ok());
}
fn generous() -> CountedAdmission {
    test_owner(10_000_000, 10_000_000)
}
fn drive(s: &mut Solver) -> SatResult {
    s.cdcl_loop_main_no_tla(|| false, None)
}
fn rows(s: &Solver) -> Vec<(u64, Vec<Literal>, bool, Vec<u64>)> {
    s.clause_trace()
        .unwrap()
        .entries()
        .iter()
        .map(|e| {
            (
                e.id,
                e.clause.to_vec(),
                e.is_original,
                e.resolution_hints.to_vec(),
            )
        })
        .collect()
}
/// Per-variable assignment state without the conflict-analysis SEEN scratch.
fn assignments(s: &Solver) -> Vec<VarData> {
    s.var_data
        .iter()
        .map(|&data| {
            let mut data = data;
            data.set_seen(false);
            data
        })
        .collect()
}
fn clean(s: &Solver) {
    assert!(s.var_data.iter().all(|v| !v.is_seen()));
    assert!(s.conflict.analyzed_vars().is_empty());
    assert_eq!(s.conflict.learned_count(), 0);
    assert!(s.min.level_seen_to_clear.is_empty());
    assert!(s.min.minimize_to_clear.is_empty());
}
fn refused(s: &Solver, owner: &CountedAdmission) {
    assert!(owner.usage().unwrap().refusal.is_some());
    assert!(s.clause_trace().unwrap().proof_work_exhausted());
    assert!(s.cold.decision_trace.is_none());
    clean(s);
}
fn observing(cut: usize, calls: &Arc<AtomicUsize>) -> CountedAdmission {
    let observed = Arc::clone(calls);
    CountedAdmission::new(
        FiniteAdmissionGrant::new(10_000_000, 10_000_000),
        None,
        Arc::new(move || observed.fetch_add(1, Ordering::SeqCst) == cut),
    )
    .unwrap()
}
