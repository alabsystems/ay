// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::counted::CountedDispatchStep;
use super::*;
use crate::counted_storage::test_owner;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError, FiniteAdmissionGrant};
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};

mod controls;
mod semantics;
mod unwind;
mod watches;

fn pos(var: u32) -> Literal {
    Literal::positive(Variable::new(var))
}
fn neg(var: u32) -> Literal {
    pos(var).negated()
}

fn configured(vars: usize) -> Solver {
    let mut s = Solver::new(vars);
    s.enable_clause_trace();
    s.set_unsat_certificate_enabled(false);
    s.set_preprocess_enabled(false);
    s
}

fn attach(s: &mut Solver, owner: &CountedAdmission) {
    assert!(s.attach_counted_admission(owner.clone()).is_ok());
}

fn generous() -> CountedAdmission {
    test_owner(100_000_000, 100_000_000)
}

fn fork(guards: u32, gap: u32) -> (Solver, ClauseRef, Vec<Vec<Literal>>) {
    let decision = guards + gap;
    let mut s = configured((decision + 3) as usize);
    let mut source = Vec::new();
    for next in [decision + 1, decision + 2] {
        let mut clause = vec![neg(decision), pos(next)];
        clause.extend((0..guards).map(neg));
        source.push(clause);
    }
    source.push(vec![neg(decision + 1), neg(decision + 2)]);
    for clause in &source {
        assert!(s.add_clause(clause.clone()));
    }
    s.initialize_watches();
    for var in 0..decision {
        s.decide(pos(var));
        assert!(s.search_propagate().is_none());
    }
    s.decide(pos(decision));
    let conflict = s.search_propagate().expect("actual BCP fork conflict");
    assert!(s.chrono_enabled && !s.cold.ic3_mode && s.cold.lrat_enabled);
    (s, conflict, source)
}

fn global_unit() -> (Solver, ClauseRef) {
    let mut s = configured(3);
    assert!(s.add_clause(vec![pos(0), pos(1)]));
    s.initialize_watches();
    s.decide(neg(0));
    assert!(s.search_propagate().is_none());
    let reference = s.add_theory_lemma(vec![pos(0)]).unwrap();
    assert_eq!(s.take_live_pending_theory_conflict(), Some(reference));
    (s, reference)
}

fn forced() -> (Solver, ClauseRef) {
    let mut s = configured(4);
    s.initialize_watches();
    for var in 0..3 {
        s.decide(pos(var));
        assert!(s.search_propagate().is_none());
    }
    let reference = s.add_theory_lemma(vec![neg(0), neg(1), neg(2)]).unwrap();
    assert_eq!(s.take_live_pending_theory_conflict(), Some(reference));
    (s, reference)
}

fn delayed() -> (Solver, ClauseRef) {
    let mut s = configured(6);
    for (guard, next) in [(0, 3), (1, 4)] {
        assert!(s.add_clause(vec![neg(2), pos(next), neg(guard)]));
    }
    s.initialize_watches();
    for var in [0, 1, 2, 5] {
        s.decide(pos(var));
        assert!(s.search_propagate().is_none());
    }
    let reference = s.add_theory_lemma(vec![neg(3), neg(4)]).unwrap();
    assert_eq!(s.take_live_pending_theory_conflict(), Some(reference));
    assert!(s.var_data[3].level < s.decision_level);
    (s, reference)
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

fn parity(s: &Solver, expected: &Solver) {
    assert_eq!(s.trail, expected.trail);
    assert_eq!(s.trail_lim, expected.trail_lim);
    assert_eq!(s.vals, expected.vals);
    assert_eq!(s.phase, expected.phase);
    assert_eq!(s.qhead, expected.qhead);
    assert_eq!(s.decision_level, expected.decision_level);
    assert_eq!(s.fixed_count, expected.fixed_count);
    assert_eq!(s.stats.forced_backtracks, expected.stats.forced_backtracks);
    assert_eq!(s.unit_proof_id, expected.unit_proof_id);
    assert_eq!(s.unit_proof_sign, expected.unit_proof_sign);
    assert_eq!(
        s.pending_theory_unit_proof_ids,
        expected.pending_theory_unit_proof_ids
    );
    assert_eq!(
        s.cold.lrat_level0_unit_materialize_pinned,
        expected.cold.lrat_level0_unit_materialize_pinned
    );
    assert_eq!(s.cold.clause_ids, expected.cold.clause_ids);
    assert_eq!(rows(s), rows(expected));
    let clauses = |solver: &Solver| {
        solver
            .arena
            .indices()
            .map(|offset| solver.arena.literals(offset).to_vec())
            .collect::<Vec<_>>()
    };
    assert_eq!(clauses(s), clauses(expected));
    for var in 0..s.num_vars {
        let a = s.var_data[var];
        let b = expected.var_data[var];
        assert_eq!(
            (a.level, a.trail_pos, a.reason),
            (b.level, b.trail_pos, b.reason)
        );
        for lit in [pos(var as u32), neg(var as u32)] {
            assert_eq!(
                s.watches.entry_slice(lit),
                expected.watches.entry_slice(lit)
            );
            assert_eq!(
                s.watches.capacity_of(lit),
                expected.watches.capacity_of(lit)
            );
        }
        assert_eq!(
            s.vsids.activity(Variable(var as u32)).to_bits(),
            expected.vsids.activity(Variable(var as u32)).to_bits()
        );
    }
}

fn clean(s: &Solver) {
    assert!(s.var_data.iter().all(|data| !data.is_seen()));
    assert_eq!(s.conflict.analyzed_vars().len(), 0);
    assert_eq!(s.conflict.learned_count(), 0);
    assert_eq!(s.min.level_seen_to_clear.len(), 0);
    assert_eq!(s.min.minimize_to_clear.len(), 0);
    assert_eq!(s.ws_shrink_entries.len(), 0);
    assert_eq!(s.ws_shrink_result.len(), 0);
    assert_eq!(s.ws_shrink_block_lits.len(), 0);
}

fn observing(cut: usize, calls: &Arc<AtomicUsize>) -> CountedAdmission {
    let calls = Arc::clone(calls);
    CountedAdmission::new(
        FiniteAdmissionGrant::new(100_000_000, 100_000_000),
        None,
        Arc::new(move || calls.fetch_add(1, Ordering::SeqCst) == cut),
    )
    .unwrap()
}
