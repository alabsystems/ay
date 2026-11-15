// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::test_owner;
use ay_core::original_query::FiniteAdmissionGrant;
use std::sync::atomic::{AtomicBool, AtomicUsize};

mod continuation;
mod controls;
mod invariants;
mod semantics;
mod unwind;

#[derive(Clone, Copy)]
enum Reasons {
    Binary,
    Long,
}

fn pos(index: u32) -> Literal {
    Literal::positive(Variable::new(index))
}
fn neg(index: u32) -> Literal {
    pos(index).negated()
}

/// Two real implication chains fork at x1 and meet in a conflict guarded by
/// the earlier decision x0. The clause is a consequence, not an UNSAT formula.
fn fixture(length: u32, kind: Reasons) -> (Solver, ClauseRef, Vec<Vec<Literal>>) {
    assert!(length > 0);
    let mut s = Solver::new((2 + 2 * length) as usize);
    s.set_ic3_mode();
    s.cold.jump_reasons_enabled = matches!(kind, Reasons::Binary);
    let mut clauses = Vec::new();
    for start in [2, 2 + length] {
        let mut previous = 1;
        for next in start..start + length {
            let mut clause = vec![neg(previous), pos(next)];
            if matches!(kind, Reasons::Long) {
                clause.push(neg(0));
            }
            clauses.push(clause);
            previous = next;
        }
    }
    clauses.push(vec![neg(1 + length), neg(1 + 2 * length), neg(0)]);
    for clause in &clauses {
        assert!(s.add_clause(clause.clone()));
    }
    s.initialize_watches();
    s.decide(pos(0));
    assert!(s.search_propagate().is_none());
    s.decide(pos(1));
    let conflict = s
        .search_propagate()
        .expect("the two chains meet in a real BCP conflict");
    (s, conflict, clauses)
}

fn attach(s: &mut Solver, owner: &CountedAdmission) {
    assert!(s.attach_counted_admission(owner.clone()).is_ok());
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Resolved {
    uip: Literal,
    lower: Vec<Literal>,
    lbd: u32,
}

fn run(s: &mut Solver, conflict: ClauseRef) -> Result<Option<Resolved>, SatUnknownReason> {
    let Some(scope) = s.begin_counted_ic3_resolution(conflict)? else {
        return Ok(None);
    };
    let resolved = Resolved {
        uip: scope.asserting_literal(),
        lower: scope.lower_literals().to_vec(),
        lbd: scope.lbd(),
    };
    scope.finish()?;
    Ok(Some(resolved))
}

fn ordinary(s: &mut Solver, conflict: ClauseRef) -> Option<Resolved> {
    s.conflict.clear(&mut s.var_data);
    let uip = s
        .resolve_ic3_first_uip(conflict, &resolution::Ordinary)
        .unwrap()?;
    s.conflict.set_asserting_literal(uip);
    let lbd = s.conflict.compute_lbd(&s.var_data);
    Some(Resolved {
        uip,
        lower: s.conflict.counted_ic3_lower_literals().to_vec(),
        lbd,
    })
}

#[derive(Debug, PartialEq, Eq)]
struct SearchState {
    trail: Vec<Literal>,
    limits: Vec<usize>,
    data: Vec<VarData>,
    vals: Vec<i8>,
    phase: Vec<i8>,
    clauses: Vec<Vec<Literal>>,
    ids: Vec<u64>,
    level: u32,
    qhead: usize,
    decisions: u64,
}

fn state(s: &Solver) -> SearchState {
    SearchState {
        trail: s.trail.clone(),
        limits: s.trail_lim.clone(),
        data: s.var_data.clone(),
        vals: s.vals.clone(),
        phase: s.phase.clone(),
        clauses: s
            .arena
            .indices()
            .map(|offset| s.arena.literals(offset).to_vec())
            .collect(),
        ids: s.cold.original_ledger.clause_ids().to_vec(),
        level: s.decision_level,
        qhead: s.qhead,
        decisions: s.num_decisions,
    }
}

fn clean(s: &Solver) {
    assert!(s.conflict.seen_to_clear.is_empty());
    assert!(s.var_data.iter().all(|data| !data.is_seen()));
    assert_eq!(s.conflict.learned_count(), 0);
    assert!(s.min.level_seen_to_clear.is_empty());
    assert!(s
        .min
        .level_seen
        .iter()
        .all(|entry| *entry == minimization_state::LevelSeen::EMPTY));
}

fn observing_owner(at: usize, calls: &Arc<AtomicUsize>) -> CountedAdmission {
    let observed = Arc::clone(calls);
    CountedAdmission::new(
        FiniteAdmissionGrant::new(10_000_000, 10_000_000),
        None,
        Arc::new(move || observed.fetch_add(1, Ordering::SeqCst) == at),
    )
    .unwrap()
}
