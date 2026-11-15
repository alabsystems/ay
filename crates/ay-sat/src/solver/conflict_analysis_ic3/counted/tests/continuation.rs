// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod blocks;
mod controls;
mod semantics;
mod unwind;

/// Root x0, lower decision x1 and an implication chain to x(length+1).
/// The higher fork conflicts on both lower endpoints, so true recursive
/// minimization can remove the chain endpoint from the learned clause.
fn removable(length: u32, kind: Reasons) -> (Solver, ClauseRef, Vec<Vec<Literal>>) {
    assert!(length > 0);
    let mut s = Solver::new((length + 5) as usize);
    s.set_ic3_mode();
    // Existing ordinary option, selected before the query. Counted code does
    // not change it: default repeated-level block shrinking has separate controls.
    s.set_shrink_enabled(false);
    s.cold.jump_reasons_enabled = matches!(kind, Reasons::Binary);
    let mut clauses = Vec::new();
    for next in 2..=length + 1 {
        let mut clause = vec![neg(next - 1), pos(next)];
        if matches!(kind, Reasons::Long) {
            clause.push(neg(0));
        }
        clauses.push(clause);
    }
    let pivot = length + 2;
    for child in [pivot + 1, pivot + 2] {
        clauses.push(vec![neg(pivot), pos(child)]);
    }
    clauses.push(vec![
        neg(pivot + 1),
        neg(pivot + 2),
        neg(1),
        neg(length + 1),
    ]);
    clauses.push(vec![pos(0)]);
    for clause in &clauses {
        assert!(s.add_clause(clause.clone()));
    }
    s.initialize_watches();
    assert!(s.process_initial_clauses().is_none());
    assert!(s.search_propagate().is_none());
    s.decide(pos(1));
    assert!(s.search_propagate().is_none());
    s.decide(pos(pivot));
    let conflict = s.search_propagate().unwrap();
    (s, conflict, clauses)
}

fn minimize(s: &mut Solver, conflict: ClauseRef) -> Result<Resolved, SatUnknownReason> {
    let scope = s.begin_counted_ic3_resolution(conflict)?.unwrap();
    let minimized = scope.minimize_selected()?;
    let result = Resolved {
        uip: minimized.asserting_literal(),
        lower: minimized.lower_literals().to_vec(),
        lbd: minimized.lbd(),
    };
    minimized.finish()?;
    Ok(result)
}

fn ordinary_minimize(s: &mut Solver, conflict: ClauseRef) -> Resolved {
    let before = ordinary(s, conflict).unwrap();
    if s.shrink_enabled {
        s.shrink_and_minimize_learned_clause();
    } else {
        s.minimize_learned_clause();
    }
    Resolved {
        lower: s.conflict.counted_ic3_lower_literals().to_vec(),
        ..before
    }
}

fn distinct_levels() -> (Solver, ClauseRef) {
    let mut s = Solver::new(5);
    s.set_ic3_mode();
    for clause in [
        vec![neg(2), pos(3)],
        vec![neg(2), pos(4)],
        vec![neg(3), neg(4), neg(0), neg(1)],
    ] {
        assert!(s.add_clause(clause));
    }
    s.initialize_watches();
    for decision in [0, 1] {
        s.decide(pos(decision));
        assert!(s.search_propagate().is_none());
    }
    s.decide(pos(2));
    let conflict = s.search_propagate().unwrap();
    (s, conflict)
}

fn dense_removable(length: u32) -> (Solver, ClauseRef) {
    let mut s = Solver::new((length + 4) as usize);
    s.set_ic3_mode();
    s.set_shrink_enabled(false);
    s.cold.jump_reasons_enabled = false;
    for next in 1..=length {
        assert!(s.add_clause(vec![neg(next - 1), pos(next)]));
    }
    for child in [length + 2, length + 3] {
        assert!(s.add_clause(vec![neg(length + 1), pos(child)]));
    }
    let mut conflict = vec![neg(length + 2), neg(length + 3)];
    conflict.extend((0..=length).rev().map(neg));
    assert!(s.add_clause(conflict));
    s.initialize_watches();
    s.decide(pos(0));
    assert!(s.search_propagate().is_none());
    s.decide(pos(length + 1));
    let conflict = s.search_propagate().unwrap();
    (s, conflict)
}

fn retired(s: &mut Solver) {
    clean(s);
    assert!(s.min.minimize_to_clear.is_empty());
    assert!(s.min.minimize_flags.iter().all(|flags| *flags == 0));
    assert!(s.min.minimize_levels_to_clear.is_empty());
    assert!(s
        .min
        .minimize_level_seen
        .iter()
        .all(|level| *level == minimization_state::LevelSeen::EMPTY));
    assert!(s.conflict.clause_buf_mut().is_empty());
}
