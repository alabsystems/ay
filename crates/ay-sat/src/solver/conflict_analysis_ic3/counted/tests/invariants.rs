// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn three_levels() -> (Solver, ClauseRef) {
    let mut s = Solver::new(6);
    s.set_ic3_mode();
    for clause in [
        vec![neg(3), pos(4), neg(1), neg(0)],
        vec![neg(3), pos(5), neg(1), neg(0)],
        vec![neg(4), neg(5), neg(1), neg(2), neg(0)],
        vec![pos(0)],
    ] {
        assert!(s.add_clause(clause));
    }
    s.initialize_watches();
    assert!(s.process_initial_clauses().is_none());
    assert!(s.search_propagate().is_none());
    assert_eq!(s.var_data[0].level, 0);
    assert_eq!(s.lit_val(pos(0)), 1);
    for decision in [1, 2] {
        s.decide(pos(decision));
        assert!(s.search_propagate().is_none());
    }
    s.decide(pos(3));
    let conflict = s.search_propagate().unwrap();
    (s, conflict)
}

#[test]
fn root_literals_are_omitted_and_distinct_lower_levels_use_the_real_lbd() {
    let (mut expected, conflict) = three_levels();
    let raw = ordinary(&mut expected, conflict).unwrap();
    assert_eq!(raw.uip, neg(3));
    assert_eq!(raw.lbd, 2);
    let mut lower = raw.lower.clone();
    lower.sort_unstable_by_key(|lit| lit.index());
    assert_eq!(lower, vec![neg(1), neg(2)]);
    let (mut s, conflict) = three_levels();
    let before = state(&s);
    attach(&mut s, &test_owner(10_000_000, 10_000_000));
    assert_eq!(run(&mut s, conflict).unwrap(), Some(raw));
    assert_eq!(state(&s), before);
    clean(&s);
}

#[test]
fn no_current_level_literal_preserves_the_actual_trail_exhaustion_bailout() {
    let (mut s, conflict, _) = fixture(2, Reasons::Long);
    // Exercise a defensive stale-conflict input below an empty level. Keep the
    // actual BCP trail, reasons and pending queue: ordinary decide correctly
    // rejects a new assignment while propagation from the conflict is pending.
    s.decision_level += 1;
    s.trail_lim.push(s.trail.len());
    assert!(s
        .arena
        .literals(conflict.0 as usize)
        .iter()
        .all(|lit| { s.var_data[lit.variable().index()].level < s.decision_level }));
    let before = state(&s);
    let bailouts = s.stats.trail_exhaustion_bailouts;
    let owner = test_owner(10_000_000, 10_000_000);
    attach(&mut s, &owner);
    assert_eq!(run(&mut s, conflict), Ok(None));
    assert_eq!(s.stats.trail_exhaustion_bailouts, bailouts + 1);
    assert_eq!(state(&s), before);
    assert_eq!(owner.check(), Ok(()));
    clean(&s);
    let (mut ordinary, conflict, _) = fixture(2, Reasons::Long);
    ordinary.decision_level += 1;
    ordinary.trail_lim.push(ordinary.trail.len());
    assert!(ordinary.analyze_conflict_ic3(conflict).is_none());
    assert_eq!(ordinary.stats.trail_exhaustion_bailouts, bailouts + 1);
    clean(&ordinary);
}

#[test]
fn non_uip_lazy_theory_reason_is_typed_refusal_before_ordinary_debug_assertion() {
    let (mut s, conflict, _) = fixture(2, Reasons::Long);
    let last = s.trail.last().unwrap().variable().index();
    s.var_data[last].reason = 0;
    s.var_data[last].set_lazy_theory_reason(true);
    let before = state(&s);
    let owner = test_owner(10_000_000, 10_000_000);
    attach(&mut s, &owner);
    assert_eq!(run(&mut s, conflict), Err(SatUnknownReason::ResourceBudget));
    assert!(owner.usage().unwrap().refusal.is_some());
    assert_eq!(state(&s), before);
    clean(&s);
}

#[test]
fn missing_or_duplicate_pivot_and_late_antecedent_are_not_learned_clauses() {
    for mode in 0..3 {
        let (mut s, conflict, _) = fixture(2, Reasons::Long);
        let last = *s.trail.last().unwrap();
        let offset = s.var_reason(last.variable().index()).unwrap().0 as usize;
        let pivot = s
            .arena
            .literals(offset)
            .iter()
            .position(|lit| *lit == last)
            .unwrap();
        let other = (0..s.arena.len_of(offset))
            .find(|index| *index != pivot)
            .unwrap();
        match mode {
            0 => s.arena.set_literal(offset, pivot, neg(0)),
            1 => s.arena.set_literal(offset, other, last),
            _ => s.arena.set_literal(offset, other, last.negated()),
        }
        let before = state(&s);
        attach(&mut s, &test_owner(10_000_000, 10_000_000));
        assert_eq!(run(&mut s, conflict), Err(SatUnknownReason::ResourceBudget));
        assert_eq!(state(&s), before);
        clean(&s);
    }
}

#[test]
fn garbage_conflict_and_reason_are_refused_without_any_clause_publication() {
    for reason in [false, true] {
        let (mut s, conflict, _) = fixture(2, Reasons::Long);
        let offset = if reason {
            s.var_reason(s.trail.last().unwrap().variable().index())
                .unwrap()
                .0 as usize
        } else {
            conflict.0 as usize
        };
        s.arena.set_garbage(offset, true);
        let before = state(&s);
        attach(&mut s, &test_owner(10_000_000, 10_000_000));
        assert_eq!(run(&mut s, conflict), Err(SatUnknownReason::ResourceBudget));
        assert_eq!(state(&s), before);
        clean(&s);
    }
}

#[test]
fn orphan_seen_and_level_marks_are_refused_without_erasing_unowned_scratch() {
    for seen in [false, true] {
        let (mut s, conflict, _) = fixture(2, Reasons::Long);
        if seen {
            s.var_data[0].set_seen(true);
        } else {
            s.min
                .level_seen
                .push(minimization_state::LevelSeen { count: 1, trail: 0 });
        }
        let before = state(&s);
        let levels = s.min.level_seen.clone();
        let tracked = s.min.level_seen_to_clear.clone();
        attach(&mut s, &test_owner(10_000_000, 10_000_000));
        assert_eq!(run(&mut s, conflict), Err(SatUnknownReason::ResourceBudget));
        assert_eq!(state(&s), before);
        assert_eq!(s.min.level_seen, levels);
        assert_eq!(s.min.level_seen_to_clear, tracked);
    }
}
