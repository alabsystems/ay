// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Eager subsumption of a duplicate learned binary, with and without
//! `--sat-eager-subsume-unlink-binaries`.
//!
//! The solver sometimes learns a binary it already holds. Eager subsumption
//! marks the older copy garbage and keeps its data for reason pointers. Left
//! watched, the husk is later flushed one literal's list at a time, and a
//! half-removed binary is an implication with no contrapositive: that is what
//! chained decompose's representative map on SAT-COMP 5314fd6c (2026-09-14).

use super::*;

/// Watch entries, on either literal's list, that point at `clause`.
fn watch_entries(solver: &Solver, clause: ClauseRef, lits: [Literal; 2]) -> usize {
    lits.iter()
        .map(|&lit| {
            let list = solver.watches.get_watches(lit);
            (0..list.len())
                .filter(|&i| list.clause_ref(i) == clause)
                .count()
        })
        .sum()
}

#[test]
fn eager_subsumption_of_a_duplicate_binary_unlinks_it_only_under_the_switch() {
    let (a, b) = (
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    );
    for unlink in [false, true] {
        let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
            eager_subsume_unlink_binaries: Some(unlink),
            ..Default::default()
        });
        let mut solver: Solver = Solver::new(2);
        let older = solver.add_learned_clause(vec![a, b], 2, &[]);
        let newer = solver.add_learned_clause(vec![a, b], 2, &[]);
        assert_eq!(watch_entries(&solver, older, [a, b]), 2);

        solver.eager_subsume(newer.0 as usize);

        assert!(solver.arena.is_garbage(older.0 as usize), "unlink={unlink}");
        assert_eq!(
            solver.num_eager_subsumed_duplicate_binaries(),
            1,
            "unlink={unlink}"
        );
        // The subsumer keeps both watches; the husk keeps both only without the switch.
        assert_eq!(watch_entries(&solver, newer, [a, b]), 2, "unlink={unlink}");
        let husk = if unlink { 0 } else { 2 };
        assert_eq!(
            watch_entries(&solver, older, [a, b]),
            husk,
            "unlink={unlink}"
        );
    }
}

/// A binary subsumed by a learned unit is satisfied at level 0: the switch
/// leaves its watches, and the event is not counted as a duplicate.
#[test]
fn a_binary_subsumed_by_a_unit_keeps_its_watches_under_the_switch() {
    let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        eager_subsume_unlink_binaries: Some(true),
        ..Default::default()
    });
    let (a, b) = (
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    );
    let mut solver: Solver = Solver::new(2);
    let binary = solver.add_learned_clause(vec![a, b], 2, &[]);
    let unit = solver.add_learned_clause(vec![a], 1, &[]);

    solver.eager_subsume(unit.0 as usize);

    assert!(solver.arena.is_garbage(binary.0 as usize));
    assert_eq!(solver.num_eager_subsumed_duplicate_binaries(), 0);
    assert_eq!(watch_entries(&solver, binary, [a, b]), 2);
}
