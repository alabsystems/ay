// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::Solver;
use crate::literal::{Literal, Variable};

#[test]
fn learned_composition_partitions_only_live_learned_clauses() {
    enum Retention {
        Live,
        GarbageKept,
        PendingGarbage,
        Deleted,
    }

    let mut solver = Solver::new(9);
    assert_eq!(solver.learned_composition(), (0, 0, 0, 0));
    // Both sides of each size boundary, plus hyper clauses at two sizes:
    // hyper takes precedence over the size buckets.
    let kinds = [
        (2, false),
        (3, false),
        (8, false),
        (9, false),
        (2, true),
        (9, true),
    ];
    for retention in [
        Retention::Live,
        Retention::GarbageKept,
        Retention::PendingGarbage,
        Retention::Deleted,
    ] {
        for (length, hyper) in kinds {
            let literals: Vec<_> = (0..length)
                .map(|index| Literal::positive(Variable(index)))
                .collect();
            let offset = solver.arena.add(&literals, true);
            solver.arena.set_hyper(offset, hyper);
            match retention {
                Retention::Live => {}
                Retention::GarbageKept => solver.arena.mark_garbage_keep_data(offset),
                Retention::PendingGarbage => solver.arena.set_pending_garbage(offset, true),
                Retention::Deleted => solver.arena.delete(offset),
            }
        }
    }
    // Original clauses remain excluded even when their size or hyper flag
    // would otherwise put them in one of the four learned buckets.
    for (length, hyper) in kinds {
        let literals: Vec<_> = (0..length)
            .map(|index| Literal::positive(Variable(index)))
            .collect();
        let offset = solver.arena.add(&literals, false);
        solver.arena.set_hyper(offset, hyper);
    }
    let active_learned = solver
        .arena
        .active_indices()
        .filter(|&offset| solver.arena.is_learned(offset))
        .count();
    assert_eq!(
        active_learned, 18,
        "retained husks must actually be present"
    );
    assert_eq!(solver.learned_composition(), (2, 1, 2, 1));
}

#[test]
fn learned_composition_tracks_pending_and_hyper_transitions() {
    let mut solver = Solver::new(2);
    let literals = [
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ];
    let offset = solver.arena.add(&literals, true);
    assert_eq!(solver.learned_composition(), (0, 1, 0, 0));
    solver.arena.set_pending_garbage(offset, true);
    assert_eq!(solver.learned_composition(), (0, 0, 0, 0));
    assert_eq!(solver.arena.literals(offset), &literals);
    solver.arena.set_pending_garbage(offset, false);
    assert_eq!(solver.learned_composition(), (0, 1, 0, 0));
    solver.arena.set_hyper(offset, true);
    assert_eq!(solver.learned_composition(), (1, 0, 0, 0));
    solver.arena.mark_garbage_keep_data(offset);
    assert_eq!(solver.learned_composition(), (0, 0, 0, 0));
    assert_eq!(solver.arena.literals(offset), &literals);
}
