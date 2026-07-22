// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn sort_shrink_entries_preserves_level_and_trail_descending_order() {
    let mut entries = vec![(2, 4, 0), (5, 1, 1), (2, 9, 2), (5, 7, 3), (1, 10, 4)];

    sort_shrink_entries(&mut entries);

    assert_eq!(
        entries,
        vec![(5, 7, 3), (5, 1, 1), (2, 9, 2), (2, 4, 0), (1, 10, 4)],
        "shrink entries must sort by decision level desc, then trail position desc"
    );
}

#[test]
fn is_redundant_cached_keep_overrides_poison() {
    let mut solver = Solver::new(2);
    let pos_lit = Literal::positive(Variable(0));
    let neg_lit = Literal::negative(Variable(0));

    solver.decision_level = 1;
    solver.enqueue(pos_lit, None);
    solver.min.minimize_flags[0] |= MIN_KEEP;
    solver.min.minimize_flags[0] |= MIN_POISON;

    assert!(
        solver.is_redundant_cached(neg_lit, 1),
        "minimize_keep must take precedence over minimize_poison"
    );
}

#[test]
fn is_literal_removable_for_shrink_keep_overrides_poison() {
    let mut solver = Solver::new(2);
    let pos_lit = Literal::positive(Variable(0));
    let neg_lit = Literal::negative(Variable(0));

    solver.decision_level = 1;
    solver.enqueue(pos_lit, None);
    solver.min.minimize_flags[0] |= MIN_KEEP;
    solver.min.minimize_flags[0] |= MIN_POISON;

    assert!(
        solver.is_literal_removable_for_shrink(neg_lit),
        "shrink removability must treat keep as a successful base case"
    );
}
