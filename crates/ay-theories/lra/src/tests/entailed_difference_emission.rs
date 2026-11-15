// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Entailed difference equalities are emitted from the asserted
//! difference atoms' reasons alone (#lra-diff-no-couple).
//!
//! The discovery previously rebuilt every co-occurring candidate
//! pair of every tableau row on every call (the top on-CPU frames
//! on QF_LIRA smtopt). The reasons bucketed by
//! `difference_pair_reasons` are entailing asserted literals by
//! construction, so emission intersects those buckets with the
//! candidate set directly.

use super::*;

#[test]
fn difference_equality_emitted_from_asserted_reasons() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let x_le_y = terms.mk_le(x, y);
    let y_le_x = terms.mk_le(y, x);
    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_le_y);
    solver.register_atom(y_le_x);
    solver.assert_literal(x_le_y, true);
    solver.assert_literal(y_le_x, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    let found = solver.find_entailed_difference_equalities(&[x, y]);
    assert_eq!(found.len(), 1, "x <= y and y <= x entail x = y: {found:?}");
    let (a, b, reasons) = &found[0];
    assert!((*a == x && *b == y) || (*a == y && *b == x));
    assert_eq!(reasons.len(), 2, "both direction literals are the reasons");
}

#[test]
fn difference_equality_not_emitted_from_one_direction() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let x_le_y = terms.mk_le(x, y);
    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_le_y);
    solver.assert_literal(x_le_y, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    let found = solver.find_entailed_difference_equalities(&[x, y]);
    assert!(
        found.is_empty(),
        "one direction does not entail equality: {found:?}"
    );
}
