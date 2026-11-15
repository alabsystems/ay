// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pointer-family offset propagation through the LIA layer: with only
//! `x = y + 1` asserted and `y` free, the sibling atoms `x < y`,
//! `x <= y + 1`, `x >= y + 1` must be decided by propagation on the
//! BCP path (`check_during_propagate` + `propagate`). The same shape
//! delivers at the bare-LRA level (ay-lra
//! `implied_propagation_entailment` tF); this pins that the LIA
//! wrapper — Diophantine handling, shared equalities, integer
//! tightening — does not swallow the delivery.

use super::*;

#[test]
fn offset_equality_with_free_vars_decides_sibling_atoms_via_bcp_check() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let one = terms.mk_int(1.into());
    let y_plus_1 = terms.mk_add(vec![y, one]);
    let x_eq_y1 = terms.mk_eq(x, y_plus_1);
    let x_lt_y = terms.mk_lt(x, y);
    let x_le_y1 = terms.mk_le(x, y_plus_1);
    let x_ge_y1 = terms.mk_ge(x, y_plus_1);

    let mut solver = LiaSolver::new(&terms);
    for atom in [x_eq_y1, x_lt_y, x_le_y1, x_ge_y1] {
        solver.register_atom(atom);
    }
    solver.assert_literal(x_eq_y1, true);
    let result = solver.check_during_propagate();
    assert!(
        matches!(result, TheoryResult::Sat),
        "expected SAT, got {result:?}"
    );

    let propagations = solver.propagate();
    for (lit, what) in [
        (TheoryLit::new(x_lt_y, false), "not (x < y)"),
        (TheoryLit::new(x_le_y1, true), "x <= y + 1"),
        (TheoryLit::new(x_ge_y1, true), "x >= y + 1"),
    ] {
        assert!(
            propagations.iter().any(|p| p.literal == lit),
            "expected {what} delivered, got {propagations:?}"
        );
    }
}

/// Transitive offset closure (the pointer-family core): the asserted
/// equalities `x = y + 1` and `y = z + 1` live on DIFFERENT slacks
/// than the target atoms over `x - z`. Deciding `x <= z + 2`,
/// `x >= z + 2`, and refuting `x < z + 2` needs the two-hop chain to
/// bound the `x - z` slack — via tableau row combination after
/// pivoting, implied-bound cascading, or the equality graph.
#[test]
fn transitive_offset_chain_decides_two_hop_atoms_via_bcp_check() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());
    let y_plus_1 = terms.mk_add(vec![y, one]);
    let z_plus_1 = terms.mk_add(vec![z, one]);
    let z_plus_2 = terms.mk_add(vec![z, two]);
    let x_eq_y1 = terms.mk_eq(x, y_plus_1);
    let y_eq_z1 = terms.mk_eq(y, z_plus_1);
    let x_lt_z2 = terms.mk_lt(x, z_plus_2);
    let x_le_z2 = terms.mk_le(x, z_plus_2);
    let x_ge_z2 = terms.mk_ge(x, z_plus_2);
    let x_eq_z2 = terms.mk_eq(x, z_plus_2);

    let mut solver = LiaSolver::new(&terms);
    for atom in [x_eq_y1, y_eq_z1, x_lt_z2, x_le_z2, x_ge_z2, x_eq_z2] {
        solver.register_atom(atom);
    }
    solver.assert_literal(x_eq_y1, true);
    solver.assert_literal(y_eq_z1, true);
    let result = solver.check_during_propagate();
    assert!(
        matches!(result, TheoryResult::Sat),
        "expected SAT, got {result:?}"
    );

    let propagations = solver.propagate();
    for (lit, what) in [
        (TheoryLit::new(x_lt_z2, false), "not (x < z + 2)"),
        (TheoryLit::new(x_le_z2, true), "x <= z + 2"),
        (TheoryLit::new(x_ge_z2, true), "x >= z + 2"),
    ] {
        assert!(
            propagations.iter().any(|p| p.literal == lit),
            "expected {what} delivered, got {propagations:?}"
        );
    }
}
