// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Farkas-conflict partition retagging regressions.

use super::*;

/// Test that retag_farkas_conflicts upgrades AB origins to B when conflict
/// term variables belong exclusively to B-partition assumptions.
///
/// This tests the #816 Phase 2 proxy partition re-tagging: when the IUC solver
/// creates proxied assumptions, atoms from B-partition expressions should be
/// tagged as B, not AB.
#[test]
fn test_retag_farkas_conflicts_ab_to_b() {
    let mut solver = IucSolver::new();

    // Set up partition variable sets: x is A-only, y is B-only, z is shared
    solver.a_vars.insert("x".to_string());
    solver.a_vars.insert("z".to_string());
    solver.b_vars.insert("y".to_string());
    solver.b_vars.insert("z".to_string());

    // Use convert_expr to create TermIds and populate var_map
    let y_le_5_expr = ChcExpr::le(
        ChcExpr::var(ChcVar::new("y", ChcSort::Int)),
        ChcExpr::int(5),
    );
    let y_le_5 = solver.smt.convert_expr(&y_le_5_expr);

    // Create a FarkasConflict with AB origin for the y<=5 term
    let conflict = FarkasConflict {
        conflict_terms: vec![y_le_5],
        polarities: vec![true],
        farkas: ay_core::FarkasAnnotation::from_ints(&[1]),
        origins: vec![Partition::AB], // This is what smt.rs produces when proxy layer masks B
    };

    let retagged = solver.retag_farkas_conflicts(vec![conflict]);

    // y is exclusively in B (not in A), so AB should be upgraded to B
    assert_eq!(retagged.len(), 1);
    assert_eq!(
        retagged[0].origins[0],
        Partition::B,
        "conflict term involving B-only variable y should be re-tagged from AB to B"
    );
}

/// Test that retag_farkas_conflicts does NOT re-tag AB to B when variables
/// are shared between A and B partitions.
#[test]
fn test_retag_farkas_conflicts_shared_var_stays_ab() {
    let mut solver = IucSolver::new();

    // z is shared between A and B
    solver.a_vars.insert("z".to_string());
    solver.b_vars.insert("z".to_string());

    let z_le_10_expr = ChcExpr::le(
        ChcExpr::var(ChcVar::new("z", ChcSort::Int)),
        ChcExpr::int(10),
    );
    let z_le_10 = solver.smt.convert_expr(&z_le_10_expr);

    let conflict = FarkasConflict {
        conflict_terms: vec![z_le_10],
        polarities: vec![true],
        farkas: ay_core::FarkasAnnotation::from_ints(&[1]),
        origins: vec![Partition::AB],
    };

    let retagged = solver.retag_farkas_conflicts(vec![conflict]);

    // z is in both A and B, so AB should stay AB (shared variable)
    assert_eq!(
        retagged[0].origins[0],
        Partition::AB,
        "shared variable z should keep AB partition"
    );
}

/// Term-origin retagging should still classify shared-variable atoms when
/// the exact conflict term came from B assumptions.
#[test]
fn test_retag_farkas_conflicts_shared_var_exact_b_atom() {
    let mut solver = IucSolver::new();

    // z is shared across A/B variable sets, so var-based retagging alone cannot decide.
    solver.a_vars.insert("z".to_string());
    solver.b_vars.insert("z".to_string());

    let z_le_10_expr = ChcExpr::le(
        ChcExpr::var(ChcVar::new("z", ChcSort::Int)),
        ChcExpr::int(10),
    );
    let z_le_10 = solver.smt.convert_expr(&z_le_10_expr);

    // Mark this exact atom as B-origin (from assumptions).
    solver.b_atom_terms.insert(z_le_10);

    let conflict = FarkasConflict {
        conflict_terms: vec![z_le_10],
        polarities: vec![true],
        farkas: ay_core::FarkasAnnotation::from_ints(&[1]),
        origins: vec![Partition::AB],
    };

    let retagged = solver.retag_farkas_conflicts(vec![conflict]);

    assert_eq!(
        retagged[0].origins[0],
        Partition::B,
        "exact B atom should be re-tagged to B even with shared vars"
    );
}

/// Term-origin retagging should classify shared-variable atoms as A when
/// the exact conflict term came from A background.
#[test]
fn test_retag_farkas_conflicts_shared_var_exact_a_atom() {
    let mut solver = IucSolver::new();

    solver.a_vars.insert("z".to_string());
    solver.b_vars.insert("z".to_string());

    let z_ge_0_expr = ChcExpr::ge(
        ChcExpr::var(ChcVar::new("z", ChcSort::Int)),
        ChcExpr::int(0),
    );
    let z_ge_0 = solver.smt.convert_expr(&z_ge_0_expr);

    // Mark this exact atom as A-origin (from background).
    solver.a_atom_terms.insert(z_ge_0);

    let conflict = FarkasConflict {
        conflict_terms: vec![z_ge_0],
        polarities: vec![true],
        farkas: ay_core::FarkasAnnotation::from_ints(&[1]),
        origins: vec![Partition::AB],
    };

    let retagged = solver.retag_farkas_conflicts(vec![conflict]);

    assert_eq!(
        retagged[0].origins[0],
        Partition::A,
        "exact A atom should be re-tagged to A even with shared vars"
    );
}

/// Test the AB → A re-tag path: when all variables in a conflict term
/// belong exclusively to A-partition background constraints.
#[test]
fn test_retag_farkas_conflicts_ab_to_a() {
    let mut solver = IucSolver::new();

    // x is A-only
    solver.a_vars.insert("x".to_string());
    // y is B-only (to ensure b_vars is non-empty, avoiding early return)
    solver.b_vars.insert("y".to_string());

    let x_le_5_expr = ChcExpr::le(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::int(5),
    );
    let x_le_5 = solver.smt.convert_expr(&x_le_5_expr);

    let conflict = FarkasConflict {
        conflict_terms: vec![x_le_5],
        polarities: vec![true],
        farkas: ay_core::FarkasAnnotation::from_ints(&[1]),
        origins: vec![Partition::AB],
    };

    let retagged = solver.retag_farkas_conflicts(vec![conflict]);

    assert_eq!(
        retagged[0].origins[0],
        Partition::A,
        "conflict term involving A-only variable x should be re-tagged from AB to A"
    );
}

/// Test multi-term conflict with mixed re-tagging: one term AB→B,
/// one term AB→A, one already B (untouched).
#[test]
fn test_retag_farkas_conflicts_multi_term_mixed() {
    let mut solver = IucSolver::new();

    solver.a_vars.insert("x".to_string());
    solver.b_vars.insert("y".to_string());

    let x_le_5_expr = ChcExpr::le(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::int(5),
    );
    let y_ge_0_expr = ChcExpr::ge(
        ChcExpr::var(ChcVar::new("y", ChcSort::Int)),
        ChcExpr::int(0),
    );
    let const_expr = ChcExpr::le(ChcExpr::int(3), ChcExpr::int(10));

    let x_le_5 = solver.smt.convert_expr(&x_le_5_expr);
    let y_ge_0 = solver.smt.convert_expr(&y_ge_0_expr);
    let const_term = solver.smt.convert_expr(&const_expr);

    let conflict = FarkasConflict {
        conflict_terms: vec![x_le_5, y_ge_0, const_term],
        polarities: vec![true, true, true],
        farkas: ay_core::FarkasAnnotation::from_ints(&[1, 1, 1]),
        origins: vec![Partition::AB, Partition::AB, Partition::B],
    };

    let retagged = solver.retag_farkas_conflicts(vec![conflict]);

    assert_eq!(retagged.len(), 1);
    assert_eq!(
        retagged[0].origins[0],
        Partition::A,
        "x-only term should be retagged AB→A"
    );
    assert_eq!(
        retagged[0].origins[1],
        Partition::B,
        "y-only term should be retagged AB→B"
    );
    assert_eq!(
        retagged[0].origins[2],
        Partition::B,
        "already-B term should remain B"
    );
}

/// Test that retag passes through unchanged when b_vars is empty (early return).
#[test]
fn test_retag_farkas_conflicts_empty_b_vars_passthrough() {
    let mut solver = IucSolver::new();

    solver.a_vars.insert("x".to_string());
    // b_vars intentionally empty

    let x_le_5_expr = ChcExpr::le(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::int(5),
    );
    let x_le_5 = solver.smt.convert_expr(&x_le_5_expr);

    let conflict = FarkasConflict {
        conflict_terms: vec![x_le_5],
        polarities: vec![true],
        farkas: ay_core::FarkasAnnotation::from_ints(&[1]),
        origins: vec![Partition::AB],
    };

    let retagged = solver.retag_farkas_conflicts(vec![conflict]);

    // Early return: b_vars empty means no B-partition info, so no re-tagging
    assert_eq!(
        retagged[0].origins[0],
        Partition::AB,
        "should not retag when b_vars is empty"
    );
}
