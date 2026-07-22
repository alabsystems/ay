// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================
// #6590: Structural snapshot tests
// =============================================================================

/// Snapshot round-trip with single-variable atoms: register, export, import
/// into fresh solver, assert the same literals, confirm check() matches.
#[test]
fn test_snapshot_round_trip_single_var_sat_6590() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let x_ge = terms.mk_ge(x, three); // x >= 3
    let x_le = terms.mk_le(x, ten); // x <= 10

    // First solver: register, assert, check
    let mut solver1 = LraSolver::new(&terms);
    solver1.register_atom(x_ge);
    solver1.register_atom(x_le);
    solver1.assert_literal(x_ge, true);
    solver1.assert_literal(x_le, true);
    let result1 = solver1.check();
    assert!(
        matches!(result1, TheoryResult::Sat),
        "first solver should be SAT (3 <= x <= 10)"
    );

    // Export snapshot
    let snapshot = solver1
        .export_structural_snapshot()
        .expect("snapshot must be Some after registering atoms");

    // Second solver: import snapshot, re-register (should be no-op), assert, check
    let mut solver2 = LraSolver::new(&terms);
    solver2.import_structural_snapshot(snapshot);
    solver2.register_atom(x_ge);
    solver2.register_atom(x_le);
    solver2.assert_literal(x_ge, true);
    solver2.assert_literal(x_le, true);
    let result2 = solver2.check();
    assert!(
        matches!(result2, TheoryResult::Sat),
        "snapshot-imported solver must also be SAT for single-var atoms"
    );
}

#[test]
fn test_restore_from_structural_snapshot_round_trip_6590() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let x_ge = terms.mk_ge(x, three);
    let x_le = terms.mk_le(x, ten);

    let mut solver1 = LraSolver::new(&terms);
    solver1.register_atom(x_ge);
    solver1.register_atom(x_le);
    solver1.assert_literal(x_ge, true);
    solver1.assert_literal(x_le, true);
    assert!(
        matches!(solver1.check(), TheoryResult::Sat),
        "baseline solver should be SAT before snapshot export"
    );

    let snapshot = solver1
        .take_structural_snapshot()
        .expect("snapshot must exist after registering atoms");

    let mut solver2 =
        <LraSolver as TheorySolver>::restore_from_structural_snapshot(&terms, snapshot)
            .unwrap_or_else(|snapshot| {
                panic!(
                    "LRA must rebuild directly from its own structural snapshot; got {:?}",
                    snapshot.as_ref().type_id()
                )
            });

    assert!(
        solver2.registered_atoms.contains(&x_ge) && solver2.registered_atoms.contains(&x_le),
        "restored solver must already contain the registered atom set"
    );

    solver2.register_atom(x_ge);
    solver2.register_atom(x_le);
    solver2.assert_literal(x_ge, true);
    solver2.assert_literal(x_le, true);
    assert!(
        matches!(solver2.check(), TheoryResult::Sat),
        "solver rebuilt through restore_from_structural_snapshot must remain SAT"
    );
}

/// Snapshot round-trip with compound atoms: both soft_reset and cross-solver
/// import must preserve SAT behavior.  The fix (#6590) recomputes basic variable
/// values from row constants after zeroing, which restores the simplex invariant.
#[test]
fn test_snapshot_compound_soft_reset_baseline_6590() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let four = terms.mk_rational(BigRational::from(BigInt::from(4)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let sum = terms.mk_add(vec![x, y]);
    let sum_le = terms.mk_le(sum, ten); // x + y <= 10
    let x_ge = terms.mk_ge(x, three); // x >= 3
    let y_ge = terms.mk_ge(y, four); // y >= 4

    // Register, assert, check
    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le);
    solver.register_atom(x_ge);
    solver.register_atom(y_ge);
    solver.assert_literal(sum_le, true);
    solver.assert_literal(x_ge, true);
    solver.assert_literal(y_ge, true);
    let result1 = solver.check();
    assert!(
        matches!(result1, TheoryResult::Sat),
        "first check should be SAT (3 + 4 = 7 <= 10)"
    );

    // Verify soft_reset preserves correctness on the SAME solver
    solver.soft_reset();
    solver.assert_literal(sum_le, true);
    solver.assert_literal(x_ge, true);
    solver.assert_literal(y_ge, true);
    let result2 = solver.check();
    assert!(
        matches!(result2, TheoryResult::Sat),
        "soft_reset + reassert on SAME solver must also be SAT"
    );

    // Export snapshot from the checked solver
    let snapshot = solver
        .export_structural_snapshot()
        .expect("snapshot must be Some after registering atoms");

    // Import into fresh solver — must produce SAT (#6590 fix).
    let mut solver2 = LraSolver::new(&terms);
    solver2.import_structural_snapshot(snapshot);
    solver2.register_atom(sum_le);
    solver2.register_atom(x_ge);
    solver2.register_atom(y_ge);
    solver2.assert_literal(sum_le, true);
    solver2.assert_literal(x_ge, true);
    solver2.assert_literal(y_ge, true);
    let result3 = solver2.check();
    assert!(
        matches!(result3, TheoryResult::Sat),
        "cross-solver import must also be SAT for compound atoms"
    );
}

/// Snapshot round-trip for UNSAT: confirm an UNSAT result is preserved after
/// export/import.
#[test]
fn test_snapshot_round_trip_preserves_unsat_6590() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let six = terms.mk_rational(BigRational::from(BigInt::from(6)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let sum = terms.mk_add(vec![x, y]);
    let sum_le = terms.mk_le(sum, ten); // x + y <= 10
    let x_ge = terms.mk_ge(x, five); // x >= 5
    let y_ge = terms.mk_ge(y, six); // y >= 6

    // First solver: register, assert, check UNSAT (5 + 6 = 11 > 10)
    let mut solver1 = LraSolver::new(&terms);
    solver1.register_atom(sum_le);
    solver1.register_atom(x_ge);
    solver1.register_atom(y_ge);
    solver1.assert_literal(sum_le, true);
    solver1.assert_literal(x_ge, true);
    solver1.assert_literal(y_ge, true);
    let result1 = solver1.check();
    assert!(
        matches!(
            result1,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "first solver should be UNSAT (5 + 6 = 11 > 10)"
    );

    // Export snapshot
    let snapshot = solver1
        .export_structural_snapshot()
        .expect("snapshot must be Some after registering atoms");

    // Second solver: import, re-register, assert same, check
    let mut solver2 = LraSolver::new(&terms);
    solver2.import_structural_snapshot(snapshot);
    solver2.register_atom(sum_le);
    solver2.register_atom(x_ge);
    solver2.register_atom(y_ge);
    solver2.assert_literal(sum_le, true);
    solver2.assert_literal(x_ge, true);
    solver2.assert_literal(y_ge, true);
    let result2 = solver2.check();
    assert!(
        matches!(
            result2,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "snapshot-imported solver must also be UNSAT for identical assertions"
    );
}

/// Idempotent registration: calling register_atom twice on the same atom
/// (before and after snapshot import) must not grow structural indices.
#[test]
fn test_snapshot_idempotent_registration_no_index_growth_6590() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    // Single-variable atom and compound atom
    let x_le = terms.mk_le(x, five); // x <= 5 (single-var)
    let sum = terms.mk_add(vec![x, y]);
    let sum_le = terms.mk_le(sum, ten); // x + y <= 10 (compound)

    // Register atoms on first solver
    let mut solver1 = LraSolver::new(&terms);
    solver1.register_atom(x_le);
    solver1.register_atom(sum_le);

    // Record structural sizes after first registration
    let atom_index_total_1: usize = solver1.atom_index.values().map(Vec::len).sum();
    let var_to_atoms_total_1: usize = solver1.var_to_atoms.values().map(Vec::len).sum();
    let compound_use_total_1: usize = solver1.compound_use_index.values().map(Vec::len).sum();

    // Export snapshot
    let snapshot = solver1
        .export_structural_snapshot()
        .expect("must have snapshot");

    // Import into fresh solver
    let mut solver2 = LraSolver::new(&terms);
    solver2.import_structural_snapshot(snapshot);

    // Re-register the same atoms (should be no-op via registered_atoms guard)
    solver2.register_atom(x_le);
    solver2.register_atom(sum_le);

    // Verify no growth
    let atom_index_total_2: usize = solver2.atom_index.values().map(Vec::len).sum();
    let var_to_atoms_total_2: usize = solver2.var_to_atoms.values().map(Vec::len).sum();
    let compound_use_total_2: usize = solver2.compound_use_index.values().map(Vec::len).sum();

    assert_eq!(
        atom_index_total_1, atom_index_total_2,
        "atom_index must not grow after snapshot import + re-register"
    );
    assert_eq!(
        var_to_atoms_total_1, var_to_atoms_total_2,
        "var_to_atoms must not grow after snapshot import + re-register"
    );
    assert_eq!(
        compound_use_total_1, compound_use_total_2,
        "compound_use_index must not grow after snapshot import + re-register"
    );

    // Also verify the solver still works correctly
    solver2.assert_literal(x_le, true);
    solver2.assert_literal(sum_le, true);
    assert!(
        matches!(solver2.check(), TheoryResult::Sat),
        "solver with imported snapshot must still produce correct SAT result"
    );
}

/// Register atoms, re-register the same atoms a second time on the same solver
/// instance (simulating multiple iterations without snapshot). Index sizes must
/// not grow.
#[test]
fn test_double_register_no_index_growth_6590() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let x_le = terms.mk_le(x, five);
    let sum = terms.mk_add(vec![x, y]);
    let sum_le = terms.mk_le(sum, ten);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_le);
    solver.register_atom(sum_le);

    let atom_index_before: usize = solver.atom_index.values().map(Vec::len).sum();
    let var_to_atoms_before: usize = solver.var_to_atoms.values().map(Vec::len).sum();
    let compound_use_before: usize = solver.compound_use_index.values().map(Vec::len).sum();

    // Second registration of the same atoms
    solver.register_atom(x_le);
    solver.register_atom(sum_le);

    let atom_index_after: usize = solver.atom_index.values().map(Vec::len).sum();
    let var_to_atoms_after: usize = solver.var_to_atoms.values().map(Vec::len).sum();
    let compound_use_after: usize = solver.compound_use_index.values().map(Vec::len).sum();

    assert_eq!(
        atom_index_before, atom_index_after,
        "atom_index must not grow on duplicate register_atom"
    );
    assert_eq!(
        var_to_atoms_before, var_to_atoms_after,
        "var_to_atoms must not grow on duplicate register_atom"
    );
    assert_eq!(
        compound_use_before, compound_use_after,
        "compound_use_index must not grow on duplicate register_atom"
    );
}

/// Snapshot-imported solver and soft_reset() solver must agree on structure and
/// check() outcome for the same assertion sequence.
#[test]
fn test_snapshot_matches_soft_reset_behavior_6590() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let seven = terms.mk_rational(BigRational::from(BigInt::from(7)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let sum = terms.mk_add(vec![x, y]);
    let sum_le = terms.mk_le(sum, ten); // x + y <= 10
    let x_ge = terms.mk_ge(x, three); // x >= 3
    let y_le = terms.mk_le(y, seven); // y <= 7

    // Path A: soft_reset
    let mut solver_a = LraSolver::new(&terms);
    solver_a.register_atom(sum_le);
    solver_a.register_atom(x_ge);
    solver_a.register_atom(y_le);
    solver_a.assert_literal(sum_le, true);
    solver_a.assert_literal(x_ge, true);
    solver_a.check(); // run to build internal state
    solver_a.soft_reset();
    // Re-assert after soft_reset
    solver_a.assert_literal(sum_le, true);
    solver_a.assert_literal(x_ge, true);
    solver_a.assert_literal(y_le, true);
    let result_a = solver_a.check();

    // Path B: snapshot import
    let mut solver_b1 = LraSolver::new(&terms);
    solver_b1.register_atom(sum_le);
    solver_b1.register_atom(x_ge);
    solver_b1.register_atom(y_le);
    solver_b1.assert_literal(sum_le, true);
    solver_b1.assert_literal(x_ge, true);
    solver_b1.check(); // run to build internal state
    let snapshot = solver_b1
        .export_structural_snapshot()
        .expect("must have snapshot");
    let mut solver_b2 = LraSolver::new(&terms);
    solver_b2.import_structural_snapshot(snapshot);
    solver_b2.register_atom(sum_le);
    solver_b2.register_atom(x_ge);
    solver_b2.register_atom(y_le);
    solver_b2.assert_literal(sum_le, true);
    solver_b2.assert_literal(x_ge, true);
    solver_b2.assert_literal(y_le, true);
    let result_b = solver_b2.check();

    // Both paths must agree on the outcome
    let a_sat = matches!(result_a, TheoryResult::Sat);
    let b_sat = matches!(result_b, TheoryResult::Sat);
    assert_eq!(
        a_sat, b_sat,
        "soft_reset path and snapshot-import path must agree on SAT/UNSAT: \
         soft_reset={a_sat}, snapshot={b_sat}"
    );

    // Structural agreement: same registered_atoms set
    assert_eq!(
        solver_a.registered_atoms, solver_b2.registered_atoms,
        "registered_atoms must match between soft_reset and snapshot paths"
    );
    // Same atom_index keys
    let a_keys: std::collections::BTreeSet<_> = solver_a.atom_index.keys().collect();
    let b_keys: std::collections::BTreeSet<_> = solver_b2.atom_index.keys().collect();
    assert_eq!(
        a_keys, b_keys,
        "atom_index key sets must match between soft_reset and snapshot paths"
    );
}

/// Snapshot import must match soft_reset() for unsupported-atom bookkeeping.
#[test]
fn test_snapshot_import_clears_unsupported_state_6590() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let five = terms.mk_int(BigInt::from(5));

    let ge_zero = terms.mk_ge(x, zero);
    let mysterious_x = terms.mk_app(Symbol::named("mysterious"), vec![x], Sort::Int);
    let mystery_le_five = terms.mk_le(mysterious_x, five);

    let mut solver1 = LraSolver::new(&terms);
    solver1.register_atom(ge_zero);
    solver1.register_atom(mystery_le_five);
    solver1.push();
    solver1.assert_literal(ge_zero, true);
    solver1.assert_literal(mystery_le_five, true);

    let result = solver1.check();
    assert!(
        matches!(result, TheoryResult::Unknown),
        "scope with unsupported atom should be Unknown, got {result:?}"
    );
    assert_eq!(
        solver1.persistent_unsupported_scope_marks,
        vec![1],
        "push() should snapshot the pre-scope unsupported trail length after registration cached the unsupported atom"
    );
    assert_eq!(
        solver1.persistent_unsupported_trail.len(),
        solver1.persistent_unsupported_atoms.len(),
        "unsupported trail should mirror the set before snapshot export"
    );

    let snapshot = solver1
        .export_structural_snapshot()
        .expect("must export a snapshot after atoms are registered");

    let mut solver2 = LraSolver::new(&terms);
    solver2.import_structural_snapshot(snapshot);

    assert!(
        solver2.persistent_unsupported_atoms.is_empty(),
        "snapshot import must clear unsupported atoms to match soft_reset()"
    );
    assert!(
        solver2.persistent_unsupported_trail.is_empty(),
        "snapshot import must clear the unsupported undo trail"
    );
    assert!(
        solver2.persistent_unsupported_scope_marks.is_empty(),
        "snapshot import must clear stale unsupported scope marks"
    );

    // Re-registering imported atoms is a no-op and must not immediately
    // resurrect unsupported state from the cached parse result.
    solver2.register_atom(ge_zero);
    solver2.register_atom(mystery_le_five);
    assert!(
        solver2.persistent_unsupported_atoms.is_empty(),
        "unsupported atoms must stay cleared until an imported unsupported atom is asserted again"
    );
    solver2.assert_literal(ge_zero, true);
    let result_after_import = solver2.check();
    assert!(
        matches!(result_after_import, TheoryResult::Sat),
        "supported atoms should still solve after snapshot import, got {result_after_import:?}"
    );

    solver2.assert_literal(mystery_le_five, true);
    let result_after_reassert = solver2.check();
    assert!(
        matches!(result_after_reassert, TheoryResult::Unknown),
        "re-asserting the imported unsupported atom must rebuild unsupported state, got {result_after_reassert:?}"
    );
    assert!(
        solver2.persistent_unsupported_atoms.contains(&mystery_le_five),
        "unsupported bookkeeping must be rebuilt from the imported atom cache when the atom is asserted again"
    );
}

/// Empty solver exports None snapshot.
#[test]
fn test_empty_solver_exports_none_snapshot_6590() {
    let terms = TermStore::new();
    let solver = LraSolver::new(&terms);
    assert!(
        solver.export_structural_snapshot().is_none(),
        "empty solver with no registered atoms must export None"
    );
}
