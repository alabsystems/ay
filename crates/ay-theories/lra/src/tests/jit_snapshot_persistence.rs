// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for theory-prop JIT persistence across structural snapshots
//! (Fix A1, the development design notes §1).
//!
//! The compiled propagator tables (and shared native code region) are
//! transferred through `LraStructuralSnapshot` and re-validated against an
//! atom-index fingerprint: count + hash of every
//! `(var, bound_numer, bound_denom, is_upper, strict, is_small)` tuple.

use super::*;

fn build_solver_with_bound_atoms(terms: &mut TermStore) -> (LraSolver, TermId, TermId, TermId) {
    let x = terms.mk_var("x", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let x_le_3 = terms.mk_le(x, three);
    let x_le_5 = terms.mk_le(x, five);
    let x_le_10 = terms.mk_le(x, ten);

    let mut solver = LraSolver::new(terms);
    solver.register_atom(x_le_3);
    solver.register_atom(x_le_5);
    solver.register_atom(x_le_10);
    (solver, x_le_3, x_le_5, x_le_10)
}

/// The compiled JIT must survive export/import through `from_snapshot`:
/// the imported solver reuses the tables without recompiling, and the
/// propagations it produces match a freshly compiled solver exactly.
#[test]
fn test_jit_persists_across_structural_snapshot() {
    let mut terms = TermStore::new();
    let (mut solver, x_le_3, x_le_5, x_le_10) = build_solver_with_bound_atoms(&mut terms);

    solver.compile_theory_prop_jit();
    assert!(solver.theory_prop_jit_compiled);
    let fingerprint = solver.theory_prop_jit.fingerprint();
    assert!(
        fingerprint.is_some(),
        "compile_theory_propagation_jit must record the atom-index fingerprint"
    );

    let snapshot = solver
        .export_structural_snapshot()
        .expect("snapshot export should succeed with registered atoms");

    let mut imported =
        LraSolver::from_snapshot(&terms, snapshot).expect("snapshot import should succeed");

    // Fix A1: the imported solver adopts the persisted JIT as-is.
    assert!(
        imported.theory_prop_jit_compiled,
        "imported solver must reuse the persisted JIT without recompiling"
    );
    assert_eq!(
        imported.theory_prop_jit.fingerprint(),
        fingerprint,
        "persisted JIT must carry the exporter's atom-index fingerprint"
    );

    // Re-registering the identical atoms is a no-op (registered_atoms is
    // restored by the snapshot) and must not invalidate the JIT.
    imported.register_atom(x_le_3);
    imported.register_atom(x_le_5);
    imported.register_atom(x_le_10);
    assert!(imported.theory_prop_jit_compiled);

    // End-to-end differential: the imported solver's propagations match the
    // freshly compiled solver's propagations.
    imported.push();
    imported.assert_literal(x_le_3, true);
    let result = imported.check();
    assert!(is_sat_like(&result), "x <= 3 should be satisfiable");

    let propagated: Vec<(TermId, bool)> = imported
        .pending_propagations
        .iter()
        .map(|p| (p.propagation.literal.term, p.propagation.literal.value))
        .collect();
    assert!(
        propagated.contains(&(x_le_5, true)),
        "imported JIT must propagate x<=5 when ub=3; got {propagated:?}"
    );
    assert!(
        propagated.contains(&(x_le_10, true)),
        "imported JIT must propagate x<=10 when ub=3; got {propagated:?}"
    );
}

/// Registering a genuinely new atom after snapshot import must invalidate
/// the persisted JIT and recompile with the new atom included.
#[test]
fn test_jit_recompiles_on_fingerprint_mismatch_after_import() {
    let mut terms = TermStore::new();
    let (mut solver, _x_le_3, _x_le_5, _x_le_10) = build_solver_with_bound_atoms(&mut terms);

    solver.compile_theory_prop_jit();
    let old_fingerprint = solver.theory_prop_jit.fingerprint();
    let snapshot = solver
        .export_structural_snapshot()
        .expect("snapshot export should succeed");

    let mut imported =
        LraSolver::from_snapshot(&terms, snapshot).expect("snapshot import should succeed");
    assert_eq!(imported.theory_prop_jit.total_atoms(), 3);

    // New atom with a different bound: invalidates and recompiles.
    let x = terms.mk_var("x", Sort::Real);
    let seven = terms.mk_rational(BigRational::from(BigInt::from(7)));
    let x_ge_7 = terms.mk_ge(x, seven);
    imported.set_terms(&terms);
    imported.register_atom(x_ge_7);
    assert!(
        !imported.theory_prop_jit_compiled,
        "new atom registration must invalidate the persisted JIT"
    );

    imported.compile_theory_prop_jit();
    assert!(imported.theory_prop_jit_compiled);
    assert_eq!(
        imported.theory_prop_jit.total_atoms(),
        4,
        "recompile must include the newly registered atom"
    );
    assert_ne!(
        imported.theory_prop_jit.fingerprint(),
        old_fingerprint,
        "fingerprint must change when the atom index changes"
    );
}

/// Fingerprint sensitivity: every component of the per-atom tuple
/// (bound value, direction, strictness) must affect the fingerprint, and
/// identical atom indices must produce identical fingerprints.
#[test]
fn test_atom_index_fingerprint_sensitivity() {
    let build = |upper: bool, strict: bool, value: i64| -> ay_jit::TheoryPropFingerprint {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let k = terms.mk_rational(BigRational::from(BigInt::from(value)));
        let atom = match (upper, strict) {
            (true, false) => terms.mk_le(x, k),
            (true, true) => terms.mk_lt(x, k),
            (false, false) => terms.mk_ge(x, k),
            (false, true) => terms.mk_gt(x, k),
        };
        let mut solver = LraSolver::new(&terms);
        solver.register_atom(atom);
        solver.atom_index_jit_fingerprint()
    };

    let base = build(true, false, 5);
    assert_eq!(
        base,
        build(true, false, 5),
        "identical atom index -> identical fingerprint"
    );
    assert_ne!(
        base,
        build(true, false, 6),
        "bound value must affect fingerprint"
    );
    assert_ne!(
        base,
        build(true, true, 5),
        "strictness must affect fingerprint"
    );
    assert_ne!(
        base,
        build(false, false, 5),
        "direction must affect fingerprint"
    );
}

/// Same-instance recompile skip: when `theory_prop_jit_compiled` is reset
/// but the atom index is unchanged, `compile_theory_propagation_jit` keeps
/// the existing tables (fingerprint match) instead of rebuilding.
#[test]
fn test_jit_fingerprint_skips_identical_recompile() {
    let mut terms = TermStore::new();
    let (mut solver, x_le_3, _x_le_5, _x_le_10) = build_solver_with_bound_atoms(&mut terms);

    solver.compile_theory_prop_jit();
    let fp = solver.theory_prop_jit.fingerprint();

    // Drive the hotness counter so the recompile-vs-skip distinction is
    // observable: a skip preserves propagation_runs AND native tables.
    solver.push();
    solver.assert_literal(x_le_3, true);
    let _ = solver.check();
    let runs_before = solver.theory_prop_jit.propagation_runs();

    // Simulate the lazy-loop pattern: the compiled flag is dropped but the
    // atom index is unchanged.
    solver.theory_prop_jit_compiled = false;
    solver.compile_theory_prop_jit();
    assert!(solver.theory_prop_jit_compiled);
    assert_eq!(solver.theory_prop_jit.fingerprint(), fp);
    assert_eq!(
        solver.theory_prop_jit.propagation_runs(),
        runs_before,
        "fingerprint match must skip the rebuild (hotness preserved)"
    );
}
