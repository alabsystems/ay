// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for JIT-compiled bound propagation in LRA (#8174).
//!
//! Verifies that the JIT compilation and integration work correctly:
//! - JIT compilation from atom_index
//! - JIT invalidation on new atom registration
//! - Compilation statistics accuracy
//! - SmallBound extraction from Rational::Small

use super::*;

/// Test that the JIT is compiled lazily and has correct statistics.
#[test]
fn test_jit_compilation_statistics() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);

    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let x_le_5 = terms.mk_le(x, five);
    let x_le_10 = terms.mk_le(x, ten);
    let five2 = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let y_le_5 = terms.mk_le(y, five2);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_le_5);
    solver.register_atom(x_le_10);
    solver.register_atom(y_le_5);

    // JIT not compiled yet.
    assert!(!solver.theory_prop_jit_compiled);

    solver.compile_theory_prop_jit();

    assert!(solver.theory_prop_jit_compiled);
    // x has 2 atoms, y has 1 atom = 3 total.
    assert_eq!(solver.theory_prop_jit.total_atoms(), 3);
    // All atoms have small-int bound values (5, 10, 5).
    assert_eq!(solver.theory_prop_jit.small_atoms(), 3);
    // 2 variables with atoms (x, y).
    assert_eq!(solver.theory_prop_jit.compiled_vars(), 2);
    assert!((solver.theory_prop_jit.small_fraction() - 1.0).abs() < f64::EPSILON);
}

/// Test that JIT compilation is invalidated when new atoms are registered.
#[test]
fn test_jit_invalidation_on_new_atom() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let x_le_5 = terms.mk_le(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_le_5);

    solver.compile_theory_prop_jit();
    assert!(solver.theory_prop_jit_compiled);
    assert_eq!(solver.theory_prop_jit.total_atoms(), 1);

    // Register another atom — should invalidate the JIT.
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let x_le_10 = terms.mk_le(x, ten);
    solver.register_atom(x_le_10);

    assert!(
        !solver.theory_prop_jit_compiled,
        "JIT should be invalidated after registering a new atom"
    );

    // Recompile should pick up new atom.
    solver.compile_theory_prop_jit();
    assert!(solver.theory_prop_jit_compiled);
    assert_eq!(solver.theory_prop_jit.total_atoms(), 2);
}

/// Test SmallBound extraction from Rational::Small bounds.
#[test]
fn test_bound_to_small_bound_extraction() {
    // Small rational bound.
    let bound = Bound::new(
        Rational::Small(3, 2),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        false,
    );
    let small = LraSolver::bound_to_small_bound(&bound);
    assert!(small.is_some());
    let sb = small.expect("should be Some for Small rational");
    assert_eq!(sb.numer, 3);
    assert_eq!(sb.denom, 2);
    assert!(!sb.strict);

    // Strict bound.
    let bound_strict = Bound::new(
        Rational::Small(7, 1),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        true,
    );
    let sb2 = LraSolver::bound_to_small_bound(&bound_strict).expect("should be Some");
    assert_eq!(sb2.numer, 7);
    assert_eq!(sb2.denom, 1);
    assert!(sb2.strict);

    // Negative bound.
    let bound_neg = Bound::new(
        Rational::Small(-5, 3),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        false,
    );
    let sb3 = LraSolver::bound_to_small_bound(&bound_neg).expect("should be Some");
    assert_eq!(sb3.numer, -5);
    assert_eq!(sb3.denom, 3);
}

/// Test that JIT propagation and fallback produce same propagations
/// when used end-to-end through check().
#[test]
fn test_jit_propagation_end_to_end() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));

    // x <= 5, x <= 10
    let x_le_5 = terms.mk_le(x, five);
    let x_le_10 = terms.mk_le(x, ten);
    let x_le_3 = terms.mk_le(x, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_le_5);
    solver.register_atom(x_le_10);
    solver.register_atom(x_le_3);

    solver.push();
    solver.assert_literal(x_le_3, true);

    // Run check to trigger full propagation pipeline.
    let result = solver.check();
    assert!(is_sat_like(&result), "x <= 3 should be satisfiable");

    // After check, the JIT should have been compiled.
    assert!(
        solver.theory_prop_jit_compiled,
        "JIT should be compiled after propagation"
    );

    // Verify that pending propagations contain the expected atoms.
    // x <= 5 and x <= 10 should be implied true (since ub = 3 <= 5, 3 <= 10).
    let propagated: Vec<(TermId, bool)> = solver
        .pending_propagations
        .iter()
        .map(|p| (p.propagation.literal.term, p.propagation.literal.value))
        .collect();

    assert!(
        propagated.contains(&(x_le_5, true)),
        "x<=5 should be implied true when ub=3; got {propagated:?}"
    );
    assert!(
        propagated.contains(&(x_le_10, true)),
        "x<=10 should be implied true when ub=3; got {propagated:?}"
    );
}

/// Mixed small/large atom lists should use JIT for small atoms and still fall
/// through to the interpreted path for large BigRational atom bounds.
#[test]
fn test_jit_mixed_atom_fallback_propagates_large_bound_atom() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let huge_value = BigRational::from(BigInt::from(i64::MAX) + BigInt::from(1u32));
    let huge = terms.mk_rational(huge_value);

    let x_le_3 = terms.mk_le(x, three);
    let x_le_5 = terms.mk_le(x, five);
    let x_le_huge = terms.mk_le(x, huge);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_le_3);
    solver.register_atom(x_le_5);
    solver.register_atom(x_le_huge);
    solver.compile_theory_prop_jit();

    assert_eq!(solver.theory_prop_jit.total_atoms(), 3);
    assert_eq!(solver.theory_prop_jit.small_atoms(), 2);

    solver.push();
    solver.assert_literal(x_le_3, true);
    let result = solver.check();
    assert!(is_sat_like(&result), "x <= 3 should be satisfiable");

    let propagated: Vec<(TermId, bool)> = solver
        .pending_propagations
        .iter()
        .map(|p| (p.propagation.literal.term, p.propagation.literal.value))
        .collect();

    assert!(
        propagated.contains(&(x_le_5, true)),
        "small bound atom should be propagated by the JIT path; got {propagated:?}"
    );
    assert!(
        propagated.contains(&(x_le_huge, true)),
        "large bound atom should be propagated by the interpreted fallback; got {propagated:?}"
    );
    assert!(
        solver.stats.jit_propagation_count > 0,
        "mixed variables should still use the JIT for small atoms"
    );
}

/// Test that JIT handles compound atoms correctly (they should not break).
#[test]
fn test_jit_compound_atom_no_crash() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let sum = terms.mk_add(vec![x, y]);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_3);

    // Compound atoms go into atom_index under a slack variable.
    // The JIT should handle them correctly.
    solver.compile_theory_prop_jit();
    assert!(solver.theory_prop_jit_compiled);

    // Should have compiled 1 variable (the slack) with 1 atom.
    assert!(solver.theory_prop_jit.compiled_vars() >= 1);
    assert!(solver.theory_prop_jit.total_atoms() >= 1);
}

/// Test that native machine code propagators are compiled on aarch64/x86_64
/// and that JIT propagation produces non-zero propagation count.
#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
#[test]
fn test_native_propagation_fires_end_to_end() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));

    let x_le_5 = terms.mk_le(x, five);
    let x_le_10 = terms.mk_le(x, ten);
    let x_le_3 = terms.mk_le(x, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_le_5);
    solver.register_atom(x_le_10);
    solver.register_atom(x_le_3);

    // Fix A1: native emission is hotness-deferred by default; force eager
    // emission since this test exercises the native path directly.
    solver.theory_prop_jit.set_native_compile_threshold(0);

    // Compile JIT -- should produce native propagators on supported platforms.
    solver.compile_theory_prop_jit();
    assert!(solver.theory_prop_jit_compiled);

    // Verify native compilation happened.
    assert!(
        solver.theory_prop_jit.native_compiled_vars() > 0,
        "Expected native machine code propagators on this platform, got 0"
    );

    // Now assert x <= 3 and run check to trigger propagation.
    solver.push();
    solver.assert_literal(x_le_3, true);
    let result = solver.check();
    assert!(is_sat_like(&result), "x <= 3 should be satisfiable");

    // After propagation, x<=5 and x<=10 should be implied true via the
    // native JIT path. The jit_propagation_count tracks this.
    assert!(
        solver.stats.jit_propagation_count > 0,
        "Expected JIT propagation count > 0 after asserting x <= 3; got {}",
        solver.stats.jit_propagation_count
    );
}
