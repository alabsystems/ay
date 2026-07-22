// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the standalone-simplex faithfulness audits (#unbounded-oo):
//! [`LraSolver::all_asserted_atoms_parsed`] and
//! [`LraSolver::all_interned_vars_are_declared_vars`].
//!
//! These two audits are the load-bearing soundness gate for trusting an
//! `OptimizationResult::Unbounded` verdict from a standalone tableau: part 1
//! rejects skipped Boolean structure (the tableau would be a relaxation),
//! part 2 rejects opaque sub-terms interned as fresh FREE variables (a free
//! variable is trivially unbounded) — in atoms AND in the objective.

use super::*;
use crate::OptimizationSense;
use num_bigint::BigInt;
use num_rational::BigRational;

fn rat(n: i64) -> BigRational {
    BigRational::from(BigInt::from(n))
}

/// Pure non-strict linear conjunction: both audits pass.
#[test]
fn audit_passes_on_pure_linear_conjunction() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let five = terms.mk_rational(rat(5));
    let zero = terms.mk_rational(rat(0));
    let sum = terms.mk_add(vec![x, y]);
    let le = terms.mk_le(sum, five);
    let ge = terms.mk_ge(x, zero);

    let mut solver = LraSolver::new(&terms);
    solver.set_standalone_simplex_mode();
    solver.assert_literal(le, true);
    solver.assert_literal(ge, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    assert!(solver.all_asserted_atoms_parsed());
    assert!(solver.all_interned_vars_are_declared_vars());
}

/// An asserted `or` term is skipped by the LRA (the SAT solver owns it), so
/// the tableau is a relaxation: part 1 must fail.
#[test]
fn audit_fails_on_asserted_or_term() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let three = terms.mk_rational(rat(3));
    let five = terms.mk_rational(rat(5));
    let le5 = terms.mk_le(x, five);
    let le3 = terms.mk_le(x, three);
    let or = terms.mk_or(vec![le5, le3]);

    let mut solver = LraSolver::new(&terms);
    solver.set_standalone_simplex_mode();
    solver.assert_literal(or, true);
    // The or-term is skipped (not an arithmetic atom); the tableau sees
    // NOTHING, so `maximize x` over it would be a relaxation-unbounded.
    solver.check();

    assert!(!solver.all_asserted_atoms_parsed());
}

/// `(assert true)` is the one non-arithmetic literal that does NOT weaken the
/// polyhedron: part 1 accepts it.
#[test]
fn audit_accepts_asserted_true_constant() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let t = terms.mk_bool(true);
    let zero = terms.mk_rational(rat(0));
    let ge = terms.mk_ge(x, zero);

    let mut solver = LraSolver::new(&terms);
    solver.set_standalone_simplex_mode();
    solver.assert_literal(t, true);
    solver.assert_literal(ge, true);
    solver.check();

    assert!(solver.all_asserted_atoms_parsed());
}

/// A Bool VARIABLE asserted as a literal is skipped without an unsupported
/// mark (#8373 ITE-condition forwarding): part 1 must fail (fail-closed).
#[test]
fn audit_fails_on_asserted_bool_var() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let p = terms.mk_var("p", Sort::Bool);
    let zero = terms.mk_rational(rat(0));
    let ge = terms.mk_ge(x, zero);

    let mut solver = LraSolver::new(&terms);
    solver.set_standalone_simplex_mode();
    solver.assert_literal(p, true);
    solver.assert_literal(ge, true);
    solver.check();

    assert!(!solver.all_asserted_atoms_parsed());
}

/// THE REFUTATION CASE (atom side): `(= y (ite c 1 2))` parses with
/// `has_unsupported == false` by design (branch semantics arrive via
/// NeedModelEqualities link lemmas, which standalone mode suppresses), so
/// part 1 PASSES — only the backing-term rule of part 2 catches the fresh
/// ITE variable. Without it, `maximize y` concluded `oo` over a relaxation
/// (z3: 2).
#[test]
fn audit_part2_fails_on_ite_atom_that_part1_accepts() {
    let mut terms = TermStore::new();
    let y = terms.mk_var("y", Sort::Real);
    let c = terms.mk_var("c", Sort::Bool);
    let one = terms.mk_rational(rat(1));
    let two = terms.mk_rational(rat(2));
    let ite = terms.mk_ite_raw(c, one, two);
    // `mk_eq` would ite-expand into a Bool ITE (which part 1 already rejects);
    // the shape that fools part 1 is the RAW arithmetic equality over a term
    // ITE — exactly what reaches the LRA when ITE lifting leaves one behind.
    let eq = terms.mk_eq_coerce_no_ite_expand(y, ite);

    let mut solver = LraSolver::new(&terms);
    solver.set_standalone_simplex_mode();
    solver.assert_literal(eq, true);
    solver.check();

    // Part 1 alone is fooled (this is exactly why part 2 exists).
    assert!(solver.all_asserted_atoms_parsed());
    assert!(!solver.all_interned_vars_are_declared_vars());
}

/// THE REFUTATION CASE (objective side): parsing an opaque OBJECTIVE
/// (`(* x x)`) interns a fresh free variable with `current_parsing_atom ==
/// None`, so no unsupported mark exists anywhere — part 2 is the only gate.
/// Without it, bounded `maximize (* x x)` read as maximizing a free variable
/// (trivially "unbounded").
#[test]
fn audit_part2_fails_on_opaque_objective_parse() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(rat(5));
    let zero = terms.mk_rational(rat(0));
    let le = terms.mk_le(x, five);
    let ge = terms.mk_ge(x, zero);
    let xx = terms.mk_mul(vec![x, x]);

    let mut solver = LraSolver::new(&terms);
    solver.set_standalone_simplex_mode();
    solver.assert_literal(le, true);
    solver.assert_literal(ge, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    // Atoms alone are faithful...
    assert!(solver.all_asserted_atoms_parsed());
    assert!(solver.all_interned_vars_are_declared_vars());

    // ...but the objective parse interns the opaque `(* x x)` term.
    let obj = solver.parse_linear_expr(xx);
    assert!(!solver.all_interned_vars_are_declared_vars());

    // And the relaxed LP is indeed "unbounded" — the exact verdict the audit
    // must prevent callers from trusting.
    assert!(matches!(
        solver.optimize(&obj, OptimizationSense::Maximize),
        OptimizationResult::Unbounded
    ));
}
