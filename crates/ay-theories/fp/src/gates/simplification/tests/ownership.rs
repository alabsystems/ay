// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::FpEncodingCache;

#[test]
fn free_numeric_literals_and_arbitrary_units_are_not_known_constants() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = solver.fresh_var();
    let b = solver.fresh_var();
    assert_eq!(a, 1);
    for lit in [a, -a, b, -b] {
        assert_eq!(solver.known_literal_value(lit), None);
    }
    solver.add_clause(CnfClause::unit(a));
    assert_eq!(solver.known_literal_value(a), None);
    let out = solver.make_and(a, b);
    assert_ne!(out, b);
    assert_eq!((solver.num_vars(), solver.clauses().len()), (3, 4));
}

#[test]
fn both_canonical_caches_and_their_negations_are_recognized() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let f = solver.const_false();
    let t = solver.const_true();
    let x = solver.fresh_var();
    assert_ne!(f, -t);
    let before = (solver.num_vars(), solver.clauses().len());
    for lit in [f, -t] {
        assert_eq!(solver.known_literal_value(lit), Some(false));
        assert_eq!(solver.make_or(lit, x), x);
        assert_eq!(solver.make_xor(x, lit), x);
    }
    for lit in [t, -f] {
        assert_eq!(solver.known_literal_value(lit), Some(true));
        assert_eq!(solver.make_and(lit, x), x);
        assert_eq!(solver.make_xor(x, lit), -x);
    }
    assert_eq!((solver.num_vars(), solver.clauses().len()), before);
}

#[test]
fn reset_forgets_constants_before_their_ids_become_free_again() -> TestResult {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let old_false = solver.const_false();
    let old_true = solver.const_true();
    ay_core::TheorySolver::reset(&mut solver);
    let a = solver.fresh_var();
    let b = solver.fresh_var();
    assert_eq!((a, b), (old_false, old_true));
    for lit in [a, -a, b, -b] {
        assert_eq!(solver.known_literal_value(lit), None);
    }
    let out = solver.make_and(a, b);
    assert_eq!((solver.num_vars(), solver.clauses().len()), (3, 3));
    check_cnf(3, solver.clauses(), 2, |bits| {
        Ok(value(bits, out)? == (value(bits, a)? && value(bits, b)?))
    })?;
    let new_false = solver.const_false();
    assert_ne!(new_false, old_false);
    assert_eq!(solver.make_or(new_false, out), out);
    Ok(())
}

#[test]
fn draining_and_importing_preserve_the_retained_cnf_namespace() -> TestResult {
    let terms = TermStore::new();
    let mut first = FpSolver::new(&terms);
    let a = first.fresh_var();
    let f = first.const_false();
    let t = first.const_true();
    let cache = first.export_cache();
    let retained = first.take_clauses();
    assert_eq!(retained.len(), 2);
    assert_eq!(first.make_or(f, a), a);
    assert_eq!(first.make_xor(t, a), -a);
    assert!(first.clauses().is_empty());

    let mut next = FpSolver::new(&terms);
    next.import_cache(cache);
    let before = next.num_vars();
    let out = next.make_ite(a, -f, -t);
    assert_eq!(out, a);
    assert_eq!(next.num_vars(), before);
    assert!(next.clauses().is_empty());
    check_cnf(next.num_vars(), &retained, 1, |bits| {
        Ok(value(bits, out)? == value(bits, a)?)
    })?;
    // Clearing the unrelated encoding-gap flag is not a constant-cache reset.
    next.has_encoding_gap = true;
    assert!(next.take_encoding_gap());
    assert_eq!(next.make_and(t, a), a);
    assert_eq!(next.fresh_var(), before as CnfLit + 1);
    Ok(())
}

#[test]
fn replacing_cache_does_not_keep_previous_constant_facts_or_reuse_ids() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let f = solver.const_false();
    let t = solver.const_true();
    let before = solver.num_vars();
    solver.import_cache(FpEncodingCache::default());
    assert_eq!(solver.num_vars(), before);
    assert_eq!(solver.known_literal_value(f), None);
    assert_eq!(solver.known_literal_value(t), None);
    let a = solver.fresh_var();
    assert!(a > t);
    let out = solver.make_or(f, a);
    assert_ne!(out, a);
    assert_eq!(solver.clauses().len(), 5);
}
