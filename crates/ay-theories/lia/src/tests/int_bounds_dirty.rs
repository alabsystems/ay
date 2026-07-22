// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #C4 tests: dirty-set short-circuit for `check_integer_bounds_conflict`,
//! i64 fast-path equivalence for the effective integer bounds, and conflict
//! literal identity (the development design notes §C4, §3).

use super::*;
use ay_core::{Sort, TheoryResult, TheorySolver};
use ay_lra::rational::Rational;
use ay_lra::Bound;
use num_bigint::BigInt;

fn mk_bound(value: Rational, strict: bool) -> Bound {
    Bound {
        value,
        reasons: Vec::new(),
        reason_values: Vec::new(),
        reason_scales: Vec::new(),
        strict,
        provenance: None,
    }
}

#[test]
fn effective_int_bounds_i64_fast_path_matches_big_path() {
    let small_cases = [
        Rational::new(5, 1),
        Rational::new(-5, 1),
        Rational::new(0, 1),
        Rational::new(11, 2),
        Rational::new(-11, 2),
        Rational::new(1, 3),
        Rational::new(-1, 3),
    ];
    for value in small_cases {
        for strict in [false, true] {
            let b = mk_bound(value.clone(), strict);
            let fast_lower = LiaSolver::effective_int_lower_i64(&b)
                .unwrap_or_else(|| panic!("i64 lower path must cover Small value {value}"));
            assert_eq!(
                BigInt::from(fast_lower),
                LiaSolver::effective_int_lower(&b),
                "lower mismatch for {value} strict={strict}"
            );
            let fast_upper = LiaSolver::effective_int_upper_i64(&b)
                .unwrap_or_else(|| panic!("i64 upper path must cover Small value {value}"));
            assert_eq!(
                BigInt::from(fast_upper),
                LiaSolver::effective_int_upper(&b),
                "upper mismatch for {value} strict={strict}"
            );
        }
    }

    // Big values: fast path declines, Big path still exact.
    let big = Rational::new(i64::MAX, 1) * Rational::new(2, 1);
    for strict in [false, true] {
        let b = mk_bound(big.clone(), strict);
        assert_eq!(LiaSolver::effective_int_lower_i64(&b), None);
        assert_eq!(LiaSolver::effective_int_upper_i64(&b), None);
        let expect = BigInt::from(i64::MAX) * BigInt::from(2);
        assert_eq!(
            LiaSolver::effective_int_lower(&b),
            if strict {
                &expect + BigInt::from(1)
            } else {
                expect.clone()
            }
        );
        assert_eq!(
            LiaSolver::effective_int_upper(&b),
            if strict {
                &expect - BigInt::from(1)
            } else {
                expect.clone()
            }
        );
    }

    // Overflow guard: strict integer bound at i64::MAX must fall back, and
    // the Big path must produce i64::MAX + 1.
    let b = mk_bound(Rational::new(i64::MAX, 1), true);
    assert_eq!(LiaSolver::effective_int_lower_i64(&b), None);
    assert_eq!(
        LiaSolver::effective_int_lower(&b),
        BigInt::from(i64::MAX) + BigInt::from(1)
    );
}

#[test]
fn integer_gap_conflict_literal_set_unchanged() {
    // x > 0 ∧ x < 1 with x : Int — LRA-feasible (x = 1/2), integer-infeasible.
    // The conflict must cite exactly the two bound atoms, both positive.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let gt = terms.mk_gt(x, zero);
    let lt = terms.mk_lt(x, one);

    let mut solver = LiaSolver::new(&terms);
    solver.register_atom(gt);
    solver.register_atom(lt);
    solver.assert_literal(gt, true);
    solver.assert_literal(lt, true);

    // The relaxation layer may report this as UnsatWithFarkas (LRA
    // integer-mode strict-bound tightening) or LIA's bounds check may catch
    // it as plain Unsat — either way the literal set must be exactly the
    // two bound atoms.
    let lits = match solver.check_during_propagate() {
        TheoryResult::Unsat(lits) => lits,
        TheoryResult::UnsatWithFarkas(conflict) => conflict.literals,
        other => panic!("expected a conflict from integer bounds gap, got {other:?}"),
    };
    let mut atoms: Vec<(TermId, bool)> = lits.iter().map(|l| (l.term, l.value)).collect();
    atoms.sort_by_key(|&(t, _)| t.0);
    atoms.dedup();
    assert_eq!(
        atoms,
        vec![(gt, true), (lt, true)],
        "integer-gap conflict must cite exactly the two bound atoms"
    );

    // Direct white-box check of #C4 `check_integer_bounds_conflict`: the
    // LRA bound slots now hold the integer-tightened gap, and the dirty
    // state still includes x (conflicts never clear it), so the rewritten
    // scan must find the same conflict with the same literal set.
    let conflict = solver
        .check_integer_bounds_conflict()
        .expect("bounds-conflict scan must detect the gap");
    let mut direct: Vec<(TermId, bool)> = conflict
        .literals
        .iter()
        .map(|l| (l.term, l.value))
        .collect();
    direct.sort_by_key(|&(t, _)| t.0);
    direct.dedup();
    assert_eq!(direct, vec![(gt, true), (lt, true)]);
}

#[test]
fn dirty_set_short_circuit_finds_gap_after_certified_check() {
    // Conflict-free check certifies the bounds and clears the dirty state;
    // a later in-scope tightening must be found through the dirty subset.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let ten = terms.mk_int(BigInt::from(10));
    let four = terms.mk_int(BigInt::from(4));
    let five = terms.mk_int(BigInt::from(5));

    let base = [
        terms.mk_ge(x, zero),
        terms.mk_le(x, ten),
        terms.mk_ge(y, zero),
        terms.mk_le(y, ten),
    ];
    let y_gt_4 = terms.mk_gt(y, four);
    let y_lt_5 = terms.mk_lt(y, five);

    let mut solver = LiaSolver::new(&terms);
    for atom in base {
        solver.register_atom(atom);
        solver.assert_literal(atom, true);
    }
    solver.register_atom(y_gt_4);
    solver.register_atom(y_lt_5);

    assert!(
        matches!(solver.check_during_propagate(), TheoryResult::Sat),
        "base bounds are satisfiable"
    );
    // White-box: the conflict-free scan certified the current bounds.
    assert!(!solver.int_bounds_all_dirty);
    assert!(solver.int_bounds_dirty.is_empty());

    solver.push();
    solver.assert_literal(y_gt_4, true);
    solver.assert_literal(y_lt_5, true);
    // White-box: y was re-marked by the assertion hooks.
    assert!(solver.int_bounds_dirty.contains(&y));
    assert!(!solver.int_bounds_all_dirty);

    let lits = match solver.check_during_propagate() {
        TheoryResult::Unsat(lits) => lits,
        TheoryResult::UnsatWithFarkas(conflict) => conflict.literals,
        other => panic!("expected a conflict via dirty-subset scan, got {other:?}"),
    };
    let atom_set: Vec<TermId> = lits.iter().map(|l| l.term).collect();
    assert!(
        atom_set.contains(&y_gt_4) && atom_set.contains(&y_lt_5),
        "gap conflict must cite the two y bound atoms, got {atom_set:?}"
    );

    // Direct white-box check: with `int_bounds_all_dirty == false`, the
    // dirty-SUBSET scan alone must find the gap on y.
    assert!(!solver.int_bounds_all_dirty);
    let conflict = solver
        .check_integer_bounds_conflict()
        .expect("dirty-subset scan must detect the y gap");
    let direct: Vec<TermId> = conflict.literals.iter().map(|l| l.term).collect();
    assert!(
        direct.contains(&y_gt_4) && direct.contains(&y_lt_5),
        "dirty-subset conflict must cite the two y bound atoms, got {direct:?}"
    );

    // Conflict keeps the dirty marks; pop widens y back and the next scan
    // re-certifies without missing anything.
    solver.pop();
    assert!(
        matches!(solver.check_during_propagate(), TheoryResult::Sat),
        "after pop the base bounds are satisfiable again"
    );
    assert!(solver.int_bounds_dirty.is_empty());
    assert!(!solver.int_bounds_all_dirty);
}

#[test]
fn lra_solver_mut_escape_hatch_forces_full_rescan() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let ge = terms.mk_ge(x, zero);

    let mut solver = LiaSolver::new(&terms);
    solver.register_atom(ge);
    solver.assert_literal(ge, true);
    assert!(matches!(solver.check_during_propagate(), TheoryResult::Sat));
    assert!(!solver.int_bounds_all_dirty);

    // External mutable access could tighten arbitrary bounds.
    let _ = solver.lra_solver_mut();
    assert!(solver.int_bounds_all_dirty);
}

#[test]
fn sorted_integer_vars_mirror_stays_consistent() {
    let mut terms = TermStore::new();
    let atoms: Vec<TermId> = (0..6)
        .map(|i| {
            let v = terms.mk_var(format!("v{i}"), Sort::Int);
            let c = terms.mk_int(BigInt::from(i));
            terms.mk_ge(v, c)
        })
        .collect();

    let mut solver = LiaSolver::new(&terms);
    // Assert in shuffled order so insertion order differs from TermId order.
    for &idx in &[3usize, 0, 5, 1, 4, 2] {
        solver.assert_literal(atoms[idx], true);
    }
    assert_eq!(solver.sorted_integer_vars.len(), solver.integer_vars.len());
    assert!(
        solver
            .sorted_integer_vars
            .windows(2)
            .all(|w| w[0].0 < w[1].0),
        "sorted_integer_vars must be strictly sorted by raw TermId"
    );
    for t in &solver.sorted_integer_vars {
        assert!(solver.integer_vars.contains(t));
    }
}
