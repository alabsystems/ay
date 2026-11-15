// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #nonlinear-shared-reasons: an NRA conflict that names the asserted set
//! also names the EUF shared equalities and disequalities its LRA holds
//! (`full_conflict.rs`; the NIA twin is `ay-nia/src/shared_reason_tests.rs`,
//! which carries the refutation the omission made wrong).

use super::*;
use ay_core::Sort;
use num_bigint::BigInt;

fn real(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_rational(BigRational::from_integer(BigInt::from(n)))
}

fn conflict_lits(result: &TheoryResult) -> Option<Vec<TheoryLit>> {
    match result {
        TheoryResult::Unsat(lits) => Some(lits.clone()),
        TheoryResult::UnsatWithFarkas(conflict) => Some(conflict.literals.clone()),
        _ => None,
    }
}

#[test]
fn full_conflict_lits_names_shared_reasons_in_scope() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let fa = terms.mk_var("f_a", Sort::Real);
    let fb = terms.mk_var("f_b", Sort::Real);
    let fc = terms.mk_var("f_c", Sort::Real);
    let a_eq_b = terms.mk_var("a_eq_b", Sort::Bool);
    let a_eq_c = terms.mk_var("a_eq_c", Sort::Bool);
    let one = real(&mut terms, 1);
    let atom = terms.mk_ge(x, one);
    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(atom, true);
    let bare = vec![TheoryLit::new(atom, true)];
    assert_eq!(solver.full_conflict_lits(), bare);

    solver.push();
    let eq_reason = TheoryLit::new(a_eq_b, true);
    let diseq_reason = TheoryLit::new(a_eq_c, false);
    solver.assert_shared_equality(fa, fb, &[eq_reason]);
    solver.assert_shared_disequality(fa, fc, &[diseq_reason]);
    solver.assert_shared_equality(fa, fb, &[eq_reason]);
    assert_eq!(
        solver.full_conflict_lits(),
        vec![bare[0], eq_reason, diseq_reason]
    );
    // A reasonless shared equality is installed with its arithmetic `lhs` as a
    // placeholder reason. That is not an atom, and it is named anyway: a
    // conflict naming it cannot become a clause and the DPLL layer fails
    // closed, where dropping it would publish a conflict resting on a fact
    // nobody can name.
    solver.assert_shared_equality(fb, fc, &[]);
    assert_eq!(
        solver.full_conflict_lits(),
        vec![bare[0], eq_reason, diseq_reason, TheoryLit::new(fb, true)]
    );

    solver.pop();
    assert_eq!(solver.full_conflict_lits(), bare);
}

/// A full-set pre-phase refutation (the exact interval phase: `x >= 2` and
/// `x*x + y*y <= 1`) returns the shared reasons with the asserted atoms.
/// That refutation reads the asserted atoms alone, so here the widening only
/// weakens the clause; the pin is that no full-set site bypasses it.
#[test]
fn prephase_full_set_conflict_carries_shared_reasons() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let fa = terms.mk_var("f_a", Sort::Real);
    let fb = terms.mk_var("f_b", Sort::Real);
    let a_eq_b = terms.mk_var("a_eq_b", Sort::Bool);
    let one = real(&mut terms, 1);
    let two = real(&mut terms, 2);
    let xx = terms.mk_mul(vec![x, x]);
    let yy = terms.mk_mul(vec![y, y]);
    let sum = terms.mk_add(vec![xx, yy]);
    let atoms = [terms.mk_ge(x, two), terms.mk_le(sum, one)];
    let mut solver = NraSolver::new(&terms);
    for atom in atoms {
        solver.assert_literal(atom, true);
    }
    let reason = TheoryLit::new(a_eq_b, true);
    solver.assert_shared_equality(fa, fb, &[reason]);
    let result = solver.check();
    let conflict = conflict_lits(&result)
        .unwrap_or_else(|| panic!("x >= 2 and x*x + y*y <= 1 are inconsistent: {result:?}"));
    for atom in atoms {
        assert!(
            conflict.contains(&TheoryLit::new(atom, true)),
            "{conflict:?}"
        );
    }
    assert!(
        conflict.contains(&reason),
        "a full-set NRA conflict omitted the shared-equality reason: {conflict:?}"
    );
}
