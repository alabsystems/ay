// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #nonlinear-shared-reasons: an NIA conflict that names the asserted set
//! must also name the EUF shared equalities the inner LIA held.
//!
//! QF_UFNIA `euf_div_010` (`x*y = 28`, `x, y >= 1`, `f(a) = x`, `f(b) = w`,
//! `w >= 29`, `a = c ∨ a = b`, `f(c) = 4`; z3 `sat` with `a = c`): with
//! `a = b` decided, EUF hands the NIA `f(a) = f(b)` with reason `(= a b)`, the
//! LIA holds it as a row, the refutation `x = w >= 29 > 28 >= x` uses it, and
//! main returned the 17 asserted atoms alone — a set z3 satisfies. The
//! learned clause was empty and the lane answered `unsat`.
//!
//! The pin: replay the shape at the theory-solver level, take whatever
//! conflict the solver returns, and RE-CHECK IT STANDALONE on a fresh solver
//! that holds only what the conflict names — the arithmetic atoms it lists,
//! and a shared equality only when its reason literal is listed. The conflict
//! is a theorem iff that fresh solver refutes it too. Remove the shared
//! reasons from `full_conflict_lits` and the re-check finds the named atoms
//! satisfiable (`f(a)` and `f(b)` unrelated) and this test fails.

use super::*;
use num_bigint::BigInt;

fn int(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_int(BigInt::from(n))
}

fn conflict_lits(result: &TheoryResult) -> Option<Vec<TheoryLit>> {
    match result {
        TheoryResult::Unsat(lits) => Some(lits.clone()),
        TheoryResult::UnsatWithFarkas(conflict) => Some(conflict.literals.clone()),
        _ => None,
    }
}

/// One EUF shared equality as the combiner forwards it.
struct Shared {
    lhs: TermId,
    rhs: TermId,
    reason: TheoryLit,
}

/// The `euf_div` shape with `f(a)`, `f(b)` as opaque Int terms and the EUF
/// literal `(= a b)` as a Boolean atom the NIA never sees asserted.
struct EufDiv {
    terms: TermStore,
    atoms: Vec<TermId>,
    shared: Shared,
}

fn euf_div_shape() -> EufDiv {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let fa = terms.mk_var("f_a", Sort::Int);
    let fb = terms.mk_var("f_b", Sort::Int);
    let a_eq_b = terms.mk_var("a_eq_b", Sort::Bool);
    let one = int(&mut terms, 1);
    let c28 = int(&mut terms, 28);
    let c29 = int(&mut terms, 29);
    let xy = terms.mk_mul(vec![x, y]);
    let atoms = vec![
        terms.mk_eq(xy, c28),
        terms.mk_ge(x, one),
        terms.mk_ge(y, one),
        terms.mk_eq(fa, x),
        terms.mk_eq(fb, w),
        terms.mk_ge(w, c29),
    ];
    EufDiv {
        terms,
        atoms,
        shared: Shared {
            lhs: fa,
            rhs: fb,
            reason: TheoryLit::new(a_eq_b, true),
        },
    }
}

/// Re-decide `conflict` on a fresh solver holding exactly what it names.
/// Returns the fresh solver's verdict.
fn recheck_standalone(shape: &EufDiv, conflict: &[TheoryLit]) -> TheoryResult {
    let mut fresh = NiaSolver::new(&shape.terms);
    for lit in conflict {
        if shape.atoms.contains(&lit.term) {
            fresh.assert_literal(lit.term, lit.value);
        }
    }
    if conflict.contains(&shape.shared.reason) {
        fresh.assert_shared_equality(shape.shared.lhs, shape.shared.rhs, &[shape.shared.reason]);
    }
    fresh.check()
}

#[test]
fn euf_div_conflict_is_a_theorem_on_its_own() {
    let shape = euf_div_shape();
    let mut solver = NiaSolver::new(&shape.terms);
    for &atom in &shape.atoms {
        solver.assert_literal(atom, true);
    }
    solver.assert_shared_equality(shape.shared.lhs, shape.shared.rhs, &[shape.shared.reason]);
    let result = solver.check();
    let conflict = conflict_lits(&result)
        .unwrap_or_else(|| panic!("x = f(a) = f(b) = w >= 29 contradicts x*y = 28: {result:?}"));
    for lit in &conflict {
        assert!(
            shape.atoms.contains(&lit.term) || *lit == shape.shared.reason,
            "the conflict names a literal that is neither an asserted atom nor a shared \
             reason: {lit:?}"
        );
    }
    let recheck = recheck_standalone(&shape, &conflict);
    assert!(
        conflict_lits(&recheck).is_some(),
        "the returned conflict ({} literals, shared reason present: {}) is NOT refuted on \
         its own — it is not a theorem, and learning it excludes models: {recheck:?}",
        conflict.len(),
        conflict.contains(&shape.shared.reason),
    );
}

/// The atoms alone are satisfiable, so a conflict that omits the reason can
/// never pass `recheck_standalone` — the control that makes the pin above
/// bite rather than pass vacuously.
#[test]
fn euf_div_atoms_without_the_shared_equality_are_satisfiable() {
    let shape = euf_div_shape();
    let bare: Vec<TheoryLit> = shape
        .atoms
        .iter()
        .map(|&atom| TheoryLit::new(atom, true))
        .collect();
    let recheck = recheck_standalone(&shape, &bare);
    assert!(
        conflict_lits(&recheck).is_none(),
        "x=4, y=7, f(a)=4, f(b)=w=29 satisfies the atoms alone: {recheck:?}"
    );
}

/// `full_conflict_lits` is the asserted set followed by every shared
/// equality AND disequality reason, deduplicated; with none held it is the
/// asserted set exactly (pure QF_NIA conflicts are unchanged).
#[test]
fn full_conflict_lits_names_shared_equality_and_disequality_reasons() {
    let shape = euf_div_shape();
    let mut terms = shape.terms;
    let u = terms.mk_var("u", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let u_eq_v = terms.mk_var("u_eq_v", Sort::Bool);
    let mut solver = NiaSolver::new(&terms);
    for &atom in &shape.atoms {
        solver.assert_literal(atom, true);
    }
    let bare: Vec<TheoryLit> = shape
        .atoms
        .iter()
        .map(|&atom| TheoryLit::new(atom, true))
        .collect();
    assert_eq!(solver.full_conflict_lits(), bare);

    solver.push();
    solver.assert_shared_equality(shape.shared.lhs, shape.shared.rhs, &[shape.shared.reason]);
    let diseq_reason = TheoryLit::new(u_eq_v, false);
    solver.assert_shared_disequality(u, v, &[diseq_reason]);
    // The same reason twice is named once.
    solver.assert_shared_equality(shape.shared.lhs, shape.shared.rhs, &[shape.shared.reason]);
    let full = solver.full_conflict_lits();
    assert_eq!(
        &full[..bare.len()],
        &bare[..],
        "asserted atoms first, in order"
    );
    assert_eq!(
        &full[bare.len()..],
        &[shape.shared.reason, diseq_reason],
        "then each shared reason once"
    );

    // Popping the scope the shared facts arrived in forgets them.
    solver.pop();
    assert_eq!(solver.full_conflict_lits(), bare);
}
