// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solver-level tests for the bounded Groebner pass (#nia-groebner): the
//! refutations below need an ideal consequence of the asserted equality
//! atoms that is linear over the tracked monomials — invisible to the
//! linearized relaxation (each product an opaque aux var), to monomial
//! congruence (no syntactic `(= a b)` link), and to every box-shaped
//! fallback (the variables are unbounded).

use super::*;
use num_bigint::BigInt;

/// Literals of either unsat representation (plain or Farkas-annotated).
fn unsat_lits(result: &TheoryResult) -> Option<Vec<TheoryLit>> {
    match result {
        TheoryResult::Unsat(lits) => Some(lits.clone()),
        TheoryResult::UnsatWithFarkas(conflict) => Some(conflict.literals.clone()),
        _ => None,
    }
}

fn int(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_int(BigInt::from(n))
}

/// `x*x = x ∧ x*y = 1 ∧ x <= 0` is unsat: the Groebner basis of
/// `{x^2 - x, x*y - 1}` contains `x - 1` (via `y*(x^2-x) - x*(x*y-1)
/// = x - x*y`, reduced by `x*y - 1`), and `x = 1` contradicts `x <= 0`
/// linearly. The relaxation admits spurious points (e.g. `x = -1`,
/// auxes chosen to satisfy only the linear rows), so this refutation
/// must come from the derived equality. The conflict must name the two
/// product equalities and the bound — the provenance of `x - 1` plus
/// the contradicting atom.
#[test]
fn groebner_derived_linear_equality_refutes() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let zero = int(&mut terms, 0);
    let one = int(&mut terms, 1);
    let xx = terms.mk_mul(vec![x, x]);
    let xy = terms.mk_mul(vec![x, y]);
    let xx_eq_x = terms.mk_eq(xx, x);
    let xy_eq_1 = terms.mk_eq(xy, one);
    let x_le_0 = terms.mk_le(x, zero);

    let mut solver = NiaSolver::new(&terms);
    for atom in [xx_eq_x, xy_eq_1, x_le_0] {
        solver.assert_literal(atom, true);
    }
    let result = solver.check();
    let Some(lits) = unsat_lits(&result) else {
        panic!("x^2=x, x*y=1 force x=1, contradicting x<=0: {result:?}");
    };
    for atom in [xx_eq_x, xy_eq_1, x_le_0] {
        assert!(
            lits.contains(&TheoryLit::new(atom, true)),
            "conflict {lits:?} must name every atom the refutation used"
        );
    }
}

/// Shared-bilinear cancellation through an arithmetic (non-syntactic)
/// factor equality: `a*l + u = 0 ∧ b*l + v = 0 ∧ a - b = 0` implies
/// `u = v` in the ideal (reduce the first polynomial by `a - b`, then
/// cancel the shared lead `b*l`). Congruence cannot link the products
/// (`a - b = 0` is not an `(= a b)` atom), and with `u = 3 ∧ v = 5`
/// nothing else in the relaxation connects `u` to `v`. This is the
/// VeryMax/Farkas shape (`Nl * lam + linear = 0` rows sharing the
/// multiplier variable) at unit scale.
#[test]
fn groebner_cancels_shared_bilinear_lead() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let l = terms.mk_var("l", Sort::Int);
    let u = terms.mk_var("u", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let zero = int(&mut terms, 0);
    let three = int(&mut terms, 3);
    let five = int(&mut terms, 5);
    let neg_one = int(&mut terms, -1);
    let al = terms.mk_mul(vec![a, l]);
    let bl = terms.mk_mul(vec![b, l]);
    let al_plus_u = terms.mk_add(vec![al, u]);
    let bl_plus_v = terms.mk_add(vec![bl, v]);
    let neg_b = terms.mk_mul(vec![neg_one, b]);
    let a_minus_b = terms.mk_add(vec![a, neg_b]);
    let row1 = terms.mk_eq(al_plus_u, zero);
    let row2 = terms.mk_eq(bl_plus_v, zero);
    let a_eq_b = terms.mk_eq(a_minus_b, zero);
    let u_eq_3 = terms.mk_eq(u, three);
    let v_eq_5 = terms.mk_eq(v, five);

    let mut solver = NiaSolver::new(&terms);
    for atom in [row1, row2, a_eq_b, u_eq_3, v_eq_5] {
        solver.assert_literal(atom, true);
    }
    let result = solver.check();
    let Some(lits) = unsat_lits(&result) else {
        panic!("a=b makes the bilinear rows force u=v, contradicting u=3,v=5: {result:?}");
    };
    for atom in [row1, row2, a_eq_b, u_eq_3, v_eq_5] {
        assert!(
            lits.contains(&TheoryLit::new(atom, true)),
            "conflict {lits:?} must name every atom the refutation used"
        );
    }
}

// Pure Buchberger tests (no solver state), against `groebner.rs`.

use super::groebner::{buchberger, integer_signature, GPoly, Mono, PolyTerms};

fn gpoly(terms: &[(Mono, i64)]) -> GPoly {
    GPoly {
        terms: terms
            .iter()
            .map(|(m, c)| (m.clone(), BigRational::from_integer((*c).into())))
            .collect(),
        provenance: vec![(TermId(900), true)],
    }
}

fn has_signature(basis: &[GPoly], want: &[(Mono, i64)]) -> bool {
    let want_terms: PolyTerms = want
        .iter()
        .map(|(m, c)| (m.clone(), BigRational::from_integer((*c).into())))
        .collect();
    let want_sig = integer_signature(&want_terms);
    basis
        .iter()
        .any(|p| integer_signature(&p.terms) == want_sig)
}

/// `x*y - 1` and `x*y - 2` share a lead; their S-polynomial is the
/// nonzero constant `1` — the ideal is the whole ring.
#[test]
fn buchberger_derives_constant_from_shared_lead() {
    let (x, y) = (TermId(1), TermId(2));
    let basis = buchberger(vec![
        gpoly(&[(vec![x, y], 1), (vec![], -1)]),
        gpoly(&[(vec![x, y], 1), (vec![], -2)]),
    ]);
    assert!(
        basis.iter().any(GPoly::is_constant),
        "basis must contain a nonzero constant"
    );
}

/// The slayer pattern at the algebra level: `a*l + u`, `b*l + v`,
/// `a - b` derive `u - v` (reduce by `a - b`, then cancel `b*l`).
#[test]
fn buchberger_cancels_bilinear_lead_after_linear_reduction() {
    let (a, b, l, u, v) = (TermId(1), TermId(2), TermId(3), TermId(4), TermId(5));
    let basis = buchberger(vec![
        gpoly(&[(vec![a, l], 1), (vec![u], 1)]),
        gpoly(&[(vec![b, l], 1), (vec![v], 1)]),
        gpoly(&[(vec![a], 1), (vec![b], -1)]),
    ]);
    assert!(
        has_signature(&basis, &[(vec![u], 1), (vec![v], -1)]),
        "basis must derive u - v"
    );
}

/// `x^2 - x` and `x*y - 1` derive `x - 1`.
#[test]
fn buchberger_derives_x_minus_one() {
    let (x, y) = (TermId(1), TermId(2));
    let basis = buchberger(vec![
        gpoly(&[(vec![x, x], 1), (vec![x], -1)]),
        gpoly(&[(vec![x, y], 1), (vec![], -1)]),
    ]);
    assert!(
        has_signature(&basis, &[(vec![x], 1), (vec![], -1)]),
        "basis must derive x - 1"
    );
}

/// Regression guard: `x*y + w = 0 ∧ y*z + w = 0` with tight boxes
/// derives (S-polynomial) `w*z - w*x = 0` with interval `[8, 22]`
/// under `w ∈ [1,2]`, `z ∈ [10,11]`, `x ∈ [0,1]`. Recorded as already
/// refuted today (interval contraction chains through `y` and `w`);
/// kept so the shape stays refuted whatever slice handles it.
#[test]
fn groebner_derived_interval_excludes_zero() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let zero = int(&mut terms, 0);
    let one = int(&mut terms, 1);
    let two = int(&mut terms, 2);
    let ten = int(&mut terms, 10);
    let eleven = int(&mut terms, 11);
    let xy = terms.mk_mul(vec![x, y]);
    let yz = terms.mk_mul(vec![y, z]);
    let row1_sum = terms.mk_add(vec![xy, w]);
    let row1 = terms.mk_eq(row1_sum, zero);
    let row2_sum = terms.mk_add(vec![yz, w]);
    let row2 = terms.mk_eq(row2_sum, zero);
    let w_lo = terms.mk_ge(w, one);
    let w_hi = terms.mk_le(w, two);
    let z_lo = terms.mk_ge(z, ten);
    let z_hi = terms.mk_le(z, eleven);
    let x_lo = terms.mk_ge(x, zero);
    let x_hi = terms.mk_le(x, one);

    let mut solver = NiaSolver::new(&terms);
    for atom in [row1, row2, w_lo, w_hi, z_lo, z_hi, x_lo, x_hi] {
        solver.assert_literal(atom, true);
    }
    let result = solver.check();
    assert!(
        unsat_lits(&result).is_some(),
        "w*(z-x)=0 has interval [8,22] under the boxes: {result:?}"
    );
}
