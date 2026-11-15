// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #nia-factor-split-premises: a factor-split conflict must name every
//! asserted atom its branch refutations used.
//!
//! Shape: `x ∈ [0, 1]` (the split's cover; `x` is a factor of the registered
//! monomial `x*w`), `x + y = 3`, `y*z >= 5`, `z <= 1`. Every branch is
//! refuted: `x = 0` gives `y = 3`, `x = 1` gives `y = 2` (the linearized-atom
//! contraction derives the pin from `x + y = 3`), and then `y*z = c*z <= c < 5`.
//! The set `{x ∈ [0, 1], y*z >= 5, z <= 1, x*w >= 0}` WITHOUT `x + y = 3` is
//! satisfiable (`x = 0, y = 5, z = 1, w = 0`), so a conflict that omits
//! `x + y = 3` is not a theorem.

use super::*;
use num_bigint::BigInt;

fn int(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_int(BigInt::from(n))
}

struct Shape {
    terms: TermStore,
    x_plus_y_eq_3: TermId,
    atoms: Vec<TermId>,
}

fn derived_pin_shape() -> Shape {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let zero = int(&mut terms, 0);
    let one = int(&mut terms, 1);
    let three = int(&mut terms, 3);
    let five = int(&mut terms, 5);
    let x_plus_y = terms.mk_add(vec![x, y]);
    let yz = terms.mk_mul(vec![y, z]);
    let xw = terms.mk_mul(vec![x, w]);
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_1 = terms.mk_le(x, one);
    let x_plus_y_eq_3 = terms.mk_eq(x_plus_y, three);
    let yz_ge_5 = terms.mk_ge(yz, five);
    let z_le_1 = terms.mk_le(z, one);
    let xw_ge_0 = terms.mk_ge(xw, zero);
    Shape {
        terms,
        x_plus_y_eq_3,
        atoms: vec![x_ge_0, x_le_1, x_plus_y_eq_3, yz_ge_5, z_le_1, xw_ge_0],
    }
}

#[test]
fn factor_split_conflict_names_the_atom_that_derived_a_pin() {
    let shape = derived_pin_shape();
    let mut solver = NiaSolver::new(&shape.terms);
    for &atom in &shape.atoms {
        solver.assert_literal(atom, true);
    }
    let result = solver.try_bounded_factor_split();
    eprintln!("factor split result: {result:?}");
    let Some(TheoryResult::Unsat(lits)) = result else {
        // No refutation: nothing unsound was claimed.
        return;
    };
    assert!(
        lits.contains(&TheoryLit::new(shape.x_plus_y_eq_3, true)),
        "the factor split refuted every branch through the pin `x + y = 3` derived, \
         but its conflict {lits:?} does not name that atom — and without it the named \
         atoms are satisfiable (x = 0, y = 5, z = 1, w = 0)"
    );
}

/// UF+NIA: a branch refuted through an EUF shared equality the LRA holds as
/// a row. `x ∈ [0, 1]`, `x*y >= 5`, `u <= 2`, shared `y = u` (reason `r`,
/// never asserted to the NIA). Branch `x = 0`: `x*y = 0 >= 5` fails; branch
/// `x = 1`: `y >= 5`, `y = u <= 2` fails through the shared row, so the LRA
/// conflict cites `r`. The split's union must be kept (it is a theorem) and
/// must name `r`; before `is_live_premise` the union was dropped for the full
/// set because `r` is not an asserted literal. An unrelated shared equality
/// `s = t` (reason `r2`) tells the two apart: the full set names `r2`, the
/// union does not.
#[test]
fn factor_split_union_keeps_the_shared_reason_its_branch_cited() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let u = terms.mk_var("u", Sort::Int);
    let r = terms.mk_var("y_eq_u", Sort::Bool);
    let s_var = terms.mk_var("s", Sort::Int);
    let t_var = terms.mk_var("t", Sort::Int);
    let r2 = terms.mk_var("s_eq_t", Sort::Bool);
    let zero = int(&mut terms, 0);
    let one = int(&mut terms, 1);
    let two = int(&mut terms, 2);
    let five = int(&mut terms, 5);
    let xy = terms.mk_mul(vec![x, y]);
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_1 = terms.mk_le(x, one);
    let xy_ge_5 = terms.mk_ge(xy, five);
    let u_le_2 = terms.mk_le(u, two);
    let atoms = [x_ge_0, x_le_1, xy_ge_5, u_le_2];
    let reason = TheoryLit::new(r, true);

    let mut solver = NiaSolver::new(&terms);
    for &atom in &atoms {
        solver.assert_literal(atom, true);
    }
    solver.assert_shared_equality(y, u, &[reason]);
    let unrelated = TheoryLit::new(r2, true);
    solver.assert_shared_equality(s_var, t_var, &[unrelated]);
    let result = solver.try_bounded_factor_split();
    let Some(TheoryResult::Unsat(lits)) = result else {
        panic!("both branches of x ∈ [0, 1] are refuted: {result:?}");
    };
    assert!(
        lits.contains(&reason),
        "branch x = 1 is refuted through the shared row y = u; the conflict {lits:?} must \
         name its reason"
    );
    assert!(
        !lits.contains(&unrelated),
        "the conflict {lits:?} names the reason of the unrelated shared equality s = t: the \
         split fell back to the full set instead of keeping its union"
    );
    for lit in &lits {
        assert!(
            atoms.contains(&lit.term) || *lit == reason,
            "the conflict names a literal that is neither asserted nor a shared reason: {lit:?}"
        );
    }
}

/// The divisor split aggregates its branches the same way: `x*y = 6` (cover:
/// `x ∈ ±{1, 2, 3, 6}`), `x + z = 10` derives `z = 10 - x > 0` in every
/// branch, and `z*w >= 100 ∧ w <= 1` then fails (`z*w <= z <= 16`). Without
/// `x + z = 10` the named atoms are satisfiable (`x = 1, y = 6, z = 100,
/// w = 1`), so the conflict must name it.
#[test]
fn divisor_split_conflict_names_the_atom_that_derived_a_pin() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let one = int(&mut terms, 1);
    let six = int(&mut terms, 6);
    let ten = int(&mut terms, 10);
    let hundred = int(&mut terms, 100);
    let xy = terms.mk_mul(vec![x, y]);
    let zw = terms.mk_mul(vec![z, w]);
    let x_plus_z = terms.mk_add(vec![x, z]);
    let xy_eq_6 = terms.mk_eq(xy, six);
    let x_plus_z_eq_10 = terms.mk_eq(x_plus_z, ten);
    let zw_ge_100 = terms.mk_ge(zw, hundred);
    let w_le_1 = terms.mk_le(w, one);

    let mut solver = NiaSolver::new(&terms);
    for atom in [xy_eq_6, x_plus_z_eq_10, zw_ge_100, w_le_1] {
        solver.assert_literal(atom, true);
    }
    let result = solver.try_divisor_split();
    eprintln!("divisor split result: {result:?}");
    let Some(TheoryResult::Unsat(lits)) = result else {
        // No refutation: nothing unsound was claimed.
        return;
    };
    assert!(
        lits.contains(&TheoryLit::new(x_plus_z_eq_10, true)),
        "every divisor branch was refuted through the pin `x + z = 10` derived, but the \
         conflict {lits:?} does not name that atom"
    );
    assert!(
        lits.contains(&TheoryLit::new(xy_eq_6, true)),
        "the cover's premise `x*y = 6` must be named: {lits:?}"
    );
}
