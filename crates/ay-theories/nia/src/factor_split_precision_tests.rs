// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Precision of the factor split's conflict beyond the per-fact provenance
//! of `factor_split_premise_provenance_tests.rs`: a derived fact the
//! refutation did not use is not named (the premise-free first layer), and
//! a linked congruence equality forces the full set only when the branch
//! TABLEAU refuted a branch (#nia-factor-split-congruence-scope).

use super::*;
use num_bigint::BigInt;

fn int(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_int(BigInt::from(n))
}

/// `x ∈ [0, 1]` (the cover, a factor of `x*z`), `y = x + 1` derives `y` in
/// every branch (its pin cut rests on that atom), and `x*z >= 5 ∧ z <= 2`
/// fails on the case pin alone: `x = 0` by contraction (`0 >= 5`), `x = 1`
/// in the LRA (`x*z = z <= 2`) before `y`'s pin cut goes in (the
/// premise-free first layer). The split conflict must not name `y = x + 1`
/// — a single-layer branch named the premises of every cut it installed —
/// nor the unrelated `u >= 7`, and it must name what the refutations used.
#[test]
fn factor_split_names_only_the_derived_facts_its_refutation_needs() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let u = terms.mk_var("u", Sort::Int);
    let zero = int(&mut terms, 0);
    let one = int(&mut terms, 1);
    let two = int(&mut terms, 2);
    let five = int(&mut terms, 5);
    let seven = int(&mut terms, 7);
    let x_plus_1 = terms.mk_add(vec![x, one]);
    let xz = terms.mk_mul(vec![x, z]);
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_1 = terms.mk_le(x, one);
    let y_eq = terms.mk_eq(y, x_plus_1);
    let xz_ge_5 = terms.mk_ge(xz, five);
    let z_le_2 = terms.mk_le(z, two);
    let u_ge_7 = terms.mk_ge(u, seven);

    let mut solver = NiaSolver::new(&terms);
    for atom in [x_ge_0, x_le_1, y_eq, xz_ge_5, z_le_2, u_ge_7] {
        solver.assert_literal(atom, true);
    }
    let result = solver.try_bounded_factor_split();
    eprintln!("factor split result: {result:?}");
    let Some(TheoryResult::Unsat(lits)) = result else {
        panic!("both branches of x ∈ [0, 1] are refuted by x*z >= 5 ∧ z <= 2: {result:?}");
    };
    assert!(
        !lits.contains(&TheoryLit::new(u_ge_7, true)),
        "the conflict {lits:?} names the unrelated `u >= 7`: the split fell back to the full set"
    );
    assert!(
        !lits.contains(&TheoryLit::new(y_eq, true)),
        "no refutation used y's pin, yet the conflict {lits:?} names `y = x + 1`"
    );
    for (atom, what) in [(xz_ge_5, "`x*z >= 5`"), (z_le_2, "`z <= 2`")] {
        assert!(
            lits.contains(&TheoryLit::new(atom, true)),
            "the conflict {lits:?} must name {what}, which the refutations used"
        );
    }
}

/// #nia-factor-split-congruence-scope: a linked congruence equality cannot
/// have been used by a branch the linearized-atom contraction refuted — the
/// contraction reads the asserted atoms alone — so it does not force the
/// split's conflict back to the full set. `x ∈ [0, 1]` (the cover),
/// `y = x + 2` derives `y`, and `x*y >= 5` is ground-false in both branches
/// (`0 >= 5`, `3 >= 5`). `y = w` links `x*y` and `x*w` (a congruence
/// equality in the inner LIA). The conflict must name the cover, `x*y >= 5`
/// and `y = x + 2`, and neither `y = w` nor the unrelated `u >= 7` (before
/// the change: every asserted literal, because a congruence was linked).
#[test]
fn factor_split_contraction_refutations_ignore_linked_congruences() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let u = terms.mk_var("u", Sort::Int);
    let zero = int(&mut terms, 0);
    let one = int(&mut terms, 1);
    let two = int(&mut terms, 2);
    let five = int(&mut terms, 5);
    let seven = int(&mut terms, 7);
    let x_plus_2 = terms.mk_add(vec![x, two]);
    let xy = terms.mk_mul(vec![x, y]);
    let xw = terms.mk_mul(vec![x, w]);
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_1 = terms.mk_le(x, one);
    let y_eq = terms.mk_eq(y, x_plus_2);
    let y_eq_w = terms.mk_eq(y, w);
    let xy_ge_5 = terms.mk_ge(xy, five);
    let xw_ge_0 = terms.mk_ge(xw, zero);
    let u_ge_7 = terms.mk_ge(u, seven);

    let mut solver = NiaSolver::new(&terms);
    for atom in [x_ge_0, x_le_1, y_eq, y_eq_w, xy_ge_5, xw_ge_0, u_ge_7] {
        solver.assert_literal(atom, true);
    }
    assert!(
        solver.add_monomial_congruence_lemmas() > 0,
        "`y = w` must link x*y and x*w"
    );
    let result = solver.try_bounded_factor_split();
    eprintln!("factor split result: {result:?}");
    let Some(TheoryResult::Unsat(lits)) = result else {
        panic!("both branches of x ∈ [0, 1] make `x*y >= 5` ground-false: {result:?}");
    };
    for (atom, what) in [(u_ge_7, "the unrelated `u >= 7`"), (y_eq_w, "`y = w`")] {
        assert!(
            !lits.contains(&TheoryLit::new(atom, true)),
            "the conflict {lits:?} names {what}: the split fell back to the full set"
        );
    }
    for (atom, what) in [(xy_ge_5, "`x*y >= 5`"), (y_eq, "`y = x + 2`")] {
        assert!(
            lits.contains(&TheoryLit::new(atom, true)),
            "the conflict {lits:?} must name {what}"
        );
    }
}

/// #nia-factor-split-congruence-scope, the other side: with a congruence
/// linked, a branch the LRA refuted may have used the congruence row, whose
/// premises an LRA conflict does not cite, so the split still answers with
/// the full set. `x ∈ [0, 1]`, `x*z >= 5 ∧ z <= 2`: `x = 0` falls to the
/// contraction, `x = 1` only to the LRA (`x*z = z <= 2`). `y = w` links
/// `x*y` and `x*w`. The conflict names every asserted literal, the
/// unrelated `u >= 7` included.
#[test]
fn factor_split_tableau_refutation_with_linked_congruence_keeps_the_full_set() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let u = terms.mk_var("u", Sort::Int);
    let zero = int(&mut terms, 0);
    let one = int(&mut terms, 1);
    let two = int(&mut terms, 2);
    let five = int(&mut terms, 5);
    let seven = int(&mut terms, 7);
    let xy = terms.mk_mul(vec![x, y]);
    let xw = terms.mk_mul(vec![x, w]);
    let xz = terms.mk_mul(vec![x, z]);
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_1 = terms.mk_le(x, one);
    let y_eq_w = terms.mk_eq(y, w);
    let xy_ge_0 = terms.mk_ge(xy, zero);
    let xw_ge_0 = terms.mk_ge(xw, zero);
    let xz_ge_5 = terms.mk_ge(xz, five);
    let z_le_2 = terms.mk_le(z, two);
    let u_ge_7 = terms.mk_ge(u, seven);

    let mut solver = NiaSolver::new(&terms);
    for atom in [
        x_ge_0, x_le_1, y_eq_w, xy_ge_0, xw_ge_0, xz_ge_5, z_le_2, u_ge_7,
    ] {
        solver.assert_literal(atom, true);
    }
    assert!(
        solver.add_monomial_congruence_lemmas() > 0,
        "`y = w` must link x*y and x*w"
    );
    let result = solver.try_bounded_factor_split();
    eprintln!("factor split result: {result:?}");
    let Some(TheoryResult::Unsat(lits)) = result else {
        panic!("both branches of x ∈ [0, 1] are refuted by x*z >= 5 ∧ z <= 2: {result:?}");
    };
    assert!(
        lits.contains(&TheoryLit::new(u_ge_7, true)),
        "an LRA-refuted branch with a linked congruence must fall back to the full set; \
         the conflict {lits:?} does not name `u >= 7`"
    );
}
