// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #nia-factor-split-provenance: a factor-split conflict names exactly the
//! asserted atoms its branch refutations rest on — every one of them (the
//! wrong answers of mechanism 3 come back otherwise) and nothing else (the
//! landing's "every asserted literal" cost ~40 corpus `sat` verdicts).
//!
//! Every test here asserts an UNRELATED asserted atom is not named, so a pass
//! cannot come from the full-set fallback: a refutation reached before any
//! derived fact mattered (the premise-free layer's rows, or the priming
//! check's full set) pins nothing about provenance. Each soundness hunk of
//! `factor_split_provenance.rs` / the branch explanation has a mutant these
//! tests catch (see the campaign report 2026-09-26-nia-precision, §5).

use super::factor_split_provenance::{BranchPremises, Premises};
use super::*;
use num_bigint::BigInt;

fn int(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_int(BigInt::from(n))
}

/// #nia-factor-split-provenance: a derived pin rests on the atom it came from
/// AND on the premises of every value substituted into that atom. Two hops:
/// `x ∈ [0, 1]` (the cover), `y = x + 1` derives `y`, `q = 10 - y` derives `q`
/// FROM `y`, and `q*c >= 20 ∧ c <= 1` then fails (`q*c <= q <= 9`). Without
/// `y = x + 1` the named atoms are satisfiable (`x = 0, y = -10, q = 20,
/// c = 1`), so a conflict that names only the atom that pinned `q` is not a
/// theorem. An unrelated asserted atom (`u >= 7`) is no premise of anything:
/// the conflict must not name it (the landing's explanation named every
/// asserted literal).
#[test]
fn factor_split_premises_are_transitive_and_name_nothing_else() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let q = terms.mk_var("q", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let e = terms.mk_var("e", Sort::Int);
    let u = terms.mk_var("u", Sort::Int);
    let zero = int(&mut terms, 0);
    let one = int(&mut terms, 1);
    let seven = int(&mut terms, 7);
    let ten = int(&mut terms, 10);
    let twenty = int(&mut terms, 20);
    let x_plus_1 = terms.mk_add(vec![x, one]);
    let ten_minus_y = terms.mk_sub(vec![ten, y]);
    let qc = terms.mk_mul(vec![q, c]);
    let xe = terms.mk_mul(vec![x, e]);
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_1 = terms.mk_le(x, one);
    let y_eq = terms.mk_eq(y, x_plus_1);
    let q_eq = terms.mk_eq(q, ten_minus_y);
    let qc_ge_20 = terms.mk_ge(qc, twenty);
    let c_le_1 = terms.mk_le(c, one);
    let xe_ge_0 = terms.mk_ge(xe, zero);
    let u_ge_7 = terms.mk_ge(u, seven);

    let mut solver = NiaSolver::new(&terms);
    for atom in [
        x_ge_0, x_le_1, y_eq, q_eq, qc_ge_20, c_le_1, xe_ge_0, u_ge_7,
    ] {
        solver.assert_literal(atom, true);
    }
    let result = solver.try_bounded_factor_split();
    eprintln!("factor split result: {result:?}");
    let Some(TheoryResult::Unsat(lits)) = result else {
        panic!("every branch of x ∈ [0, 1] is refuted through the derived pins: {result:?}");
    };
    assert!(
        lits.contains(&TheoryLit::new(q_eq, true)),
        "`q = 10 - y` pinned q; the conflict {lits:?} must name it"
    );
    assert!(
        lits.contains(&TheoryLit::new(y_eq, true)),
        "`q`'s pin was derived from `y`'s, which `y = x + 1` derived; the conflict {lits:?} \
         must name that atom too (without it: x = 0, y = -10, q = 20, c = 1)"
    );
    assert!(
        !lits.contains(&TheoryLit::new(u_ge_7, true)),
        "`u >= 7` is no premise of any branch refutation, but the conflict {lits:?} names it: \
         the explanation fell back to every asserted literal"
    );
}

/// #nia-factor-split-provenance: a monotonicity cut `b*c <= g*c` rests on the
/// ordering atom `b <= g` it was derived from and on what makes the shared
/// factor `c` non-negative — the asserted sign atom `c >= 0`. Shape: `a ∈
/// [0, 1]` (the cover, a factor of `a*e`; `c ∈ [0, 100]` is too wide to
/// split), `b*c >= 30`, `g*c <= 20`: every branch is refuted by
/// `30 <= b*c <= g*c <= 20`, and only through the cut (the LRA sees `b*c` and
/// `g*c` as unrelated columns). Without `c >= 0` the named atoms are
/// satisfiable (`b = -30, c = -1, g = 0`), and without `b <= g` too (`b = 30,
/// c = 1, g = 0`). `u >= 5` is named by nothing.
#[test]
fn factor_split_monotone_cut_names_its_ordering_and_sign_atoms() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let g = terms.mk_var("g", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let e = terms.mk_var("e", Sort::Int);
    let u = terms.mk_var("u", Sort::Int);
    let zero = int(&mut terms, 0);
    let one = int(&mut terms, 1);
    let five = int(&mut terms, 5);
    let twenty = int(&mut terms, 20);
    let thirty = int(&mut terms, 30);
    let hundred = int(&mut terms, 100);
    let bc = terms.mk_mul(vec![b, c]);
    let gc = terms.mk_mul(vec![g, c]);
    let ae = terms.mk_mul(vec![a, e]);
    let a_ge_0 = terms.mk_ge(a, zero);
    let a_le_1 = terms.mk_le(a, one);
    let b_le_g = terms.mk_le(b, g);
    let c_ge_0 = terms.mk_ge(c, zero);
    let c_le_100 = terms.mk_le(c, hundred);
    let bc_ge_30 = terms.mk_ge(bc, thirty);
    let gc_le_20 = terms.mk_le(gc, twenty);
    let ae_ge_0 = terms.mk_ge(ae, zero);
    let u_ge_5 = terms.mk_ge(u, five);

    let mut solver = NiaSolver::new(&terms);
    for atom in [
        a_ge_0, a_le_1, b_le_g, c_ge_0, c_le_100, bc_ge_30, gc_le_20, ae_ge_0, u_ge_5,
    ] {
        solver.assert_literal(atom, true);
    }
    let result = solver.try_bounded_factor_split();
    eprintln!("factor split result: {result:?}");
    let Some(TheoryResult::Unsat(lits)) = result else {
        panic!("every branch is refuted through the monotonicity cut b*c <= g*c: {result:?}");
    };
    assert!(
        lits.contains(&TheoryLit::new(c_ge_0, true)),
        "the monotonicity cut b*c <= g*c needs c >= 0; the conflict {lits:?} must name it \
         (without it: b = -30, c = -1, g = 0)"
    );
    assert!(
        lits.contains(&TheoryLit::new(b_le_g, true)),
        "the monotonicity cut rests on the ordering b <= g; the conflict {lits:?} must name it"
    );
    assert!(
        !lits.contains(&TheoryLit::new(u_ge_5, true)),
        "`u >= 5` is no premise, but the conflict {lits:?} names it"
    );
}

/// #nia-factor-split-provenance: a GROUND refutation by a linearized atom
/// (no LRA involved: the relaxation leaves `q*q` free) names the atom and,
/// transitively, every atom the substituted values came from. `x ∈ [0, 1]`
/// (the cover), `y = x + 1` pins `y`, `q = 10 - y` pins `q` from `y`, and
/// `q*q >= 100` is then ground-false (`q ∈ {9, 8}`). Without `y = x + 1` the
/// named atoms are satisfiable (`x = 0, y = 0, q = 10`), and without
/// `q = 10 - y` too. `u >= 7` is no premise: naming it means the split fell
/// back to the full set.
#[test]
fn factor_split_two_hop_ground_refutation_names_every_hop() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let q = terms.mk_var("q", Sort::Int);
    let e = terms.mk_var("e", Sort::Int);
    let u = terms.mk_var("u", Sort::Int);
    let zero = int(&mut terms, 0);
    let one = int(&mut terms, 1);
    let seven = int(&mut terms, 7);
    let ten = int(&mut terms, 10);
    let hundred = int(&mut terms, 100);
    let x_plus_1 = terms.mk_add(vec![x, one]);
    let ten_minus_y = terms.mk_sub(vec![ten, y]);
    let qq = terms.mk_mul(vec![q, q]);
    let xe = terms.mk_mul(vec![x, e]);
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_1 = terms.mk_le(x, one);
    let y_eq = terms.mk_eq(y, x_plus_1);
    let q_eq = terms.mk_eq(q, ten_minus_y);
    let qq_ge_100 = terms.mk_ge(qq, hundred);
    let xe_ge_0 = terms.mk_ge(xe, zero);
    let u_ge_7 = terms.mk_ge(u, seven);

    let mut solver = NiaSolver::new(&terms);
    for atom in [x_ge_0, x_le_1, y_eq, q_eq, qq_ge_100, xe_ge_0, u_ge_7] {
        solver.assert_literal(atom, true);
    }
    let result = solver.try_bounded_factor_split();
    eprintln!("factor split result: {result:?}");
    let Some(TheoryResult::Unsat(lits)) = result else {
        panic!("both branches make `q*q >= 100` ground-false: {result:?}");
    };
    assert!(
        !lits.contains(&TheoryLit::new(u_ge_7, true)),
        "the conflict {lits:?} names the unrelated `u >= 7`: the split fell back to the full set"
    );
    for (atom, what) in [
        (qq_ge_100, "the refuting atom `q*q >= 100`"),
        (q_eq, "`q = 10 - y`, which pinned q"),
        (
            y_eq,
            "`y = x + 1`, which pinned the y that q's pin was derived from",
        ),
    ] {
        assert!(
            lits.contains(&TheoryLit::new(atom, true)),
            "the conflict {lits:?} must name {what}"
        );
    }
}

/// #nia-factor-split-provenance: a derived pin the round-0 FIRST layer must
/// not see, and the premises it rests on. `x ∈ [0, 1]` (the cover), `x + y =
/// 3` pins `y`, `y*v = 6` then pins `v` (`v = 6 / y`: only once `y` is fixed,
/// the relaxation cannot see through the product), and `v + w*w >= 10 ∧ w*w
/// <= 1` fails because `v <= 3` (the contraction cannot refute it: the atom
/// keeps the unknown `w*w`, so only the LRA does, through `v`'s derived pin).
/// The case pins alone leave the branch feasible, so the refutation needs the
/// derived facts and must name `y*v = 6` and `x + y = 3` (without `y*v = 6`:
/// `x = 0, y = 3, v = 9, w = 1`). `u >= 7` is no premise of anything: a
/// conflict naming it fell back to the full set, which proves nothing here.
#[test]
fn factor_split_derived_pin_refutation_names_its_derivation() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let e = terms.mk_var("e", Sort::Int);
    let u = terms.mk_var("u", Sort::Int);
    let zero = int(&mut terms, 0);
    let one = int(&mut terms, 1);
    let three = int(&mut terms, 3);
    let six = int(&mut terms, 6);
    let seven = int(&mut terms, 7);
    let ten = int(&mut terms, 10);
    let x_plus_y = terms.mk_add(vec![x, y]);
    let yv = terms.mk_mul(vec![y, v]);
    let ww = terms.mk_mul(vec![w, w]);
    let xe = terms.mk_mul(vec![x, e]);
    let v_plus_ww = terms.mk_add(vec![v, ww]);
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_1 = terms.mk_le(x, one);
    let x_plus_y_eq_3 = terms.mk_eq(x_plus_y, three);
    let yv_eq_6 = terms.mk_eq(yv, six);
    let xe_ge_0 = terms.mk_ge(xe, zero);
    let v_plus_ww_ge_10 = terms.mk_ge(v_plus_ww, ten);
    let ww_le_1 = terms.mk_le(ww, one);
    let u_ge_7 = terms.mk_ge(u, seven);

    let mut solver = NiaSolver::new(&terms);
    for atom in [
        x_ge_0,
        x_le_1,
        x_plus_y_eq_3,
        yv_eq_6,
        xe_ge_0,
        v_plus_ww_ge_10,
        ww_le_1,
        u_ge_7,
    ] {
        solver.assert_literal(atom, true);
    }
    let result = solver.try_bounded_factor_split();
    eprintln!("factor split result: {result:?}");
    let Some(TheoryResult::Unsat(lits)) = result else {
        panic!("both branches are refuted through v's derived pin: {result:?}");
    };
    assert!(
        !lits.contains(&TheoryLit::new(u_ge_7, true)),
        "the conflict {lits:?} names the unrelated `u >= 7`: the split fell back to the full set"
    );
    assert!(
        lits.contains(&TheoryLit::new(yv_eq_6, true)),
        "v's pin was derived from `y*v = 6`; the conflict {lits:?} must name it \
         (without it: x = 0, y = 3, v = 9, w = 1)"
    );
    assert!(
        lits.contains(&TheoryLit::new(x_plus_y_eq_3, true)),
        "y's pin, which v's rests on, was derived from `x + y = 3`: {lits:?}"
    );
}

/// #nia-factor-split-provenance: a derived pin whose ONLY way into the LRA
/// is its own pin cut. As `factor_split_derived_pin_refutation_names_its_
/// derivation`, but `v` comes from the SCALED product `2*y*v = 12`: scaled
/// products are not registered monomials, so no linearization ties the
/// product's column to `v` and the relaxation cannot re-derive `v` from the
/// atom's row — the refutation uses `v`'s pin cut, whose premises (`2*y*v =
/// 12` and, through `y`, `x + y = 3`) the explanation must name. The premise-
/// free first layer must not contain that pin: with it, the layer refutes
/// and names neither atom.
#[test]
fn factor_split_scaled_product_pin_cut_names_its_derivation() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let e = terms.mk_var("e", Sort::Int);
    let u = terms.mk_var("u", Sort::Int);
    let zero = int(&mut terms, 0);
    let one = int(&mut terms, 1);
    let two = int(&mut terms, 2);
    let three = int(&mut terms, 3);
    let seven = int(&mut terms, 7);
    let ten = int(&mut terms, 10);
    let twelve = int(&mut terms, 12);
    let x_plus_y = terms.mk_add(vec![x, y]);
    let two_yv = terms.mk_mul(vec![two, y, v]);
    let ww = terms.mk_mul(vec![w, w]);
    let xe = terms.mk_mul(vec![x, e]);
    let v_plus_ww = terms.mk_add(vec![v, ww]);
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_1 = terms.mk_le(x, one);
    let x_plus_y_eq_3 = terms.mk_eq(x_plus_y, three);
    let two_yv_eq_12 = terms.mk_eq(two_yv, twelve);
    let xe_ge_0 = terms.mk_ge(xe, zero);
    let v_plus_ww_ge_10 = terms.mk_ge(v_plus_ww, ten);
    let ww_le_1 = terms.mk_le(ww, one);
    let u_ge_7 = terms.mk_ge(u, seven);

    let mut solver = NiaSolver::new(&terms);
    for atom in [
        x_ge_0,
        x_le_1,
        x_plus_y_eq_3,
        two_yv_eq_12,
        xe_ge_0,
        v_plus_ww_ge_10,
        ww_le_1,
        u_ge_7,
    ] {
        solver.assert_literal(atom, true);
    }
    let result = solver.try_bounded_factor_split();
    eprintln!("factor split result: {result:?}");
    let Some(TheoryResult::Unsat(lits)) = result else {
        panic!("both branches are refuted through v's pin cut: {result:?}");
    };
    assert!(
        !lits.contains(&TheoryLit::new(u_ge_7, true)),
        "the conflict {lits:?} names the unrelated `u >= 7`: the split fell back to the full set"
    );
    assert!(
        lits.contains(&TheoryLit::new(two_yv_eq_12, true)),
        "v's pin was derived from `2*y*v = 12`; the conflict {lits:?} must name it"
    );
    assert!(
        lits.contains(&TheoryLit::new(x_plus_y_eq_3, true)),
        "y's pin, which v's rests on, was derived from `x + y = 3`: {lits:?}"
    );
}

/// Premise identities are Vec indices, not TermIds. Repeated assertions can
/// make an index wider than u32 even when the term store remains small.
#[cfg(target_pointer_width = "64")]
#[test]
fn premise_positions_above_u32_do_not_alias_earlier_assertions() {
    let high = u32::MAX as usize + 1;
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let atom = terms.mk_ge(x, zero);

    let mut provenance = BranchPremises::default();
    provenance.pins.insert(x, Premises(vec![high + 1]));
    let derived = provenance.derivation(high, &[x]);
    assert_eq!(derived.0, vec![high, high + 1]);
    let mut cuts = Premises(vec![high + 1]);
    cuts.union(&derived);
    assert_eq!(cuts.0, vec![high, high + 1]);

    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(atom, true);
    assert_eq!(
        solver.asserted_lits_at(&[0]),
        Some(vec![TheoryLit::new(atom, true)])
    );
    assert!(
        solver.asserted_lits_at(&[high]).is_none(),
        "a high out-of-range position must fail closed, not alias assertion 0"
    );
}
