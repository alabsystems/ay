// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #nia-sign-cut-soundness: an UNSAT never rests on a model guess.
//!
//! `inject_tentative_sign_cuts` asserts `x >= 0` / `x <= 0` from the CURRENT
//! LRA model value, and `try_integer_rounding` / `try_tentative_patch` pin
//! `x = round(model(x))`, all as bounds whose reason is the variable term. On
//! main `b1c1f8f201` the LIA's side checks read those bounds as facts and the
//! loop published the resulting UNSAT as genuine ("Only exact lemmas were
//! used") on 18 satisfiable QF_NIA problems
//! (`benchmarks/smt/wrong-verdict/sat_nia_sign_cut_{1,2,3,4}.smt2` and the
//! attack corpus `~/ay-bench/signcut/`). These tests replay the witnesses at
//! the theory-solver level, force a crafted `x*y = -k` shape through the path
//! with the guesses injected by hand, and pin the guess bookkeeping the
//! debug-build audit relies on. The executor-level pins live in
//! `ay-dpll/tests/group_regression/nia_sign_cut_wrong_unsat.rs`.

use super::*;
use ay_lra::GomoryCut;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::One;

fn int(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_int(BigInt::from(n))
}

fn is_unsat(result: &TheoryResult) -> bool {
    matches!(
        result,
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
    )
}

/// `sat_nia_sign_cut_1`: `2x = y ∧ 3z = y + 1 ∧ -2000 <= y <= 1 ∧ 1 <= x*z
/// <= 400`, z3 model x = -23, y = -46, z = -15. Main: the LIA's direct
/// enumeration answers Sat with a stale fractional LRA point (x = 0,
/// z = 1/3), the loop guesses `z >= 0` and pins `z = 0`, and
/// `check_modular_for_var` refutes `z ≡ 1 (mod 2)` on `z in [0, 0]`.
#[test]
fn witness_1_two_x_eq_y_three_z_eq_y_plus_1_is_not_refuted() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let two = int(&mut terms, 2);
    let three = int(&mut terms, 3);
    let one = int(&mut terms, 1);
    let m2000 = int(&mut terms, -2000);
    let c400 = int(&mut terms, 400);
    let two_x = terms.mk_mul(vec![two, x]);
    let three_z = terms.mk_mul(vec![three, z]);
    let y_plus_1 = terms.mk_add(vec![y, one]);
    let xz = terms.mk_mul(vec![x, z]);
    let atoms = [
        terms.mk_eq(two_x, y),
        terms.mk_eq(three_z, y_plus_1),
        terms.mk_ge(y, m2000),
        terms.mk_le(y, one),
        terms.mk_ge(xz, one),
        terms.mk_le(xz, c400),
    ];
    let mut solver = NiaSolver::new(&terms);
    for atom in atoms {
        solver.assert_literal(atom, true);
    }
    let result = solver.check();
    assert!(
        !is_unsat(&result),
        "satisfiable (x=-23, y=-46, z=-15) — a sign guess / pin made it UNSAT on main: {result:?}"
    );
}

/// `sat_nia_sign_cut_2`: `3w = z + 1 ∧ 2x + z = -9 ∧ -2000 <= z <= 1 ∧
/// 1 <= x*z <= 400`, z3 model x = -1, w = -2, z = -7. Main: stale point
/// x = -9/2, z = 0; guess `x <= 0`, pin `x = -5`; `x ≡ 2 (mod 3)` refuted on
/// `x in [-5, -5]`.
#[test]
fn witness_2_three_w_eq_z_plus_1_is_not_refuted() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let two = int(&mut terms, 2);
    let three = int(&mut terms, 3);
    let one = int(&mut terms, 1);
    let m9 = int(&mut terms, -9);
    let m2000 = int(&mut terms, -2000);
    let c400 = int(&mut terms, 400);
    let three_w = terms.mk_mul(vec![three, w]);
    let z_plus_1 = terms.mk_add(vec![z, one]);
    let two_x = terms.mk_mul(vec![two, x]);
    let two_x_plus_z = terms.mk_add(vec![two_x, z]);
    let xz = terms.mk_mul(vec![x, z]);
    let atoms = [
        terms.mk_eq(three_w, z_plus_1),
        terms.mk_eq(two_x_plus_z, m9),
        terms.mk_le(z, one),
        terms.mk_ge(z, m2000),
        terms.mk_ge(xz, one),
        terms.mk_le(xz, c400),
    ];
    let mut solver = NiaSolver::new(&terms);
    for atom in atoms {
        solver.assert_literal(atom, true);
    }
    let result = solver.check();
    assert!(
        !is_unsat(&result),
        "satisfiable (x=-1, w=-2, z=-7) — a sign guess / pin made it UNSAT on main: {result:?}"
    );
}

/// `sat_nia_sign_cut_3` / e9: `3w = z + 1 ∧ 5x - 2z = 45 ∧ x <= 1 ∧ x >= -1000
/// ∧ 1 <= x*z <= 400`, z3 model w = -13, x = -7, z = -40. Main: contradictory
/// sign guesses `x >= 0` then `x <= 0` accumulated in ONE tentative scope
/// pinned `x = 0` by guesses alone, and `x ≡ 5 (mod 6)` was refuted on it.
#[test]
fn witness_3_contradictory_sign_guesses_do_not_refute() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let two = int(&mut terms, 2);
    let three = int(&mut terms, 3);
    let five = int(&mut terms, 5);
    let one = int(&mut terms, 1);
    let c45 = int(&mut terms, 45);
    let m1000 = int(&mut terms, -1000);
    let c400 = int(&mut terms, 400);
    let three_w = terms.mk_mul(vec![three, w]);
    let z_plus_1 = terms.mk_add(vec![z, one]);
    let five_x = terms.mk_mul(vec![five, x]);
    let two_z = terms.mk_mul(vec![two, z]);
    let five_x_minus_two_z = terms.mk_sub(vec![five_x, two_z]);
    let xz = terms.mk_mul(vec![x, z]);
    let atoms = [
        terms.mk_eq(three_w, z_plus_1),
        terms.mk_eq(five_x_minus_two_z, c45),
        terms.mk_le(x, one),
        terms.mk_ge(x, m1000),
        terms.mk_ge(xz, one),
        terms.mk_le(xz, c400),
    ];
    let mut solver = NiaSolver::new(&terms);
    for atom in atoms {
        solver.assert_literal(atom, true);
    }
    let result = solver.check();
    assert!(
        !is_unsat(&result),
        "satisfiable (w=-13, x=-7, z=-40) — sign guesses made it UNSAT on main: {result:?}"
    );
}

/// A crafted `x*y = -k` shape FORCED through the path: `x*y = -2 ∧ 3x + y =
/// 1 ∧ -100 <= y <= 1` (solution x = 1, y = -2). The guesses a positive
/// starting model would produce — sign cut `y >= 0` and rounding pin `y = 0`
/// — are injected by hand, exactly as `inject_tentative_sign_cuts` and
/// `apply_patch` inject them (reason = the variable term, tentative scope
/// open, guess count bumped). With `y in [0, 0]` and `y ≡ 1 (mod 3)` the
/// inner LIA is "UNSAT" on main. The loop must not publish that: the LIA
/// ignores the unjustified bounds (and in debug builds the loop audits any
/// LIA UNSAT observed with guesses in force by re-deriving it without them).
#[test]
fn crafted_xy_eq_minus_k_with_hand_injected_guesses_is_not_refuted() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let one = int(&mut terms, 1);
    let three = int(&mut terms, 3);
    let m2 = int(&mut terms, -2);
    let m100 = int(&mut terms, -100);
    let xy = terms.mk_mul(vec![x, y]);
    let three_x = terms.mk_mul(vec![three, x]);
    let lhs = terms.mk_add(vec![three_x, y]);
    let atoms = [
        terms.mk_eq(xy, m2),
        terms.mk_eq(lhs, one),
        terms.mk_le(y, one),
        terms.mk_ge(y, m100),
    ];
    let mut solver = NiaSolver::new(&terms);
    for atom in atoms {
        solver.assert_literal(atom, true);
    }
    // Prime the LIA (the loop's iteration 0 would do this).
    let primed = solver.lia.check();
    assert!(!is_unsat(&primed), "{primed:?}");

    // Open the tentative scope and inject the guesses of a positive model.
    solver.lia.push();
    solver.tentative_depth += 1;
    let y_var = solver.lia.lra_solver_mut().ensure_var_registered(y);
    for is_lower in [true, false] {
        solver.lia.lra_solver_mut().add_gomory_cut(
            &GomoryCut {
                coeffs: vec![(y_var, BigRational::one())],
                bound: BigRational::from_integer(BigInt::from(0)),
                is_lower,
                reasons: Vec::new(),
                source_term: None,
            },
            y,
        );
    }
    solver.tentative_guess_count += 2;

    // The LIA itself must not refute from the guesses ...
    let lia = solver.lia.check();
    assert!(
        !is_unsat(&lia),
        "the LIA refuted from a model guess (y pinned to 0 by a non-atom reason): {lia:?}"
    );
    // ... and the loop, entered with the guesses in force, must not either.
    let looped = solver.nia_check_loop();
    assert!(
        !is_unsat(&looped),
        "the NIA loop published an UNSAT resting on a model guess: {looped:?}"
    );
    // Whatever it returned, no guess is left in force afterwards unless the
    // result is a verified-later Sat with its scope intentionally kept.
    if !matches!(looped, TheoryResult::Sat) {
        assert_eq!(
            solver.tentative_guess_count, 0,
            "a non-Sat return leaves no guess in force"
        );
    }
}

/// `undo_tentative_patch` forgets every guess with the scopes it pops, and
/// the injector counts each sign cut it asserts (the debug-build audit in
/// the check loop keys on that count).
#[test]
fn guess_bookkeeping_follows_the_tentative_scopes() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let one = int(&mut terms, 1);
    let xy = terms.mk_mul(vec![x, y]);
    let atom = terms.mk_ge(xy, one);
    let mut solver = NiaSolver::new(&terms);
    solver.assert_literal(atom, true);
    let _ = solver.lia.check();

    solver.lia.push();
    solver.tentative_depth += 1;
    solver.tentative_guess_count = 3;
    solver.undo_tentative_patch();
    assert_eq!(solver.tentative_depth, 0);
    assert_eq!(solver.tentative_guess_count, 0);

    // Every sign cut the injector asserts is counted.
    solver.lia.push();
    solver.tentative_depth += 1;
    let injected = solver.inject_tentative_sign_cuts();
    assert_eq!(
        solver.tentative_guess_count as usize, injected,
        "each injected sign cut is one counted guess"
    );
    solver.undo_tentative_patch();
    assert_eq!(solver.tentative_guess_count, 0);
    let _ = (x, y);
}

/// The bounded enumeration decides `Unsat` from the box it enumerates, so
/// the box is read through the JUSTIFIED accessor: `x*y = 3`, `x, y ∈ [1,
/// 10]` is satisfiable (`x = 1, y = 3`), and a model-derived pin `x = 2`
/// (reason = the variable term) that is NOT inside a tentative scope — so
/// `undo_tentative_patch` cannot pop it — must not shrink the box to `x = 2`,
/// where no `y` works. With raw `lra.get_bounds` reads the enumeration answered
/// `Unsat` here.
#[test]
fn bounded_enumeration_box_ignores_a_guess_outside_the_tentative_scopes() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let one = int(&mut terms, 1);
    let three = int(&mut terms, 3);
    let ten = int(&mut terms, 10);
    let xy = terms.mk_mul(vec![x, y]);
    let atoms = [
        terms.mk_eq(xy, three),
        terms.mk_ge(x, one),
        terms.mk_le(x, ten),
        terms.mk_ge(y, one),
        terms.mk_le(y, ten),
    ];
    let mut solver = NiaSolver::new(&terms);
    for atom in atoms {
        solver.assert_literal(atom, true);
    }
    let primed = solver.lia.check();
    assert!(!is_unsat(&primed), "{primed:?}");

    let x_var = solver.lia.lra_solver_mut().ensure_var_registered(x);
    for is_lower in [true, false] {
        solver.lia.lra_solver_mut().add_gomory_cut(
            &GomoryCut {
                coeffs: vec![(x_var, BigRational::one())],
                bound: BigRational::from_integer(BigInt::from(2)),
                is_lower,
                reasons: Vec::new(),
                source_term: None,
            },
            x,
        );
    }

    let result = solver.try_bounded_enumeration();
    assert!(
        !matches!(result, Some(TheoryResult::Unsat(_))),
        "the enumeration refuted x*y = 3 over a box shrunk by a model guess (x pinned to 2 \
         by a non-atom reason): {result:?}"
    );
}
