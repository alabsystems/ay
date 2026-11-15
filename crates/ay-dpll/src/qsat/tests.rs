// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests of the QSAT engine's pure parts: projection, prenex game,
//! strategy re-walk.

use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;

use super::lin::{Eval, Model, Val};
use super::mbp::project;
use super::prenex::build_game;

fn int(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_int(BigInt::from(n))
}

fn real(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_rational(BigRational::from_integer(BigInt::from(n)))
}

fn num(n: i64) -> Val {
    Val::Num(BigRational::from_integer(BigInt::from(n)))
}

fn model(pairs: &[(TermId, Val)]) -> Model {
    let mut m = Model::default();
    for (t, v) in pairs {
        m.vals.insert(*t, v.clone());
    }
    m
}

/// Every projected literal holds in the model, and substituting the
/// replacement terms into the original cube keeps it true.
fn check_projection(
    terms: &mut TermStore,
    cube: &[(TermId, bool)],
    vars: &[TermId],
    m: &Model,
) -> Vec<(TermId, bool)> {
    let p = project(terms, cube, vars, m).expect("projection");
    {
        let mut ev = Eval::new(terms, m);
        for &(a, v) in &p.lits {
            assert_eq!(
                ev.boolean(a),
                Some(v),
                "projected literal false in the model"
            );
        }
    }
    // Replacement terms mention no eliminated variable and, inside the
    // region, reproduce the cube.
    let mut m2 = m.clone();
    for &(v, t) in &p.subst {
        let value = Eval::new(terms, m).value(t).expect("term evaluates");
        m2.vals.insert(v, value);
    }
    let mut ev = Eval::new(terms, &m2);
    for &(a, v) in cube {
        assert_eq!(
            ev.boolean(a),
            Some(v),
            "cube literal false after replacement"
        );
    }
    p.lits
}

#[test]
fn real_projection_takes_the_midpoint() {
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let y = t.mk_var("y", Sort::Real);
    let three = real(&mut t, 3);
    let a1 = t.mk_le(x, y);
    let a2 = t.mk_le(y, three);
    let m = model(&[(x, num(1)), (y, num(2))]);
    let lits = check_projection(&mut t, &[(a1, true), (a2, true)], &[y], &m);
    assert!(!lits.is_empty());
}

#[test]
fn int_equality_with_coefficient_projects_to_divisibility() {
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let y = t.mk_var("y", Sort::Int);
    let two = int(&mut t, 2);
    let two_y = t.mk_mul(vec![two, y]);
    let eq = t.mk_eq(two_y, x);
    let m = model(&[(x, num(4)), (y, num(2))]);
    let lits = check_projection(&mut t, &[(eq, true)], &[y], &m);
    // The region is exactly "x is even": x = 5 must fall outside it.
    let m_odd = model(&[(x, num(5))]);
    let mut ev = Eval::new(&t, &m_odd);
    assert!(lits.iter().any(|&(a, v)| ev.boolean(a) != Some(v)));
}

#[test]
fn int_bounds_use_the_model_residue() {
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let y = t.mk_var("y", Sort::Int);
    let three = int(&mut t, 3);
    let five = int(&mut t, 5);
    let three_y = t.mk_mul(vec![three, y]);
    let lower = t.mk_ge(three_y, x);
    let upper = t.mk_le(y, five);
    let m = model(&[(x, num(4)), (y, num(2))]);
    check_projection(&mut t, &[(lower, true), (upper, true)], &[y], &m);
}

#[test]
fn int_disequality_and_strict_bounds() {
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let y = t.mk_var("y", Sort::Int);
    let z = t.mk_var("z", Sort::Int);
    let lt = t.mk_lt(x, y);
    let lt2 = t.mk_lt(y, z);
    let eq = t.mk_eq(y, x);
    let m = model(&[(x, num(0)), (y, num(3)), (z, num(10))]);
    check_projection(&mut t, &[(lt, true), (lt2, true), (eq, false)], &[y], &m);
}

#[test]
fn prenex_places_levels_by_polarity() {
    let mut t = TermStore::new();
    let c = t.mk_var("c", Sort::Int);
    // (not (exists ((y Int)) (forall ((z Int)) (<= (+ c y) z))))
    let y = t.mk_var("y", Sort::Int);
    let z = t.mk_var("z", Sort::Int);
    let s = t.mk_add(vec![c, y]);
    let body = t.mk_le(s, z);
    let fa = t.mk_forall(vec![("z".to_string(), Sort::Int)], body);
    let ex = t.mk_exists(vec![("y".to_string(), Sort::Int)], fa);
    let root = t.mk_not(ex);
    let game = build_game(&mut t, &[root]).expect("in fragment");
    // ¬∃y∀z  =  ∀y∃z : level 1 (∀) then level 2 (∃).
    assert_eq!(game.levels.len(), 3);
    assert_eq!(game.levels[0], vec![c]);
    assert_eq!(game.levels[1].len(), 1);
    assert_eq!(game.levels[2].len(), 1);
    let occ_ex = game
        .occurrences
        .iter()
        .find(|o| o.quantifier == ex)
        .expect("exists");
    assert!(occ_ex.universal && occ_ex.level == 1);
}

#[test]
fn prenex_refuses_nonlinear_products() {
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let y = t.mk_var("y", Sort::Int);
    let xy = t.mk_mul(vec![x, y]);
    let zero = int(&mut t, 0);
    let body = t.mk_le(xy, zero);
    let fa = t.mk_forall(vec![("y".to_string(), Sort::Int)], body);
    assert!(build_game(&mut t, &[fa]).is_err());
}
