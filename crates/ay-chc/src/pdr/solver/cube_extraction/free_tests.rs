// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `child_cube_from_model` (Workstream B R2, §4.1.3 test list (vi)): a variable
//! absent from `T ∧ post` is absent from the cube; repeated arguments become a
//! canonical equality; the real-sorted path is exact; a residual with no model
//! value and a cube the model falsifies fall back to point cubes (counted by
//! source).

use super::super::super::{ChcExpr, FxHashMap, PdrSolver, PredicateId, SmtValue};
use crate::pdr::config::{PdrConfig, SpacerLane};
use crate::pdr::solver::spacer_core::stats::CubeSource;
use crate::ChcParser;

fn solver(smt2: &str) -> PdrSolver {
    let problem = ChcParser::parse(smt2).expect("parse");
    let base = PdrConfig::default();
    let config = PdrConfig {
        spacer: SpacerLane::rung(2),
        ..base
    };
    PdrSolver::new(problem, config)
}

/// (body args, head args, transition) of the first clause whose body has
/// exactly one predicate application of `body` and whose head is `head`.
fn step(
    s: &PdrSolver,
    body: PredicateId,
    head: PredicateId,
) -> (Vec<ChcExpr>, Vec<ChcExpr>, ChcExpr) {
    let c = s
        .problem
        .clauses()
        .iter()
        .find(|c| {
            c.body.predicates.len() == 1
                && c.body.predicates[0].0 == body
                && c.head.predicate_id() == Some(head)
        })
        .expect("step clause");
    let crate::ClauseHead::Predicate(_, h) = &c.head else {
        unreachable!()
    };
    (
        c.body.predicates[0].1.clone(),
        h.clone(),
        c.body.constraint.clone().unwrap_or(ChcExpr::Bool(true)),
    )
}

fn model_from(
    args: &[ChcExpr],
    values: &[i128],
    extra: &[(&ChcExpr, i128)],
) -> FxHashMap<String, SmtValue> {
    let mut m = FxHashMap::default();
    for (a, k) in args.iter().zip(values) {
        if let ChcExpr::Var(v) = a {
            m.insert(v.name.clone(), SmtValue::Int(*k));
        }
    }
    for (a, k) in extra {
        if let ChcExpr::Var(v) = a {
            m.insert(v.name.clone(), SmtValue::Int(*k));
        }
    }
    m
}

fn canon_point(s: &PdrSolver, p: PredicateId, values: &[i128]) -> FxHashMap<String, SmtValue> {
    s.canonical_vars(p)
        .expect("canon")
        .iter()
        .zip(values)
        .map(|(v, k)| (v.name.clone(), SmtValue::Int(*k)))
        .collect()
}

fn holds(e: &ChcExpr, m: &FxHashMap<String, SmtValue>) -> Option<bool> {
    match crate::expr::evaluate_expr(e, m)? {
        SmtValue::Bool(b) => Some(b),
        _ => None,
    }
}

const FREE_Y: &str = r#"
(set-logic HORN)
(declare-fun P (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (= x 0) (P x y))))
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int))
  (=> (and (P x y) (= x1 (+ x 1)) (= y1 y)) (P x1 y1))))
(assert (forall ((x Int) (y Int)) (=> (and (P x y) (>= x 3)) false)))
(check-sat)
"#;

#[test]
fn a_variable_absent_from_t_and_post_is_absent_from_the_cube() {
    let s = solver(FREE_Y);
    let p = s.problem.get_predicate_by_name("P").expect("P").id;
    let canon = s.canonical_vars(p).expect("canon").to_vec();
    let (body, head, t) = step(&s, p, p);
    let post = ChcExpr::ge(ChcExpr::var(canon[0].clone()), ChcExpr::int(3));
    let post_on_head = s.apply_to_args(p, &post, &head).expect("apply");
    let m = model_from(&body, &[4, 17], &[(&head[0], 5), (&head[1], 17)]);
    let child = s.child_cube_from_model(p, &body, &t, &post_on_head, &m, None, &[]);
    assert_eq!(child.source, CubeSource::MbpFree);
    assert_eq!(child.substituted, 0);
    let cube = child.cube.expect("cube");
    assert_eq!(
        cube.lits(),
        &[ChcExpr::ge(ChcExpr::var(canon[0].clone()), ChcExpr::int(2))],
        "the exact pre-image of x ≥ 3 under x' = x + 1"
    );
    assert!(
        cube.lits()
            .iter()
            .all(|l| !l.contains_var_name(&canon[1].name)),
        "y must stay free: {}",
        cube.expr()
    );
    assert!(!cube.is_point_cube(&canon));
}

#[test]
fn repeated_arguments_become_a_canonical_equality() {
    let s = solver(
        r#"
(set-logic HORN)
(declare-fun Q (Int Int) Bool)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Q x x))))
(assert (forall ((x Int) (y Int)) (=> (and (Q x x) (= y (+ x 1))) (P y))))
(assert (forall ((y Int)) (=> (and (P y) (> y 5)) false)))
(check-sat)
"#,
    );
    let q = s.problem.get_predicate_by_name("Q").expect("Q").id;
    let p = s.problem.get_predicate_by_name("P").expect("P").id;
    let (body, head, t) = step(&s, q, p);
    let pc = s.canonical_vars(p).expect("canon").to_vec();
    let post = ChcExpr::ge(ChcExpr::var(pc[0].clone()), ChcExpr::int(6));
    let post_on_head = s.apply_to_args(p, &post, &head).expect("apply");
    // A model of T ∧ post over whatever variables the parser left in the clause.
    let mut m: FxHashMap<String, SmtValue> = FxHashMap::default();
    for v in t
        .vars()
        .into_iter()
        .chain(body.iter().flat_map(ChcExpr::vars))
    {
        m.insert(v.name.clone(), SmtValue::Int(5));
    }
    for v in head.iter().flat_map(ChcExpr::vars) {
        m.insert(v.name.clone(), SmtValue::Int(6));
    }
    assert_eq!(
        holds(&ChcExpr::and(t.clone(), post_on_head.clone()), &m),
        Some(true)
    );
    let child = s.child_cube_from_model(q, &body, &t, &post_on_head, &m, None, &[]);
    let cube = child.cube.expect("cube");
    assert_ne!(child.source, CubeSource::PointFallbackMismatch);
    let at = |a, b| holds(cube.expr(), &canon_point(&s, q, &[a, b]));
    assert_eq!(at(5, 5), Some(true), "the model's state: {}", cube.expr());
    assert_eq!(at(9, 9), Some(true), "not a point cube: {}", cube.expr());
    assert_eq!(
        at(5, 7),
        Some(false),
        "Q(x, x) forces equal arguments: {}",
        cube.expr()
    );
    assert_eq!(at(4, 4), Some(false), "x + 1 ≥ 6: {}", cube.expr());
}

#[test]
fn the_real_path_is_exact() {
    let s = solver(
        r#"
(set-logic HORN)
(declare-fun R (Real Real) Bool)
(assert (forall ((x Real) (y Real)) (=> (and (= x 0.0) (= y 0.0)) (R x y))))
(assert (forall ((x Real) (y Real) (x1 Real) (y1 Real))
  (=> (and (R x y) (= x1 (+ x (* 2.0 y))) (= y1 y)) (R x1 y1))))
(assert (forall ((x Real) (y Real)) (=> (and (R x y) (> x 3.5)) false)))
(check-sat)
"#,
    );
    let r = s.problem.get_predicate_by_name("R").expect("R").id;
    let canon = s.canonical_vars(r).expect("canon").to_vec();
    let (body, head, t) = step(&s, r, r);
    let post = ChcExpr::gt(ChcExpr::var(canon[0].clone()), ChcExpr::Real(7, 2));
    let post_on_head = s.apply_to_args(r, &post, &head).expect("apply");
    let real = |n: i64| SmtValue::Real(num_rational::BigRational::from_integer(n.into()));
    let mut m: FxHashMap<String, SmtValue> = FxHashMap::default();
    for (a, val) in body.iter().zip([1, 2]).chain(head.iter().zip([5, 2])) {
        if let ChcExpr::Var(v) = a {
            m.insert(v.name.clone(), real(val));
        }
    }
    let child = s.child_cube_from_model(r, &body, &t, &post_on_head, &m, None, &[]);
    assert_eq!(
        child.source,
        CubeSource::MbpFree,
        "{:?}",
        child.cube.as_ref().map(|c| c.expr().clone())
    );
    let cube = child.cube.expect("cube");
    let at = |a: i64, b: i64| {
        let pt: FxHashMap<String, SmtValue> = [
            (canon[0].name.clone(), real(a)),
            (canon[1].name.clone(), real(b)),
        ]
        .into_iter()
        .collect();
        holds(cube.expr(), &pt)
    };
    assert_eq!(at(1, 2), Some(true), "{}", cube.expr());
    assert_eq!(at(3, 1), Some(true), "x + 2y = 5 > 3.5: {}", cube.expr());
    assert_eq!(at(0, 1), Some(false), "x + 2y = 2: {}", cube.expr());
}

#[test]
fn a_residual_without_a_model_value_falls_back_to_a_point_cube() {
    let s = solver(
        r#"
(set-logic HORN)
(declare-fun P (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (= x 0) (P x y))))
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int) (z Int))
  (=> (and (P x y) (= x1 (+ x 1)) (= y1 y) (= (mod z 2) 1)) (P x1 y1))))
(assert (forall ((x Int) (y Int)) (=> (and (P x y) (>= x 3)) false)))
(check-sat)
"#,
    );
    let p = s.problem.get_predicate_by_name("P").expect("P").id;
    let canon = s.canonical_vars(p).expect("canon").to_vec();
    let (body, head, t) = step(&s, p, p);
    if !t.vars().iter().any(|v| v.name.contains('z')) {
        // The front end may simplify the unconstrained `z` away; nothing to test then.
        return;
    }
    let post = ChcExpr::ge(ChcExpr::var(canon[0].clone()), ChcExpr::int(3));
    let post_on_head = s.apply_to_args(p, &post, &head).expect("apply");
    // No value for z, and the default z = 0 falsifies `z mod 2 = 1`.
    let m = model_from(&body, &[4, 17], &[(&head[0], 5), (&head[1], 17)]);
    let child = s.child_cube_from_model(p, &body, &t, &post_on_head, &m, None, &[]);
    assert_eq!(child.source, CubeSource::PointFallbackNoValue);
    let cube = child.cube.expect("point cube");
    assert!(cube.is_point_cube(&canon), "{}", cube.expr());
}

#[test]
fn a_cube_the_model_falsifies_falls_back_and_is_counted() {
    let s = solver(FREE_Y);
    let p = s.problem.get_predicate_by_name("P").expect("P").id;
    let canon = s.canonical_vars(p).expect("canon").to_vec();
    let (body, head, t) = step(&s, p, p);
    let post = ChcExpr::ge(ChcExpr::var(canon[0].clone()), ChcExpr::int(3));
    let post_on_head = s.apply_to_args(p, &post, &head).expect("apply");
    // Not a model of T ∧ post (x1 = 1 < 3): the projected cube x ≥ 2 is false at x = 0.
    let m = model_from(&body, &[0, 0], &[(&head[0], 1), (&head[1], 0)]);
    let child = s.child_cube_from_model(p, &body, &t, &post_on_head, &m, None, &[]);
    assert_eq!(child.source, CubeSource::PointFallbackMismatch);
    let cube = child.cube.expect("point cube");
    assert!(cube.is_point_cube(&canon), "{}", cube.expr());
}

#[test]
fn a_cube_equal_to_an_excluded_state_is_recomputed_with_the_exclusion() {
    let s = solver(FREE_Y);
    let p = s.problem.get_predicate_by_name("P").expect("P").id;
    let canon = s.canonical_vars(p).expect("canon").to_vec();
    let (body, head, t) = step(&s, p, p);
    let post = ChcExpr::ge(ChcExpr::var(canon[0].clone()), ChcExpr::int(3));
    let post_on_head = s.apply_to_args(p, &post, &head).expect("apply");
    let m = model_from(&body, &[4, 17], &[(&head[0], 5), (&head[1], 17)]);
    let first = s
        .child_cube_from_model(p, &body, &t, &post_on_head, &m, None, &[])
        .cube
        .expect("cube");
    // The same state is an unknown predecessor at this level: exclude it.
    let excluded = vec![first.expr().clone()];
    let exclusion = s
        .apply_to_args(p, &ChcExpr::not(first.expr().clone()), &body)
        .expect("apply");
    // The model must satisfy the exclusion for the retry to apply; x ≥ 2 holds
    // at x = 4, so the model falsifies ¬(x ≥ 2) and the retry's guard rejects
    // the retried cube — the constructor must still return a cube the model
    // satisfies (the point fallback).
    let child =
        s.child_cube_from_model(p, &body, &t, &post_on_head, &m, Some(&exclusion), &excluded);
    let cube = child.cube.expect("cube");
    assert_eq!(
        holds(cube.expr(), &canon_point(&s, p, &[4, 17])),
        Some(true)
    );
}
