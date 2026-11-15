// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `canonical_query_error` translates a query's error region onto the body
//! predicate's canonical variables exactly. Renaming an expression argument's
//! variables onto its canonical variable (#2492's shape) described another
//! region, and an ill-sorted one when the variable's sort differs.
//!
//! The queries are built, not parsed: the parser propagates a query's
//! defining literals into its arguments, which would change the shapes under
//! test.

#![allow(clippy::unwrap_used)]
use super::*;
use crate::pdr::PdrConfig;
use crate::{ChcParser, ClauseBody};

const PREDICATES: &str = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int Int) Bool)
(assert (forall ((A Int)) (=> (= A 0) (P A))))
(assert (forall ((A Int)) (=> (= A 0) (Q A A))))
(check-sat)
"#;

/// The query `name(args) ∧ constraint → false`, its translation, and the
/// canonical variables of `name`.
fn translate(
    name: &str,
    args: Vec<ChcExpr>,
    constraint: ChcExpr,
) -> (PdrSolver, Vec<ChcVar>, ChcExpr) {
    let problem = ChcParser::parse(PREDICATES).unwrap();
    let solver = PdrSolver::new(problem, PdrConfig::default());
    let pred = solver.problem.get_predicate_by_name(name).unwrap().id;
    let query = HornClause::query(ClauseBody::new(vec![(pred, args)], Some(constraint)));
    let (translated, canonical, error) = solver.canonical_query_error(&query).unwrap();
    assert_eq!(translated, pred);
    assert_eq!(error.sort(), ChcSort::Bool, "{error}");
    (solver, canonical, error)
}

fn sat(solver: &mut PdrSolver, expr: ChcExpr) -> bool {
    solver.smt.reset();
    let result = solver.smt.check_sat(&expr);
    assert!(result.is_sat() || result.is_unsat(), "{expr}: {result:?}");
    result.is_sat()
}

/// `error` is satisfiable and every model of it satisfies `region`.
fn assert_region(solver: &mut PdrSolver, error: &ChcExpr, region: ChcExpr) {
    assert!(sat(solver, error.clone()), "empty error {error}");
    let outside = ChcExpr::and(error.clone(), ChcExpr::not(region.clone()));
    assert!(!sat(solver, outside), "{error} leaves {region}");
}

fn int(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

/// `P(x + 1) ∧ 1 <= x <= 1`: the error is `P(2)`, not `P(1)`.
#[test]
fn an_offset_argument_translates_to_its_own_value() {
    let x = int("x");
    let one = ChcExpr::int(1);
    let (mut solver, canonical, error) = translate(
        "P",
        vec![ChcExpr::add(x.clone(), one.clone())],
        ChcExpr::and(ChcExpr::ge(x.clone(), one.clone()), ChcExpr::le(x, one)),
    );
    let c = ChcExpr::var(canonical[0].clone());
    assert_region(&mut solver, &error, ChcExpr::eq(c, ChcExpr::int(2)));
}

/// `P((ite b 1 0)) ∧ b`: `b` is Bool, and renaming it onto `P`'s Int
/// variable made the error the bare Int `__p0_a0`.
#[test]
fn a_bool_inside_an_int_argument_keeps_its_sort() {
    let b = ChcExpr::var(ChcVar::new("b", ChcSort::Bool));
    let arg = ChcExpr::ite(b.clone(), ChcExpr::int(1), ChcExpr::int(0));
    let (mut solver, canonical, error) = translate("P", vec![arg], b);
    let c = ChcExpr::var(canonical[0].clone());
    assert_region(&mut solver, &error, ChcExpr::eq(c, ChcExpr::int(1)));
}

/// `Q(x, x) ∧ x >= 3`: both positions are `x`.
#[test]
fn a_variable_passed_twice_equates_both_positions() {
    let x = int("x");
    let (mut solver, canonical, error) = translate(
        "Q",
        vec![x.clone(), x.clone()],
        ChcExpr::ge(x, ChcExpr::int(3)),
    );
    let c0 = ChcExpr::var(canonical[0].clone());
    let c1 = ChcExpr::var(canonical[1].clone());
    let region = ChcExpr::and(
        ChcExpr::eq(c0.clone(), c1),
        ChcExpr::ge(c0, ChcExpr::int(3)),
    );
    assert_region(&mut solver, &error, region);
}
