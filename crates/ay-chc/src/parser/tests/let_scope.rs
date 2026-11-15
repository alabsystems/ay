// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `let` against stripped quantifier binders of the same name.
//!
//! A `let` is expanded by substituting its value for the bound name after its
//! body is parsed, while a stripped `exists`/`forall` binder lives on in the
//! flat clause scope. Both nesting orders captured (found by the 2026-09-29
//! CHC differential generator, `gen/chc` shape `binders`):
//!
//! - `(let ((y 5)) (and (> x y) (exists ((y Int)) (= y (+ x 10)))))`: the let
//!   substitution rewrote the exists binder's own `y`, so `exists y. y = x+10`
//!   became `5 = x + 10`;
//! - `(exists ((y Int)) (let ((y 5)) (> y 3)))`, the binder renamed apart
//!   because a clause binder is also `y`: the let body's `y` resolved through
//!   the binder rename and the let was dropped, leaving `y' > 3`.
//!
//! AY answered `sat` on unsafe systems of both shapes; z3 answers `unsat`.

use super::*;
use crate::expr::evaluate_expr;
use crate::{HornClause, SmtValue};
use ay_core::kani_compat::DetHashMap;

const LET_OVER_EXISTS: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (P 7))
(assert (forall ((x Int)) (=> (and (P x) (let ((y 5)) (and (> x y) (exists ((y Int)) (= y (+ x 10)))))) false)))
(check-sat)
";

const LET_INSIDE_RENAMED_EXISTS: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (P 0))
(assert (Q 1))
(assert (forall ((y Int)) (=> (and (P y) (exists ((y Int)) (and (Q y) (let ((y 5)) (> y 3))))) false)))
(check-sat)
";

fn query(input: &str) -> HornClause {
    let problem = ChcParser::parse(input).expect("parses");
    problem
        .clauses()
        .iter()
        .find(|clause| clause.is_query())
        .expect("a query clause")
        .clone()
}

fn holds(constraint: &ChcExpr, values: &[(&str, i64)]) -> bool {
    let model: DetHashMap<String, SmtValue> = values
        .iter()
        .map(|(name, value)| ((*name).to_owned(), SmtValue::Int(i128::from(*value))))
        .collect();
    match evaluate_expr(constraint, &model) {
        Some(SmtValue::Bool(value)) => value,
        other => panic!("constraint {constraint} did not evaluate to a Bool: {other:?}"),
    }
}

#[test]
fn a_binder_inside_a_let_of_the_same_name_is_renamed_apart() {
    let clause = query(LET_OVER_EXISTS);
    let constraint = clause.body.constraint.clone().expect("a constraint");
    let binder = clause
        .vars()
        .into_iter()
        .find(|var| var.name.starts_with("ay!cap!"))
        .unwrap_or_else(|| {
            panic!("the exists binder must be renamed apart from the let: {clause}")
        });
    let x = &clause.body.predicates[0].1[0];
    let ChcExpr::Var(x) = x else {
        panic!("P's argument is a variable: {clause}");
    };
    // x = 7 reaches the query: 7 > 5 and the binder can be 17.
    assert!(
        holds(
            &constraint,
            &[(x.name.as_str(), 7), (binder.name.as_str(), 17)]
        ),
        "the let must bind only the outer `y`: {constraint}"
    );
    assert!(!holds(
        &constraint,
        &[(x.name.as_str(), 5), (binder.name.as_str(), 15)]
    ));
}

#[test]
fn a_let_inside_a_renamed_binder_of_the_same_name_shadows_the_binder() {
    let clause = query(LET_INSIDE_RENAMED_EXISTS);
    let binder = clause
        .vars()
        .into_iter()
        .find(|var| var.name.starts_with("ay!cap!"))
        .unwrap_or_else(|| panic!("the exists binder must be renamed apart: {clause}"));
    // `(let ((y 5)) (> y 3))` is true whatever the binder is; before the fix
    // it read `(> binder 3)`.
    if let Some(constraint) = &clause.body.constraint {
        let outer = clause
            .vars()
            .into_iter()
            .find(|var| !var.name.starts_with("ay!cap!"))
            .map(|var| var.name)
            .unwrap_or_default();
        assert!(
            holds(
                constraint,
                &[(binder.name.as_str(), 1), (outer.as_str(), 0)]
            ),
            "the let body must read the let, not the binder: {constraint}"
        );
    }
}

#[test]
fn nested_lets_and_same_named_clause_binders_are_unchanged() {
    // Controls: shapes that were always right keep their meaning.
    let clause = query(
        "(set-logic HORN)
         (declare-fun P (Int) Bool)
         (assert (forall ((x Int)) (=> (and (P x) (let ((x 5)) (> x 4))) false)))
         (check-sat)",
    );
    assert!(
        !format!("{clause}").contains("ay!cap!"),
        "a let over a clause binder renames nothing: {clause}"
    );
    let clause = query(
        "(set-logic HORN)
         (declare-fun P (Int) Bool)
         (assert (forall ((x Int)) (=> (and (P x) (let ((y x)) (let ((x 1)) (> y (+ x 5))))) false)))
         (check-sat)",
    );
    let constraint = clause.body.constraint.clone().expect("a constraint");
    let ChcExpr::Var(x) = &clause.body.predicates[0].1[0] else {
        panic!("P's argument is a variable: {clause}");
    };
    assert!(
        holds(&constraint, &[(x.name.as_str(), 7)]),
        "y = x = 7 > 1 + 5: {constraint}"
    );
    assert!(
        !holds(&constraint, &[(x.name.as_str(), 6)]),
        "y = x = 6 is not > 6: {constraint}"
    );
}
