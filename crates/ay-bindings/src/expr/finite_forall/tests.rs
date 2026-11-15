// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use std::sync::Arc;

mod boundaries;
mod metadata;
mod producer;
mod resources;
mod semantics;
mod translated_metadata;
mod translated_producer;
mod translated_resources;
mod translated_semantics;

fn raw(value: ExprValue, sort: Sort) -> Expr {
    Expr {
        sort,
        value: Arc::new(value),
    }
}

fn boolean(value: ExprValue) -> Expr {
    raw(value, Sort::bool())
}

fn index() -> Expr {
    Expr::var("i", Sort::bitvec(64))
}

fn array(name: &str, element: Sort) -> Expr {
    Expr::var(name, Sort::array(Sort::bitvec(64), element))
}

fn bounded_equality(upper: u64) -> Expr {
    index()
        .bvult(Expr::bitvec_const(upper, 64))
        .implies(array("a", Sort::bool()).select(index()).eq(Expr::true_()))
}

fn quantify(body: Expr) -> Expr {
    Expr::forall(vec![("i".to_owned(), Sort::bitvec(64))], body)
}

fn retained(body: Expr) {
    retained_with(vec![("i".to_owned(), Sort::bitvec(64))], body, Vec::new());
}

fn retained_with(vars: Vec<(String, Sort)>, body: Expr, triggers: Vec<Vec<Expr>>) {
    let result = Expr::try_forall_with_triggers(vars.clone(), body.clone(), triggers.clone())
        .expect("Boolean test body");
    let ExprValue::Forall {
        vars: actual_vars,
        body: actual_body,
        triggers: actual_triggers,
    } = result.value()
    else {
        panic!("unsupported body was normalized")
    };
    assert_eq!(actual_vars, &vars);
    assert!(Arc::ptr_eq(&actual_body.value, &body.value));
    assert_eq!(actual_triggers.len(), triggers.len());
    for (actual, expected) in actual_triggers.iter().zip(&triggers) {
        assert_eq!(actual.len(), expected.len());
        for (actual, expected) in actual.iter().zip(expected) {
            assert!(Arc::ptr_eq(&actual.value, &expected.value));
        }
    }
}
