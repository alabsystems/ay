// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn nonempty_triggers_and_non_singleton_bv_binders_preserve_the_original_body() {
    let body = bounded_equality(2);
    for vars in [
        Vec::new(),
        vec![("i".to_owned(), Sort::int())],
        vec![("i".to_owned(), Sort::bitvec(65))],
        vec![
            ("i".to_owned(), Sort::bitvec(64)),
            ("j".to_owned(), Sort::bitvec(64)),
        ],
    ] {
        retained_with(vars, body.clone(), Vec::new());
    }
    let vars = vec![("i".to_owned(), Sort::bitvec(64))];
    for triggers in [
        vec![Vec::new()],
        vec![vec![array("a", Sort::bool()).select(index())]],
    ] {
        retained_with(vars.clone(), body.clone(), triggers);
    }
    assert!(Expr::try_forall(vars, Expr::int_const(0)).is_err());
    retained_with(
        vec![("x".to_owned(), Sort::int())],
        Expr::true_(),
        Vec::new(),
    );
    let existential = Expr::exists(vec![("i".to_owned(), Sort::bitvec(64))], body.clone());
    let ExprValue::Exists { body: actual, .. } = existential.value() else {
        panic!("exists representation changed")
    };
    assert!(Arc::ptr_eq(&actual.value, &body.value));
}

#[test]
fn nested_quantifiers_and_binder_capture_surfaces_are_not_erased() {
    let guard = index().bvult(Expr::bitvec_const(2, 64));
    for inner in [
        Expr::exists(
            vec![("j".to_owned(), Sort::bool())],
            Expr::var("j", Sort::bool()),
        ),
        boolean(ExprValue::Forall {
            vars: vec![("i".to_owned(), Sort::bitvec(64))],
            body: bounded_equality(1),
            triggers: Vec::new(),
        }),
    ] {
        retained(guard.clone().implies(inner));
    }
    retained(
        guard.clone().implies(
            array("a", Sort::bool())
                .select(index())
                .eq(Expr::var("i", Sort::bool())),
        ),
    );
    retained(guard.implies(array("i", Sort::bool()).select(index()).eq(Expr::true_())));
}

#[test]
fn computed_arrays_and_fills_remain_outside_the_exact_slice() {
    let a = array("a", Sort::bool());
    let guard = index().bvult(Expr::bitvec_const(2, 64));
    let stored = a.clone().store(Expr::bitvec_const(0, 64), Expr::false_());
    let selected = Expr::ite(
        Expr::var("c", Sort::bool()),
        a.clone(),
        array("b", Sort::bool()),
    );
    for base in [stored, selected] {
        retained(
            guard
                .clone()
                .implies(base.select(index()).eq(Expr::true_())),
        );
    }
    let fill = Expr::ite(Expr::var("c", Sort::bool()), Expr::true_(), Expr::false_());
    retained(guard.implies(a.select(index()).eq(fill)));
}

#[test]
fn empty_support_does_not_hide_a_later_unsupported_guard_or_consequent() {
    let empty = index().bvult(Expr::bitvec_const(0, 64));
    let equality = array("a", Sort::bool()).select(index()).eq(Expr::true_());
    retained(empty.clone().implies(Expr::true_()));
    retained(empty.clone().and(Expr::true_()).implies(equality));
    let valid_empty = bounded_equality(0);
    retained(valid_empty.and(empty.implies(Expr::true_())));
    assert!(matches!(
        quantify(bounded_equality(0)).value(),
        ExprValue::BoolConst(true)
    ));
}

#[test]
fn depth_names_and_wide_shared_edges_refuse_without_partial_output() {
    let mut deep = bounded_equality(0);
    for _ in 0..=MAX_DEPTH {
        deep = boolean(ExprValue::And(vec![deep]));
    }
    retained(deep);
    retained(boolean(ExprValue::And(vec![
        bounded_equality(0);
        MAX_WORK + 1
    ])));
    let long_name = "x".repeat(MAX_NAME_BYTES + 1);
    retained_with(
        vec![(long_name, Sort::bitvec(64))],
        bounded_equality(0),
        Vec::new(),
    );
    retained(
        index().bvult(Expr::bitvec_const(0, 64)).implies(
            array(&"a".repeat(MAX_NAME_BYTES + 1), Sort::bool())
                .select(index())
                .eq(Expr::true_()),
        ),
    );
}

#[test]
fn signed_symbolic_and_computed_guards_are_not_admitted_as_literal_bounds() {
    let equality = array("a", Sort::bool()).select(index()).eq(Expr::true_());
    for guard in [
        index().bvslt(Expr::bitvec_const(2, 64)),
        index().bvult(Expr::var("n", Sort::bitvec(64))),
        index().bvult(Expr::bitvec_const(1, 64).bvadd(Expr::bitvec_const(1, 64))),
        boolean(ExprValue::And(Vec::new())),
        index()
            .bvult(Expr::bitvec_const(2, 64))
            .or(index().bvugt(Expr::bitvec_const(5, 64))),
    ] {
        retained(guard.implies(equality.clone()));
    }
}
