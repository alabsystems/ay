// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

fn resize_body(old: Expr, new: Expr, fill: Option<Expr>) -> Expr {
    let preserved = index().bvult(old.clone()).implies(
        array("b", Sort::bool())
            .select(index())
            .eq(array("a", Sort::bool()).select(index())),
    );
    match fill {
        Some(fill) => preserved.and(
            index()
                .bvuge(old)
                .and(index().bvult(new))
                .implies(array("b", Sort::bool()).select(index()).eq(fill)),
        ),
        None => preserved,
    }
}

fn evaluate_output(expr: &Expr, a: &[bool], b: &[bool]) -> bool {
    match expr.value() {
        ExprValue::BoolConst(value) => *value,
        ExprValue::And(args) => args.iter().all(|arg| evaluate_output(arg, a, b)),
        ExprValue::Eq(left, right) => evaluate_output(left, a, b) == evaluate_output(right, a, b),
        ExprValue::Select { array, index } => {
            let ExprValue::Var { name } = array.value() else {
                panic!("plain array")
            };
            let ExprValue::BitVecConst { value, width: 64 } = index.value() else {
                panic!("literal index")
            };
            let cells = match name.as_str() {
                "a" => a,
                "b" => b,
                _ => panic!("unexpected source name"),
            };
            cells[value.to_usize().unwrap()]
        }
        _ => panic!("output retained an unsupported operator"),
    }
}

#[test]
fn resize_2_to_65_preserves_prefix_fills_slot_64_and_leaves_the_tail_free() {
    let body = resize_body(
        Expr::bitvec_const(2, 64),
        Expr::bitvec_const(65, 64),
        Some(Expr::true_()),
    );
    let result = quantify(body);
    let ExprValue::And(equalities) = result.value() else {
        panic!("finite output")
    };
    assert_eq!(equalities.len(), 65);
    let mut a = [false; 66];
    a[1] = true;
    let mut b = [true; 66];
    b[0] = false;
    for tail in [false, true] {
        b[65] = tail;
        assert!(evaluate_output(&result, &a, &b));
    }
    b[0] = true;
    assert!(!evaluate_output(&result, &a, &b));
    b[0] = false;
    b[64] = false;
    assert!(!evaluate_output(&result, &a, &b));
}

#[test]
fn missing_fill_does_not_invent_constraints_for_new_cells() {
    let result = quantify(resize_body(
        Expr::bitvec_const(2, 64),
        Expr::bitvec_const(65, 64),
        None,
    ));
    let ExprValue::And(equalities) = result.value() else {
        panic!("finite output")
    };
    assert_eq!(equalities.len(), 2);
    for fill in [false, true] {
        let mut b = [fill; 66];
        b[..2].fill(false);
        assert!(evaluate_output(&result, &[false; 66], &b));
    }
}

#[test]
fn wide_scalar_literals_and_source_array_roots_are_shared_unchanged() {
    let a = array("payload", Sort::bitvec(129));
    let fill = Expr::bitvec_const((BigInt::from(1u8) << 128usize) + 17, 129);
    let result = quantify(
        index()
            .bvult(Expr::bitvec_const(2, 64))
            .implies(a.clone().select(index()).eq(fill.clone())),
    );
    let ExprValue::And(equalities) = result.value() else {
        panic!("finite output")
    };
    assert_eq!(equalities.len(), 2);
    for (ordinal, equality) in equalities.iter().enumerate() {
        let ExprValue::Eq(left, right) = equality.value() else {
            panic!("equality")
        };
        let ExprValue::Select { array, index } = left.value() else {
            panic!("read")
        };
        assert!(Arc::ptr_eq(&array.value, &a.value));
        assert!(Arc::ptr_eq(&right.value, &fill.value));
        assert_eq!(index, &Expr::bitvec_const(ordinal, 64));
        assert_eq!(left.sort(), &Sort::bitvec(129));
    }
}

#[test]
fn literal_reconstruction_normalizes_but_generic_rebuild_preserves_the_variant() {
    let vars = vec![("i".to_owned(), Sort::bitvec(64))];
    let symbolic = resize_body(
        Expr::var("old", Sort::bitvec(64)),
        Expr::var("new", Sort::bitvec(64)),
        Some(Expr::true_()),
    );
    retained(symbolic.clone());
    let original = Expr::forall(vars.clone(), symbolic);
    let substituted = resize_body(
        Expr::bitvec_const(2, 64),
        Expr::bitvec_const(65, 64),
        Some(Expr::true_()),
    );
    let rebuilt = crate::expr::fold::rebuild_with_children(&original, vec![substituted.clone()]);
    assert!(matches!(rebuilt.value(), ExprValue::Forall { .. }));
    let ExprValue::Forall { body, .. } = rebuilt.value() else {
        unreachable!()
    };
    assert!(Arc::ptr_eq(&body.value, &substituted.value));
    let normalized = Expr::forall_with_triggers(vars, substituted, Vec::new());
    assert!(matches!(normalized.value(), ExprValue::And(args) if args.len() == 65));
}
