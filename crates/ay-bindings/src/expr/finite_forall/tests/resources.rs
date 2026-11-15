// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn exact_work_limit_accepts_then_one_more_name_byte_or_instance_refuses() {
    // This concrete grammar costs 17 input units and 11 per output equality.
    // Padding the one array name spends the remaining three input units.
    let instances = (MAX_WORK - 17) / 11;
    assert_eq!(instances, 5956);
    let padding = MAX_WORK - (17 + 11 * instances);
    assert_eq!(padding, 3);
    let body = |name: &str, upper| {
        index()
            .bvult(Expr::bitvec_const(upper, 64))
            .implies(array(name, Sort::bool()).select(index()).eq(Expr::true_()))
    };
    let exact = quantify(body("abcd", instances as u64));
    assert!(matches!(exact.value(), ExprValue::And(args) if args.len() == instances));
    retained(body("abcde", instances as u64));
    retained(body("a", instances as u64 + 1));
    // Refusal is attempt-local; it cannot poison a subsequent small request.
    assert!(
        matches!(quantify(bounded_equality(2)).value(), ExprValue::And(args) if args.len() == 2)
    );
}

#[test]
fn conjunction_depth_at_the_boundary_is_admitted_without_recursion() {
    let mut body = bounded_equality(0);
    for _ in 0..MAX_DEPTH {
        body = boolean(ExprValue::And(vec![body]));
    }
    assert!(matches!(
        quantify(body.clone()).value(),
        ExprValue::BoolConst(true)
    ));
    retained(boolean(ExprValue::And(vec![body])));
}

#[test]
fn maximum_name_lengths_are_accepted_when_the_total_budget_fits() {
    let binder = "i".repeat(MAX_NAME_BYTES);
    let bound_index = Expr::var(binder.clone(), Sort::bitvec(64));
    let body = bound_index
        .clone()
        .bvult(Expr::bitvec_const(1, 64))
        .implies(
            array("a", Sort::bool())
                .select(bound_index)
                .eq(Expr::true_()),
        );
    let result = Expr::forall(vec![(binder, Sort::bitvec(64))], body);
    assert!(matches!(result.value(), ExprValue::And(args) if args.len() == 1));
    let result = quantify(
        index().bvult(Expr::bitvec_const(1, 64)).implies(
            array(&"a".repeat(MAX_NAME_BYTES), Sort::bool())
                .select(index())
                .eq(Expr::true_()),
        ),
    );
    assert!(matches!(result.value(), ExprValue::And(args) if args.len() == 1));
}

#[test]
fn maximum_bv64_index_is_a_singleton_but_the_full_domain_exceeds_admission() {
    let equality = array("a", Sort::bool()).select(index()).eq(Expr::true_());
    let result = quantify(
        index()
            .bvuge(Expr::bitvec_const(u64::MAX, 64))
            .implies(equality.clone()),
    );
    let ExprValue::And(args) = result.value() else {
        panic!("one ground equality")
    };
    assert_eq!(args.len(), 1);
    let ExprValue::Eq(left, _) = args[0].value() else {
        panic!("equality")
    };
    let ExprValue::Select { index: last, .. } = left.value() else {
        panic!("read")
    };
    assert_eq!(last, &Expr::bitvec_const(u64::MAX, 64));
    retained(index().bvuge(Expr::bitvec_const(0, 64)).implies(equality));
}
