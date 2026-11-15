// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::super::check::{Check, CHECK_LIMIT};
use super::*;

#[test]
fn exact_attempt_budget_is_sticky_and_a_new_check_has_the_full_allowance() {
    assert_eq!(CHECK_LIMIT, 32_768);
    let mut check = Check::new("budget_test");
    check.charge(0).unwrap();
    check.charge(CHECK_LIMIT - 1).unwrap();
    check.charge(1).unwrap();
    check.charge(0).unwrap();
    assert!(check.charge(1).is_err());
    assert!(check.charge(0).is_err());

    let mut overflow = Check::new("budget_test");
    assert!(overflow.charge(usize::MAX).is_err());
    assert!(overflow.charge(0).is_err());

    let mut retry = Check::new("budget_test");
    retry.charge(CHECK_LIMIT).unwrap();
    retry.charge(0).unwrap();
}

#[test]
fn iterative_sort_comparison_charges_exactly_its_scheduled_pairs() {
    let depth = 64;
    let declared = sort_spine(depth);
    let requested = sort_spine(depth);
    // One root pair and two child pairs for every array, including the scalar
    // index. Scalar comparison does not schedule any additional pairs.
    let work = 1 + 2 * depth;
    for allowance in [work - 1, work] {
        let mut check = Check::new("sort_budget_test");
        check.charge(CHECK_LIMIT - allowance).unwrap();
        let result = check.same_sort(declared.last().unwrap(), requested.last().unwrap());
        if allowance == work {
            assert_eq!(result.unwrap(), true);
            check.charge(0).unwrap();
            assert!(check.charge(1).is_err());
        } else {
            assert!(result.is_err());
            assert!(check.charge(0).is_err());
        }
    }
    let mut retry = Check::new("sort_budget_test");
    assert!(retry
        .same_sort(declared.last().unwrap(), requested.last().unwrap())
        .unwrap());
    retry.charge(CHECK_LIMIT - work).unwrap();
    assert!(retry.charge(1).is_err());
    drop_sorts_parent_first(requested);
    drop_sorts_parent_first(declared);
}

fn shared_ite_chain(leaf: Expr, depth: usize) -> Vec<Expr> {
    let mut nodes = Vec::with_capacity(depth + 1);
    let condition = Expr::var("c", Sort::bool());
    nodes.push(leaf);
    for _ in 0..depth {
        let child = nodes.last().unwrap();
        nodes.push(raw_ite(
            condition.clone(),
            child.clone(),
            child.clone(),
            child.sort().clone(),
        ));
    }
    nodes
}

fn drop_parent_first(mut nodes: Vec<Expr>) {
    // Keep each child alive while dropping its parents. This tests traversal,
    // not recursive destruction of an otherwise unowned deep source graph.
    while let Some(node) = nodes.pop() {
        drop(node);
    }
}

#[test]
fn deep_shared_ite_projection_collapses_without_exponential_revisits() {
    let flag = Expr::var("original_flag", Sort::bool());
    let nodes = shared_ite_chain(pair(flag.clone(), Expr::bitvec_const(7, 8)), 256);
    let selected = nodes
        .last()
        .unwrap()
        .clone()
        .try_field_select("Pair", "flag", Sort::bool())
        .expect("bounded shared DAG");
    assert!(Arc::ptr_eq(&selected.value, &flag.value));
    drop(selected);
    drop_parent_first(nodes);
}

#[test]
fn a_very_deep_shared_ite_graph_refuses_and_a_fresh_small_attempt_succeeds() {
    let flag = Expr::var("original_flag", Sort::bool());
    let nodes = shared_ite_chain(pair(flag.clone(), Expr::bitvec_const(7, 8)), 40_000);
    let result = nodes
        .last()
        .unwrap()
        .clone()
        .try_field_select("Pair", "flag", Sort::bool());
    assert!(result.is_err());
    drop(result);
    drop_parent_first(nodes);
    let retry = pair(flag.clone(), Expr::bitvec_const(7, 8))
        .try_field_select("Pair", "flag", Sort::bool())
        .expect("refusal is attempt-local");
    assert!(Arc::ptr_eq(&retry.value, &flag.value));
}

#[test]
fn a_malformed_branch_cannot_hide_behind_a_completed_shared_subgraph() {
    let flag = Expr::true_();
    let valid = shared_ite_chain(pair(flag.clone(), Expr::bitvec_const(7, 8)), 128);
    let bad_leaf = raw_constructor("Pair", "Pair_mk", vec![flag, Expr::false_()], pair_sort(8));
    let malformed = shared_ite_chain(bad_leaf, 128);
    for reverse in [false, true] {
        let (left, right) = if reverse {
            (malformed.last().unwrap(), valid.last().unwrap())
        } else {
            (valid.last().unwrap(), malformed.last().unwrap())
        };
        let root = raw_ite(
            Expr::var("branch", Sort::bool()),
            left.clone(),
            right.clone(),
            pair_sort(8),
        );
        assert!(root.try_field_select("Pair", "flag", Sort::bool()).is_err());
    }
    drop_parent_first(malformed);
    drop_parent_first(valid);
}

#[test]
fn identical_value_arcs_with_different_outer_sorts_do_not_share_validation() {
    for original in [
        Expr::var("state", pair_sort(8)),
        pair(Expr::true_(), Expr::bitvec_const(7, 8)),
    ] {
        let altered = Expr {
            sort: pair_sort(16),
            value: Arc::clone(&original.value),
        };
        assert!(Arc::ptr_eq(&original.value, &altered.value));
        for reverse in [false, true] {
            let (left, right) = if reverse {
                (altered.clone(), original.clone())
            } else {
                (original.clone(), altered.clone())
            };
            let root = raw_ite(Expr::var("branch", Sort::bool()), left, right, pair_sort(8));
            assert!(root.try_field_select("Pair", "flag", Sort::bool()).is_err());
        }
    }
}

fn sort_spine(depth: usize) -> Vec<Sort> {
    let mut sorts = Vec::with_capacity(depth + 1);
    sorts.push(Sort::bool());
    for _ in 0..depth {
        sorts.push(Sort::array(Sort::bv8(), sorts.last().unwrap().clone()));
    }
    sorts
}

fn drop_sorts_parent_first(mut sorts: Vec<Sort>) {
    while let Some(sort) = sorts.pop() {
        drop(sort);
    }
}

#[test]
fn separately_allocated_equal_deep_sorts_compare_without_recursive_equality() {
    let declared = sort_spine(512);
    let requested = sort_spine(512);
    assert!(!std::ptr::eq(
        declared.last().unwrap().inner(),
        requested.last().unwrap().inner()
    ));
    let record_sort = Sort::struct_type("Deep", [("field", declared.last().unwrap().clone())]);
    let source = Expr::var("source", record_sort);
    let selected = source
        .clone()
        .try_field_select("Deep", "field", requested.last().unwrap().clone())
        .expect("equal separately allocated sort trees");
    let ExprValue::DatatypeSelector { expr, .. } = selected.value() else {
        panic!("symbolic source retains the selector")
    };
    assert!(Arc::ptr_eq(&expr.value, &source.value));
    drop(selected);
    drop(source);
    drop_sorts_parent_first(requested);
    drop_sorts_parent_first(declared);
}

#[test]
fn oversized_names_and_constructor_fanout_refuse_without_poisoning_retry() {
    let oversized = "D".repeat(32_769);
    let sort = Sort::struct_type(&oversized, [("field", Sort::bool())]);
    assert!(Expr::var("v", sort)
        .try_field_select(&oversized, "field", Sort::bool())
        .is_err());

    let sort = Sort::simple_enum_type("Many", (0..16_385).map(|index| format!("C{index}")));
    assert!(Expr::var("v", sort)
        .try_is_constructor("Many", "C0")
        .is_err());
    assert!(Expr::var("v", pair_sort(8))
        .try_is_constructor("Pair", "Pair_mk")
        .is_ok());
}
