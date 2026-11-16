// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

mod arrays;
mod comparison;

#[test]
fn identical_borrowed_value_avoids_product_but_distinct_values_pay_comparison_work() {
    let value = ModelValue::Str("payload".repeat(10));
    let mut one = WitnessBudget {
        value_work: MAX_WITNESS_VALUE_WORK - 1,
        ..WitnessBudget::default()
    };
    assert!(equal(&value, &value, &mut one).is_some());
    assert_eq!(one.value_work, MAX_WITNESS_VALUE_WORK);
    let copy = value.clone();
    let mut measured = WitnessBudget::default();
    assert!(equal(&value, &copy, &mut measured).is_some());
    assert!(measured.value_work > 100);
    let mut exact = WitnessBudget {
        value_work: MAX_WITNESS_VALUE_WORK - measured.value_work,
        ..WitnessBudget::default()
    };
    assert!(equal(&value, &copy, &mut exact).is_some());
    let mut short = WitnessBudget {
        value_work: MAX_WITNESS_VALUE_WORK - measured.value_work + 1,
        ..WitnessBudget::default()
    };
    assert!(equal(&value, &copy, &mut short).is_none());
}

#[test]
fn trie_node_admission_refuses_before_retaining_a_child_and_fresh_retry_works() {
    let path = vec!["parent".to_string(), "leaf".to_string()];
    let value = ModelValue::Bool(true);
    let mut node = Node::default();
    let mut budget = WitnessBudget {
        value_work: MAX_WITNESS_VALUE_WORK - 1,
        ..WitnessBudget::default()
    };
    assert!(node
        .insert(Path::Fields(&path), &value, &mut budget)
        .is_none());
    assert!(node.children.is_empty());
    assert!(node.value.is_none());
    let mut fresh = WitnessBudget::default();
    assert!(node
        .insert(Path::Fields(&path), &value, &mut fresh)
        .is_some());
    assert!(matches!(node.children[0].0, Key::Field("parent")));
    assert!(matches!(
        node.children[0].1.children[0].0,
        Key::Field("leaf")
    ));
    assert!(std::ptr::eq(
        node.children[0].1.children[0]
            .1
            .value
            .expect("retained leaf"),
        &raw const value
    ));
}
