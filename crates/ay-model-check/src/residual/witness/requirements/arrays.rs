// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Finite inner-array requirements, sharing the enclosing witness allowance.

use super::*;
use ay_core::ArraySort;

pub(super) fn build(
    node: &Node<'_>,
    sort: &ArraySort,
    resolve: &DtResolve<'_>,
    budget: &mut WitnessBudget,
    depth: usize,
) -> Option<ModelValue> {
    // Prepay the box and the complete finite-store vector before allocation.
    if !budget.spend_value_nodes(node.children.len().checked_mul(2)?.checked_add(1)?) {
        return None;
    }
    let mut store = Vec::new();
    store.try_reserve(node.children.len()).ok()?;
    let default = canonical_inhabitant(
        &sort.element_sort,
        resolve,
        &mut Vec::new(),
        budget,
        depth + 1,
    )?;
    for (key, child) in &node.children {
        let Key::Index(index) = key else {
            return None;
        };
        let value = child.build(&sort.element_sort, resolve, budget, depth + 1)?;
        if !budget.account_value(index) {
            return None;
        }
        store.push(((*index).clone(), value));
    }
    Some(ModelValue::Array(Box::new(ArrayValue { default, store })))
}

pub(super) fn verify(
    node: &Node<'_>,
    sort: &ArraySort,
    value: &ModelValue,
    resolve: &DtResolve<'_>,
    budget: &mut WitnessBudget,
    depth: usize,
) -> Option<()> {
    let ModelValue::Array(array) = value else {
        return None;
    };
    for (key, child) in &node.children {
        let Key::Index(index) = key else {
            return None;
        };
        let actual = lookup(array, index, budget)?;
        child.verify(&sort.element_sort, actual, resolve, budget, depth + 1)?;
    }
    Some(())
}

fn lookup<'a>(
    array: &'a ArrayValue,
    index: &ModelValue,
    budget: &mut WitnessBudget,
) -> Option<&'a ModelValue> {
    // No clone and no parent mutation: the newest matching committed store
    // dominates; the original default governs all remaining observed keys.
    for (key, value) in array.store.iter().rev() {
        if index_equal(key, index, budget)? {
            return Some(value);
        }
    }
    Some(&array.default)
}
