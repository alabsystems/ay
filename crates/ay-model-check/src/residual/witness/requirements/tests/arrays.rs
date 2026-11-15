// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn key(value: u8) -> ModelValue {
    ModelValue::bitvec(BigInt::from(value), 4)
}

fn array(default: bool, store: Vec<(ModelValue, ModelValue)>) -> ModelValue {
    ModelValue::Array(Box::new(ArrayValue {
        default: ModelValue::Bool(default),
        store,
    }))
}

#[test]
fn semantic_inner_keys_merge_without_collapsing_distinct_keys() {
    let original = array(false, Vec::new());
    let equivalent = array(false, vec![(key(3), ModelValue::Bool(false))]);
    let first = [AccessStep::Index(original)];
    let same = [AccessStep::Index(equivalent)];
    let yes = ModelValue::Bool(true);
    let no = ModelValue::Bool(false);
    let mut budget = WitnessBudget::default();
    let mut node = Node::default();
    assert!(node
        .insert(Path::Access(&first), &yes, &mut budget)
        .is_some());
    assert!(node
        .insert(Path::Access(&same), &yes, &mut budget)
        .is_some());
    assert_eq!(node.children.len(), 1);
    assert_eq!(budget.index_comparisons, 1);
    assert!(node.insert(Path::Access(&same), &no, &mut budget).is_none());

    let left = [AccessStep::Index(key(1))];
    let right = [AccessStep::Index(key(2))];
    let mut distinct = Node::default();
    assert!(distinct
        .insert(Path::Access(&left), &yes, &mut budget)
        .is_some());
    assert!(distinct
        .insert(Path::Access(&right), &no, &mut budget)
        .is_some());
    assert_eq!(distinct.children.len(), 2);
}

#[test]
fn synthesized_array_retains_observations_and_canonical_default() {
    let first = [AccessStep::Index(key(1))];
    let second = [AccessStep::Index(key(2))];
    let yes = ModelValue::Bool(true);
    let no = ModelValue::Bool(false);
    let mut node = Node::default();
    let mut budget = WitnessBudget::default();
    node.insert(Path::Access(&first), &yes, &mut budget)
        .unwrap();
    node.insert(Path::Access(&second), &no, &mut budget)
        .unwrap();
    let sort = Sort::array(Sort::bitvec(4), Sort::Bool);
    let value = node.build(&sort, &|_| None, &mut budget, 0).unwrap();
    let ModelValue::Array(value) = value else {
        panic!("concrete array");
    };
    assert!(matches!(value.default, ModelValue::Bool(false)));
    assert_eq!(value.store.len(), 2);
    assert!(matches!(value.store[0].1, ModelValue::Bool(true)));
    assert!(matches!(value.store[1].1, ModelValue::Bool(false)));
    assert!(matches!(value_eq(&value.store[0].0, &key(1)), Ok(true)));
    assert!(matches!(value_eq(&value.store[1].0, &key(2)), Ok(true)));
}

#[test]
fn pinned_array_uses_last_store_and_default_without_rewriting_parent() {
    let pinned = array(
        false,
        vec![
            (key(3), ModelValue::Bool(false)),
            (key(3), ModelValue::Bool(true)),
        ],
    );
    let hit = [AccessStep::Index(key(3))];
    let miss = [AccessStep::Index(key(4))];
    let yes = ModelValue::Bool(true);
    let no = ModelValue::Bool(false);
    let sort = Sort::array(Sort::bitvec(4), Sort::Bool);
    let mut node = Node {
        value: Some(&pinned),
        ..Node::default()
    };
    let mut budget = WitnessBudget::default();
    node.insert(Path::Access(&hit), &yes, &mut budget).unwrap();
    node.insert(Path::Access(&miss), &no, &mut budget).unwrap();
    let rebuilt = node.build(&sort, &|_| None, &mut budget, 0).unwrap();
    let ModelValue::Array(value) = rebuilt else {
        panic!("array pin");
    };
    assert_eq!(value.store.len(), 2);
    assert!(matches!(value.store[0].1, ModelValue::Bool(false)));
    assert!(matches!(value.store[1].1, ModelValue::Bool(true)));

    let mut conflict = Node {
        value: Some(&pinned),
        ..Node::default()
    };
    conflict
        .insert(Path::Access(&hit), &no, &mut budget)
        .unwrap();
    assert!(conflict.build(&sort, &|_| None, &mut budget, 0).is_none());
    let mut bad_default = Node {
        value: Some(&pinned),
        ..Node::default()
    };
    bad_default
        .insert(Path::Access(&miss), &yes, &mut budget)
        .unwrap();
    assert!(bad_default
        .build(&sort, &|_| None, &mut budget, 0)
        .is_none());
}

#[test]
fn mixed_children_wrong_carrier_and_undecidable_keys_refuse() {
    let field = [AccessStep::Field("field".into())];
    let index = [AccessStep::Index(key(0))];
    let yes = ModelValue::Bool(true);
    let mut budget = WitnessBudget::default();
    let mut node = Node::default();
    node.insert(Path::Access(&field), &yes, &mut budget)
        .unwrap();
    assert!(node
        .insert(Path::Access(&index), &yes, &mut budget)
        .is_none());
    assert!(node
        .build(
            &Sort::array(Sort::bitvec(4), Sort::Bool),
            &|_| None,
            &mut budget,
            0
        )
        .is_none());
    let mut indexed = Node::default();
    indexed
        .insert(Path::Access(&index), &yes, &mut budget)
        .unwrap();
    assert!(indexed
        .build(&Sort::Bool, &|_| None, &mut budget, 0)
        .is_none());

    // Different defaults do not decide equality without a key-domain census.
    let first = [AccessStep::Index(array(false, Vec::new()))];
    let unknown = [AccessStep::Index(array(true, Vec::new()))];
    let mut opaque_equality = Node::default();
    opaque_equality
        .insert(Path::Access(&first), &yes, &mut budget)
        .unwrap();
    assert!(opaque_equality
        .insert(Path::Access(&unknown), &yes, &mut budget)
        .is_none());
}

#[test]
fn work_and_index_caps_are_shared_and_fresh_retry_has_no_residual_state() {
    let path = [AccessStep::Index(key(1))];
    let yes = ModelValue::Bool(true);
    let sort = Sort::array(Sort::bitvec(4), Sort::Bool);
    let run = |budget: &mut WitnessBudget| {
        let mut node = Node::default();
        node.insert(Path::Access(&path), &yes, budget)?;
        node.build(&sort, &|_| None, budget, 0)
    };
    let mut measured = WitnessBudget::default();
    assert!(run(&mut measured).is_some());
    let mut exact = WitnessBudget {
        value_work: MAX_WITNESS_VALUE_WORK - measured.value_work,
        ..WitnessBudget::default()
    };
    assert!(run(&mut exact).is_some());
    assert_eq!(exact.value_work, MAX_WITNESS_VALUE_WORK);
    let mut short = WitnessBudget {
        value_work: MAX_WITNESS_VALUE_WORK - measured.value_work + 1,
        ..WitnessBudget::default()
    };
    assert!(run(&mut short).is_none());
    let mut zero = WitnessBudget {
        value_work: MAX_WITNESS_VALUE_WORK,
        ..WitnessBudget::default()
    };
    assert!(run(&mut zero).is_none());
    assert!(run(&mut WitnessBudget::default()).is_some());

    let mut lookup = WitnessBudget {
        index_comparisons: MAX_INDEX_COMPARISONS - 1,
        ..WitnessBudget::default()
    };
    assert_eq!(index_equal(&key(1), &key(2), &mut lookup), Some(false));
    assert_eq!(index_equal(&key(1), &key(1), &mut lookup), None);
    assert_eq!(
        index_equal(&key(1), &key(1), &mut WitnessBudget::default()),
        Some(true)
    );
}

#[test]
fn access_depth_is_checked_before_trie_allocation() {
    let mut terms = TermStore::new();
    let root = terms.mk_var("outer", Sort::array(Sort::bitvec(4), Sort::Bool));
    let entry = Entry {
        array: root,
        index: key(0),
        slot: Slot::Access(vec![AccessStep::Index(key(0)); MAX_CLASSIFY_DEPTH + 1]),
        value: ModelValue::Bool(true),
    };
    let mut budget = WitnessBudget::default();
    assert!(materialize(&Sort::Bool, &[&entry], &|_| None, &mut budget).is_none());
    assert_eq!(budget.value_work, 1);
    let mut fresh = WitnessBudget::default();
    assert!(Node::default()
        .build(&Sort::Bool, &|_| None, &mut fresh, MAX_CLASSIFY_DEPTH)
        .is_some());
    assert!(Node::default()
        .build(&Sort::Bool, &|_| None, &mut fresh, MAX_CLASSIFY_DEPTH + 1)
        .is_none());
}
