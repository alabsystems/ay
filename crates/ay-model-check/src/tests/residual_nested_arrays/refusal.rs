// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn inner_keys_require_concrete_exactly_typed_bounded_values() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let key = terms.mk_var("key", Sort::bitvec(64));
    let [_, _, _, cell] = f.read(&mut terms, f.a, f.outer, key);
    let assertion = eq_bv(&mut terms, cell, 5, 40);
    refused(&terms, &Model::default(), &[assertion]);
    for value in [
        ModelValue::Bool(false),
        ModelValue::Int(BigInt::from(33)),
        bv(33, 32),
        ModelValue::BitVec {
            value: BigInt::from(-1),
            width: 64,
        },
        ModelValue::BitVec {
            value: BigInt::from(1) << 64,
            width: 64,
        },
        ModelValue::BitVec {
            value: BigInt::from(1) << (residual::MAX_WITNESS_VALUE_WORK * 8),
            width: 64,
        },
    ] {
        let mut model = Model::default();
        model.leaves.insert(key, Arc::new(value));
        refused(&terms, &model, &[assertion]);
    }
    let mut model = Model::default();
    model.leaves.insert(key, Arc::new(bv(33, 64)));
    assert_eq!(complete(&terms, &model, &[assertion]).len(), 1);
}

#[test]
fn malformed_select_metadata_and_opaque_receiver_paths_stay_refused() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let [_, _, data_term, _] = f.read(&mut terms, f.a, f.outer, f.inner);
    let wrong_key = terms.mk_bitvec(BigInt::from(33), 32);
    let wrong_index = app(
        &mut terms,
        "select",
        &[data_term, wrong_key],
        Sort::bitvec(40),
    );
    let wrong_result = app(&mut terms, "select", &[data_term, f.inner], Sort::bitvec(8));
    let yes = terms.mk_bool(true);
    let unrelated = terms.mk_var("unrelated", f.data.clone());
    let conditional = terms.mk_ite_raw(yes, data_term, unrelated);
    let opaque = app(
        &mut terms,
        "select",
        &[conditional, f.inner],
        Sort::bitvec(40),
    );
    let wrapped = app(
        &mut terms,
        "unknown_array_function",
        &[data_term],
        f.data.clone(),
    );
    let wrapped = app(&mut terms, "select", &[wrapped, f.inner], Sort::bitvec(40));
    for (term, width) in [
        (wrong_index, 40),
        (wrong_result, 8),
        (opaque, 40),
        (wrapped, 40),
    ] {
        let root = eq_bv(&mut terms, term, 5, width);
        refused(&terms, &Model::default(), &[root]);
    }
}

#[test]
fn nested_read_expressions_do_not_supply_unproved_inner_indices() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let keys_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(64));
    let keys = terms.mk_var("uncommitted_keys", keys_sort);
    let key = app(&mut terms, "select", &[keys, f.inner], Sort::bitvec(64));
    let [_, _, _, read] = f.read(&mut terms, f.a, f.outer, key);
    let root = eq_bv(&mut terms, read, 5, 40);
    refused(&terms, &Model::default(), &[root]);
}

#[test]
fn nested_entry_budget_refuses_without_publishing_a_partial_array() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let mut roots = Vec::new();
    for index in 0..=residual::MAX_WITNESS_ENTRIES {
        let index = terms.mk_bitvec(BigInt::from(index), 64);
        let [_, _, _, cell] = f.read(&mut terms, f.a, f.outer, index);
        roots.push(eq_bv(&mut terms, cell, 5, 40));
    }
    let model = Model::default();
    assert_eq!(complete(&terms, &model, &roots[..1]).len(), 1);
    refused(&terms, &model, &roots);
    assert!(model.leaf_value(f.a).is_none());
    assert_eq!(complete(&terms, &model, &roots[..1]).len(), 1);
}

#[test]
fn alternating_nested_array_paths_obey_the_existing_depth_bound() {
    for depth in [2, residual::MAX_CLASSIFY_DEPTH + 1] {
        let mut terms = TermStore::new();
        let mut sorts = vec![Sort::Bool];
        for index in 0..depth {
            sorts.push(Sort::array(Sort::bitvec(64), sorts[index].clone()));
        }
        let outer_sort = record(
            "Nested",
            "mkNested",
            vec![DatatypeField::new("data", sorts[depth].clone())],
        );
        let array = terms.mk_var("nested", Sort::array(Sort::bitvec(64), outer_sort.clone()));
        let zero = terms.mk_bitvec(BigInt::from(0), 64);
        let selected = app(&mut terms, "select", &[array, zero], outer_sort);
        let mut selected = app(&mut terms, "data", &[selected], sorts[depth].clone());
        for index in (0..depth).rev() {
            selected = app(
                &mut terms,
                "select",
                &[selected, zero],
                sorts[index].clone(),
            );
        }
        let yes = terms.mk_bool(true);
        let root = eq(&mut terms, selected, yes);
        let mut model = Model::default();
        if depth == 2 {
            let assignments = complete(&terms, &model, &[root]);
            model.install(&terms, assignments);
            assert_confirmed(&confirm_completed_model(&terms, &model, &[root]));
        } else {
            refused(&terms, &model, &[root]);
        }
    }
}
