// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;

fn arr(value: ChcSort) -> ChcSort {
    ChcSort::Array(Box::new(bv(64)), Box::new(value))
}

fn record(name: &str, fields: Vec<(&str, ChcSort)>) -> ChcSort {
    ChcSort::Datatype {
        name: name.into(),
        constructors: crate::ChcDtConstructors::new(vec![crate::ChcDtConstructor {
            name: format!("mk_{name}"),
            selectors: fields
                .into_iter()
                .map(|(name, sort)| crate::ChcDtSelector {
                    name: name.into(),
                    sort,
                })
                .collect(),
        }]),
    }
}

fn add(problem: &mut ChcProblem, sort: &ChcSort) {
    let ChcSort::Datatype { name, constructors } = sort else {
        panic!("record")
    };
    let constructor = &constructors[0];
    problem.add_datatype_def(
        name.clone(),
        vec![(
            constructor.name.clone(),
            constructor
                .selectors
                .iter()
                .map(|f| (f.name.clone(), f.sort.clone()))
                .collect(),
        )],
    );
}

#[test]
fn rank_is_accumulated_through_record_cells_and_every_field_path() {
    let inner = record("Inner", vec![("len", bv(64)), ("data", arr(bv(8)))]);
    let outer = record(
        "Outer",
        vec![("tag", ChcSort::Bool), ("cells", arr(inner.clone()))],
    );
    let mut declarations = ChcProblem::new();
    add(&mut declarations, &outer);
    add(&mut declarations, &inner);
    let registry = Registry::new(&declarations).unwrap();
    for accepted in [&outer, &arr(inner.clone()), &arr(arr(ChcSort::Bool))] {
        assert!(registry.validate_sort(accepted).is_ok());
    }
    for excessive in [
        arr(outer.clone()),
        arr(arr(inner.clone())),
        arr(arr(arr(bv(8)))),
    ] {
        assert!(sort_bytes(&excessive).is_none());
        assert!(registry.validate_sort(&excessive).is_err());
    }
    assert_eq!(
        registry.application("cells", &[outer]).unwrap(),
        arr(inner.clone())
    );
    assert_eq!(
        registry
            .application("mk_Inner", &[bv(64), arr(bv(8))])
            .unwrap(),
        inner
    );
}

#[test]
fn array_wrappers_cannot_hide_missing_or_forged_record_metadata() {
    let cell = record("Cell", vec![("payload", ChcSort::Bool)]);
    let holder = record("Holder", vec![("cells", arr(cell.clone()))]);
    let mut declarations = ChcProblem::new();
    add(&mut declarations, &holder);
    assert!(Registry::new(&declarations).is_err());
    add(&mut declarations, &cell);
    let registry = Registry::new(&declarations).unwrap();
    let forged = record("Cell", vec![("payload", bv(8))]);
    assert!(registry.validate_sort(&arr(forged.clone())).is_err());
    assert!(registry.application("mk_Holder", &[arr(forged)]).is_err());
    assert_eq!(
        registry
            .application("mk_Holder", &[arr(cell.clone())])
            .unwrap(),
        holder.clone()
    );
    let wrong_key = ChcSort::Array(Box::new(bv(8)), Box::new(cell));
    assert!(registry.application("mk_Holder", &[wrong_key]).is_err());
    let bad_holder = record(
        "Holder",
        vec![("cells", arr(record("Cell", vec![("payload", bv(8))])))],
    );
    add(&mut declarations, &bad_holder);
    assert!(Registry::new(&declarations).is_err());
}

#[test]
fn array_dependencies_and_recursive_placeholders_are_not_opaque_leaves() {
    let leaf_a = record("A", vec![("leaf", ChcSort::Bool)]);
    let b = record("B", vec![("a_cells", arr(leaf_a))]);
    let a = record("A", vec![("b_cells", arr(b.clone()))]);
    let mut declarations = ChcProblem::new();
    add(&mut declarations, &a);
    add(&mut declarations, &b);
    assert!(registry_bytes(&declarations).is_some());
    assert!(Registry::new(&declarations).is_err());
    for unsupported in [
        ChcSort::Uninterpreted("A".into()),
        ChcSort::Int,
        bv(crate::MAX_BITVECTOR_WIDTH + 1),
    ] {
        assert!(sort_bytes(&arr(unsupported)).is_none());
    }
    for key in [
        ChcSort::Bool,
        bv(0),
        bv(crate::MAX_BITVECTOR_WIDTH + 1),
        arr(ChcSort::Bool),
    ] {
        assert!(sort_bytes(&ChcSort::Array(Box::new(key), Box::new(a.clone()))).is_none());
    }
}

#[test]
fn array_wrapped_products_keep_leaf_and_repeated_metadata_limits() {
    let leaf = record("Leaf", (0..64).map(|_| ("v", ChcSort::Bool)).collect());
    // Duplicate names here intentionally test structural resource counting,
    // not declaration authority. Every repeated occurrence must be charged.
    let tree = record(
        "Tree",
        vec![
            ("a", leaf.clone()),
            ("b", leaf.clone()),
            ("c", leaf.clone()),
            ("d", leaf),
        ],
    );
    let exact = arr(arr(tree.clone()));
    assert!(sort_bytes(&exact).is_some());
    assert!(sort_bytes(&arr(record(
        "TooMany",
        vec![("tree", tree), ("extra", ChcSort::Bool)]
    )))
    .is_none());
    let long = record("Payload", vec![(&"n".repeat(12_000), ChcSort::Bool)]);
    let one = sort_bytes(&arr(long.clone())).unwrap();
    assert!(one > sort_bytes(&long).unwrap());
    let two = record(
        "Twice",
        vec![("left", arr(long.clone())), ("right", arr(long.clone()))],
    );
    assert!(sort_bytes(&two).unwrap() > 2 * one);
    let many = record(
        "Many",
        (0..64).map(|_| ("cell", arr(long.clone()))).collect(),
    );
    assert!(sort_bytes(&record("Doubled", vec![("a", many.clone()), ("b", many)])).is_none());
}
