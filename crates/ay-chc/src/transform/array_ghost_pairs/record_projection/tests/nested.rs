// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

mod fixtures;

use super::super::expression::Value;
use super::*;
use fixtures::{iterator_source, make_sort, schema};
use std::collections::BTreeSet;

fn components(value: Value) -> Vec<Arc<ChcExpr>> {
    let Value::Record(fields, _) = value else {
        panic!("expected a complete record tuple")
    };
    fields
}

#[test]
fn vec_into_iter_flattens_exact_paths_in_source_order_and_replays_original_selectors() {
    let source = iterator_source(64);
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let projection = RecordProjection::new(&source, &control).unwrap();
    let projected = projection.project(&source, &control).unwrap();
    let array = ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::Bool));
    assert_eq!(
        projected.source_problem().predicates()[0].arg_sorts,
        vec![
            ChcSort::BitVec(64),
            ChcSort::BitVec(64),
            ChcSort::BitVec(64),
            array.clone(),
            ChcSort::BitVec(64)
        ]
    );
    let original = &source.source_problem().clauses()[0].body.predicates[0].1;
    let replay = projection
        .project_arguments(PredicateId::new(0), original, &control)
        .unwrap();
    assert_eq!(replay.len(), 5);
    for (index, expected) in ["fld_ptr", "fld_len", "fld_cap", "fld_data"]
        .iter()
        .enumerate()
    {
        let ChcExpr::FuncApp(name, _, args) = &replay[index] else {
            panic!("missing outer selector")
        };
        assert_eq!(name.as_str(), *expected);
        let ChcExpr::FuncApp(inner, sort, child) = args[0].as_ref() else {
            panic!("missing record-valued selector")
        };
        assert_eq!(inner, "fld_vec");
        assert!(matches!(sort, ChcSort::Datatype { name, .. } if name == "Vec"));
        assert_eq!(child[0].as_ref(), &original[0]);
    }
    assert!(
        matches!(&replay[4], ChcExpr::FuncApp(name, ChcSort::BitVec(64), args) if name == "fld_pos" && args[0].as_ref() == &original[0])
    );
    let ChcExpr::FuncApp(_, _, first) = &replay[0] else {
        unreachable!()
    };
    let ChcExpr::FuncApp(_, _, second) = &replay[1] else {
        unreachable!()
    };
    assert!(
        Arc::ptr_eq(&first[0], &second[0]),
        "selector prefixes should stay shared"
    );
    assert_eq!(
        projected.premises()[0][0].binder(),
        source.premises()[0][0].binder()
    );
    assert_eq!(
        projected.source_problem().clauses()[1].source_query_ordinal,
        Some(0)
    );
}

#[test]
fn record_valued_selector_returns_its_tuple_instead_of_becoming_a_constructor() {
    let (declarations, vector, iterator) = schema(2);
    let registry = Registry::new(&declarations).unwrap();
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let layouts = Layouts::new(&registry, &control).unwrap();
    let reserved = BTreeSet::from(["iter"]);
    let functions = no_functions(&control);
    let mut context = Context::new(&registry, &functions, &layouts, &reserved, &control);
    let original = var("iter", iterator);
    let all = components(context.rewrite(&original, 0).unwrap());
    let selected = select("fld_vec", vector, original);
    let prefix = components(context.rewrite(&selected, 0).unwrap());
    assert_eq!(prefix.len(), 4);
    assert!(prefix
        .iter()
        .zip(&all)
        .all(|(left, right)| Arc::ptr_eq(left, right)));
    let length = context
        .rewrite(&select("fld_len", ChcSort::BitVec(2), selected), 0)
        .unwrap()
        .scalar()
        .unwrap();
    assert!(Arc::ptr_eq(&length.0, &all[1]));
}

#[test]
fn nested_constructor_concatenates_every_child_tuple_and_authenticates_unused_children() {
    let (declarations, vector, iterator) = schema(2);
    let registry = Registry::new(&declarations).unwrap();
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let layouts = Layouts::new(&registry, &control).unwrap();
    let reserved = BTreeSet::new();
    let functions = no_functions(&control);
    let mut context = Context::new(&registry, &functions, &layouts, &reserved, &control);
    let array = ChcExpr::ConstArray(ChcSort::BitVec(2), Arc::new(ChcExpr::Bool(true)));
    let make_vec = |cap| {
        ChcExpr::FuncApp(
            "mk-vec".into(),
            vector.clone(),
            vec![
                Arc::new(ChcExpr::BitVec(0, 2)),
                Arc::new(ChcExpr::BitVec(1, 2)),
                Arc::new(cap),
                Arc::new(array.clone()),
            ],
        )
    };
    let original = ChcExpr::FuncApp(
        "mk-iter".into(),
        iterator.clone(),
        vec![
            Arc::new(make_vec(ChcExpr::BitVec(2, 2))),
            Arc::new(ChcExpr::BitVec(3, 2)),
        ],
    );
    let fields = components(context.rewrite(&original, 0).unwrap());
    let expected = [
        ChcExpr::BitVec(0, 2),
        ChcExpr::BitVec(1, 2),
        ChcExpr::BitVec(2, 2),
        array.clone(),
        ChcExpr::BitVec(3, 2),
    ];
    assert!(fields
        .iter()
        .zip(&expected)
        .all(|(actual, expected)| actual.as_ref() == expected));
    let malformed = ChcExpr::FuncApp(
        "mk-iter".into(),
        iterator,
        vec![
            Arc::new(make_vec(ChcExpr::BitVec(4, 2))),
            Arc::new(ChcExpr::BitVec(3, 2)),
        ],
    );
    assert!(context
        .rewrite(&select("fld_pos", ChcSort::BitVec(2), malformed), 0)
        .is_none());
}

#[test]
fn repeated_nested_schema_occurrences_have_distinct_field_paths_and_variable_ranges() {
    let (mut declarations, vector, _) = schema(2);
    let fields = vec![("left".into(), vector.clone()), ("right".into(), vector)];
    let wrapper = make_sort("Both", "both", &fields);
    declarations.add_datatype_def("Both".into(), vec![("both".into(), fields)]);
    let registry = Registry::new(&declarations).unwrap();
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let layouts = Layouts::new(&registry, &control).unwrap();
    let layout = layouts.get(&wrapper).unwrap();
    assert_eq!(layout.fields, vec![0..4, 4..8]);
    assert_eq!(layout.leaves.len(), 8);
    let reserved = BTreeSet::new();
    let functions = no_functions(&control);
    let mut context = Context::new(&registry, &functions, &layouts, &reserved, &control);
    let original = var("pair", wrapper);
    let flattened = components(context.rewrite(&original, 0).unwrap());
    let names: BTreeSet<_> = flattened
        .iter()
        .map(|expr| {
            let ChcExpr::Var(var) = expr.as_ref() else {
                panic!("expected a fresh leaf variable")
            };
            var.name.as_str()
        })
        .collect();
    assert_eq!(names.len(), 8);
    let nested = registry.lookup("Vec").unwrap().clone();
    let right = components(
        context
            .rewrite(&select("right", nested, original), 0)
            .unwrap(),
    );
    assert!(right
        .iter()
        .zip(&flattened[4..])
        .all(|(a, b)| Arc::ptr_eq(a, b)));
}

#[test]
fn nested_leaf_limit_admits_the_boundary_and_rejects_the_next_expansion() {
    let mut declarations = ChcProblem::new();
    let fields = vec![("bit".into(), ChcSort::Bool)];
    let mut current = make_sort("L0", "c0", &fields);
    declarations.add_datatype_def("L0".into(), vec![("c0".into(), fields)]);
    for level in 1..=8 {
        let fields = vec![("left".into(), current.clone()), ("right".into(), current)];
        let name = format!("L{level}");
        let constructor = format!("c{level}");
        current = make_sort(&name, &constructor, &fields);
        declarations.add_datatype_def(name, vec![(constructor, fields)]);
    }
    let registry = Registry::new(&declarations).unwrap();
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let layouts = Layouts::new(&registry, &control).unwrap();
    assert_eq!(layouts.get(&current).unwrap().leaves.len(), 256);
    let fields = vec![("left".into(), current.clone()), ("right".into(), current)];
    declarations.add_datatype_def("TooMany".into(), vec![("too-many".into(), fields)]);
    assert!(Registry::new(&declarations).is_err());
    let stopped = SourceControl::new(deadline(), &token);
    assert!(stopped.bytes(usize::MAX).is_none());
    assert!(Layouts::new(&registry, &stopped).is_none());
    assert!(control.poll().is_some());
}

#[test]
fn nested_product_equality_disequality_and_ite_match_all_boolean_tuples() {
    use crate::expr::evaluate_expr;
    use crate::smt::SmtValue;
    use ay_core::kani_compat::DetHashMap as FxHashMap;

    let mut declarations = ChcProblem::new();
    let fields = vec![("bit".into(), ChcSort::Bool)];
    let inner = make_sort("Bit", "bit-box", &fields);
    declarations.add_datatype_def("Bit".into(), vec![("bit-box".into(), fields)]);
    let fields = vec![("left".into(), inner.clone()), ("right".into(), inner)];
    let outer = make_sort("Duo", "duo", &fields);
    declarations.add_datatype_def("Duo".into(), vec![("duo".into(), fields)]);
    let registry = Registry::new(&declarations).unwrap();
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let layouts = Layouts::new(&registry, &control).unwrap();
    let reserved = BTreeSet::from(["choose"]);
    let functions = no_functions(&control);
    let mut context = Context::new(&registry, &functions, &layouts, &reserved, &control);
    let left = var("l", outer.clone());
    let right = var("r", outer);
    let left_vars = components(context.rewrite(&left, 0).unwrap());
    let right_vars = components(context.rewrite(&right, 0).unwrap());
    let equal = context
        .rewrite(&op(ChcOp::Eq, vec![left.clone(), right.clone()]), 0)
        .unwrap()
        .boolean(&control)
        .unwrap();
    let different = context
        .rewrite(&op(ChcOp::Ne, vec![left.clone(), right.clone()]), 0)
        .unwrap()
        .boolean(&control)
        .unwrap();
    let choice = components(
        context
            .rewrite(
                &op(ChcOp::Ite, vec![var("choose", ChcSort::Bool), left, right]),
                0,
            )
            .unwrap(),
    );
    for a in 0..4 {
        for b in 0..4 {
            for choose in [false, true] {
                let mut model = FxHashMap::default();
                model.insert("choose".into(), SmtValue::Bool(choose));
                for (value, variables) in [(a, &left_vars), (b, &right_vars)] {
                    for (index, leaf) in variables.iter().enumerate() {
                        let ChcExpr::Var(var) = leaf.as_ref() else {
                            panic!("expected leaf variable")
                        };
                        model.insert(var.name.clone(), SmtValue::Bool(value & (1 << index) != 0));
                    }
                }
                assert_eq!(evaluate_expr(&equal, &model), Some(SmtValue::Bool(a == b)));
                assert_eq!(
                    evaluate_expr(&different, &model),
                    Some(SmtValue::Bool(a != b))
                );
                for (index, leaf) in choice.iter().enumerate() {
                    let expected = if choose { a } else { b };
                    assert_eq!(
                        evaluate_expr(leaf, &model),
                        Some(SmtValue::Bool(expected & (1 << index) != 0))
                    );
                }
            }
        }
    }
}
