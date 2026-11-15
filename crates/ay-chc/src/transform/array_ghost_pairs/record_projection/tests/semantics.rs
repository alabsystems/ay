// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::super::expression::Value;
use super::*;
use crate::expr::evaluate_expr;
use crate::smt::SmtValue;
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::collections::BTreeSet;

fn pair() -> (ChcProblem, ChcSort) {
    let fields = vec![
        ("first".into(), ChcSort::Bool),
        ("second".into(), ChcSort::BitVec(1)),
    ];
    let mut declarations = ChcProblem::new();
    declarations.add_datatype_def("Pair".into(), vec![("pair".into(), fields.clone())]);
    let sort = ChcSort::Datatype {
        name: "Pair".into(),
        constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
            name: "pair".into(),
            selectors: fields
                .into_iter()
                .map(|(name, sort)| ChcDtSelector { name, sort })
                .collect(),
        }]),
    };
    (declarations, sort)
}

fn components(value: Value) -> Vec<Arc<ChcExpr>> {
    let Value::Record(fields, _) = value else {
        panic!("record disappeared")
    };
    fields
}

fn bind(model: &mut FxHashMap<String, SmtValue>, fields: &[Arc<ChcExpr>], value: u128) {
    for (index, field) in fields.iter().enumerate() {
        let ChcExpr::Var(var) = field.as_ref() else {
            panic!("expected a projected variable")
        };
        let value = if index == 0 {
            SmtValue::Bool(value & 1 != 0)
        } else {
            SmtValue::BitVec(value >> 1, 1)
        };
        model.insert(var.name.clone(), value);
    }
}

#[test]
fn finite_product_equality_disequality_ite_and_selectors_match_all_assignments() {
    let (declarations, sort) = pair();
    let registry = Registry::new(&declarations).unwrap();
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let reserved = BTreeSet::from(["r", "s", "condition"]);
    let layouts = Layouts::new(&registry, &control).unwrap();
    let functions = no_functions(&control);
    let mut context = Context::new(&registry, &functions, &layouts, &reserved, &control);
    let r = var("r", sort.clone());
    let s = var("s", sort.clone());
    let left = components(context.rewrite(&r, 0).unwrap());
    let right = components(context.rewrite(&s, 0).unwrap());
    let eq = context
        .rewrite(&op(ChcOp::Eq, vec![r.clone(), s.clone()]), 0)
        .unwrap()
        .boolean(&control)
        .unwrap();
    let ne = context
        .rewrite(&op(ChcOp::Ne, vec![r.clone(), s.clone()]), 0)
        .unwrap()
        .boolean(&control)
        .unwrap();
    let choice = op(ChcOp::Ite, vec![var("condition", ChcSort::Bool), r, s]);
    let chosen = components(context.rewrite(&choice, 0).unwrap());
    let selected = context
        .rewrite(&select("first", ChcSort::Bool, choice), 0)
        .unwrap()
        .boolean(&control)
        .unwrap();
    for a in 0..4_u128 {
        for b in 0..4_u128 {
            for condition in [false, true] {
                let mut model = FxHashMap::default();
                bind(&mut model, &left, a);
                bind(&mut model, &right, b);
                model.insert("condition".into(), SmtValue::Bool(condition));
                assert_eq!(evaluate_expr(&eq, &model), Some(SmtValue::Bool(a == b)));
                assert_eq!(evaluate_expr(&ne, &model), Some(SmtValue::Bool(a != b)));
                let expected = if condition { a } else { b };
                assert_eq!(
                    evaluate_expr(&chosen[0], &model),
                    Some(SmtValue::Bool(expected & 1 != 0))
                );
                assert_eq!(
                    evaluate_expr(&chosen[1], &model),
                    Some(SmtValue::BitVec(expected >> 1, 1))
                );
                assert_eq!(
                    evaluate_expr(&selected, &model),
                    Some(SmtValue::Bool(expected & 1 != 0))
                );
            }
        }
    }
}

#[test]
fn constructors_keep_order_and_unused_fields_in_predicate_actuals() {
    let original = source("r", "i", "n");
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let projection = RecordProjection::new(&original, &control).unwrap();
    let default = ChcExpr::ConstArray(ChcSort::BitVec(2), Arc::new(ChcExpr::Bool(false)));
    let actual = ChcExpr::FuncApp(
        "make-r".into(),
        record(),
        vec![
            Arc::new(ChcExpr::Bool(true)),
            Arc::new(ChcExpr::BitVec(3, 2)),
            Arc::new(default.clone()),
        ],
    );
    let reserved = BTreeSet::new();
    let mut context = Context::new(
        &projection.registry,
        &projection.functions,
        &projection.layouts,
        &reserved,
        &control,
    );
    let args = projection
        .arguments(
            PredicateId::new(0),
            &[actual.clone(), ChcExpr::BitVec(1, 2)],
            &mut context,
        )
        .unwrap();
    assert_eq!(
        args,
        vec![
            ChcExpr::Bool(true),
            ChcExpr::BitVec(3, 2),
            default,
            ChcExpr::BitVec(1, 2)
        ]
    );
    let replay = projection
        .project_arguments(
            PredicateId::new(0),
            &[actual.clone(), ChcExpr::BitVec(1, 2)],
            &control,
        )
        .unwrap();
    assert!(
        matches!(&replay[2], ChcExpr::FuncApp(name, _, children) if name == "data" && children[0].as_ref() == &actual)
    );
}

#[test]
fn same_named_scalar_binder_does_not_capture_outer_record_expansion() {
    let (declarations, sort) = pair();
    let registry = Registry::new(&declarations).unwrap();
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let reserved = BTreeSet::from(["r"]);
    let layouts = Layouts::new(&registry, &control).unwrap();
    let functions = no_functions(&control);
    let mut context = Context::new(&registry, &functions, &layouts, &reserved, &control);
    let first = components(context.rewrite(&var("r", sort.clone()), 0).unwrap());
    let scalar = context
        .rewrite(&var("r", ChcSort::BitVec(1)), 0)
        .unwrap()
        .scalar()
        .unwrap();
    assert_eq!(scalar.0.as_ref(), &var("r", ChcSort::BitVec(1)));
    let again = components(context.rewrite(&var("r", sort), 0).unwrap());
    assert_eq!(first.len(), 2);
    assert!(first.iter().zip(&again).all(|(a, b)| Arc::ptr_eq(a, b)));
}

#[test]
fn typed_selector_metadata_and_late_malformed_children_cannot_be_projected_away() {
    let (declarations, sort) = pair();
    let registry = Registry::new(&declarations).unwrap();
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let reserved = BTreeSet::new();
    let layouts = Layouts::new(&registry, &control).unwrap();
    let functions = no_functions(&control);
    let mut context = Context::new(&registry, &functions, &layouts, &reserved, &control);
    let bad = ChcExpr::FuncApp(
        "pair".into(),
        sort.clone(),
        vec![
            Arc::new(ChcExpr::Bool(true)),
            Arc::new(ChcExpr::BitVec(2, 1)),
        ],
    );
    // Selecting the first field must still authenticate the unused second.
    assert!(context
        .rewrite(&select("first", ChcSort::Bool, bad), 0)
        .is_none());
    assert!(context
        .rewrite(
            &select("first", ChcSort::BitVec(1), var("r", sort.clone())),
            0
        )
        .is_none());
    assert!(context
        .rewrite(&select("missing", ChcSort::Bool, var("r", sort)), 0)
        .is_none());
    assert!(context
        .rewrite(
            &ChcExpr::FuncApp("is-pair".into(), ChcSort::Bool, vec![]),
            0
        )
        .is_none());
}

#[test]
fn wide_field_expansion_exhausts_the_shared_budget_without_publishing_a_prefix() {
    let fields: Vec<_> = (0..64)
        .map(|index| (format!("field-{index}"), ChcSort::Bool))
        .collect();
    let mut declarations = ChcProblem::new();
    declarations.add_datatype_def("Wide".into(), vec![("wide".into(), fields)]);
    let registry = Registry::new(&declarations).unwrap();
    let sort = registry.lookup("Wide").unwrap().clone();
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    // Leave enough for complete tuples, but not eight independent expansions.
    control.bytes(64 * 1024 * 1024 - 128 * 1024).unwrap();
    let reserved = BTreeSet::new();
    let layouts = Layouts::new(&registry, &control).unwrap();
    let functions = no_functions(&control);
    let mut context = Context::new(&registry, &functions, &layouts, &reserved, &control);
    let mut completed = 0;
    for index in 0..8 {
        let Some(value) = context.rewrite(&var(&format!("record-{index}"), sort.clone()), 0) else {
            break;
        };
        assert_eq!(components(value).len(), 64);
        completed += 1;
    }
    assert!((1..8).contains(&completed));
    assert!(control.poll().is_none());
    assert!(context.rewrite(&var("record-0", sort.clone()), 0).is_none());
    let fresh = SourceControl::new(deadline(), &token);
    let mut retry = Context::new(&registry, &functions, &layouts, &reserved, &fresh);
    assert_eq!(
        components(retry.rewrite(&var("record-0", sort), 0).unwrap()).len(),
        64
    );
}
