// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_dpll::api::ModelValue;

fn record_source() -> QuantifiedChcProblem {
    QuantifiedChcProblem::parse_smtlib(
        "(set-logic HORN)
         (declare-datatype Inner ((mkInner (tag (_ BitVec 136))
           (data (Array (_ BitVec 136) (Array (_ BitVec 136) (_ BitVec 72)))))))
         (declare-datatype Outer ((mkOuter (flag Bool) (inner Inner))))
         (assert (forall ((r Outer)) (=> (= r r) false)))
         (check-sat)",
    )
    .unwrap()
}

fn bv(value: u64, width: u32) -> ModelValue {
    ModelValue::BitVec {
        value: value.into(),
        width,
    }
}

fn record_value() -> ModelValue {
    let inner = ModelValue::Array {
        default: Box::new(bv(7, 72)),
        stores: vec![(bv(3, 136), bv(8, 72)), (bv(3, 136), bv(9, 72))],
    };
    ModelValue::Datatype {
        constructor: "mkOuter".to_owned(),
        args: vec![
            ModelValue::Bool(true),
            ModelValue::Datatype {
                constructor: "mkInner".to_owned(),
                args: vec![
                    bv(1, 136),
                    ModelValue::Array {
                        default: Box::new(inner.clone()),
                        stores: vec![(bv(2, 136), inner)],
                    },
                ],
            },
        ],
    }
}

#[test]
fn nested_record_rank_two_arrays_and_wide_keys_retain_defaults_and_ordered_duplicate_stores() {
    let token = CancellationToken::new();
    let source = record_source();
    let rendered =
        render::render_with_bindings(&source, &[0], &[vec![]], &control(&token)).unwrap();
    let registry = registry(&source, &control(&token)).unwrap();
    let sort = &rendered.bindings[0].variable.sort;
    let value =
        super::super::values::decode(&record_value(), sort, &registry, &control(&token)).unwrap();
    let trace = fixtures::unchecked(&source, vec![0], vec![vec![]], vec![value], &token);
    let wire = fixtures::wire(&source, &trace, &token);
    let decoded = bindings::import(&wire.steps, &rendered, &registry, &control(&token)).unwrap();
    assert_eq!(decoded[0].value(), trace.bindings()[0].value());
    assert_eq!(
        wire.steps[0].bindings[0].value.matches("(store ").count(),
        5
    );
    assert!(wire.steps[0].bindings[0].value.contains("(_ bv9 72)"));
    let prepared = rebuild::prepare(&source, &wire, &control(&token)).unwrap();
    assert_eq!(prepared.test_pins(), trace.replay_obligation());
}

#[test]
fn wrong_array_ascriptions_record_constructors_and_trailing_commands_are_not_value_data() {
    let token = CancellationToken::new();
    let source = record_source();
    let rendered =
        render::render_with_bindings(&source, &[0], &[vec![]], &control(&token)).unwrap();
    let registry = registry(&source, &control(&token)).unwrap();
    let value = super::super::values::decode(
        &record_value(),
        &rendered.bindings[0].variable.sort,
        &registry,
        &control(&token),
    )
    .unwrap();
    let trace = fixtures::unchecked(&source, vec![0], vec![vec![]], vec![value], &token);
    for mutation in 0..4 {
        let mut wire = fixtures::wire(&source, &trace, &token);
        let literal = &mut wire.steps[0].bindings[0].value;
        *literal = match mutation {
            0 => literal.replace("mkInner", "wrongConstructor"),
            1 => literal.replace("(Array (_ BitVec 136)", "(Array (_ BitVec 135)"),
            2 => format!("{literal} (check-sat)"),
            _ => "opaque!record".to_owned(),
        };
        assert!(bindings::import(&wire.steps, &rendered, &registry, &control(&token)).is_none());
    }
}
