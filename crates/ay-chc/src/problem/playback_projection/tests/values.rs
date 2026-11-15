// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn preserve_value(sort: ChcSort, value: SmtValue) {
    let mut source = ChcProblem::new();
    let p = source.declare_predicate("P", vec![sort.clone()]);
    source.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(p, vec![ChcExpr::var(ChcVar::new("input", sort.clone()))]),
    ));
    source.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        p,
        vec![ChcExpr::var(ChcVar::new("output", sort))],
    )])));
    let mut callback = || true;
    let mut owner = control(&mut callback);
    let row = source
        .query_obligations_with_playback(&mut owner)
        .unwrap()
        .remove(0);
    let bytes = wire(
        row.problem(),
        vec![
            step(0, "input", value.clone(), vec![]),
            step(1, "output", value.clone(), vec![0]),
        ],
        1,
    );
    let (_, view) = row.lift_ground_derivation_v2(&bytes, &mut owner).unwrap();
    assert_eq!(view.step(0).unwrap().source_binding("input"), Some(&value));
    assert_eq!(view.step(1).unwrap().source_binding("output"), Some(&value));
}

#[test]
fn complete_typed_wide_and_array_values_are_not_narrowed_or_defaulted() {
    use std::sync::Arc;
    preserve_value(ChcSort::Bool, SmtValue::Bool(true));
    preserve_value(
        ChcSort::Int,
        SmtValue::BigInt(Arc::new(num_bigint::BigInt::from(1u8) << 180usize)),
    );
    preserve_value(
        ChcSort::BitVec(256),
        SmtValue::BigBitVec(Arc::new(num_bigint::BigUint::from(1u8) << 180usize), 256),
    );
    preserve_value(
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(42)),
            entries: vec![
                (SmtValue::Int(3), SmtValue::Int(5)),
                (SmtValue::Int(3), SmtValue::Int(9)),
            ],
        },
    );
}

#[test]
fn nested_datatype_and_rational_fields_keep_exact_typed_values() {
    let sort = ChcSort::Datatype {
        name: "Record".into(),
        constructors: crate::ChcDtConstructors::new(vec![crate::ChcDtConstructor {
            name: "record".into(),
            selectors: vec![
                crate::ChcDtSelector {
                    name: "flag".into(),
                    sort: ChcSort::Bool,
                },
                crate::ChcDtSelector {
                    name: "value".into(),
                    sort: ChcSort::Real,
                },
            ],
        }]),
    };
    let rational =
        num_rational::BigRational::new(num_bigint::BigInt::from(-17), num_bigint::BigInt::from(3));
    preserve_value(
        sort,
        SmtValue::Datatype(
            "record".into(),
            vec![SmtValue::Bool(true), SmtValue::Real(rational)],
        ),
    );
}

#[test]
fn v2_finite_uf_observations_survive_without_becoming_source_bindings() {
    use std::sync::Arc;
    let mut source = ChcProblem::new();
    let p = source.declare_predicate("P", vec![ChcSort::Int]);
    let var = |name| ChcExpr::var(ChcVar::new(name, ChcSort::Int));
    let fx = ChcExpr::FuncApp("f".into(), ChcSort::Int, vec![Arc::new(var("x"))]);
    let fy = ChcExpr::FuncApp("f".into(), ChcSort::Int, vec![Arc::new(var("y"))]);
    source.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(fx.clone(), ChcExpr::int(7))),
        ClauseHead::Predicate(p, vec![var("x")]),
    ));
    source.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![var("y")])],
        Some(ChcExpr::eq(fy.clone(), ChcExpr::int(7))),
    )));
    let mut first = step(0, "x", SmtValue::Int(0), vec![]);
    let mut last = step(1, "y", SmtValue::Int(0), vec![0]);
    assert!(
        crate::smt::executor_adapter::install_observed_uf_application_values(
            &mut first.env,
            &[(fx, SmtValue::Int(7))]
        )
    );
    assert!(
        crate::smt::executor_adapter::install_observed_uf_application_values(
            &mut last.env,
            &[(fy, SmtValue::Int(7))]
        )
    );
    let mut callback = || true;
    let mut owner = control(&mut callback);
    let row = source
        .query_obligations_with_playback(&mut owner)
        .unwrap()
        .remove(0);
    let bytes = wire(row.problem(), vec![first, last], 1);
    let (_, view) = row.lift_ground_derivation_v2(&bytes, &mut owner).unwrap();
    assert_eq!(view.uf_observation_count(), 2);
    for step in view.steps() {
        assert_eq!(step.source_bindings().count(), 1);
        assert!(step
            .source_bindings()
            .all(|(name, _)| !name.starts_with('\0')));
    }
}
