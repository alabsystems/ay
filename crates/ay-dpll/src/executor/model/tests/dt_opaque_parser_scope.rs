// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded parser controls for opaque datatype completion.

use super::*;
use ay_model_check::ModelValue;

fn parser_fixture() -> Executor {
    let commands = ay_frontend::parse(
        r#"
        (set-logic ALL)
        (declare-datatype GuardCell
            ((GuardCell_mk (GuardCell_value (_ BitVec 8)))))
        (declare-datatype IntCell
            ((IntCell_mk (IntCell_value Int))))
    "#,
    )
    .expect("valid rendered-datatype fixture");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("fixture declarations execute");
    executor
}

#[test]
fn array_cell_parser_admits_only_concrete_bounded_integer_payloads() {
    let executor = parser_fixture();
    let sort = Sort::Uninterpreted("IntCell".to_string());
    let guard = rendered_dt_guard::RenderedDatatypeGuard::new(&executor);
    assert!(
        !guard.is_exact(&sort),
        "unbounded integer schemas remain outside ordinary opaque completion"
    );
    assert!(
        guard.is_exact_array_cell(&sort),
        "a concrete rendered cell is bounded by the value parser's resource envelope"
    );
    assert!(matches!(
        executor.parse_rendered_dt_value_cached("(IntCell_mk (- 7))", &sort, &guard),
        Some(ModelValue::Datatype { ctor, args })
            if ctor == "IntCell_mk"
                && matches!(args.as_slice(), [ModelValue::Int(value)] if value == &BigInt::from(-7))
    ));
    assert!(
        executor
            .parse_rendered_dt_value_cached("(IntCell_mk (/ 1 2))", &sort, &guard)
            .is_none(),
        "a non-integral payload cannot inhabit Int"
    );
}

fn is_guard_cell_42(value: Option<ModelValue>) -> bool {
    matches!(
        value,
        Some(ModelValue::Datatype { ctor, args })
            if ctor == "GuardCell_mk"
                && matches!(
                    args.as_slice(),
                    [ModelValue::BitVec { width: 8, value }]
                        if value == &BigInt::from(0x2a_u8)
                )
    )
}

#[test]
fn cached_datatype_parser_rejects_an_oversized_registry_snapshot() {
    let mut executor = parser_fixture();
    let mut declarations = String::new();
    for index in 0..600 {
        declarations.push_str(&format!(
            "(declare-datatype Padding{index} ((PaddingCtor{index})))\n"
        ));
    }
    let commands = ay_frontend::parse(&declarations).expect("valid padding declarations");
    executor
        .execute_all(&commands)
        .expect("padding declarations execute");

    let guard = rendered_dt_guard::RenderedDatatypeGuard::new(&executor);
    assert!(
        !guard.is_bounded(),
        "fixture must exhaust the schema budget"
    );
    assert!(
        executor
            .parse_rendered_dt_value_cached(
                "(GuardCell_mk #x00)",
                &Sort::Uninterpreted("GuardCell".to_string()),
                &guard,
            )
            .is_none(),
        "an invalid registry must not collapse constructor text to an opaque value"
    );
}

#[test]
fn guarded_datatype_parser_requires_exact_bitvector_payload() {
    let executor = parser_fixture();
    let sort = Sort::Uninterpreted("GuardCell".to_string());
    let guard = rendered_dt_guard::RenderedDatatypeGuard::new(&executor);
    assert!(
        is_guard_cell_42(executor.parse_rendered_dt_value_guarded(
            "(GuardCell_mk #x2a)",
            &sort,
            &guard,
        )),
        "an exact BV8 field must round-trip"
    );
    assert!(
        is_guard_cell_42(executor.parse_rendered_dt_value_guarded(
            "(GuardCell_mk (_ bv42 8))",
            &sort,
            &guard,
        )),
        "an exact explicitly-sized BV8 field must round-trip"
    );

    for invalid in [
        "(GuardCell_mk #b0101010)",
        "(GuardCell_mk (_ bv256 8))",
        "(GuardCell_mk (_ bv42 7))",
    ] {
        assert!(
            executor
                .parse_rendered_dt_value_guarded(invalid, &sort, &guard)
                .is_none(),
            "an inexact BV8 payload must be rejected: {invalid}"
        );
    }
}
