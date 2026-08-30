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

/// The verification-consumer SELF-CARRIER facade shape, which no prior fixture covered: a
/// datatype registered on a SAME-NAMED uninterpreted carrier, never
/// constructor-applied, whose fields are an UNINTERPRETED sort that is NOT a
/// datatype plus a scalar. Every earlier fixture used a datatype-sorted or
/// scalar field only, so the uninterpreted-field carrier gap went unmeasured.
fn self_carrier_fixture() -> Executor {
    let commands = ay_frontend::parse(
        r#"
        (set-logic ALL)
        (declare-sort FMap 0)
        (declare-datatype Mapping
            ((Mapping (mapping_entries FMap) (mapping_default Int))))
    "#,
    )
    .expect("valid self-carrier fixture");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("fixture declarations execute");
    executor
}

/// #dt-uninterpreted-field-carrier — an EUF element token at a NON-datatype
/// uninterpreted FIELD sort must round-trip, exactly as it already does for a
/// top-level uninterpreted leaf. Dropping it made the whole enclosing
/// constructor tree unparseable, so the gate fell back to an opaque
/// `@Mapping!N` carrier that `datatype_eq_at_sort` then refused even
/// reflexively.
#[test]
fn uninterpreted_field_carrier_round_trips_inside_a_constructor_tree() {
    let executor = self_carrier_fixture();
    let sort = Sort::Uninterpreted("Mapping".to_string());
    let guard = rendered_dt_guard::RenderedDatatypeGuard::new(&executor);
    assert!(
        guard.is_registered(&sort),
        "the self-carrier facade must resolve to its registered schema"
    );
    assert!(
        guard
            .datatype_name(&Sort::Uninterpreted("FMap".to_string()))
            .is_none(),
        "the field carrier is a plain uninterpreted sort, not a datatype"
    );

    let parsed =
        executor.parse_rendered_dt_value_cached("(Mapping (as @FMap!0 FMap) 0)", &sort, &guard);
    assert!(
        matches!(
            &parsed,
            Some(ModelValue::Datatype { ctor, args })
                if ctor == "Mapping"
                    && matches!(
                        args.as_slice(),
                        [ModelValue::Uninterpreted(token), ModelValue::Int(default)]
                            if token == "@FMap!0" && default == &BigInt::from(0)
                    )
        ),
        "the printed constructor tree must parse into a constructor-bearing \
         value, got {parsed:?}"
    );

    // The carrier keeps EUF identity: distinct class tokens stay distinct
    // values, so a disequality over them is still decided, not collapsed into
    // one value (which is the only way this arm could over-confirm).
    let other =
        executor.parse_rendered_dt_value_cached("(Mapping (as @FMap!1 FMap) 0)", &sort, &guard);
    assert!(
        matches!(
            &other,
            Some(ModelValue::Datatype { args, .. })
                if matches!(
                    args.as_slice(),
                    [ModelValue::Uninterpreted(token), _] if token == "@FMap!1"
                )
        ),
        "a distinct EUF class token must stay a distinct value, got {other:?}"
    );
}

/// The complement, so a future widening is caught: admitting an uninterpreted
/// carrier must stop dead at any sort the guard DOES register. Constructor
/// identity and arity stay decisive at every depth — including the
/// non-well-founded self-recursive facade, whose canonical rendering applies an
/// arity-1 constructor to zero arguments and must therefore stay unparseable
/// rather than be waved through as an opaque token.
#[test]
fn registered_datatype_fields_never_accept_an_opaque_carrier() {
    let commands = ay_frontend::parse(
        r#"
        (set-logic ALL)
        (declare-datatype Inner ((Inner_mk (Inner_value Int))))
        (declare-datatype Outer ((Outer_mk (Outer_inner Inner))))
    "#,
    )
    .expect("valid nested-datatype fixture");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("fixture declarations execute");
    let outer = Sort::Uninterpreted("Outer".to_string());
    let guard = rendered_dt_guard::RenderedDatatypeGuard::new(&executor);

    // Positive control: the registered-datatype field path is untouched.
    assert!(
        matches!(
            executor.parse_rendered_dt_value_cached("(Outer_mk (Inner_mk 7))", &outer, &guard),
            Some(ModelValue::Datatype { ctor, .. }) if ctor == "Outer_mk"
        ),
        "a well-formed nested constructor tree must still parse"
    );

    for blocked in [
        // An EUF token at a REGISTERED datatype field: constructor identity is
        // required, and an opaque carrier does not supply it.
        "(Outer_mk (as @Inner!0 Inner))",
        // The same at the TOP level, which is what the entry guard exists for.
        "(as @Outer!0 Outer)",
        // Arity stays decisive: `Inner_mk` has one field.
        "(Outer_mk Inner_mk)",
        "(Outer_mk (Inner_mk 1 2))",
        // Constructor identity stays decisive.
        "(Outer_mk (Outer_mk (Inner_mk 1)))",
    ] {
        assert!(
            executor
                .parse_rendered_dt_value_cached(blocked, &outer, &guard)
                .is_none(),
            "a datatype-sorted position must not collapse to an opaque carrier: {blocked}"
        );
    }
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
