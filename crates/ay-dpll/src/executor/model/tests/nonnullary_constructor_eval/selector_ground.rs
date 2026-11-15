// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[derive(Clone, Copy, Debug)]
enum Case {
    Exact,
    MissingGround,
    PinOnly,
    Indexed,
    WrongArgument,
    ZeroArguments,
    ExtraArgument,
    OrdinaryUf,
    ConflictingPin,
}

fn field_value() -> ModelValue {
    ModelValue::Datatype {
        ctor: "LiteralPayload".to_string(),
        args: vec![
            ModelValue::bitvec(BigInt::from(0x2a), 8),
            ModelValue::bitvec(BigInt::from(0x7f), 8),
            ModelValue::Bool(true),
        ],
    }
}

fn selector_case(case: Case) -> (Executor, Model, TermId) {
    let mut exec = fixture();
    let outer_sort = Sort::Uninterpreted("Outer".to_string());
    let argument = exec.ctx.terms.mk_var(
        "selector_source",
        match case {
            Case::WrongArgument => field_sort(),
            _ => outer_sort.clone(),
        },
    );
    let (symbol, arguments) = match case {
        Case::Indexed => (Symbol::indexed("payload", vec![0]), vec![argument]),
        Case::ZeroArguments => (Symbol::named("payload"), vec![]),
        Case::ExtraArgument => (Symbol::named("payload"), vec![argument, argument]),
        Case::OrdinaryUf => (
            Symbol::named("opaque_payload"),
            vec![exec.ctx.terms.mk_bitvec(BigInt::from(0x2a), 8)],
        ),
        _ => (Symbol::named("payload"), vec![argument]),
    };
    let selector = exec.ctx.terms.mk_app(symbol, arguments, field_sort());
    let outer = exec
        .ctx
        .terms
        .mk_app(Symbol::named("WrapPayload"), vec![selector], outer_sort);
    let mut model = raw_model(&[
        (outer, "@Outer!selector_fallback"),
        (selector, "(LiteralPayload #x2a #x7f true)"),
    ]);
    if !matches!(case, Case::MissingGround | Case::PinOnly) {
        model.dt_ground.insert(selector, field_value());
    }
    if !matches!(case, Case::MissingGround) {
        let pin = if matches!(case, Case::ConflictingPin) {
            "(LiteralPayload #x00 #x00 false)"
        } else {
            "(LiteralPayload #x2a #x7f true)"
        };
        model
            .dt_pins
            .insert(selector, EvalValue::Element(pin.to_string()));
    }
    (exec, model, outer)
}

#[test]
fn constructor_reads_only_exact_grounded_datatype_selectors() {
    for case in [
        Case::Exact,
        Case::MissingGround,
        Case::PinOnly,
        Case::Indexed,
        Case::WrongArgument,
        Case::ZeroArguments,
        Case::ExtraArgument,
        Case::OrdinaryUf,
        Case::ConflictingPin,
    ] {
        let (exec, model, outer) = selector_case(case);
        let before = format!("{model:?}");
        let expected = if matches!(case, Case::Exact) {
            "(WrapPayload (LiteralPayload #x2a #x7f true))"
        } else {
            "@Outer!selector_fallback"
        };
        assert_eq!(
            exec.evaluate_term(&model, outer),
            EvalValue::Element(expected.to_string()),
            "{case:?}: only a live exact selector with typed ground can rebuild a constructor",
        );
        assert_eq!(format!("{model:?}"), before, "{case:?}: model mutated");
    }
}
