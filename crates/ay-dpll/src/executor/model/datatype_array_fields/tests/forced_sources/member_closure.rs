// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn solve(source: &str) -> (Executor, Model) {
    let commands = ay_frontend::parse(source).expect("member-closure fixture parses");
    let mut executor = Executor::new();
    let outputs = executor
        .execute_all(&commands)
        .expect("member-closure fixture executes");
    assert_eq!(outputs.first().map(String::as_str), Some("sat"));
    let model = executor.last_model.clone().expect("sat retains model");
    (executor, model)
}

fn required_constructor_member(
    executor: &Executor,
    model: &Model,
) -> (usize, TermId, String, Sort) {
    let required = executor
        .datatype_array_field_required_terms()
        .expect("fixture has a bounded authored closure");
    model
        .dt_array_field_classes
        .iter()
        .enumerate()
        .find_map(|(index, authority)| {
            authority.members.keys().find_map(|&member| {
                (required.contains(&member)
                    && matches!(
                        executor.ctx.terms.get(member),
                        TermData::App(symbol, _) if symbol.name() == "mk"
                    ))
                .then(|| {
                    (
                        index,
                        member,
                        authority.carrier.clone(),
                        authority.cell_sort.clone(),
                    )
                })
            })
        })
        .expect("fixture inventories its authored constructor")
}

fn rewrite_array_field(model: &mut Model, members: &[TermId], value: bool) {
    for &member in members {
        let ModelValue::Datatype { args, .. } = model
            .dt_ground
            .get_mut(&member)
            .expect("authority member has a ground row")
        else {
            panic!("authority member is a structured datatype value");
        };
        args[0] = ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Bool(value),
            store: Vec::new(),
        }));
    }
}

#[test]
fn authored_constructor_omission_is_closed_before_replay() {
    let (mut executor, model) = solve(DIRECT_UF_FORCED_CONST);
    let (class_index, constructor, carrier, cell_sort) =
        required_constructor_member(&executor, &model);

    let mut omitted = model.clone();
    assert!(omitted.dt_array_field_classes[class_index]
        .members
        .remove(&constructor)
        .is_some());
    assert!(
        !omitted.dt_array_field_classes[class_index]
            .members
            .is_empty(),
        "the omission must leave a forged anchor for the adversarial replay"
    );
    let authenticated = executor
        .authenticated_datatype_array_field_classes(&omitted)
        .expect("the independent census restores an honestly omitted member");
    assert!(authenticated.iter().any(|class| {
        class.carrier == carrier
            && class.cell_sort == cell_sort
            && class.members.contains_key(&constructor)
    }));

    let mut forged = omitted;
    let retained: Vec<_> = forged.dt_array_field_classes[class_index]
        .members
        .keys()
        .copied()
        .collect();
    rewrite_array_field(&mut forged, &retained, false);
    assert!(executor
        .authenticated_datatype_array_field_classes(&forged)
        .is_none());

    // A same-carrier constructor retained after the solve is not authority by
    // mere presence: it is outside both the authored query and the recovered
    // direct-declaration channel, so its contradictory row remains irrelevant.
    let source = executor.ctx.terms.mk_var(
        "w6-unrooted-constructor-source",
        Sort::Array(Box::new(ArraySort {
            index_sort: Sort::Int,
            element_sort: Sort::Bool,
        })),
    );
    let generated = executor
        .ctx
        .terms
        .mk_app(Symbol::named("mk"), [source], cell_sort.clone());
    let mut unrelated = model.clone();
    unrelated
        .euf_model
        .as_mut()
        .expect("fixture has EUF evidence")
        .term_values
        .insert(generated, carrier);
    unrelated.dt_ground.insert(
        generated,
        ModelValue::Datatype {
            ctor: "mk".to_string(),
            args: vec![ModelValue::Array(Box::new(ArrayValue {
                default: ModelValue::Bool(false),
                store: Vec::new(),
            }))],
        },
    );
    assert!(executor
        .authenticated_datatype_array_field_classes(&unrelated)
        .is_some());
}

#[test]
fn eager_declaration_recovery_requires_a_live_hard_definition() {
    let (mut executor, model) = solve(FORCED_CONST);
    let constructor = executor
        .ctx
        .symbol_iter()
        .find_map(|(surface, info)| (surface == "x").then_some(info.term).flatten())
        .expect("x retains its eagerly elaborated constructor term");
    assert!(matches!(
        executor.ctx.terms.get(constructor),
        TermData::App(symbol, _) if symbol.name() == "mk"
    ));
    let required = executor
        .datatype_array_field_required_terms()
        .expect("fixture has a bounded authored closure");
    assert!(
        !required.contains(&constructor),
        "the eager constructor itself was erased from the authored assertion"
    );
    let authority = model
        .dt_array_field_classes
        .iter()
        .find(|authority| authority.members.contains_key(&constructor))
        .expect("producer inventory contains the recovered declaration")
        .clone();
    let guard = RenderedDatatypeGuard::new(&executor);
    let mut work = 0;
    let mut budget = SchemaSourceBudget::new();
    let census = executor
        .certificate_datatype_array_member_census(&model, &required, &guard, &mut work, &mut budget)
        .expect("hard definition authenticates declaration recovery");
    let mut omitted = authority.clone();
    omitted.members.clear();
    assert!(census
        .close(&omitted)
        .expect("bounded closure succeeds")
        .contains_key(&constructor));

    executor.independent_gate_authored_assertions = Some(Vec::new());
    let required = executor
        .datatype_array_field_required_terms()
        .expect("empty authored closure is bounded");
    let guard = RenderedDatatypeGuard::new(&executor);
    let mut work = 0;
    let mut budget = SchemaSourceBudget::new();
    let census = executor
        .certificate_datatype_array_member_census(&model, &required, &guard, &mut work, &mut budget)
        .expect("a free declaration is not itself malformed");
    assert!(!census
        .close(&omitted)
        .expect("bounded empty closure succeeds")
        .contains_key(&constructor));
}
