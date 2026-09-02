// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

const FIXTURE: &str = "(set-logic ALL)\
     (declare-datatype U1 ((mk (g (Array Int Bool)))))\
     (declare-const v3 (Array Int U1))\
     (declare-const v5 (Array Int U1))\
     (assert (distinct v3 v5))\
     (check-sat)\
     (check-sat)";

struct Fixture {
    executor: Executor,
    model: Model,
    outer_sort: ArraySort,
    cell: TermId,
    stale: (TermId, TermId),
    outer: TermId,
    carrier: String,
    cell_sort: Sort,
    other_carrier: String,
}

fn build_fixture() -> Fixture {
    let commands = ay_frontend::parse(FIXTURE).expect("certificate fixture parses");
    let mut executor = Executor::new();
    let mut outputs = Vec::new();
    for command in &commands {
        let Some(output) = executor
            .execute(command)
            .expect("certificate fixture command executes")
        else {
            continue;
        };
        let model_shape = executor.last_model.as_ref().map(|model| {
            (
                model.dt_ground.len(),
                model.dt_array_field_classes.len(),
                model
                    .euf_model
                    .as_ref()
                    .map_or(0, |euf| euf.term_values.len()),
                model
                    .array_model
                    .as_ref()
                    .map_or(0, |arrays| arrays.array_values.len()),
            )
        });
        assert_ne!(
            output,
            "unknown",
            "reason={:?}, validated={}, dt_constructed={:?}, arrays_completed={:?}, phase={:?}, detail={:?}, validation={:?}, model={model_shape:?}",
            executor.unknown_reason(),
            executor.last_model_validated,
            executor
                .statistics()
                .get_int("model_completion.dt_constructed"),
            executor
                .statistics()
                .get_int("model_completion.arrays_completed"),
            executor.statistics().get_string("unknown.phase"),
            executor.statistics().get_string("unknown.detail"),
            executor.last_validation_stats,
        );
        outputs.push(output);
    }
    assert_eq!(outputs, ["sat", "sat"]);
    let model = executor
        .last_model
        .as_ref()
        .expect("sat retains the completed model")
        .clone();
    let outer_sort = executor
        .ctx
        .terms
        .term_ids()
        .find_map(|term| match executor.ctx.terms.sort(term) {
            Sort::Array(array) if array.element_sort == Sort::Uninterpreted("U1".to_string()) => {
                Some(array.as_ref().clone())
            }
            _ => None,
        })
        .expect("fixture owns its outer array sort");
    assert!(executor.observed_datatype_array_fields_complete(&model, &outer_sort));
    let authenticated = executor
        .authenticated_datatype_array_field_classes(&model)
        .expect("the current typed inventory revalidates");
    assert_eq!(authenticated.len(), 2);
    assert!(
        !same_datatype_array_value(&authenticated[0].value, &authenticated[1].value),
        "the two outer-array witness cells must remain extensionally distinct after exact field reconstruction"
    );
    for class in &authenticated {
        let member = *class
            .members
            .keys()
            .next()
            .expect("an authenticated class has a stamped anchor");
        let normalized = executor
            .independent_datatype_term_value_for_test(&model, member)
            .expect("the independent view normalizes an authenticated term");
        assert!(same_value(&normalized, &class.value));
        assert!(executor
            .independent_datatype_element_value_for_test(&model, &class.carrier, &class.cell_sort,)
            .is_none());
    }
    fixture_from_authenticated(executor, model, outer_sort, authenticated)
}

fn fixture_from_authenticated(
    executor: Executor,
    model: Model,
    outer_sort: ArraySort,
    authenticated: Vec<AuthenticatedDatatypeArrayClass>,
) -> Fixture {
    let guard = RenderedDatatypeGuard::new(&executor);
    let inventoried: HashSet<TermId> = model
        .dt_array_field_classes
        .iter()
        .flat_map(|authority| authority.members.keys().copied())
        .collect();
    let stale = executor
        .ctx
        .terms
        .term_ids()
        .find_map(|field_app| {
            executor
                .outer_array_field_cell(field_app, &outer_sort, &guard)
                .filter(|cell| !inventoried.contains(cell))
                .map(|cell| (field_app, cell))
        })
        .expect("the second pass retains old syntax outside its inventory");
    let cell = executor
        .ctx
        .terms
        .term_ids()
        .find_map(|field_app| {
            executor
                .outer_array_field_cell(field_app, &outer_sort, &guard)
                .filter(|cell| inventoried.contains(cell))
        })
        .expect("fixture inventories a current exact array-field cell");
    let current = authenticated
        .iter()
        .find(|class| class.members.contains_key(&cell))
        .expect("the selected cell has current typed authority");
    let other = authenticated
        .iter()
        .find(|class| class.carrier != current.carrier)
        .expect("fixture has a distinct second carrier");
    let outer = match executor.ctx.terms.get(cell) {
        TermData::App(symbol, args) if symbol.name() == "select" => args[0],
        _ => panic!("inventoried cell is an outer-array select"),
    };
    Fixture {
        executor,
        model,
        outer_sort,
        cell,
        stale,
        outer,
        carrier: current.carrier.clone(),
        cell_sort: current.cell_sort.clone(),
        other_carrier: other.carrier.clone(),
    }
}

fn assert_complete_coverage(fixture: &Fixture) {
    let mut uncovered = fixture.model.clone();
    uncovered
        .dt_array_field_classes
        .pop()
        .expect("fixture has a second current class to leave uncovered");
    assert_eq!(
        fixture
            .executor
            .authenticated_datatype_array_field_classes(&uncovered)
            .expect("the retained class remains authenticated")
            .len(),
        1
    );
    assert!(!fixture
        .executor
        .observed_datatype_array_fields_complete(&uncovered, &fixture.outer_sort));
    assert!(fixture.model.euf_model.as_ref().is_some_and(|euf| {
        !euf.term_values.contains_key(&fixture.stale.0)
            && !euf.term_values.contains_key(&fixture.stale.1)
    }));
}

fn assert_partial_and_outer_mismatch(fixture: &Fixture) -> Model {
    let mut partial = fixture.model.clone();
    assert!(partial
        .euf_model
        .as_ref()
        .is_some_and(|euf| euf.term_values.contains_key(&fixture.cell)));
    partial.dt_ground.remove(&fixture.cell);
    assert!(fixture
        .executor
        .independent_datatype_term_value_for_test(&fixture.model, fixture.cell)
        .is_some());
    assert!(fixture
        .executor
        .independent_array_select_value_for_test(&fixture.model, fixture.cell)
        .is_some());

    let mut outer_mismatch = fixture.model.clone();
    let interpretation = outer_mismatch
        .array_model
        .as_mut()
        .and_then(|arrays| arrays.array_values.get_mut(&fixture.outer))
        .expect("fixture has an emitted outer-array interpretation");
    interpretation.stores.clear();
    interpretation.default = Some(fixture.other_carrier.clone());
    assert!(fixture
        .executor
        .independent_array_select_value_for_test(&outer_mismatch, fixture.cell)
        .is_none());
    assert!(fixture
        .executor
        .authenticated_datatype_array_field_classes(&partial)
        .is_none());
    assert!(!fixture
        .executor
        .observed_datatype_array_fields_complete(&partial, &fixture.outer_sort));
    partial
}

fn assert_omitted_and_forged_rows(fixture: &Fixture) {
    let mut omitted = fixture.model.clone();
    omitted.dt_array_field_classes.clear();
    assert!(omitted.dt_ground.contains_key(&fixture.cell));
    assert!(fixture
        .executor
        .independent_datatype_term_value_for_test(&omitted, fixture.cell)
        .is_none());
    assert!(
        fixture
            .executor
            .independent_datatype_element_value_for_test(
                &omitted,
                &fixture.carrier,
                &fixture.cell_sort,
            )
            .is_none()
    );
    assert!(fixture
        .executor
        .independent_array_select_value_for_test(&omitted, fixture.cell)
        .is_none());

    let mut forged = fixture.model.clone();
    forged.dt_ground.insert(
        fixture.cell,
        ModelValue::Datatype {
            ctor: "mk".to_string(),
            args: vec![ModelValue::Array(Box::new(ArrayValue {
                default: ModelValue::Int(BigInt::from(0)),
                store: Vec::new(),
            }))],
        },
    );
    assert!(fixture
        .executor
        .independent_datatype_term_value_for_test(&forged, fixture.cell)
        .is_none());
    assert!(fixture
        .executor
        .independent_array_select_value_for_test(&forged, fixture.cell)
        .is_none());

    let mut forged_provenance = fixture.model.clone();
    forged_provenance
        .dt_array_field_classes
        .iter_mut()
        .find(|class| class.members.contains_key(&fixture.cell))
        .expect("fixture has the selected class")
        .unobserved_fields
        .clear();
    assert!(fixture
        .executor
        .authenticated_datatype_array_field_classes(&forged_provenance)
        .is_none());
}

fn assert_structural_collision_declines(fixture: &Fixture) {
    let mut collision = fixture.model.clone();
    let rendered = super::super::super::dt_construct::dt_canonical_string(
        collision
            .dt_ground
            .get(&fixture.cell)
            .expect("fixture has its structured member"),
    );
    let second_anchor = fixture.stale.1;
    let second_stamp = fixture
        .executor
        .ctx
        .terms
        .entry_stamp(second_anchor)
        .expect("stale syntax still has a live birth stamp");
    collision
        .dt_array_field_classes
        .iter_mut()
        .find(|class| class.members.contains_key(&fixture.cell))
        .expect("fixture has the current authority class")
        .members
        .insert(second_anchor, second_stamp);
    collision
        .euf_model
        .as_mut()
        .expect("fixture has current EUF evidence")
        .term_values
        .insert(second_anchor, fixture.carrier.clone());
    collision
        .dt_ground
        .insert(second_anchor, ModelValue::Uninterpreted(rendered));
    assert!(fixture
        .executor
        .authenticated_datatype_array_field_classes(&collision)
        .is_none());
    for anchor in [fixture.cell, second_anchor] {
        assert!(fixture
            .executor
            .independent_datatype_term_value_for_test(&collision, anchor)
            .is_none());
        assert!(fixture
            .executor
            .independent_array_select_value_for_test(&collision, anchor)
            .is_none());
    }
}

fn authored_selector_observation_invalidates_free_field(fixture: &mut Fixture) {
    let field_sort = fixture
        .executor
        .ctx
        .constructor_selector_info("mk")
        .and_then(|fields| fields.first())
        .map(|(_, sort)| sort.clone())
        .expect("fixture has its array field");
    let fresh_cell = fixture
        .executor
        .ctx
        .terms
        .mk_var("w6-unrooted-cell", fixture.cell_sort.clone());
    let fresh_stamp = fixture
        .executor
        .ctx
        .terms
        .entry_stamp(fresh_cell)
        .expect("fresh member has a birth stamp");
    let installed = fixture
        .model
        .dt_ground
        .get(&fixture.cell)
        .expect("fixture has its exact installed value")
        .clone();
    fixture.model.dt_ground.insert(fresh_cell, installed);
    fixture
        .model
        .euf_model
        .as_mut()
        .expect("fixture has EUF evidence")
        .term_values
        .insert(fresh_cell, fixture.carrier.clone());
    fixture
        .model
        .dt_array_field_classes
        .iter_mut()
        .find(|authority| authority.members.contains_key(&fixture.cell))
        .expect("fixture has exact class authority")
        .members
        .insert(fresh_cell, fresh_stamp);
    let app =
        fixture
            .executor
            .ctx
            .terms
            .mk_app(Symbol::named("g"), [fresh_cell], field_sort.clone());
    fixture
        .model
        .array_model
        .get_or_insert_with(Default::default)
        .array_values
        .insert(
            app,
            ay_arrays::ArrayInterpretation {
                default: Some("true".to_string()),
                stores: Vec::new(),
                index_sort: Some(Sort::Int),
                element_sort: Some(Sort::Bool),
            },
        );
    assert!(fixture
        .executor
        .authenticated_datatype_array_field_classes(&fixture.model)
        .is_some());

    let zero = fixture.executor.ctx.terms.mk_int(BigInt::from(0));
    let read = fixture.executor.ctx.terms.mk_select(app, zero);
    let false_term = fixture.executor.ctx.terms.false_term();
    let observation = fixture.executor.ctx.terms.mk_eq(read, false_term);
    let mut roots = fixture.executor.independent_gate_query_roots();
    roots.push(observation);
    fixture.executor.independent_gate_authored_assertions = Some(roots);
    let required = fixture
        .executor
        .datatype_array_field_required_terms()
        .expect("the augmented authored query remains bounded");
    assert!(required.contains(&app) && required.contains(&read));
    assert!(fixture
        .executor
        .authenticated_datatype_array_field_classes(&fixture.model)
        .is_none());
}

mod certificate_lifecycle;
mod extensionality_roots;
mod projection;
