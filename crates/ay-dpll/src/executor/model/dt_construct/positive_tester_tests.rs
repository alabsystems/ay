// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::datatype_array_fields::{
    normalize_datatype_array_value, SemanticNormalizationBudget, MAX_EXACT_ARRAY_FIELD_TERMS,
};
use super::*;
use ay_frontend::parse;
use num_bigint::BigInt;

fn loaded(input: &str) -> Executor {
    let commands = parse(input).expect("valid SMT-LIB fixture");
    let mut exec = Executor::new();
    for command in &commands {
        assert!(
            exec.execute(command).expect("fixture executes").is_none(),
            "fixture must not contain a query"
        );
    }
    exec
}

fn executed(input: &str) -> (Executor, Vec<String>) {
    let commands = parse(input).expect("valid SMT-LIB fixture");
    let mut exec = Executor::new();
    let mut outputs = Vec::new();
    for command in &commands {
        if let Some(output) = exec.execute(command).expect("fixture executes") {
            outputs.push(output);
        }
    }
    (exec, outputs)
}

fn class_for_term(builder: &DtBuilder<'_>, term: TermId) -> usize {
    let index = *builder.index.get(&term).expect("term is collected");
    builder.class_of[index]
}

fn forced_constructor<'a>(builder: &'a DtBuilder<'_>, root: usize) -> &'a ForcedConstructor {
    builder.info[&root]
        .forced
        .as_ref()
        .expect("class has a fixed constructor tag")
}

fn constructor_app_root(builder: &DtBuilder<'_>) -> usize {
    builder
        .members
        .iter()
        .find_map(|(&root, members)| {
            members
                .iter()
                .any(|&member| matches!(builder.kinds[member], DtTermKind::CtorApp { .. }))
                .then_some(root)
        })
        .expect("fixture has a constructor-application class")
}

fn f_application_values<'a>(exec: &'a Executor, model: &'a Model) -> Vec<(TermId, &'a ModelValue)> {
    let mut values: Vec<_> = model
        .dt_ground
        .iter()
        .filter_map(|(&term, value)| {
            matches!(
                exec.ctx.terms.get(term),
                TermData::App(symbol, _) if symbol.name() == "f"
            )
            .then_some((term, value))
        })
        .collect();
    values.sort_by_key(|(term, _)| term.index());
    values
}

fn assert_distinct_array_values_are_authenticated(exec: &Executor, model: &Model, expected: usize) {
    let values = f_application_values(exec, model);
    assert_eq!(values.len(), expected, "every f application needs a value");
    let mut budget = SemanticNormalizationBudget::new();
    let normalized: HashSet<_> = values
        .iter()
        .map(|(_, value)| {
            normalize_datatype_array_value(value, &mut budget)
                .expect("W6 value has a bounded semantic identity")
        })
        .collect();
    assert_eq!(
        normalized.len(),
        expected,
        "disequal classes need extensionally distinct array-bearing values"
    );
    let authenticated = exec
        .authenticated_datatype_array_field_classes(model)
        .expect("every W6 authority reauthenticates");
    for (term, _) in values {
        assert!(
            authenticated
                .iter()
                .any(|class| class.members.contains_key(&term)),
            "{term:?} is absent from authenticated W6 inventory"
        );
    }
}

#[test]
fn authored_guarded_uf_owner_mints_stamped_array_field_authorization() {
    let exec = loaded(
        r#"
            (declare-datatype U ((mk (g (Array Int Bool)))))
            (declare-fun f (Int) U)
            (assert (is-mk (f 0)))
        "#,
    );
    let application = exec
        .ctx
        .terms
        .term_ids()
        .find(|&term| {
            matches!(exec.ctx.terms.get(term), TermData::App(symbol, _) if symbol.name() == "f")
        })
        .expect("fixture retains the authored UF application");
    let cells = exec
        .authored_datatype_array_construction_cells()
        .expect("authored capability census stays bounded");
    assert!(cells.iter().any(|cell| {
        cell.term == application
            && exec.ctx.terms.entry_stamp(application) == Some(cell.stamp)
            && &cell.cell_sort == exec.ctx.terms.sort(application)
    }));
}

#[test]
fn supplemental_hazardous_owner_cannot_override_without_typed_authorization() {
    let mut exec = loaded(
        r#"
            (declare-datatype U ((mk (g (Array Int Bool)))))
            (assert true)
        "#,
    );
    let generated = exec
        .ctx
        .terms
        .mk_var("generated_u", Sort::Uninterpreted("U".to_string()));
    exec.dt_lazy_splits = Some((Vec::new(), Vec::new()));
    let mut model = Model::empty();
    assert_eq!(
        exec.construct_total_datatype_model(
            &mut model,
            &[generated],
            &DatatypeArrayConstructionAuthorization::Ordinary,
        ),
        0,
        "an arbitrary supplemental hazardous-sort root must not arm W6 construction"
    );
    assert!(model.dt_ground.is_empty());
    assert!(model.dt_array_field_classes.is_empty());
}

#[test]
fn constructor_app_force_outweighs_same_tag_positive_tester() {
    let exec = loaded(
        r#"
            (declare-datatype U ((mk (g (Array Int Bool)))))
            (declare-fun f (Int) U)
            (assert (= (f 0) (mk ((as const (Array Int Bool)) false))))
            (assert (is-mk (f 0)))
            (assert (is-mk (f 1)))
            (assert (distinct (f 0) (f 1)))
        "#,
    );
    let model = Model::empty();
    let mut builder = exec.dt_collect(&model, &[]).expect("fixture collects");
    assert!(builder.force_constructors());

    let exact_root = constructor_app_root(&builder);
    let exact = forced_constructor(&builder, exact_root);
    assert_eq!(exact.ctor, "mk");
    assert_eq!(exact.origin, ConstructorForceOrigin::CtorApp);
    assert!(
        !exact.vary_free_fields,
        "a same-tag tester must not downgrade an exact constructor source"
    );

    let tested_root = builder
        .tester_apps
        .iter()
        .filter(|(_, ctor, _)| ctor == "mk")
        .map(|(_, _, argument)| class_for_term(&builder, *argument))
        .find(|&root| root != exact_root)
        .expect("fixture has a tester-only disequality neighbor");
    let tested = forced_constructor(&builder, tested_root);
    assert_eq!(tested.ctor, "mk");
    assert_eq!(tested.origin, ConstructorForceOrigin::PositiveTester);
    assert!(tested.vary_free_fields);
}

#[test]
fn conflicting_constructor_app_and_positive_tester_fail_closed() {
    let exec = loaded(
        r#"
            (declare-datatype U
                ((mk (g (Array Int Bool)))
                 (other)))
            (declare-const x U)
            (assert (= x (mk ((as const (Array Int Bool)) false))))
            (assert ((_ is other) x))
        "#,
    );
    let model = Model::empty();
    let mut builder = exec.dt_collect(&model, &[]).expect("fixture collects");
    assert!(builder.force_constructors());
    let root = constructor_app_root(&builder);
    let force = forced_constructor(&builder, root);
    assert_eq!(force.ctor, "mk");
    assert_eq!(force.origin, ConstructorForceOrigin::CtorApp);
    assert!(!force.vary_free_fields);
    assert!(builder.info[&root].conflicted);
}

#[test]
fn positive_testers_get_distinct_array_fields_across_repeated_checks() {
    let (exec, outputs) = executed(
        r#"
            (set-logic ALL)
            (declare-datatype U ((mk (g (Array Int Bool)))))
            (declare-fun f (Int) U)
            (assert (is-mk (f 0)))
            (assert (is-mk (f 1)))
            (assert (distinct (f 0) (f 1)))
            (check-sat)
            (check-sat)
        "#,
    );
    assert_eq!(outputs, ["sat", "sat"]);
    assert!(exec.last_model_validated);
    let model = exec.last_model.as_ref().expect("sat retains a model");
    assert_distinct_array_values_are_authenticated(&exec, model, 2);
}

#[test]
fn committed_vec_scalars_do_not_mask_free_data_array_variation() {
    let (exec, outputs) = executed(
        r#"
            (set-logic ALL)
            (declare-datatype VecLike
                ((vec (ptr (_ BitVec 64))
                      (len (_ BitVec 64))
                      (cap (_ BitVec 64))
                      (data (Array (_ BitVec 64) (_ BitVec 32))))))
            (declare-fun f (Int) VecLike)
            (assert (distinct (f 0) (f 1)))
            (assert (= (ptr (f 0)) (_ bv0 64)))
            (assert (= (ptr (f 1)) (_ bv0 64)))
            (assert (= (len (f 0)) (_ bv7 64)))
            (assert (= (len (f 1)) (_ bv7 64)))
            (assert (= (cap (f 0)) (_ bv8 64)))
            (assert (= (cap (f 1)) (_ bv8 64)))
            (check-sat)
        "#,
    );
    assert_eq!(outputs, ["sat"]);
    assert!(exec.last_model_validated);
    let model = exec.last_model.as_ref().expect("sat retains a model");
    assert_distinct_array_values_are_authenticated(&exec, model, 2);
}

#[test]
fn later_unbounded_scalar_survives_finite_field_exhaustion() {
    let (exec, outputs) = executed(
        r#"
            (set-logic ALL)
            (declare-datatype U ((mk (tag (_ BitVec 1)) (n Int))))
            (declare-fun f (Int) U)
            (assert (distinct (f 0) (f 1) (f 2)))
            (check-sat)
        "#,
    );
    assert_eq!(outputs, ["sat"]);
    assert!(exec.last_model_validated);
    let model = exec.last_model.as_ref().expect("sat retains a model");
    let values = f_application_values(&exec, model);
    assert_eq!(values.len(), 3);
    let canonical: HashSet<_> = values
        .iter()
        .map(|(_, value)| dt_canonical_string(value))
        .collect();
    assert_eq!(canonical.len(), 3, "disequal scalar classes collapsed");
}

#[test]
fn multiple_free_finite_arrays_form_one_product_family() {
    let (exec, outputs) = executed(
        r#"
            (set-logic ALL)
            (declare-datatype U
                ((mk (a (Array Bool Bool)) (b (Array Bool Bool)))))
            (declare-fun f (Int) U)
            (assert (distinct (f 0) (f 1) (f 2) (f 3) (f 4)))
            (check-sat)
        "#,
    );
    assert_eq!(outputs, ["sat"]);
    assert!(exec.last_model_validated);
    let model = exec.last_model.as_ref().expect("sat retains a model");
    assert_distinct_array_values_are_authenticated(&exec, model, 5);
}

#[test]
fn unrelated_generated_terms_do_not_consume_exact_field_work() {
    let mut exec = loaded(
        r#"
            (set-logic ALL)
            (declare-datatype U
                ((mk (a (Array Bool Bool)) (b (Array Bool Bool)))))
            (declare-fun f (Int) U)
            (assert (distinct (f 0) (f 1) (f 2) (f 3) (f 4)))
        "#,
    );
    for ordinal in 0..(MAX_EXACT_ARRAY_FIELD_TERMS + 128) {
        let integer = exec.ctx.terms.mk_int(BigInt::from(10_000 + ordinal));
        let _ = exec.ctx.terms.mk_eq(integer, integer);
    }
    assert!(exec.ctx.terms.len() > MAX_EXACT_ARRAY_FIELD_TERMS);
    let check = parse("(check-sat)").expect("check-sat parses");
    let output = exec
        .execute(&check[0])
        .expect("fixture executes")
        .expect("check-sat returns output");
    assert_eq!(output, "sat");
    let model = exec.last_model.as_ref().expect("sat retains a model");
    assert_distinct_array_values_are_authenticated(&exec, model, 5);
}

#[test]
fn equal_exact_constructor_arrays_are_never_repaired_by_variation() {
    let (_, outputs) = executed(
        r#"
            (set-logic ALL)
            (declare-datatype U ((mk (g (Array Int Bool)))))
            (declare-const x U)
            (declare-const y U)
            (assert (= x (mk ((as const (Array Int Bool)) false))))
            (assert (= y (mk ((as const (Array Int Bool)) false))))
            (assert (distinct x y))
            (check-sat)
        "#,
    );
    assert_eq!(outputs, ["unsat"]);
}

#[test]
fn redundant_store_neighbor_gets_an_extensionally_fresh_free_array() {
    let (exec, outputs) = executed(
        r#"
            (set-logic ALL)
            (declare-datatype U ((mk (m (Array Bool Bool)))))
            (declare-const x U)
            (declare-const y U)
            (assert (= x
                (mk (store ((as const (Array Bool Bool)) false) false false))))
            (assert (distinct x y))
            (check-sat)
        "#,
    );
    assert_eq!(outputs, ["sat"]);
    assert!(exec.last_model_validated);
    assert!(exec
        .last_model
        .as_ref()
        .is_some_and(|model| !model.dt_array_field_classes.is_empty()));
}
