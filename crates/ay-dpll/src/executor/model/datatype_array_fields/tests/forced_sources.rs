// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

mod member_closure;
mod source_census;

const FORCED_CONST: &str = "(set-logic ALL)
    (declare-datatype U ((mk (g (Array Int Bool)))))
    (declare-const x U)
    (assert (= x (mk ((as const (Array Int Bool)) true))))
    (check-sat)
    (get-value (x (g x) (select (g x) 0)))";

const FORCED_DEFINITION: &str = "(set-logic ALL)
    (declare-datatype U ((mk (g (Array Int Bool)))))
    (declare-const a (Array Int Bool))
    (declare-const x U)
    (assert (= a ((as const (Array Int Bool)) true)))
    (assert (= x (mk a)))
    (check-sat)
    (get-value (x (g x) (select (g x) 0)))";

const FORCED_ALIAS_DEFINITION: &str = "(set-logic ALL)
    (declare-datatype U ((mk (g (Array Int Bool)))))
    (declare-const a (Array Int Bool))
    (declare-const b (Array Int Bool))
    (declare-const x U)
    (assert (= a b))
    (assert (= b ((as const (Array Int Bool)) true)))
    (assert (= x (mk a)))
    (check-sat)
    (get-value (x (g x) (select (g x) 0)))";

const FORCED_OWNER_ALIAS: &str = "(set-logic ALL)
    (declare-datatype U ((mk (g (Array Int Bool)))))
    (declare-const x U)
    (declare-const y U)
    (assert (= x y))
    (assert (= y (mk ((as const (Array Int Bool)) true))))
    (check-sat)
    (get-value (x (g x) (select (g x) 0)))";

const FORCED_STORE_BASE_DEFINITION: &str = "(set-logic ALL)
    (declare-datatype U ((mk (g (Array Int Bool)))))
    (declare-const b (Array Int Bool))
    (declare-const x U)
    (assert (= b ((as const (Array Int Bool)) false)))
    (assert (= x (mk (store b 0 true))))
    (check-sat)
    (get-value (x (g x) (select (g x) 0)))";

const FORCED_NESTED_STORE_BASE_DEFINITION: &str = "(set-logic ALL)
    (declare-datatype U ((mk (g (Array Int Bool)))))
    (declare-const b (Array Int Bool))
    (declare-const x U)
    (assert (= b ((as const (Array Int Bool)) false)))
    (assert (= x (mk (store (store b 0 true) 1 true))))
    (check-sat)
    (get-value (x (g x) (select (g x) 0) (select (g x) 1)))";

const FORCED_ITE_BASE_DEFINITION: &str = "(set-logic ALL)
    (declare-datatype U ((mk (g (Array Int Bool)))))
    (declare-const b (Array Int Bool))
    (declare-const x U)
    (assert (= b ((as const (Array Int Bool)) false)))
    (assert (= x (mk (ite true (store b 0 true) b))))
    (check-sat)
    (get-value (x (g x) (select (g x) 0)))";

const DIRECT_UF_FORCED_CONST: &str = "(set-logic ALL)
    (declare-datatype U ((mk (g (Array Int Bool)))))
    (declare-fun f (Int) U)
    (declare-const outer (Array Int U))
    (assert (= (f 0) (mk ((as const (Array Int Bool)) true))))
    (assert (= (select outer 0) (f 0)))
    (check-sat)
    (get-value ((g (f 0)) (select (g (f 0)) 0)))";

const DIRECT_UF_NESTED_STORE: &str = "(set-logic ALL)
    (declare-datatype U ((mk (g (Array Int Bool)))))
    (declare-fun f (Int) U)
    (declare-const outer (Array Int U))
    (assert (= (f 0)
               (mk (store (store ((as const (Array Int Bool)) false) 0 true) 1 true))))
    (assert (= (select outer 0) (f 0)))
    (check-sat)
    (get-value ((g (f 0)) (select (g (f 0)) 0) (select (g (f 0)) 1)))";

fn forced_array_source_round_trip(source: &str) -> String {
    let commands = ay_frontend::parse(source).expect("forced source fixture parses");
    let mut executor = Executor::new();
    let outputs = executor
        .execute_all(&commands)
        .expect("forced source fixture executes");
    assert_eq!(outputs.first().map(String::as_str), Some("sat"));
    let values = outputs.get(1).expect("get-value returns the forced fields");
    assert!(
        values.contains("true"),
        "constructor source must not collapse to the false base default: {values}"
    );
    assert!(executor.last_model_validated);
    values.clone()
}

fn assert_forced_array_source_round_trips(source: &str) {
    let values = forced_array_source_round_trip(source);
    assert!(values.contains("true"));
}

fn opaque_completion_source(source: &str, owner: &str) -> String {
    let with_outer = source.replacen(
        "    (declare-const x U)",
        "    (declare-const x U)\n    (declare-const outer (Array Int U))",
        1,
    );
    assert_ne!(with_outer, source, "fixture declares the owner x");
    let rooted = with_outer.replacen(
        "    (check-sat)",
        &format!("    (assert (= (select outer 0) {owner}))\n    (check-sat)"),
        1,
    );
    assert_ne!(rooted, with_outer, "fixture has one check-sat command");
    rooted
}

fn opaque_forced_array_source_for_owner(
    source: &str,
    owner: &str,
) -> (Executor, Model, ArrayValue) {
    let source = opaque_completion_source(source, owner);
    let commands = ay_frontend::parse(&source).expect("opaque forced source fixture parses");
    let mut executor = Executor::new();
    let outputs = executor
        .execute_all(&commands)
        .expect("opaque forced source fixture executes");
    assert_eq!(outputs.first().map(String::as_str), Some("sat"));
    assert!(executor
        .forced_datatype_array_support()
        .is_some_and(|support| !support.roots.is_empty() && !support.carrier_terms.is_empty()));
    let model = executor.last_model.clone().expect("sat retains model");
    let classes = executor
        .authenticated_datatype_array_field_classes(&model)
        .expect("opaque completion installs durable source authority");
    assert!(!classes.is_empty());
    let ModelValue::Datatype { args, .. } = &classes[0].value else {
        panic!("forced source class is structured");
    };
    let [ModelValue::Array(array)] = args.as_slice() else {
        panic!("forced source has one array field");
    };
    (executor, model, array.as_ref().clone())
}

fn opaque_forced_array_source(source: &str) -> (Executor, Model, ArrayValue) {
    opaque_forced_array_source_for_owner(source, "x")
}

fn direct_uf_forced_array_source(source: &str) -> ArrayValue {
    let commands = ay_frontend::parse(source).expect("direct UF source fixture parses");
    let mut executor = Executor::new();
    let outputs = executor
        .execute_all(&commands)
        .expect("direct UF source fixture executes");
    assert_eq!(outputs.first().map(String::as_str), Some("sat"));
    assert!(executor
        .forced_datatype_array_support()
        .is_some_and(|support| !support.roots.is_empty() && !support.carrier_terms.is_empty()));
    let model = executor.last_model.as_ref().expect("sat retains model");
    let classes = executor
        .authenticated_datatype_array_field_classes(model)
        .expect("direct UF source installs exact authority");
    let ModelValue::Datatype { args, .. } = &classes
        .first()
        .expect("direct UF source has an authenticated class")
        .value
    else {
        panic!("direct UF source is structured");
    };
    let [ModelValue::Array(array)] = args.as_slice() else {
        panic!("direct UF source has one array field");
    };
    array.as_ref().clone()
}

#[test]
fn exact_const_constructor_array_argument_round_trips() {
    assert_forced_array_source_round_trips(FORCED_CONST);
}

#[test]
fn exact_defined_constructor_array_argument_round_trips() {
    assert_forced_array_source_round_trips(FORCED_DEFINITION);
}

#[test]
fn exact_alias_defined_constructor_array_argument_round_trips() {
    assert_forced_array_source_round_trips(FORCED_ALIAS_DEFINITION);
}

#[test]
fn exact_forced_constructor_owner_alias_round_trips() {
    assert_forced_array_source_round_trips(FORCED_OWNER_ALIAS);
}

#[test]
fn exact_store_over_defined_base_round_trips() {
    let values = forced_array_source_round_trip(FORCED_STORE_BASE_DEFINITION);
    assert!(values.contains("false") && values.contains("true"));
}

#[test]
fn exact_nested_store_over_defined_base_round_trips() {
    let values = forced_array_source_round_trip(FORCED_NESTED_STORE_BASE_DEFINITION);
    assert!(values.contains("false") && values.contains("true"));
}

#[test]
fn exact_ite_over_defined_base_round_trips() {
    let values = forced_array_source_round_trip(FORCED_ITE_BASE_DEFINITION);
    assert!(values.contains("false") && values.contains("true"));
}

#[test]
fn opaque_array_alias_source_installs_exact_authority() {
    let (_, _, array) = opaque_forced_array_source(FORCED_ALIAS_DEFINITION);
    assert!(matches!(array.default, ModelValue::Bool(true)));
}

#[test]
fn opaque_defined_array_source_installs_exact_authority() {
    let (_, _, array) = opaque_forced_array_source(FORCED_DEFINITION);
    assert!(matches!(array.default, ModelValue::Bool(true)));
}

#[test]
fn opaque_datatype_owner_alias_installs_exact_authority() {
    let (_, _, array) = opaque_forced_array_source(FORCED_OWNER_ALIAS);
    assert!(matches!(array.default, ModelValue::Bool(true)));
}

#[test]
fn opaque_defined_middle_owner_installs_exact_authority() {
    let (_, _, array) = opaque_forced_array_source_for_owner(FORCED_OWNER_ALIAS, "y");
    assert!(matches!(array.default, ModelValue::Bool(true)));
}

#[test]
fn opaque_store_source_installs_exact_authority() {
    let (_, _, array) = opaque_forced_array_source(FORCED_STORE_BASE_DEFINITION);
    assert!(matches!(array.default, ModelValue::Bool(false)));
    assert_eq!(array.store.len(), 1);
}

#[test]
fn opaque_nested_store_source_installs_exact_authority() {
    let (_, _, array) = opaque_forced_array_source(FORCED_NESTED_STORE_BASE_DEFINITION);
    assert!(matches!(array.default, ModelValue::Bool(false)));
    assert_eq!(array.store.len(), 2);
}

#[test]
fn opaque_ite_source_installs_exact_authority() {
    let (_, _, array) = opaque_forced_array_source(FORCED_ITE_BASE_DEFINITION);
    assert!(matches!(array.default, ModelValue::Bool(false)));
    assert_eq!(array.store.len(), 1);
}

#[test]
fn direct_uf_owner_const_source_installs_exact_authority() {
    let array = direct_uf_forced_array_source(DIRECT_UF_FORCED_CONST);
    assert!(matches!(array.default, ModelValue::Bool(true)));
    assert!(array.store.is_empty());
}

#[test]
fn direct_uf_owner_nested_store_installs_exact_authority() {
    let array = direct_uf_forced_array_source(DIRECT_UF_NESTED_STORE);
    assert!(matches!(array.default, ModelValue::Bool(false)));
    assert_eq!(array.store.len(), 2);
}

#[test]
fn retained_constructor_source_revokes_tampered_ground_value() {
    let (executor, mut model, _) = opaque_forced_array_source(FORCED_CONST);
    let members: Vec<_> = model
        .dt_array_field_classes
        .first()
        .expect("forced source has authority")
        .members
        .keys()
        .copied()
        .collect();
    for member in members {
        let ModelValue::Datatype { args, .. } = model
            .dt_ground
            .get_mut(&member)
            .expect("authority member has ground value")
        else {
            panic!("forced source value is structured");
        };
        args[0] = ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Bool(false),
            store: Vec::new(),
        }));
    }
    assert!(executor
        .authenticated_datatype_array_field_classes(&model)
        .is_none());
}

#[test]
fn competing_hard_array_definitions_mint_no_forced_support() {
    let commands = ay_frontend::parse(
        "(set-logic ALL)
         (declare-datatype U ((mk (g (Array Int Bool)))))
         (declare-const a (Array Int Bool))
         (declare-const b (Array Int Bool))
         (declare-const x U)
         (assert (= a ((as const (Array Int Bool)) false)))
         (assert (= a b))
         (assert (= b ((as const (Array Int Bool)) true)))
         (assert (= x (mk a)))",
    )
    .expect("competing source fixture parses");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("competing source declarations execute");
    assert!(executor
        .forced_datatype_array_support()
        .is_none_or(|support| support.roots.is_empty() && support.carrier_terms.is_empty()));
}

#[test]
fn component_sources_cannot_hide_aliases_in_scalar_children() {
    for source in [
        "(set-logic ALL)
         (declare-datatype U ((mk (g (Array Int Bool)))))
         (declare-const a (Array Int Bool))
         (declare-const b (Array Int Bool))
         (declare-const c (Array Int Bool))
         (declare-const x U)
         (assert (= a b))
         (assert (= b (store c 0 (select a 1))))
         (assert (= c ((as const (Array Int Bool)) false)))
         (assert (= x (mk b)))",
        "(set-logic ALL)
         (declare-datatype U ((mk (g (Array Int Bool)))))
         (declare-fun p ((Array Int Bool)) Bool)
         (declare-const a (Array Int Bool))
         (declare-const b (Array Int Bool))
         (declare-const x U)
         (assert (= a b))
         (assert (= b (ite (p a)
                           ((as const (Array Int Bool)) false)
                           ((as const (Array Int Bool)) true))))
         (assert (= x (mk b)))",
    ] {
        let commands = ay_frontend::parse(source).expect("hidden dependency fixture parses");
        let mut executor = Executor::new();
        executor
            .execute_all(&commands)
            .expect("hidden dependency declarations execute");
        assert!(executor
            .forced_datatype_array_support()
            .is_none_or(|support| support.roots.is_empty() && support.carrier_terms.is_empty()));
    }
}

#[test]
fn nonconjunctive_constructor_equality_mints_no_forced_support() {
    let commands = ay_frontend::parse(
        "(set-logic ALL)
         (declare-datatype U ((mk (g (Array Int Bool)))))
         (declare-const x U)
         (declare-const q Bool)
         (assert (or (= x (mk ((as const (Array Int Bool)) true))) q))",
    )
    .expect("nonconjunctive source fixture parses");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("nonconjunctive source declarations execute");
    assert!(executor
        .forced_datatype_array_support()
        .is_none_or(|support| support.roots.is_empty() && support.carrier_terms.is_empty()));
}

#[test]
fn complete_array_model_leaf_is_charged_once_per_row() {
    let commands = ay_frontend::parse(
        "(set-logic ALL)
         (declare-const a (Array Int Bool))
         (assert (= (select a 0) false))
         (check-sat)",
    )
    .expect("array leaf fixture parses");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("array leaf fixture executes");
    let array = executor
        .ctx
        .terms
        .term_ids()
        .find(|&term| matches!(executor.ctx.terms.get(term), TermData::Var(name, _) if name == "a"))
        .expect("fixture retains a");
    let mut model = executor.last_model.clone().expect("sat retains model");
    let interp = model
        .array_model
        .get_or_insert_with(Default::default)
        .array_values
        .entry(array)
        .or_default();
    interp.default = Some("false".to_string());
    interp.index_sort = Some(Sort::Int);
    interp.element_sort = Some(Sort::Bool);
    interp.stores = (0..511)
        .map(|index| (index.to_string(), "true".to_string()))
        .collect();
    let mut work = 0;
    let mut budget = TypedArrayParseBudget::new();
    let sort = ArraySort {
        index_sort: Sort::Int,
        element_sort: Sort::Bool,
    };
    assert!(executor
        .exact_constructor_array_source(&model, array, &sort, &mut work, &mut budget)
        .is_some());
    assert!(work < 600, "rows must not be multiply charged: {work}");

    model
        .array_model
        .as_mut()
        .and_then(|arrays| arrays.array_values.get_mut(&array))
        .expect("array row remains installed")
        .stores
        .push(("511".to_string(), "true".to_string()));
    let mut rejected_work = 0;
    let mut rejected_budget = TypedArrayParseBudget::new();
    assert!(executor
        .exact_constructor_array_source(
            &model,
            array,
            &sort,
            &mut rejected_work,
            &mut rejected_budget,
        )
        .is_none());
}
