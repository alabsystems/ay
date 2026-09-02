// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn array_equality_normalizes_redundant_and_shadowed_stores() {
    let canonical = ArrayValue {
        default: ModelValue::Bool(false),
        store: vec![(int(1), ModelValue::Bool(true))],
    };
    let redundant = ArrayValue {
        default: ModelValue::Bool(false),
        store: vec![
            (int(2), ModelValue::Bool(false)),
            (int(1), ModelValue::Bool(false)),
            (int(1), ModelValue::Bool(true)),
        ],
    };
    assert!(same_array_value(&canonical, &redundant));
    let conflicting = ArrayValue {
        default: ModelValue::Bool(false),
        store: vec![(int(1), ModelValue::Bool(false))],
    };
    assert!(!same_array_value(&canonical, &conflicting));
    let changed_default = ArrayValue {
        default: ModelValue::Bool(true),
        store: vec![(int(1), ModelValue::Bool(true))],
    };
    assert!(!same_array_value(&canonical, &changed_default));

    let canonical_dt = ModelValue::Datatype {
        ctor: "mk".to_string(),
        args: vec![ModelValue::Array(Box::new(canonical))],
    };
    let redundant_dt = ModelValue::Datatype {
        ctor: "mk".to_string(),
        args: vec![ModelValue::Array(Box::new(redundant))],
    };
    assert!(same_datatype_array_value(&canonical_dt, &redundant_dt));
}

#[test]
fn borrowed_array_sort_is_bounded_before_clone_and_render() {
    let mut oversized = SchemaSourceBudget::new();
    let oversized_name = Sort::Uninterpreted("x".repeat(257));
    assert!(!oversized.charge_array_sort(&oversized_name, &Sort::Bool));
    let (executor, _) = array_field_parser_fixture();
    assert!(executor
        .independent_array_text_value_for_test(
            &Model::empty(),
            "((as const (Array TooLarge Bool)) false)",
            &oversized_name,
            &Sort::Bool,
        )
        .is_none());

    let mut over_depth_sort = Sort::Bool;
    for _ in 0..=super::super::super::rendered_dt_limits::MAX_RENDERED_DT_DEPTH {
        over_depth_sort = Sort::array(Sort::Bool, over_depth_sort);
    }
    let mut over_depth = SchemaSourceBudget::new();
    assert!(!over_depth.charge_array_sort(&Sort::Int, &over_depth_sort));
}

#[test]
fn recursive_datatype_array_hazard_fails_closed() {
    let commands = ay_frontend::parse(
        "(set-logic ALL)\
         (declare-datatype Inner ((inner (payload (Array Int Bool)))))\
         (declare-datatype Outer ((outer (nested Inner))))",
    )
    .expect("nested hazard fixture parses");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("nested hazard fixture executes");
    assert!(executor.datatype_sort_carries_array_field(&Sort::Uninterpreted("Outer".to_string())));

    let inline = Sort::Datatype(ay_core::DatatypeSort::new(
        "Inline",
        vec![ay_core::DatatypeConstructor::new(
            "inline",
            vec![ay_core::DatatypeField::new(
                "payload",
                Sort::array(Sort::Int, Sort::Bool),
            )],
        )],
    ));
    assert!(executor.datatype_sort_carries_array_field(&inline));

    let divergent_inline = Sort::Datatype(ay_core::DatatypeSort::new(
        "Inner",
        vec![ay_core::DatatypeConstructor::new("inline-safe", Vec::new())],
    ));
    assert!(
        executor.datatype_sort_carries_array_field(&divergent_inline),
        "the same-name registered array schema remains hazardous"
    );
}

#[test]
fn unbounded_hazard_schema_cannot_mint_empty_completion_capability() {
    let datatype = format!("W6{}", "x".repeat(300));
    let selector = format!("w6{}", "y".repeat(300));
    let source = format!(
        "(set-logic ALL) (declare-datatype {datatype} ((mk ({selector} (Array Int Bool)))))"
    );
    let commands = ay_frontend::parse(&source).expect("oversized schema fixture parses");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("oversized schema declaration executes");
    let outer_sort = ArraySort::new(Sort::Int, Sort::Uninterpreted(datatype));
    assert!(executor.datatype_sort_carries_array_field(&outer_sort.element_sort));
    assert!(executor
        .authenticated_datatype_array_completion_members(&Model::empty(), &outer_sort)
        .is_none());
}

#[test]
fn authored_source_roots_own_array_field_reads_after_preprocessing() {
    let commands = ay_frontend::parse(
        "(set-logic ALL)\
         (declare-datatype ArrayCell ((mk (field (Array Int Bool)))))\
         (declare-const cell ArrayCell)\
         (assert (= (select (field cell) 0) true))",
    )
    .expect("source-root fixture parses");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("source-root fixture executes");
    let authored = executor.ctx.assertions.clone();
    let read = executor
        .ctx
        .terms
        .term_ids()
        .find(|&term| {
            matches!(executor.ctx.terms.get(term), TermData::App(symbol, args)
                if symbol.name() == "select" && args.len() == 2)
        })
        .expect("fixture contains the authored field read");
    executor.independent_gate_authored_assertions = Some(authored);
    let trivial = executor.ctx.terms.true_term();
    executor.ctx.assertions = vec![trivial];
    assert!(!executor.term_is_required_by_last_query(read));
    assert!(executor
        .datatype_array_field_required_terms()
        .is_some_and(|terms| terms.contains(&read)));
}

#[test]
fn whole_array_equalities_are_not_field_reads_in_either_operand_order() {
    let (mut executor, cell_sort) = array_field_parser_fixture();
    let array_sort = Sort::array(Sort::Int, Sort::Bool);
    let cell = executor.ctx.terms.mk_var("w6-equality-cell", cell_sort);
    let field = executor
        .ctx
        .terms
        .mk_app(Symbol::named("field"), [cell], array_sort.clone());
    let whole = executor.ctx.terms.mk_var("w6-whole-array", array_sort);
    // Use raw applications so both source operand orders survive the term
    // store's normal equality canonicalization.
    let field_first = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), [field, whole], Sort::Bool);
    let field_second = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), [whole, field], Sort::Bool);
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let read = executor.ctx.terms.mk_select(field, zero);

    for equality in [field_first, field_second] {
        let required_terms = [equality].into_iter().collect();
        assert!(executor
            .exact_array_field_reads(field, &required_terms)
            .is_empty());
    }

    let required_terms = [field_first, field_second, read].into_iter().collect();
    assert_eq!(
        executor.exact_array_field_reads(field, &required_terms),
        [read]
    );
}

#[test]
fn typed_array_rejects_noncanonical_bitvector_payloads() {
    let sort = ArraySort::new(Sort::Int, Sort::bitvec(3));
    let negative = ArrayValue {
        default: ModelValue::BitVec {
            width: 3,
            value: BigInt::from(-1),
        },
        store: Vec::new(),
    };
    let out_of_range = ArrayValue {
        default: ModelValue::BitVec {
            width: 3,
            value: BigInt::from(8),
        },
        store: Vec::new(),
    };
    let canonical = ArrayValue {
        default: ModelValue::BitVec {
            width: 3,
            value: BigInt::from(7),
        },
        store: Vec::new(),
    };
    assert!(!typed_array_value(&negative, &sort));
    assert!(!typed_array_value(&out_of_range, &sort));
    assert!(typed_array_value(&canonical, &sort));
}

#[test]
fn no_app_selector_scans_share_one_many_field_work_cap() {
    let commands = ay_frontend::parse(
        "(set-logic ALL)\
         (declare-datatype Cell ((mk (g (Array Int Bool)))))",
    )
    .expect("scan-budget fixture parses");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("scan-budget declarations execute");
    let cell_sort = Sort::Uninterpreted("Cell".to_string());
    let cell = executor.ctx.terms.mk_var("w6-scan-cell", cell_sort.clone());
    let carrier = "@U!0".to_string();
    let mut model = Model::empty();
    let mut euf = ay_euf::EufModel::default();
    euf.term_values.insert(cell, carrier.clone());
    model.euf_model = Some(euf);
    let class = ExactClass {
        cell_sort,
        carrier,
        members: [cell].into_iter().collect(),
        fields: vec![(0, "g".to_string(), Sort::array(Sort::Int, Sort::Bool))],
    };
    let required_terms: HashSet<_> = executor.ctx.terms.term_ids().collect();
    let scan_cost = required_terms.len();
    assert!(scan_cost > 0);
    let complete_scans = MAX_EXACT_ARRAY_FIELD_TERMS / scan_cost;
    let mut work = 0;
    for _ in 0..complete_scans {
        assert_eq!(
            executor
                .selector_apps(
                    &model,
                    &class,
                    "g",
                    &class.fields[0].2,
                    &required_terms,
                    &mut work,
                )
                .expect("a scan within the aggregate cap succeeds")
                .len(),
            0
        );
    }
    assert!(executor
        .selector_apps(
            &model,
            &class,
            "g",
            &class.fields[0].2,
            &required_terms,
            &mut work,
        )
        .is_none());
}
