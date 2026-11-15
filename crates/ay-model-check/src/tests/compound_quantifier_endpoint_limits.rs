// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `compound_quantifier_endpoints` to preserve test FQNs.

#[test]
fn finite_quantifier_compound_validates_model_width_before_arithmetic_normalization() {
    let mut terms = TermStore::new();
    let sort = Sort::bitvec(64);
    let i = terms.mk_var("i", sort.clone());
    let length = terms.mk_var("length", sort.clone());
    let one = terms.mk_bitvec(int(1), 64);
    let endpoint = app(&mut terms, "bvadd", &[length, one], sort);
    let no = terms.mk_bool(false);
    let all = compound_endpoint_forall(&mut terms, i, endpoint, no);
    for value in [
        ModelValue::BitVec {
            width: u32::MAX,
            value: int(0),
        },
        ModelValue::BitVec {
            width: 64,
            value: BigInt::from(1u8) << 65usize,
        },
        ModelValue::BitVec {
            width: 64,
            value: int(-1),
        },
        ModelValue::Int(int(0)),
    ] {
        let model = StubModel::new().with(length, value);
        assert_cannot(&verdict(&terms, &model, &[all]));
    }
}

#[test]
fn finite_quantifier_compound_depth_cap_accepts_64_and_rejects_65() {
    let mut terms = TermStore::new();
    let sort = Sort::bitvec(64);
    let i = terms.mk_var("i", sort.clone());
    let zero = terms.mk_bitvec(int(0), 64);
    let no = terms.mk_bool(false);
    let mut endpoint = zero;
    for _ in 0..64 {
        endpoint = app(&mut terms, "bvadd", &[endpoint, zero], sort.clone());
    }
    let at_limit = compound_endpoint_forall(&mut terms, i, endpoint, no);
    endpoint = app(&mut terms, "bvadd", &[endpoint, zero], sort);
    let over_limit = compound_endpoint_forall(&mut terms, i, endpoint, no);
    let model = StubModel::new();
    let evaluator = Evaluator::new(&terms, &model);
    assert!(
        matches!(evaluator.evaluate(over_limit), EvalOutcome::Unevaluable(reason)
        if reason.contains("nesting or native evaluation depth"))
    );
    assert!(matches!(
        evaluator.evaluate(at_limit),
        EvalOutcome::Value(ModelValue::Bool(true))
    ));
}

#[test]
fn finite_quantifier_compound_shared_dag_work_is_charged_before_vacuity() {
    let mut terms = TermStore::new();
    let sort = Sort::bitvec(64);
    let i = terms.mk_var("i", sort.clone());
    let no = terms.mk_bool(false);
    let mut endpoint = terms.mk_bitvec(int(0), 64);
    for _ in 0..20 {
        endpoint = app(&mut terms, "bvadd", &[endpoint, endpoint], sort.clone());
    }
    let all = compound_endpoint_forall(&mut terms, i, endpoint, no);
    assert!(
        matches!(evaluate_term(&terms, &StubModel::new(), all), EvalOutcome::Unevaluable(reason)
        if reason.contains("evaluation work budget"))
    );
}

#[test]
fn finite_quantifier_compound_selector_preflights_schema_depth_before_model_lookup() {
    let mut terms = TermStore::new();
    let mut payload_sort = Sort::Int;
    for _ in 0..65 {
        payload_sort = Sort::array(Sort::Bool, payload_sort);
    }
    let datatype = Sort::Datatype(DatatypeSort::new(
        "Deep",
        vec![DatatypeConstructor::new(
            "mkDeep",
            vec![
                DatatypeField::new("fld_len", Sort::bitvec(64)),
                DatatypeField::new("payload", payload_sort),
            ],
        )],
    ));
    let vector = terms.mk_var("vector", datatype);
    let length = app(&mut terms, "fld_len", &[vector], Sort::bitvec(64));
    let i = terms.mk_var("i", Sort::bitvec(64));
    let no = terms.mk_bool(false);
    let all = compound_endpoint_forall(&mut terms, i, length, no);
    assert!(
        matches!(evaluate_term(&terms, &StubModel::new(), all), EvalOutcome::Unevaluable(reason)
        if reason.contains("nesting or native evaluation depth"))
    );
}

#[test]
fn finite_quantifier_compound_selector_preflights_nested_registry_cycles_before_value_lookup() {
    struct RegistryOnly {
        definition: DatatypeSort,
        leaf_calls: Cell<usize>,
    }
    impl ModelView for RegistryOnly {
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            self.leaf_calls.set(self.leaf_calls.get() + 1);
            None
        }
        fn datatype_def(&self, name: &str) -> Option<DatatypeSort> {
            (name == self.definition.name).then(|| self.definition.clone())
        }
    }
    let mut terms = TermStore::new();
    let cycle_sort = Sort::Uninterpreted("Cycle".to_string());
    let model = RegistryOnly {
        definition: DatatypeSort::new(
            "Cycle",
            vec![DatatypeConstructor::new(
                "link",
                vec![DatatypeField::new("next", cycle_sort.clone())],
            )],
        ),
        leaf_calls: Cell::new(0),
    };
    let datatype = Sort::Datatype(DatatypeSort::new(
        "Outer",
        vec![DatatypeConstructor::new(
            "mkOuter",
            vec![
                DatatypeField::new("fld_len", Sort::bitvec(64)),
                DatatypeField::new("payload", cycle_sort),
            ],
        )],
    ));
    let vector = terms.mk_var("vector", datatype);
    let i = terms.mk_var("i", Sort::bitvec(64));
    let length = app(&mut terms, "fld_len", &[vector], Sort::bitvec(64));
    let no = terms.mk_bool(false);
    let all = compound_endpoint_forall(&mut terms, i, length, no);
    assert!(
        matches!(evaluate_term(&terms, &model, all), EvalOutcome::Unevaluable(reason)
        if reason.contains("nesting or native evaluation depth"))
    );
    assert_eq!(model.leaf_calls.get(), 0);
}

#[test]
fn finite_quantifier_compound_grammar_keeps_int_multiplication_and_indexed_ops_closed() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    let two = terms.mk_int(int(2));
    let product = app(&mut terms, "*", &[two, two], Sort::Int);
    let added = app(&mut terms, "+", &[two, two], Sort::Int);
    for endpoint in [product, added] {
        let body = app(&mut terms, "=", &[i, endpoint], Sort::Bool);
        let some = terms.mk_exists(vec![("i".to_string(), Sort::Int)], body);
        // The equality-only planner (#eq-only-quantifier-eval) decides the
        // bare form EXACTLY — `∃i. i = e` holds for every `e` — by
        // evaluating `e` itself, not by admitting it as a range endpoint.
        assert_confirmed(&verdict(&terms, &StubModel::new(), &[some]));
        // A non-equality occurrence keeps that planner out; the guarded-range
        // grammar must still refuse the compound endpoint.
        let bound = app(&mut terms, "<=", &[i, endpoint], Sort::Bool);
        let guarded = app(&mut terms, "and", &[body, bound], Sort::Bool);
        let some = terms.mk_exists(vec![("i".to_string(), Sort::Int)], guarded);
        assert_cannot(&verdict(&terms, &StubModel::new(), &[some]));
    }
    let i = terms.mk_var("i", Sort::bitvec(64));
    let two = terms.mk_bitvec(int(2), 64);
    let indexed = terms.mk_app(
        Symbol::indexed("zero_extend", vec![0]),
        &[two],
        Sort::bitvec(64),
    );
    let body = app(&mut terms, "=", &[i, indexed], Sort::Bool);
    let some = terms.mk_exists(vec![("i".to_string(), Sort::bitvec(64))], body);
    assert_cannot(&verdict(&terms, &StubModel::new(), &[some]));
}
