// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `finite_quantifiers` to preserve test FQNs.

fn compound_endpoint_forall(
    terms: &mut TermStore,
    index: TermId,
    endpoint: TermId,
    property: TermId,
) -> TermId {
    let sort = terms.sort(index).clone();
    let guard = app(terms, "bvult", &[index, endpoint], Sort::Bool);
    let body = app(terms, "=>", &[guard, property], Sort::Bool);
    terms.mk_forall(vec![("i".to_string(), sort)], body)
}

fn compound_endpoint_vec_sort() -> Sort {
    Sort::Datatype(DatatypeSort::new(
        "RangeVec",
        vec![DatatypeConstructor::new(
            "mkRangeVec",
            vec![
                DatatypeField::new("fld_len", Sort::bitvec(64)),
                DatatypeField::new("fld_data", Sort::array(Sort::bitvec(64), Sort::Int)),
            ],
        )],
    ))
}

fn compound_endpoint_vec_value(len: u64, data: ModelValue) -> ModelValue {
    ModelValue::Datatype {
        ctor: "mkRangeVec".to_string(),
        args: vec![ModelValue::bitvec(BigInt::from(len), 64), data],
    }
}

#[test]
fn finite_quantifier_compound_subslice_bounds_preserve_the_excluded_endpoint() {
    let mut terms = TermStore::new();
    let sort = Sort::bitvec(64);
    let i = terms.mk_var("i", sort.clone());
    let start = terms.mk_var("start", sort.clone());
    let end = terms.mk_var("end", sort.clone());
    let one = terms.mk_bitvec(int(1), 64);
    let length = app(&mut terms, "bvsub", &[end, start], sort.clone());
    let inclusive = app(&mut terms, "bvadd", &[length, one], sort.clone());
    let array = terms.mk_var("data", Sort::array(sort.clone(), Sort::Int));
    let index = app(&mut terms, "bvadd", &[start, i], sort);
    let read = app(&mut terms, "select", &[array, index], Sort::Int);
    let zero = terms.mk_int(int(0));
    let property = app(&mut terms, "=", &[read, zero], Sort::Bool);
    let exclusive = compound_endpoint_forall(&mut terms, i, length, property);
    let inclusive = compound_endpoint_forall(&mut terms, i, inclusive, property);
    let model = StubModel::new()
        .with(start, ModelValue::bitvec(int(5), 64))
        .with(end, ModelValue::bitvec(int(8), 64))
        .with(
            array,
            ModelValue::Array(Box::new(ArrayValue {
                default: ModelValue::Int(int(0)),
                store: vec![(ModelValue::bitvec(int(8), 64), ModelValue::Int(int(1)))],
            })),
        );
    assert_confirmed(&verdict(&terms, &model, &[exclusive]));
    assert_violates(&verdict(&terms, &model, &[inclusive]));
}

#[test]
fn finite_quantifier_compound_vec_equality_uses_a_typed_selector_length() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::bitvec(64));
    let vector = terms.mk_var("vector", compound_endpoint_vec_sort());
    let length = app(&mut terms, "fld_len", &[vector], Sort::bitvec(64));
    let data = app(
        &mut terms,
        "fld_data",
        &[vector],
        Sort::array(Sort::bitvec(64), Sort::Int),
    );
    let read = app(&mut terms, "select", &[data, i], Sort::Int);
    let seven = terms.mk_int(int(7));
    let equal = app(&mut terms, "=", &[read, seven], Sort::Bool);
    let all = compound_endpoint_forall(&mut terms, i, length, equal);
    let cells = ModelValue::Array(Box::new(ArrayValue {
        default: ModelValue::Int(int(7)),
        store: vec![(ModelValue::bitvec(int(3), 64), ModelValue::Int(int(8)))],
    }));
    let short = StubModel::new().with(vector, compound_endpoint_vec_value(3, cells.clone()));
    let long = StubModel::new().with(vector, compound_endpoint_vec_value(4, cells));
    assert_confirmed(&verdict(&terms, &short, &[all]));
    assert_violates(&verdict(&terms, &long, &[all]));
}

#[test]
fn finite_quantifier_compound_resize_uses_selector_and_arithmetic_endpoints() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::bitvec(64));
    let vector = terms.mk_var("vector", compound_endpoint_vec_sort());
    let old_len = app(&mut terms, "fld_len", &[vector], Sort::bitvec(64));
    let two = terms.mk_bitvec(int(2), 64);
    let new_len = app(&mut terms, "bvadd", &[old_len, two], Sort::bitvec(64));
    let array = terms.mk_var("resized", Sort::array(Sort::bitvec(64), Sort::Int));
    let read = app(&mut terms, "select", &[array, i], Sort::Int);
    let seven = terms.mk_int(int(7));
    let nine = terms.mk_int(int(9));
    let kept = app(&mut terms, "=", &[read, seven], Sort::Bool);
    let filled = app(&mut terms, "=", &[read, nine], Sort::Bool);
    let prefix_guard = app(&mut terms, "bvult", &[i, old_len], Sort::Bool);
    let suffix_guard = finite_quantifier_half_open_guard(&mut terms, i, old_len, new_len);
    let prefix = app(&mut terms, "=>", &[prefix_guard, kept], Sort::Bool);
    let suffix = app(&mut terms, "=>", &[suffix_guard, filled], Sort::Bool);
    let body = app(&mut terms, "and", &[prefix, suffix], Sort::Bool);
    let all = terms.mk_forall(vec![("i".to_string(), Sort::bitvec(64))], body);
    let original = ModelValue::Array(Box::new(ArrayValue {
        default: ModelValue::Int(int(7)),
        store: Vec::new(),
    }));
    let model = StubModel::new().with(vector, compound_endpoint_vec_value(2, original));
    let mut resized = ArrayValue {
        default: ModelValue::Int(int(7)),
        store: vec![
            (ModelValue::bitvec(int(2), 64), ModelValue::Int(int(9))),
            (ModelValue::bitvec(int(3), 64), ModelValue::Int(int(9))),
            (ModelValue::bitvec(int(4), 64), ModelValue::Int(int(100))),
        ],
    };
    let good = model.with(array, ModelValue::Array(Box::new(resized.clone())));
    assert_confirmed(&verdict(&terms, &good, &[all]));
    resized
        .store
        .push((ModelValue::bitvec(int(3), 64), ModelValue::Int(int(8))));
    let bad = good.with(array, ModelValue::Array(Box::new(resized)));
    assert_violates(&verdict(&terms, &bad, &[all]));
}

#[test]
fn finite_quantifier_compound_registered_datatype_endpoints_project_structurally() {
    let mut terms = TermStore::new();
    let schema = DatatypeSort::new(
        "Length",
        vec![DatatypeConstructor::new(
            "mkLength",
            vec![DatatypeField::new("length", Sort::bitvec(64))],
        )],
    );
    let vector = terms.mk_var("vector", Sort::Uninterpreted("Length".to_string()));
    let i = terms.mk_var("i", Sort::bitvec(64));
    let length = app(&mut terms, "length", &[vector], Sort::bitvec(64));
    let upper = terms.mk_bitvec(int(3), 64);
    let property = app(&mut terms, "bvult", &[i, upper], Sort::Bool);
    let all = compound_endpoint_forall(&mut terms, i, length, property);
    let model = StubModel::new().with_datatype(schema).with(
        vector,
        ModelValue::Datatype {
            ctor: "mkLength".to_string(),
            args: vec![ModelValue::bitvec(int(3), 64)],
        },
    );
    assert_confirmed(&verdict(&terms, &model, &[all]));
}

#[test]
fn finite_quantifier_compound_selector_retains_valid_registered_datatype_fields() {
    let mut terms = TermStore::new();
    let cell = DatatypeSort::new(
        "Cell",
        vec![DatatypeConstructor::new(
            "mkCell",
            vec![DatatypeField::new("value", Sort::Int)],
        )],
    );
    let container = Sort::Datatype(DatatypeSort::new(
        "Container",
        vec![DatatypeConstructor::new(
            "mkContainer",
            vec![
                DatatypeField::new("fld_len", Sort::bitvec(64)),
                DatatypeField::new("payload", Sort::Uninterpreted("Cell".to_string())),
            ],
        )],
    ));
    let vector = terms.mk_var("vector", container);
    let i = terms.mk_var("i", Sort::bitvec(64));
    let length = app(&mut terms, "fld_len", &[vector], Sort::bitvec(64));
    let no = terms.mk_bool(false);
    let all = compound_endpoint_forall(&mut terms, i, length, no);
    let model = StubModel::new().with_datatype(cell).with(
        vector,
        ModelValue::Datatype {
            ctor: "mkContainer".to_string(),
            args: vec![
                ModelValue::bitvec(int(0), 64),
                ModelValue::Datatype {
                    ctor: "mkCell".to_string(),
                    args: vec![ModelValue::Int(int(7))],
                },
            ],
        },
    );
    assert_confirmed(&verdict(&terms, &model, &[all]));
}

#[test]
fn finite_quantifier_compound_selector_respects_an_outer_datatype_lambda_binding() {
    let mut terms = TermStore::new();
    let sort = Sort::Datatype(DatatypeSort::new(
        "Meta",
        vec![DatatypeConstructor::new(
            "mkMeta",
            vec![DatatypeField::new("fld_len", Sort::bitvec(64))],
        )],
    ));
    let vector = terms.mk_var("vector", sort.clone());
    let i = terms.mk_var("i", Sort::bitvec(64));
    let length = app(&mut terms, "fld_len", &[vector], Sort::bitvec(64));
    let no = terms.mk_bool(false);
    let all = compound_endpoint_forall(&mut terms, i, length, no);
    let lambda = terms.mk_lambda_array(vector, all);
    let zero = terms.mk_bitvec(int(0), 64);
    let one = terms.mk_bitvec(int(1), 64);
    let empty = app(&mut terms, "mkMeta", &[zero], sort.clone());
    let nonempty = app(&mut terms, "mkMeta", &[one], sort);
    let at_empty = app(&mut terms, "select", &[lambda, empty], Sort::Bool);
    let at_nonempty = app(&mut terms, "select", &[lambda, nonempty], Sort::Bool);
    let model = StubModel::new().with(
        vector,
        ModelValue::Datatype {
            ctor: "mkMeta".to_string(),
            args: vec![ModelValue::bitvec(int(100), 64)],
        },
    );
    let evaluator = Evaluator::new(&terms, &model);
    assert!(
        matches!(evaluator.evaluate(length), EvalOutcome::Value(ModelValue::BitVec { value, .. })
        if value == int(100))
    );
    assert!(matches!(
        evaluator.evaluate(at_empty),
        EvalOutcome::Value(ModelValue::Bool(true))
    ));
    assert!(matches!(
        evaluator.evaluate(at_nonempty),
        EvalOutcome::Value(ModelValue::Bool(false))
    ));
}

#[test]
fn finite_quantifier_compound_bv64_and_bv128_endpoints_wrap_before_range_analysis() {
    let mut terms = TermStore::new();
    for width in [64, 128] {
        let sort = Sort::bitvec(width);
        let i = terms.mk_var("i", sort.clone());
        let zero = terms.mk_bitvec(int(0), width);
        let one = terms.mk_bitvec(int(1), width);
        let maximum = terms.mk_bitvec((BigInt::from(1u8) << width) - 1, width);
        let wrapped = app(&mut terms, "bvadd", &[maximum, one], sort.clone());
        let negative = app(&mut terms, "bvsub", &[zero, one], sort.clone());
        let no = terms.mk_bool(false);
        let empty = compound_endpoint_forall(&mut terms, i, wrapped, no);
        let equal = app(&mut terms, "=", &[i, negative], Sort::Bool);
        let at_max = app(&mut terms, "=", &[i, maximum], Sort::Bool);
        let body = app(&mut terms, "and", &[equal, at_max], Sort::Bool);
        let last = terms.mk_exists(vec![("i".to_string(), sort)], body);
        assert_confirmed(&verdict(&terms, &StubModel::new(), &[empty, last]));
    }
}

#[test]
fn finite_quantifier_compound_endpoints_follow_outer_bindings_despite_warm_memo() {
    let mut terms = TermStore::new();
    let sort = Sort::bitvec(64);
    let outer = terms.mk_var("outer", sort.clone());
    let i = terms.mk_var("i", sort.clone());
    let zero = terms.mk_bitvec(int(0), 64);
    let one = terms.mk_bitvec(int(1), 64);
    let two = terms.mk_bitvec(int(2), 64);
    let endpoint = app(&mut terms, "bvadd", &[outer, one], sort.clone());
    let inner_guard = app(&mut terms, "bvult", &[i, endpoint], Sort::Bool);
    let equal = app(&mut terms, "=", &[i, outer], Sort::Bool);
    let inner = app(&mut terms, "and", &[inner_guard, equal], Sort::Bool);
    let inner = terms.mk_exists(vec![("i".to_string(), sort.clone())], inner);
    let outer_guard = finite_quantifier_half_open_guard(&mut terms, outer, zero, two);
    let body = app(&mut terms, "=>", &[outer_guard, inner], Sort::Bool);
    let all = terms.mk_forall(vec![("outer".to_string(), sort)], body);
    let model = StubModel::new().with(outer, ModelValue::bitvec(int(100), 64));
    let evaluator = Evaluator::new(&terms, &model);
    assert!(
        matches!(evaluator.evaluate(endpoint), EvalOutcome::Value(ModelValue::BitVec { value, .. })
        if value == int(101))
    );
    assert!(matches!(
        evaluator.evaluate(all),
        EvalOutcome::Value(ModelValue::Bool(true))
    ));
}

#[test]
fn finite_quantifier_compound_endpoints_reject_same_named_aliases_at_any_depth() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::bitvec(64));
    let alias = terms.mk_fresh_named_var("i", Sort::bitvec(64));
    let one = terms.mk_bitvec(int(1), 64);
    let two = terms.mk_bitvec(int(2), 64);
    let zero = terms.mk_bitvec(int(0), 64);
    let added = app(&mut terms, "bvadd", &[alias, two], Sort::bitvec(64));
    let endpoint = app(&mut terms, "bvsub", &[added, one], Sort::bitvec(64));
    let property = app(&mut terms, "=", &[i, zero], Sort::Bool);
    let all = compound_endpoint_forall(&mut terms, i, endpoint, property);
    let model = StubModel::new().with(alias, ModelValue::bitvec(int(0), 64));
    assert_cannot(&verdict(&terms, &model, &[all]));
}

#[test]
fn finite_quantifier_compound_endpoints_refuse_root_and_nested_projection_overrides() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::bitvec(64));
    let two = terms.mk_bitvec(int(2), 64);
    let three = terms.mk_bitvec(int(3), 64);
    let sum = app(&mut terms, "bvadd", &[two, two], Sort::bitvec(64));
    let nested = app(&mut terms, "bvsub", &[sum, two], Sort::bitvec(64));
    let property = app(&mut terms, "bvult", &[i, three], Sort::Bool);
    for endpoint in [sum, nested] {
        let all = compound_endpoint_forall(&mut terms, i, endpoint, property);
        let model = UfStubModel::new().projection(sum, 0);
        assert_cannot(&verdict(&terms, &model, &[all]));
        let model = UfStubModel::new().projection_error(sum, "stale endpoint projection");
        assert!(
            matches!(evaluate_term(&terms, &model, all), EvalOutcome::Unevaluable(reason)
            if reason.contains("stale endpoint projection"))
        );
    }
}

#[test]
fn finite_quantifier_compound_selector_does_not_override_normal_builtin_dispatch() {
    let mut terms = TermStore::new();
    let datatype = Sort::Datatype(DatatypeSort::new(
        "Odd",
        vec![DatatypeConstructor::new(
            "mkOdd",
            vec![DatatypeField::new("bvnot", Sort::bitvec(64))],
        )],
    ));
    let vector = terms.mk_var("vector", datatype);
    let endpoint = app(&mut terms, "bvnot", &[vector], Sort::bitvec(64));
    let i = terms.mk_var("i", Sort::bitvec(64));
    let no = terms.mk_bool(false);
    let all = compound_endpoint_forall(&mut terms, i, endpoint, no);
    let model = StubModel::new().with(
        vector,
        ModelValue::Datatype {
            ctor: "mkOdd".to_string(),
            args: vec![ModelValue::bitvec(int(0), 64)],
        },
    );
    // Directly projecting the same-spelled field would falsely prove vacuity.
    assert_cannot(&verdict(&terms, &model, &[all]));
}

#[test]
fn finite_quantifier_compound_selector_rejects_opaque_pins_and_prefers_structural_value() {
    let mut terms = TermStore::new();
    let vector = terms.mk_var("vector", compound_endpoint_vec_sort());
    let length = app(&mut terms, "fld_len", &[vector], Sort::bitvec(64));
    let i = terms.mk_var("i", Sort::bitvec(64));
    let no = terms.mk_bool(false);
    let all = compound_endpoint_forall(&mut terms, i, length, no);
    let opaque = UfStubModel::new().uf(length, ModelValue::bitvec(int(0), 64));
    assert_cannot(&verdict(&terms, &opaque, &[all]));
    let data = ModelValue::Array(Box::new(ArrayValue {
        default: ModelValue::Int(int(0)),
        store: Vec::new(),
    }));
    let structural = opaque.leaf(vector, compound_endpoint_vec_value(1, data));
    assert_violates(&verdict(&terms, &structural, &[all]));
}

#[test]
fn finite_quantifier_compound_selector_refuses_malformed_fields_and_wrong_constructors() {
    let mut terms = TermStore::new();
    let sort = Sort::Datatype(DatatypeSort::new(
        "MetaChecked",
        vec![
            DatatypeConstructor::new(
                "withLength",
                vec![DatatypeField::new("fld_len", Sort::bitvec(64))],
            ),
            DatatypeConstructor::unit("withoutLength"),
        ],
    ));
    let vector = terms.mk_var("vector", sort);
    let length = app(&mut terms, "fld_len", &[vector], Sort::bitvec(64));
    let i = terms.mk_var("i", Sort::bitvec(64));
    let no = terms.mk_bool(false);
    let all = compound_endpoint_forall(&mut terms, i, length, no);
    for value in [
        ModelValue::Datatype {
            ctor: "withLength".to_string(),
            args: vec![ModelValue::BitVec {
                width: u32::MAX,
                value: int(0),
            }],
        },
        ModelValue::Datatype {
            ctor: "withLength".to_string(),
            args: Vec::new(),
        },
        ModelValue::Datatype {
            ctor: "withoutLength".to_string(),
            args: Vec::new(),
        },
        ModelValue::Datatype {
            ctor: "foreign".to_string(),
            args: Vec::new(),
        },
    ] {
        let model = UfStubModel::new()
            .leaf(vector, value)
            .uf(length, ModelValue::bitvec(int(0), 64));
        assert_cannot(&verdict(&terms, &model, &[all]));
    }
    let wrong_sort = app(&mut terms, "fld_len", &[vector], Sort::bitvec(128));
    let i = terms.mk_var("i", Sort::bitvec(128));
    let all = compound_endpoint_forall(&mut terms, i, wrong_sort, no);
    let model = StubModel::new().with(
        vector,
        ModelValue::Datatype {
            ctor: "withLength".to_string(),
            args: vec![ModelValue::bitvec(int(0), 64)],
        },
    );
    assert_cannot(&verdict(&terms, &model, &[all]));
}

include!("compound_quantifier_endpoint_limits.rs");
