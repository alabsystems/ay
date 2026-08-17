// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array-select evaluation tests.

use super::*;

#[test]
fn test_evaluate_select_matches_array_store_with_lia_index_value() {
    let mut executor = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = executor.ctx.terms.mk_var("a", array_sort);
    let i = executor.ctx.terms.mk_var("i", Sort::Int);
    let select = executor.ctx.terms.mk_select(a, i);

    let mut lia_values = HashMap::default();
    lia_values.insert(i, BigInt::from(5));

    let mut array_values = HashMap::default();
    array_values.insert(
        a,
        ay_arrays::ArrayInterpretation {
            default: None,
            stores: vec![("5".to_string(), "42".to_string())],
            index_sort: Some(Sort::Int),
            element_sort: Some(Sort::Int),
        },
    );

    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });
    model.array_model = Some(ArrayModel {
        array_values,
        ..Default::default()
    });

    assert_eq!(
        executor.evaluate_term(&model, select),
        EvalValue::Rational(BigRational::from(BigInt::from(42)))
    );
}

#[test]
fn test_evaluate_select_matches_array_store_with_lra_and_merged_euf_index_value() {
    let mut executor = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Real);
    let a = executor.ctx.terms.mk_var("a", array_sort);
    let i = executor.ctx.terms.mk_var("i", Sort::Int);
    let select = executor.ctx.terms.mk_select(a, i);

    let mut term_values = HashMap::default();
    term_values.insert(i, "3".to_string());

    let mut array_values = HashMap::default();
    array_values.insert(
        a,
        ay_arrays::ArrayInterpretation {
            default: None,
            stores: vec![("3".to_string(), "(/ 7 2)".to_string())],
            index_sort: Some(Sort::Int),
            element_sort: Some(Sort::Real),
        },
    );

    let mut model = empty_model();
    model.lra_model = Some(LraModel {
        values: HashMap::default(),
    });
    model.euf_model = Some(EufModel {
        term_values,
        ..Default::default()
    });
    model.array_model = Some(ArrayModel {
        array_values,
        ..Default::default()
    });

    assert_eq!(
        executor.evaluate_term(&model, select),
        EvalValue::Rational(BigRational::new(BigInt::from(7), BigInt::from(2)))
    );
}
