// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ==========================================================================
// evaluate_term: theory predicates
// ==========================================================================

#[test]
fn test_evaluate_symbolic_array_default_from_materialized_model() {
    let mut executor = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = executor.ctx.terms.mk_var("a", array_sort);
    let default = executor
        .ctx
        .terms
        .mk_app(Symbol::named("default"), vec![a], Sort::Int);

    let mut model = empty_model();
    model.array_model = Some(ArrayModel {
        array_values: HashMap::from_iter([(
            a,
            ay_arrays::ArrayInterpretation {
                default: Some("5".to_string()),
                stores: vec![],
                index_sort: Some(Sort::Int),
                element_sort: Some(Sort::Int),
            },
        )]),
        ..Default::default()
    });

    assert_eq!(
        executor.evaluate_term(&model, default),
        EvalValue::Rational(BigRational::from(BigInt::from(5)))
    );
}

#[test]
fn test_materialize_symbolic_bool_array_default_from_sat_model() {
    let mut executor = Executor::new();
    let a = executor
        .ctx
        .terms
        .mk_var("a", Sort::array(Sort::Int, Sort::Bool));
    let default = executor.ctx.terms.mk_array_default(a);
    executor.last_model = Some(model_with_sat_assignments(&[(default, true)]));
    executor.last_model_validated = true;

    assert!(executor.materialize_symbolic_array_defaults());
    let interp = executor
        .last_model
        .as_ref()
        .and_then(|model| model.array_model.as_ref())
        .and_then(|arrays| arrays.array_values.get(&a))
        .expect("the Bool default must materialize an array interpretation");
    assert_eq!(interp.default.as_deref(), Some("true"));
    assert_eq!(interp.index_sort.as_ref(), Some(&Sort::Int));
    assert_eq!(interp.element_sort.as_ref(), Some(&Sort::Bool));
    assert!(
        !executor.last_model_validated,
        "materializing the printer-visible model must invalidate stale validation evidence"
    );
}

#[test]
fn test_evaluate_select_beta_reduces_lambda_exposed_below_store() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let body = executor.ctx.terms.mk_add(vec![x, one]);
    let lambda = executor.ctx.terms.mk_lambda_array(x, body);
    let three = executor.ctx.terms.mk_int(BigInt::from(3));
    let five = executor.ctx.terms.mk_int(BigInt::from(5));
    let forty_two = executor.ctx.terms.mk_int(BigInt::from(42));
    let stored = executor.ctx.terms.mk_store(lambda, five, forty_two);

    // Build raw selects so the test exercises model-time store peeling and
    // beta evaluation, not TermStore::mk_select's construction-time rewrite.
    let at_stored =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), vec![stored, five], Sort::Int);
    let at_lambda =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), vec![stored, three], Sort::Int);

    // Give the lambda's syntactic bound Var a conflicting ambient value. The
    // beta binding must override it only while evaluating the lambda body, then
    // restore it afterward.
    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(99));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });

    assert_eq!(
        executor.evaluate_term(&model, at_stored),
        EvalValue::Rational(BigRational::from(BigInt::from(42)))
    );
    assert_eq!(
        executor.evaluate_term(&model, at_lambda),
        EvalValue::Rational(BigRational::from(BigInt::from(4)))
    );
    assert_eq!(
        executor.evaluate_term(&model, body),
        EvalValue::Rational(BigRational::from(BigInt::from(100))),
        "lambda beta binding must be restored after the read"
    );
}

#[test]
fn test_evaluate_select_string_index_preserves_outermost_store() {
    let mut executor = Executor::new();
    let key = executor.ctx.terms.mk_string("key".to_string());
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let forty_one = executor.ctx.terms.mk_int(BigInt::from(41));
    let forty_two = executor.ctx.terms.mk_int(BigInt::from(42));
    let base = executor.ctx.terms.mk_const_array(Sort::String, zero);
    let inner = executor.ctx.terms.mk_store(base, key, forty_one);
    let outer = executor.ctx.terms.mk_store(inner, key, forty_two);

    // Bypass construction-time select rewriting. Model-time ROW1 must compare
    // every concrete EvalValue sort and the newest same-index write must win.
    let select = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![outer, key], Sort::Int);

    assert_eq!(
        executor.evaluate_term(&empty_model(), select),
        EvalValue::Rational(BigRational::from(BigInt::from(42)))
    );
}

#[test]
fn test_lambda_beta_nested_same_term_binding_restores_outer_value() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let three = executor.ctx.terms.mk_int(BigInt::from(3));
    let seven = executor.ctx.terms.mk_int(BigInt::from(7));

    let inner_body = executor.ctx.terms.mk_add(vec![x, one]);
    let inner_lambda = executor.ctx.terms.mk_lambda_array(x, inner_body);
    let inner_select = executor.ctx.terms.mk_app(
        Symbol::named("select"),
        vec![inner_lambda, seven],
        Sort::Int,
    );
    let outer_body = executor.ctx.terms.mk_add(vec![inner_select, x]);
    let outer_lambda = executor.ctx.terms.mk_lambda_array(x, outer_body);
    let outer_select = executor.ctx.terms.mk_app(
        Symbol::named("select"),
        vec![outer_lambda, three],
        Sort::Int,
    );

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(99));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });

    assert_eq!(
        executor.evaluate_term(&model, outer_select),
        EvalValue::Rational(BigRational::from(BigInt::from(11))),
        "the inner x=7 binding must restore the outer x=3 binding"
    );
    assert_eq!(
        executor.evaluate_term(&model, x),
        EvalValue::Rational(BigRational::from(BigInt::from(99))),
        "both nested bindings must restore the ambient model value"
    );
}

#[test]
fn test_lambda_beta_uf_table_uses_bound_argument_value() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let f_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], Sort::Int);
    let lambda = executor.ctx.terms.mk_lambda_array(x, f_x);
    let three = executor.ctx.terms.mk_int(BigInt::from(3));
    let read = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![lambda, three], Sort::Int);

    let mut int_values = HashMap::default();
    int_values.insert(x, BigInt::from(99));
    let mut function_tables = HashMap::default();
    function_tables.insert(
        "f".to_string(),
        vec![
            (vec!["3".to_string()], "7".to_string()),
            (vec!["99".to_string()], "11".to_string()),
        ],
    );
    let mut model = empty_model();
    model.euf_model = Some(EufModel {
        int_values,
        function_tables,
        ..Default::default()
    });

    assert_eq!(
        executor.evaluate_term(&model, read),
        EvalValue::Rational(BigRational::from(BigInt::from(7))),
        "the table key must be f(3), not the ambient f(99) point"
    );
    assert_eq!(
        executor.evaluate_term(&model, f_x),
        EvalValue::Rational(BigRational::from(BigInt::from(11))),
        "the beta binding must be restored before ambient evaluation"
    );
}

#[test]
fn test_scoped_binding_does_not_inherit_dependent_materializer_pin() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let five = executor.ctx.terms.mk_int(BigInt::from(5));
    let dependent = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], Sort::Int);
    let independent = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![five], Sort::Int);
    let seven = EvalValue::Rational(BigRational::from(BigInt::from(7)));
    let nine = EvalValue::Rational(BigRational::from(BigInt::from(9)));
    let mut ambient = HashMap::default();
    ambient.insert(dependent, seven.clone());
    ambient.insert(independent, nine.clone());

    let observations = dt_model::with_dt_field_overrides_for_test(ambient, || {
        let ambient_before = executor.evaluate_term(&empty_model(), dependent);
        let scoped = dt_model::with_scoped_term_override(
            x,
            EvalValue::Rational(BigRational::from(BigInt::from(3))),
            || {
                (
                    executor.evaluate_term(&empty_model(), dependent),
                    executor.evaluate_term(&empty_model(), independent),
                )
            },
        );
        let ambient_after = executor.evaluate_term(&empty_model(), dependent);
        (ambient_before, scoped, ambient_after)
    });

    assert_eq!(observations.0, seven);
    assert_eq!(observations.1 .0, EvalValue::Unknown);
    assert_eq!(observations.1 .1, nine);
    assert_eq!(observations.2, seven);
}

#[test]
fn test_lambda_beta_uf_table_rejects_dependent_entry_placeholder() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let g_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("g"), vec![x], Sort::Int);
    let f_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], Sort::Int);
    let lambda = executor.ctx.terms.mk_lambda_array(x, f_x);
    let three = executor.ctx.terms.mk_int(BigInt::from(3));
    let read = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![lambda, three], Sort::Int);

    let mut int_values = HashMap::default();
    int_values.insert(x, BigInt::from(99));
    int_values.insert(g_x, BigInt::from(3));
    let mut function_tables = HashMap::default();
    function_tables.insert(
        "f".to_string(),
        vec![
            (vec![format!("@?{}", g_x.0)], "13".to_string()),
            (vec!["3".to_string()], "7".to_string()),
            (vec!["99".to_string()], "11".to_string()),
        ],
    );
    let mut model = empty_model();
    model.euf_model = Some(EufModel {
        int_values,
        function_tables,
        ..Default::default()
    });

    assert_eq!(
        executor.evaluate_term(&model, read),
        EvalValue::Rational(BigRational::from(BigInt::from(7))),
        "the ambient g(x)=3 placeholder is not a schema for the beta point"
    );
    assert_eq!(
        executor.evaluate_term(&model, f_x),
        EvalValue::Rational(BigRational::from(BigInt::from(11)))
    );
}

#[test]
fn test_lambda_beta_uf_table_rejects_dependent_result_placeholder() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let h_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("h"), vec![x], Sort::Int);
    let f_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], Sort::Int);
    let lambda = executor.ctx.terms.mk_lambda_array(x, f_x);
    let three = executor.ctx.terms.mk_int(BigInt::from(3));
    let read = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![lambda, three], Sort::Int);

    let mut int_values = HashMap::default();
    int_values.insert(x, BigInt::from(99));
    int_values.insert(h_x, BigInt::from(13));
    let mut function_tables = HashMap::default();
    function_tables.insert(
        "f".to_string(),
        vec![
            (vec!["3".to_string()], format!("@?{}", h_x.0)),
            (vec!["3".to_string()], "7".to_string()),
            (vec!["99".to_string()], "11".to_string()),
        ],
    );
    let mut model = empty_model();
    model.euf_model = Some(EufModel {
        int_values,
        function_tables,
        ..Default::default()
    });

    assert_eq!(
        executor.evaluate_term(&model, read),
        EvalValue::Rational(BigRational::from(BigInt::from(7))),
        "the ambient h(x)=13 result cannot be imported into the beta point"
    );
}

#[test]
fn test_lambda_beta_bv_congruence_rejects_dependent_ambient_candidate() {
    let mut executor = Executor::new();
    let bv8 = Sort::bitvec(8);
    let x = executor.ctx.terms.mk_var("x", bv8.clone());
    let three = executor.ctx.terms.mk_bitvec(BigInt::from(3), 8);
    let f_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], bv8.clone());
    let f_three = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![three], bv8.clone());
    let lambda = executor.ctx.terms.mk_lambda_array(x, f_three);
    let read = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![lambda, three], bv8);

    let mut values = HashMap::default();
    values.insert(x, BigInt::from(99));
    values.insert(f_x, BigInt::from(7));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    assert_eq!(
        executor.evaluate_term(&model, read),
        EvalValue::Unknown,
        "f(x)'s ambient result belongs to x=99, even though x evaluates to 3 in beta"
    );
}

#[test]
fn test_distinct_exact_does_not_treat_nested_unknown_as_disequality() {
    let unknown = EvalValue::Seq(vec![EvalValue::Unknown]);
    let zero = EvalValue::Seq(vec![EvalValue::Rational(BigRational::from(BigInt::from(
        0,
    )))]);
    let one = EvalValue::Seq(vec![EvalValue::Rational(BigRational::from(BigInt::from(
        1,
    )))]);

    assert_eq!(
        Executor::eval_values_distinct_exact(&[unknown, zero.clone()]),
        None
    );
    assert_eq!(
        Executor::eval_values_distinct_exact(&[zero.clone(), zero.clone()]),
        Some(false)
    );
    assert_eq!(
        Executor::eval_values_distinct_exact(&[zero, one]),
        Some(true)
    );
}

#[test]
fn test_ite_branch_split_requires_exact_negative_evidence() {
    let unknown = EvalValue::Seq(vec![EvalValue::Unknown]);
    let zero = EvalValue::Seq(vec![EvalValue::Rational(BigRational::from(BigInt::from(
        0,
    )))]);
    let one = EvalValue::Seq(vec![EvalValue::Rational(BigRational::from(BigInt::from(
        1,
    )))]);
    let two = EvalValue::Seq(vec![EvalValue::Rational(BigRational::from(BigInt::from(
        2,
    )))]);

    assert!(!Executor::ite_branches_definitively_exclude(
        &zero, &unknown, &one
    ));
    assert!(Executor::ite_branches_definitively_exclude(
        &zero, &one, &two
    ));
}

#[test]
fn test_lambda_beta_select_rejects_context_free_term_pin() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let a = executor
        .ctx
        .terms
        .mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let select_a_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![a, x], Sort::Int);
    let lambda = executor.ctx.terms.mk_lambda_array(x, select_a_x);
    let three = executor.ctx.terms.mk_int(BigInt::from(3));
    let read = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![lambda, three], Sort::Int);

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(99));
    lia_values.insert(select_a_x, BigInt::from(7));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });

    assert_eq!(
        executor.evaluate_term(&model, read),
        EvalValue::Unknown,
        "the ambient value of select(a, x) is not the value of select(a, 3)"
    );
    assert_eq!(
        executor.evaluate_term(&model, select_a_x),
        EvalValue::Rational(BigRational::from(BigInt::from(7))),
        "the context-free model pin remains valid outside beta evaluation"
    );
}

#[test]
fn test_lambda_beta_select_rejects_context_free_bv_pin() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let a = executor
        .ctx
        .terms
        .mk_var("a", Sort::array(Sort::Int, Sort::bitvec(8)));
    let select_a_x =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), vec![a, x], Sort::bitvec(8));
    let lambda = executor.ctx.terms.mk_lambda_array(x, select_a_x);
    let three = executor.ctx.terms.mk_int(BigInt::from(3));
    let read = executor.ctx.terms.mk_app(
        Symbol::named("select"),
        vec![lambda, three],
        Sort::bitvec(8),
    );

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(99));
    let mut bv_values = HashMap::default();
    bv_values.insert(select_a_x, BigInt::from(7));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    assert_eq!(
        executor.evaluate_term(&model, read),
        EvalValue::Unknown,
        "the ambient bit-blasted select(a, x) pin is not select(a, 3)"
    );
    assert_eq!(
        executor.evaluate_term(&model, select_a_x),
        EvalValue::BitVec {
            value: BigInt::from(7),
            width: 8,
        }
    );
}

#[test]
fn test_lambda_beta_rejects_context_free_total_model_pin() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let projected = executor
        .ctx
        .terms
        .mk_app(Symbol::named("selector_like"), vec![x], Sort::Int);
    let lambda = executor.ctx.terms.mk_lambda_array(x, projected);
    let three = executor.ctx.terms.mk_int(BigInt::from(3));
    let read = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![lambda, three], Sort::Int);

    let pinned = EvalValue::Rational(BigRational::from(BigInt::from(7)));
    let mut model = empty_model();
    model.dt_pins.insert(projected, pinned.clone());

    assert_eq!(executor.evaluate_term(&model, read), EvalValue::Unknown);
    assert_eq!(
        executor.evaluate_term(&model, projected),
        pinned,
        "the total-model pin remains valid outside beta evaluation"
    );
}

#[test]
fn test_lambda_beta_allows_binder_independent_uf_pin() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let five = executor.ctx.terms.mk_int(BigInt::from(5));
    let f_five = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![five], Sort::Int);
    let lambda = executor.ctx.terms.mk_lambda_array(x, f_five);
    let three = executor.ctx.terms.mk_int(BigInt::from(3));
    let read = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![lambda, three], Sort::Int);

    let mut term_values = HashMap::default();
    term_values.insert(f_five, "7".to_string());
    let mut model = empty_model();
    model.euf_model = Some(EufModel {
        term_values,
        ..Default::default()
    });

    assert_eq!(
        executor.evaluate_term(&model, read),
        EvalValue::Rational(BigRational::from(BigInt::from(7)))
    );
}

#[test]
fn test_lambda_beta_bv_cache_rejects_only_dependent_term_pins() {
    let mut executor = Executor::new();
    let bv8 = Sort::bitvec(8);
    let x = executor.ctx.terms.mk_var("x", bv8.clone());
    let three = executor.ctx.terms.mk_bitvec(BigInt::from(3), 8);
    let one = executor.ctx.terms.mk_bitvec(BigInt::from(1), 8);
    let opaque = executor
        .ctx
        .terms
        .mk_app(Symbol::named("opaque_bv"), vec![], bv8.clone());

    let dependent = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvadd"), vec![x, opaque], bv8.clone());
    let dependent_lambda = executor.ctx.terms.mk_lambda_array(x, dependent);
    let dependent_read = executor.ctx.terms.mk_app(
        Symbol::named("select"),
        vec![dependent_lambda, three],
        bv8.clone(),
    );

    let independent =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("bvadd"), vec![one, opaque], bv8.clone());
    let independent_lambda = executor.ctx.terms.mk_lambda_array(x, independent);
    let independent_read = executor.ctx.terms.mk_app(
        Symbol::named("select"),
        vec![independent_lambda, three],
        bv8,
    );

    let mut values = HashMap::default();
    values.insert(x, BigInt::from(99));
    values.insert(dependent, BigInt::from(7));
    values.insert(independent, BigInt::from(8));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    assert_eq!(
        executor.evaluate_term(&model, dependent_read),
        EvalValue::Unknown,
        "the ambient bvadd(x, opaque) cache entry is not a beta value"
    );
    assert_eq!(
        executor.evaluate_term(&model, independent_read),
        EvalValue::BitVec {
            value: BigInt::from(8),
            width: 8,
        },
        "an unrelated binding must not hide a binder-independent BV pin"
    );
    assert_eq!(
        executor.evaluate_term(&model, dependent),
        EvalValue::BitVec {
            value: BigInt::from(7),
            width: 8,
        }
    );
}

#[test]
fn test_lambda_beta_bv2nat_rejects_only_dependent_lia_fallback() {
    let mut executor = Executor::new();
    let bv8 = Sort::bitvec(8);
    let x = executor.ctx.terms.mk_var("x", bv8.clone());
    let three = executor.ctx.terms.mk_bitvec(BigInt::from(3), 8);
    let five = executor.ctx.terms.mk_bitvec(BigInt::from(5), 8);
    let f_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], bv8.clone());
    let f_five = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![five], bv8);
    let dependent = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bv2nat"), vec![f_x], Sort::Int);
    let independent = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bv2nat"), vec![f_five], Sort::Int);
    let dependent_lambda = executor.ctx.terms.mk_lambda_array(x, dependent);
    let independent_lambda = executor.ctx.terms.mk_lambda_array(x, independent);
    let dependent_read = executor.ctx.terms.mk_app(
        Symbol::named("select"),
        vec![dependent_lambda, three],
        Sort::Int,
    );
    let independent_read = executor.ctx.terms.mk_app(
        Symbol::named("select"),
        vec![independent_lambda, three],
        Sort::Int,
    );

    let mut values = HashMap::default();
    values.insert(dependent, BigInt::from(7));
    values.insert(independent, BigInt::from(9));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values });

    assert_eq!(
        executor.evaluate_term(&model, dependent_read),
        EvalValue::Unknown
    );
    assert_eq!(
        executor.evaluate_term(&model, independent_read),
        EvalValue::Rational(BigRational::from(BigInt::from(9)))
    );
    assert_eq!(
        executor.evaluate_term(&model, dependent),
        EvalValue::Rational(BigRational::from(BigInt::from(7)))
    );
}

#[test]
fn test_scoped_lookup_term_value_rejects_only_dependent_pins() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let five = executor.ctx.terms.mk_int(BigInt::from(5));
    let dependent = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], Sort::Int);
    let independent = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![five], Sort::Int);

    let mut values = HashMap::default();
    values.insert(dependent, BigInt::from(7));
    values.insert(independent, BigInt::from(9));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values });

    let (dependent_scoped, independent_scoped) = dt_model::with_scoped_term_override(
        x,
        EvalValue::Rational(BigRational::from(BigInt::from(3))),
        || {
            (
                executor.lookup_term_value(&model, dependent),
                executor.lookup_term_value(&model, independent),
            )
        },
    );
    assert_eq!(dependent_scoped, EvalValue::Unknown);
    assert_eq!(
        independent_scoped,
        EvalValue::Rational(BigRational::from(BigInt::from(9)))
    );
    assert_eq!(
        executor.lookup_term_value(&model, dependent),
        EvalValue::Rational(BigRational::from(BigInt::from(7)))
    );
}

#[test]
fn test_lambda_beta_fp_pin_rejects_only_dependent_applications() {
    let mut executor = Executor::new();
    let fp16 = Sort::FloatingPoint(5, 11);
    let x = executor.ctx.terms.mk_var("x", fp16.clone());
    let y = executor.ctx.terms.mk_var("y", fp16.clone());
    let zero = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp.zero"), vec![], fp16.clone());
    let dependent = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp.neg"), vec![x], fp16.clone());
    let independent = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp.neg"), vec![y], fp16.clone());
    let dependent_lambda = executor.ctx.terms.mk_lambda_array(x, dependent);
    let independent_lambda = executor.ctx.terms.mk_lambda_array(x, independent);
    let dependent_read = executor.ctx.terms.mk_app(
        Symbol::named("select"),
        vec![dependent_lambda, zero],
        fp16.clone(),
    );
    let independent_read = executor.ctx.terms.mk_app(
        Symbol::named("select"),
        vec![independent_lambda, zero],
        fp16,
    );

    let ambient_x = FpModelValue::NegInf { eb: 5, sb: 11 };
    let pinned_result = FpModelValue::PosInf { eb: 5, sb: 11 };
    let mut values = HashMap::default();
    values.insert(x, ambient_x);
    values.insert(dependent, pinned_result.clone());
    values.insert(independent, pinned_result.clone());
    let mut model = empty_model();
    model.fp_model = Some(FpModel { values });

    assert_eq!(
        executor.evaluate_term(&model, dependent_read),
        EvalValue::Fp(FpModelValue::NegZero { eb: 5, sb: 11 })
    );
    assert_eq!(
        executor.evaluate_term(&model, independent_read),
        EvalValue::Fp(pinned_result.clone()),
        "an unrelated binding must not hide a binder-independent FP pin"
    );
    assert_eq!(
        executor.evaluate_term(&model, dependent),
        EvalValue::Fp(pinned_result)
    );
}

#[test]
fn test_lambda_beta_fp_bitblast_concretizes_bound_value() {
    let mut executor = Executor::new();
    let fp16 = Sort::FloatingPoint(5, 11);
    let x = executor.ctx.terms.mk_var("x", fp16.clone());
    let rtp = executor
        .ctx
        .terms
        .mk_var("RTP", Sort::Uninterpreted("RoundingMode".to_string()));
    let zero = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp.zero"), vec![], fp16.clone());
    let add = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp.add"), vec![rtp, x, zero], fp16.clone());
    let lambda = executor.ctx.terms.mk_lambda_array(x, add);
    let read = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![lambda, zero], fp16);

    let mut values = HashMap::default();
    values.insert(x, FpModelValue::PosInf { eb: 5, sb: 11 });
    let mut model = empty_model();
    model.fp_model = Some(FpModel { values });

    assert_eq!(
        executor.evaluate_term(&model, read),
        EvalValue::Fp(FpModelValue::PosZero { eb: 5, sb: 11 }),
        "FP completion must clone x=+zero, not the ambient x=+oo pin"
    );
    assert_eq!(
        executor.evaluate_term(&model, add),
        EvalValue::Fp(FpModelValue::PosInf { eb: 5, sb: 11 })
    );
}

#[test]
fn test_lambda_beta_equality_rejects_only_dependent_euf_class_pins() {
    let mut executor = Executor::new();
    let seq_sort = Sort::seq(Sort::Int);
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let five = executor.ctx.terms.mk_int(BigInt::from(5));
    let three = executor.ctx.terms.mk_int(BigInt::from(3));
    let u = executor.ctx.terms.mk_var("u", seq_sort.clone());
    let v = executor.ctx.terms.mk_var("v", seq_sort.clone());
    let unit_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("seq.unit"), vec![x], seq_sort.clone());
    let unit_five =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("seq.unit"), vec![five], seq_sort.clone());
    let dependent_lhs =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("seq.++"), vec![unit_x, u], seq_sort.clone());
    let dependent_rhs =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("seq.++"), vec![unit_x, v], seq_sort.clone());
    let independent_lhs = executor.ctx.terms.mk_app(
        Symbol::named("seq.++"),
        vec![unit_five, u],
        seq_sort.clone(),
    );
    let independent_rhs =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("seq.++"), vec![unit_five, v], seq_sort);
    let dependent_eq = executor.ctx.terms.mk_eq(dependent_lhs, dependent_rhs);
    let independent_eq = executor.ctx.terms.mk_eq(independent_lhs, independent_rhs);
    let dependent_lambda = executor.ctx.terms.mk_lambda_array(x, dependent_eq);
    let independent_lambda = executor.ctx.terms.mk_lambda_array(x, independent_eq);
    let dependent_read = executor.ctx.terms.mk_app(
        Symbol::named("select"),
        vec![dependent_lambda, three],
        Sort::Bool,
    );
    let independent_read = executor.ctx.terms.mk_app(
        Symbol::named("select"),
        vec![independent_lambda, three],
        Sort::Bool,
    );

    let mut term_values = HashMap::default();
    term_values.insert(dependent_lhs, "@Seq!0".to_string());
    term_values.insert(dependent_rhs, "@Seq!0".to_string());
    term_values.insert(independent_lhs, "@Seq!1".to_string());
    term_values.insert(independent_rhs, "@Seq!1".to_string());
    let mut model = empty_model();
    model.euf_model = Some(EufModel {
        term_values,
        ..Default::default()
    });

    assert_eq!(
        executor.evaluate_term(&model, dependent_read),
        EvalValue::Unknown,
        "ambient EUF class equality is not evidence inside a beta instance"
    );
    assert_eq!(
        executor.evaluate_term(&model, independent_read),
        EvalValue::Bool(true)
    );
    assert_eq!(
        executor.evaluate_term(&model, dependent_eq),
        EvalValue::Bool(true)
    );
}

#[test]
fn test_evaluate_term_bv_predicates_evaluate_concretely() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));
    let bvult = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvult"), vec![x, y], Sort::Bool);
    let bvslt = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvslt"), vec![x, y], Sort::Bool);

    let mut bv_values = HashMap::default();
    bv_values.insert(x, BigInt::from(0xFFu8)); // -1 signed, 255 unsigned
    bv_values.insert(y, BigInt::from(1u8));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    // Unsigned: 255 < 1 is false
    assert_eq!(
        executor.evaluate_term(&model, bvult),
        EvalValue::Bool(false)
    );
    // Signed: -1 < 1 is true
    assert_eq!(executor.evaluate_term(&model, bvslt), EvalValue::Bool(true));
}

#[test]
fn test_validate_model_rejects_false_bv_predicate_assertion() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));
    let bvult = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvult"), vec![x, y], Sort::Bool);
    executor.ctx.assertions.push(bvult);

    let mut bv_values = HashMap::default();
    bv_values.insert(x, BigInt::from(0u8));
    bv_values.insert(y, BigInt::from(0u8));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    let err = executor
        .validate_model()
        .expect_err("Expected false bvult assertion to be rejected");
    assert!(
        err.contains("Assertion 0 violated"),
        "Unexpected error: {err}"
    );
}

#[test]
fn test_validate_model_rejects_unknown_bv_with_uf_subterms() {
    // (#3903) Fail closed: if bvult(f(u), g(u)) is Unknown, model
    // validation must reject and the SAT path must degrade to Unknown.
    let mut executor = Executor::new();
    let u = executor
        .ctx
        .terms
        .mk_var("u", Sort::Uninterpreted("U".to_string()));
    let f_u = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![u], Sort::bitvec(8));
    let g_u = executor
        .ctx
        .terms
        .mk_app(Symbol::named("g"), vec![u], Sort::bitvec(8));
    let bvult = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvult"), vec![f_u, g_u], Sort::Bool);
    executor.ctx.assertions.push(bvult);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_model()
        .expect_err("UF-containing BV assertion Unknown should be rejected");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
}

#[test]
fn test_evaluate_bv_shift_operations() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));
    let shl = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvshl"), vec![x, y], Sort::bitvec(8));
    let lshr = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvlshr"), vec![x, y], Sort::bitvec(8));
    let ashr = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvashr"), vec![x, y], Sort::bitvec(8));

    let mut bv_values = HashMap::default();
    bv_values.insert(x, BigInt::from(0b1100_0011u8)); // 195 unsigned, -61 signed
    bv_values.insert(y, BigInt::from(2u8));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    // shl: 0b1100_0011 << 2 = 0b0000_1100 (mod 256)
    assert_eq!(
        executor.evaluate_term(&model, shl),
        EvalValue::BitVec {
            value: BigInt::from(0b0000_1100u8),
            width: 8,
        }
    );
    // lshr (logical): 0b1100_0011 >> 2 = 0b0011_0000
    assert_eq!(
        executor.evaluate_term(&model, lshr),
        EvalValue::BitVec {
            value: BigInt::from(0b0011_0000u8),
            width: 8,
        }
    );
    // ashr (arithmetic): -61 >> 2 = -16 = 0b1111_0000 (240 unsigned)
    assert_eq!(
        executor.evaluate_term(&model, ashr),
        EvalValue::BitVec {
            value: BigInt::from(0b1111_0000u8),
            width: 8,
        }
    );
}

#[test]
fn test_evaluate_bv_div_rem() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));
    let udiv = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvudiv"), vec![x, y], Sort::bitvec(8));
    let urem = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvurem"), vec![x, y], Sort::bitvec(8));

    let mut bv_values = HashMap::default();
    bv_values.insert(x, BigInt::from(200u8));
    bv_values.insert(y, BigInt::from(7u8));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    // 200 / 7 = 28
    assert_eq!(
        executor.evaluate_term(&model, udiv),
        EvalValue::BitVec {
            value: BigInt::from(28u8),
            width: 8,
        }
    );
    // 200 % 7 = 4
    assert_eq!(
        executor.evaluate_term(&model, urem),
        EvalValue::BitVec {
            value: BigInt::from(4u8),
            width: 8,
        }
    );
}

#[test]
fn test_evaluate_bv_concat_extend() {
    let mut executor = Executor::new();
    let hi = executor.ctx.terms.mk_var("hi", Sort::bitvec(4));
    let lo = executor.ctx.terms.mk_var("lo", Sort::bitvec(4));
    let concat = executor
        .ctx
        .terms
        .mk_app(Symbol::named("concat"), vec![hi, lo], Sort::bitvec(8));

    let narrow = executor.ctx.terms.mk_var("narrow", Sort::bitvec(4));
    let zext =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("zero_extend"), vec![narrow], Sort::bitvec(8));
    let sext =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("sign_extend"), vec![narrow], Sort::bitvec(8));

    let mut bv_values = HashMap::default();
    bv_values.insert(hi, BigInt::from(0b1010u8));
    bv_values.insert(lo, BigInt::from(0b0101u8));
    bv_values.insert(narrow, BigInt::from(0b1100u8)); // -4 in 4-bit signed
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });

    // concat(0b1010, 0b0101) = 0b10100101 = 165
    assert_eq!(
        executor.evaluate_term(&model, concat),
        EvalValue::BitVec {
            value: BigInt::from(0b10100101u8),
            width: 8,
        }
    );
    // zero_extend(0b1100) = 0b00001100 = 12
    assert_eq!(
        executor.evaluate_term(&model, zext),
        EvalValue::BitVec {
            value: BigInt::from(0b00001100u8),
            width: 8,
        }
    );
    // sign_extend(0b1100) = 0b11111100 = 252 (sign bit propagated)
    assert_eq!(
        executor.evaluate_term(&model, sext),
        EvalValue::BitVec {
            value: BigInt::from(0b11111100u8),
            width: 8,
        }
    );
}

#[test]
fn test_validate_model_rejects_unknown_non_bv_comparison() {
    // (#3903) Non-BV-comparison assertions that evaluate to Unknown are rejected.
    // Unknown means the evaluator cannot verify the model satisfies the assertion.
    // Use an uninterpreted function (UF) application: the evaluator cannot resolve
    // UF applications without a UF model, so it returns Unknown and is rejected.
    let mut executor = Executor::new();
    let hello = executor.ctx.terms.mk_string("hello".to_string());
    let uf_app =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("my_uf_predicate"), vec![hello], Sort::Bool);
    executor.ctx.assertions.push(uf_app);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_model()
        .expect_err("Unknown UF application should be rejected by validate_model");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
}

#[test]
fn test_validate_model_rejects_unknown_string_var_assertion() {
    // (#3903) Fail closed for String assertions that evaluate to Unknown.
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::String);
    let pattern = executor.ctx.terms.mk_string("hello".to_string());
    let contains =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("str.contains"), vec![x, pattern], Sort::Bool);
    executor.ctx.assertions.push(contains);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_model()
        .expect_err("Unknown String assertion should be rejected");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
}

#[test]
fn test_validate_model_accepts_quantified_assertion_skipped_before_evaluation() {
    // Quantified assertions are skipped before evaluation —
    // validate_model returns Ok because the solver already verified
    // them via E-matching/CEGQI during solving.
    let mut executor = Executor::new();
    let body = executor.ctx.terms.mk_var("x", Sort::Bool);
    let forall = executor
        .ctx
        .terms
        .mk_forall(vec![("x".to_string(), Sort::Bool)], body);
    executor.ctx.assertions.push(forall);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    executor
        .validate_model()
        .expect("Quantified assertion should be accepted (skipped before evaluation)");
}

#[test]
fn test_validate_model_rejects_unknown_bv_comparison_with_uf_arguments() {
    // (#3903) Fail closed even when the Unknown originates from UF args.
    let mut executor = Executor::new();
    let x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bv_x"), vec![], Sort::bitvec(8));
    let y = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bv_y"), vec![], Sort::bitvec(8));
    let comparison = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvult"), vec![x, y], Sort::Bool);
    executor.ctx.assertions.push(comparison);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_model()
        .expect_err("Unknown BV comparison should be rejected");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
}

#[test]
fn test_validate_model_accepts_unknown_quantified_assertion() {
    // Quantified assertions cannot be model-checked; Unknown is acceptable.
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let body = executor
        .ctx
        .terms
        .mk_app(Symbol::named(">="), vec![x, zero], Sort::Bool);
    let forall = executor
        .ctx
        .terms
        .mk_forall(vec![("x".to_string(), Sort::Int)], body);
    executor.ctx.assertions.push(forall);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    executor
        .validate_model()
        .expect("Quantified assertion Unknown should be accepted");
}

#[test]
fn test_validate_model_rejects_unknown_uf_assertion_empty_model() {
    // UF assertions are fail-closed (#4686): with an empty model, the UF
    // predicate P(x) evaluates to Unknown, which is rejected.
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let p_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("P"), vec![x], Sort::Bool);
    executor.ctx.assertions.push(p_x);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_model()
        .expect_err("Unknown UF predicate assertion must be rejected (fail-closed #4686)");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
}

#[test]
fn test_validate_model_rejects_unknown_array_assertion() {
    // Unknown array assertions return Incomplete so
    // finalize_sat_model_validation can return Unknown instead of
    // silently accepting a potentially wrong SAT answer (#5116).
    let mut executor = Executor::new();
    let a = executor
        .ctx
        .terms
        .mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let i = executor.ctx.terms.mk_var("i", Sort::Int);
    let v = executor.ctx.terms.mk_var("v", Sort::Int);
    let sel = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![a, i], Sort::Int);
    let eq = executor.ctx.terms.mk_eq(sel, v);
    executor.ctx.assertions.push(eq);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_model()
        .expect_err("Unknown array assertion should now be rejected");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
}

#[test]
fn test_finalize_sat_model_validation_degrades_array_false_with_sat_assignment() {
    let mut executor = Executor::new();
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let const_array = executor.ctx.terms.mk_app(
        Symbol::named("const-array"),
        vec![zero],
        Sort::array(Sort::Int, Sort::Int),
    );
    let stored = executor.ctx.terms.mk_app(
        Symbol::named("store"),
        vec![const_array, zero, one],
        Sort::array(Sort::Int, Sort::Int),
    );
    let selected =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), vec![stored, zero], Sort::Int);
    let assertion = executor
        .ctx
        .terms
        .mk_app(Symbol::named("<"), vec![selected, zero], Sort::Bool);
    assert!(
        executor.contains_array_term(assertion),
        "assertion must retain array structure"
    );
    executor.ctx.assertions.push(assertion);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model_with_sat_assignments(&[(assertion, true)]));

    let result = executor
        .finalize_sat_model_validation()
        .expect("array false assertion should degrade to Unknown");

    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(executor.last_result, Some(SolveResult::Unknown));
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::Incomplete)
    );
}

#[test]
fn test_finalize_sat_model_validation_delegates_array_false_with_array_model_8785() {
    let mut executor = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = executor.ctx.terms.mk_var("a", array_sort.clone());
    let b = executor.ctx.terms.mk_var("b", array_sort);
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let stored = executor.ctx.terms.mk_app(
        Symbol::named("store"),
        vec![b, zero, one],
        Sort::array(Sort::Int, Sort::Int),
    );
    let assertion = executor.ctx.terms.mk_eq(a, stored);
    assert!(
        executor.contains_array_term(assertion),
        "assertion must retain array structure"
    );

    let mut model = model_with_sat_assignments(&[(assertion, true)]);
    let mut array_values = HashMap::default();
    array_values.insert(a, ay_arrays::ArrayInterpretation::default());
    array_values.insert(b, ay_arrays::ArrayInterpretation::default());
    model.array_model = Some(ArrayModel {
        array_values,
        ..Default::default()
    });

    assert_eq!(
        executor.evaluate_term(&model, assertion),
        EvalValue::Bool(false),
        "partial extracted array models can make a solver-backed store definition evaluate false",
    );

    executor.ctx.assertions.push(assertion);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    let result = executor
        .finalize_sat_model_validation()
        .expect("array-theory-backed false evaluation should be delegated");

    assert_eq!(result, SolveResult::Sat);
    assert_eq!(executor.last_result, Some(SolveResult::Sat));
}

#[test]
fn test_validate_model_equality_sat_fallback() {
    // (#5499) When both operands of an equality evaluate to Unknown
    // (e.g., string variables with no string model), the equality
    // returns Unknown (no SAT-model fallback — that would be circular).
    // If the SAT variable is true, validate_model tracks this as
    // sat_fallback_count. With only one assertion and no independent
    // evidence, the zero-check guard rejects the model.
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("a", Sort::String);
    let b = executor.ctx.terms.mk_var("b", Sort::String);
    let eq_ab = executor.ctx.terms.mk_eq(a, b);
    executor.ctx.assertions.push(eq_ab);

    // Build a model where the equality term has SAT variable = true
    let model = model_with_sat_assignments(&[(eq_ab, true)]);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    let err = executor
        .validate_model()
        .expect_err("SAT-fallback-only model should be rejected (#5499)");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
}

#[test]
fn test_validate_model_equality_sat_fallback_false_rejects() {
    // (#5499) When the equality evaluates to Unknown and the SAT model
    // says false, validation rejects with "evaluates to Unknown".
    // Use Uninterpreted sort (not String) so the assertion hits the general
    // evaluator's SAT-fallback path — String-sorted vars are intercepted by
    // the dedicated string handler (#4057) and route to skipped_internal.
    let mut executor = Executor::new();
    let a = executor
        .ctx
        .terms
        .mk_var("a", Sort::Uninterpreted("UFSort".into()));
    let b = executor
        .ctx
        .terms
        .mk_var("b", Sort::Uninterpreted("UFSort".into()));
    let eq_ab = executor.ctx.terms.mk_eq(a, b);
    executor.ctx.assertions.push(eq_ab);

    let model = model_with_sat_assignments(&[(eq_ab, false)]);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    let err = executor
        .validate_model()
        .expect_err("SAT fallback false should reject");
    assert!(
        err.contains("evaluates to Unknown"),
        "Expected 'evaluates to Unknown' error, got: {err}"
    );
}

#[test]
fn test_validate_model_sat_fallback_mixed_with_independent_passes() {
    // (#5499) When some assertions are independently validated (checked > 0)
    // and others use SAT fallback, the model passes. The zero-check guard
    // only fires when ALL assertions are SAT-fallback (no independent evidence).
    let mut executor = Executor::new();
    // Independent assertion: Bool(true) evaluates directly.
    let true_const = executor.ctx.terms.mk_bool(true);
    executor.ctx.assertions.push(true_const);
    // SAT-fallback assertion: string equality with no string model.
    let a = executor.ctx.terms.mk_var("a", Sort::String);
    let b = executor.ctx.terms.mk_var("b", Sort::String);
    let eq_ab = executor.ctx.terms.mk_eq(a, b);
    executor.ctx.assertions.push(eq_ab);

    let model = model_with_sat_assignments(&[(eq_ab, true)]);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    executor
        .validate_model()
        .expect("Mixed independent+SAT-fallback model should pass (#5499)");
}

#[test]
fn test_validate_model_string_equality_uses_string_model() {
    // Validate leaf string equality without SAT-literal fallback by
    // providing a concrete string model assignment.
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::String);
    let abc = executor.ctx.terms.mk_string("abc".to_string());
    let eq_x_abc = executor.ctx.terms.mk_eq(x, abc);
    executor.ctx.assertions.push(eq_x_abc);

    let mut string_values = HashMap::default();
    string_values.insert(x, "abc".to_string());
    let mut model = empty_model();
    model.string_model = Some(StringModel {
        values: string_values,
    });
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    executor
        .validate_model()
        .expect("String equality should validate from string model");
}

#[test]
fn test_validate_model_rejects_unknown_extf_string_equality() {
    // (#3903) Unsupported extf terms evaluating to Unknown are rejected.
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::String);
    let lower_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("str.to_lower"), vec![x], Sort::String);
    let abc = executor.ctx.terms.mk_string("abc".to_string());
    let eq_term = executor.ctx.terms.mk_eq(lower_x, abc);
    executor.ctx.assertions.push(eq_term);

    let model = model_with_sat_assignments(&[(eq_term, true)]);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    let err = executor
        .validate_model()
        .expect_err("Unknown extf equality should be rejected");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
}

#[test]
fn test_finalize_sat_model_validation_returns_unknown_for_unevaluable_string_term() {
    // (#3903) Unknown validation must degrade SAT to Unknown.
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::String);
    let pattern = executor.ctx.terms.mk_string("hello".to_string());
    let contains =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("str.contains"), vec![x, pattern], Sort::Bool);
    executor.ctx.assertions.push(contains);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let result = executor.finalize_sat_model_validation();
    assert!(
        matches!(result, Ok(SolveResult::Unknown)),
        "Expected Unknown for unevaluable string term, got: {result:?}"
    );
}

#[test]
fn test_finalize_sat_assumption_validation_accepts_true_assumption() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("a", Sort::Bool);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model_with_sat_assignments(&[(a, true)]));

    let result = executor
        .finalize_sat_assumption_validation(&[a])
        .expect("true assumption should pass assumption validation");

    assert_eq!(result, SolveResult::Sat);
}

#[test]
fn test_finalize_sat_assumption_validation_degrades_unknown_assumption() {
    // Use an uninterpreted function — the evaluator cannot resolve it without
    // a UF model, so the assumption evaluates to Unknown and degrades to Unknown.
    let mut executor = Executor::new();
    let hello = executor.ctx.terms.mk_string("hello".to_string());
    let uf_app =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("my_uf_predicate"), vec![hello], Sort::Bool);

    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let result = executor
        .finalize_sat_assumption_validation(&[uf_app])
        .expect("unknown assumption evaluability should degrade to Unknown");

    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(executor.last_result, Some(SolveResult::Unknown));
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::Incomplete)
    );
}

#[test]
fn test_finalize_sat_assumption_validation_degrades_unknown_bv_with_uf_subterms() {
    // Keep fail-closed behavior consistent with assertion validation:
    // bv comparison assumptions with UF arguments must not be skipped.
    let mut executor = Executor::new();
    let u = executor
        .ctx
        .terms
        .mk_var("u", Sort::Uninterpreted("U".to_string()));
    let f_u = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![u], Sort::bitvec(8));
    let g_u = executor
        .ctx
        .terms
        .mk_app(Symbol::named("g"), vec![u], Sort::bitvec(8));
    let bvult = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvult"), vec![f_u, g_u], Sort::Bool);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let result = executor
        .finalize_sat_assumption_validation(&[bvult])
        .expect("UF-containing BV assumption should degrade to Unknown");

    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(executor.last_result, Some(SolveResult::Unknown));
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::Incomplete)
    );
}

#[test]
fn test_finalize_sat_assumption_validation_degrades_array_false_assumption() {
    let mut executor = Executor::new();
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let const_array = executor.ctx.terms.mk_app(
        Symbol::named("const-array"),
        vec![zero],
        Sort::array(Sort::Int, Sort::Int),
    );
    let stored = executor.ctx.terms.mk_app(
        Symbol::named("store"),
        vec![const_array, zero, one],
        Sort::array(Sort::Int, Sort::Int),
    );
    let selected =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), vec![stored, zero], Sort::Int);
    let assumption =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("<"), vec![selected, zero], Sort::Bool);
    assert!(
        executor.contains_array_term(assumption),
        "assumption must retain array structure"
    );

    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model_with_sat_assignments(&[(assumption, true)]));

    let result = executor
        .finalize_sat_assumption_validation(&[assumption])
        .expect("array false assumption should degrade to Unknown");

    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(executor.last_result, Some(SolveResult::Unknown));
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::Incomplete)
    );
}

#[test]
fn test_validate_model_rejects_false_seq_assertion_6044() {
    // (#6044) When a Seq assertion evaluates to Bool(false), validate_model
    // must reject it — not silently skip it as skipped_internal.
    // Construct: (= (seq.len s) 5) where s is a 3-element sequence.
    let mut executor = Executor::new();
    let seq_sort = Sort::Seq(Box::new(Sort::Int));
    let s = executor.ctx.terms.mk_var("s", seq_sort);
    let seq_len = executor
        .ctx
        .terms
        .mk_app(Symbol::named("seq.len"), vec![s], Sort::Int);
    let five = executor.ctx.terms.mk_int(BigInt::from(5));
    let assertion = executor.ctx.terms.mk_eq(seq_len, five);
    executor.ctx.assertions.push(assertion);

    // Build a SeqModel where s = [10, 20, 30] (length 3, not 5).
    let mut seq_values = HashMap::default();
    seq_values.insert(
        s,
        vec!["10".to_string(), "20".to_string(), "30".to_string()],
    );
    let mut model = empty_model();
    model.seq_model = Some(SeqModel { values: seq_values });
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    let err = executor
        .validate_model()
        .expect_err("Seq assertion evaluating to false must be rejected (#6044)");
    assert!(
        err.contains("evaluates to false"),
        "Expected 'evaluates to false' error, got: {err}"
    );
}

#[test]
fn test_validate_model_rejects_unknown_seq_assertion_without_independent_evidence() {
    // (#6273, #4057) Unknown Seq assertions contribute only skipped_internal
    // evidence. When no assertion was independently checked, validation must
    // fail closed so finalize_sat_model_validation can degrade SAT to Unknown.
    let mut executor = Executor::new();
    let seq_sort = Sort::Seq(Box::new(Sort::Int));
    let s = executor.ctx.terms.mk_var("s", seq_sort);
    let seq_len = executor
        .ctx
        .terms
        .mk_app(Symbol::named("seq.len"), vec![s], Sort::Int);
    let five = executor.ctx.terms.mk_int(BigInt::from(5));
    let assertion = executor.ctx.terms.mk_eq(seq_len, five);
    executor.ctx.assertions.push(assertion);

    // No SeqModel -> seq.len(s) evaluates to Unknown, so the assertion only
    // contributes skipped_internal evidence.
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_model()
        .expect_err("Unknown Seq assertion with zero checked evidence must be rejected");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
    // Rejected at per-assertion Unknown path (line 4728), not summary accounting.
    assert!(err.contains("evaluates to Unknown"), "got: {err}");
}

#[test]
fn test_validate_model_proportional_sat_fallback_rejects() {
    // (#6223) When >90% of assertions use SAT-fallback, the model is
    // rejected even if some assertions independently validated. A single
    // independent check should not validate 10+ circularly-checked assertions.
    // Use Uninterpreted sort (not String) so assertions hit the general
    // evaluator's SAT-fallback path — String-sorted vars are intercepted by
    // the dedicated string handler (#4057) and route to skipped_internal.
    let mut executor = Executor::new();

    // 1 independent assertion: Bool(true) evaluates directly.
    let true_const = executor.ctx.terms.mk_bool(true);
    executor.ctx.assertions.push(true_const);

    // 10 SAT-fallback assertions: UF equalities with no UF model.
    // These will evaluate to Unknown → SAT-fallback.
    let mut sat_assignments = Vec::new();
    for i in 0..10 {
        let a = executor
            .ctx
            .terms
            .mk_var(format!("a{i}"), Sort::Uninterpreted("UFSort".into()));
        let b = executor
            .ctx
            .terms
            .mk_var(format!("b{i}"), Sort::Uninterpreted("UFSort".into()));
        let eq = executor.ctx.terms.mk_eq(a, b);
        executor.ctx.assertions.push(eq);
        sat_assignments.push((eq, true));
    }

    let model = model_with_sat_assignments(&sat_assignments);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    // total=11, checked=1, sat_fallback=10 → ~91% SAT-fallback (>90%) → rejected
    let result = executor.validate_model();
    assert!(
        result.is_err(),
        "Model with >90% SAT-fallback should be rejected (#6223)"
    );
    let msg = result.unwrap_err();
    assert!(
        msg.contains("SAT-fallback"),
        "Error should mention SAT-fallback: {msg}"
    );
}

#[test]
fn test_validate_model_proportional_sat_fallback_below_threshold_passes() {
    // (#6223) When SAT-fallback is <=90% of assertions, the model passes.
    // 3 independent + 2 SAT-fallback = 40% → below threshold.
    let mut executor = Executor::new();

    // 3 independent assertions
    for _ in 0..3 {
        let true_const = executor.ctx.terms.mk_bool(true);
        executor.ctx.assertions.push(true_const);
    }

    // 2 SAT-fallback assertions
    let mut sat_assignments = Vec::new();
    for i in 0..2 {
        let a = executor.ctx.terms.mk_var(format!("x{i}"), Sort::String);
        let b = executor.ctx.terms.mk_var(format!("y{i}"), Sort::String);
        let eq = executor.ctx.terms.mk_eq(a, b);
        executor.ctx.assertions.push(eq);
        sat_assignments.push((eq, true));
    }

    let model = model_with_sat_assignments(&sat_assignments);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    // total=5, checked=3, sat_fallback=2 → 40% → passes
    executor
        .validate_model()
        .expect("Model with 40% SAT-fallback should pass (#6223)");
}

#[test]
fn test_validate_model_proportional_guard_skips_small_formulas() {
    // (#6223) The proportional guard requires total >= 5. Small formulas
    // with high SAT-fallback ratios are not rejected.
    let mut executor = Executor::new();

    // 1 independent + 3 SAT-fallback = 75% but only 4 assertions total
    let true_const = executor.ctx.terms.mk_bool(true);
    executor.ctx.assertions.push(true_const);

    let mut sat_assignments = Vec::new();
    for i in 0..3 {
        let a = executor.ctx.terms.mk_var(format!("s{i}"), Sort::String);
        let b = executor.ctx.terms.mk_var(format!("t{i}"), Sort::String);
        let eq = executor.ctx.terms.mk_eq(a, b);
        executor.ctx.assertions.push(eq);
        sat_assignments.push((eq, true));
    }

    let model = model_with_sat_assignments(&sat_assignments);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    // total=4, checked=1, sat_fallback=3 → 75% but total < 5 → passes
    executor
        .validate_model()
        .expect("Small formula should skip proportional guard (#6223)");
}

/// (#6280) Build an executor with a pure-BV assertion (bvult(f(x), y)) that
/// evaluates to Unknown despite a BV model being present. The UF application
/// f(x) makes evaluate_term return Unknown.
fn setup_pure_bv_unknown_with_model_6280() -> Executor {
    let mut executor = Executor::new();
    let x = executor
        .ctx
        .terms
        .mk_var("x", Sort::Uninterpreted("U".to_string()));
    let f_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));
    let bvult = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvult"), vec![f_x, y], Sort::Bool);
    executor.ctx.assertions.push(bvult);
    let mut bv_values = HashMap::default();
    bv_values.insert(y, BigInt::from(42));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    model.sat_model = vec![true];
    model.term_to_var.insert(bvult, 0);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);
    executor
}

#[test]
fn test_validate_model_rejects_pure_bv_unknown_with_bv_model_6280() {
    // (#6280) Pure-BV assertion with BV model that evaluates to Unknown must
    // be rejected — BV bit-blasting is complete, so Unknown indicates a bug.
    let executor = setup_pure_bv_unknown_with_model_6280();
    let err = executor
        .validate_model()
        .expect_err("Pure BV Unknown with BV model should be rejected (#6280)");
    assert!(err.is_incomplete(), "Expected Incomplete error: {err}");
    assert!(err.contains("pure BV assertion"), "Error: {err}");
}

#[test]
fn test_finalize_pure_bv_unknown_degrades_to_unknown_6280() {
    // (#6280) End-to-end: finalize must convert pure-BV Unknown rejection
    // into SolveResult::Unknown (not crash, not Sat).
    let mut executor = setup_pure_bv_unknown_with_model_6280();
    let result = executor
        .finalize_sat_model_validation()
        .expect("finalize should not crash");
    assert_eq!(
        result,
        SolveResult::Unknown,
        "Should degrade to Unknown (#6280)"
    );
}
