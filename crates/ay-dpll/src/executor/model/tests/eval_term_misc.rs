// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! evaluate_term tests: let bindings, quantifiers, uninterpreted function
//! applications, additional coverage, parsing, and array evaluation.

use super::*;

// ==========================================================================
// evaluate_term: let bindings and quantifiers
// ==========================================================================

#[test]
fn test_evaluate_term_let_binding() {
    let mut executor = Executor::new();
    let val = executor.ctx.terms.mk_int(BigInt::from(42));
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    // (let ((x 42)) x) should evaluate to 42
    let let_term = executor.ctx.terms.mk_let(vec![("x".to_string(), val)], x);

    // Evaluate the let body (let bindings should be expanded already, but if not,
    // we just evaluate the body)
    let model = empty_model();
    // The current implementation just evaluates the body, ignoring the bindings
    // since they should have been substituted already
    let result = executor.evaluate_term(&model, let_term);
    // Body is `x` which defaults to 0 since it's not in the model
    assert_eq!(result, EvalValue::Rational(BigRational::zero()));
}

#[test]
fn test_evaluate_term_quantifiers_return_unknown() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let body = executor.ctx.terms.mk_gt(x, zero);

    let forall = executor
        .ctx
        .terms
        .mk_forall(vec![("x".to_string(), Sort::Int)], body);
    let exists = executor
        .ctx
        .terms
        .mk_exists(vec![("x".to_string(), Sort::Int)], body);

    let model = empty_model();
    assert_eq!(executor.evaluate_term(&model, forall), EvalValue::Unknown);
    assert_eq!(executor.evaluate_term(&model, exists), EvalValue::Unknown);
}

// ==========================================================================
// evaluate_term: uninterpreted function applications
// ==========================================================================

#[test]
fn test_evaluate_term_uf_app_from_sat_model() {
    let mut executor = Executor::new();
    // p() is a 0-ary predicate (Bool-sorted UF application)
    let p = executor
        .ctx
        .terms
        .mk_app(Symbol::named("p"), vec![], Sort::Bool);

    let model = model_with_sat_assignments(&[(p, true)]);
    assert_eq!(executor.evaluate_term(&model, p), EvalValue::Bool(true));
}

#[test]
fn test_evaluate_term_builtin_predicate_does_not_use_sat_fallback() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::String);
    let a = executor.ctx.terms.mk_string("a".to_string());
    let contains = executor
        .ctx
        .terms
        .mk_app(Symbol::named("str.contains"), vec![x, a], Sort::Bool);

    // Built-in theory predicate must not be accepted from raw SAT literal.
    let model = model_with_sat_assignments(&[(contains, true)]);
    assert_eq!(executor.evaluate_term(&model, contains), EvalValue::Unknown);
}

#[test]
fn test_evaluate_term_uf_app_from_euf_model() {
    let mut executor = Executor::new();
    let sort = Sort::Uninterpreted("U".to_string());
    let x = executor.ctx.terms.mk_var("x", sort.clone());
    let f_x = executor.ctx.terms.mk_app(Symbol::named("f"), vec![x], sort);

    let mut term_values = HashMap::default();
    term_values.insert(f_x, "@U!1".to_string());

    let euf_model = EufModel {
        term_values,
        ..Default::default()
    };

    let mut model = empty_model();
    model.euf_model = Some(euf_model);

    assert_eq!(
        executor.evaluate_term(&model, f_x),
        EvalValue::Element("@U!1".to_string())
    );
}

#[test]
fn test_evaluate_term_uf_app_uses_function_table_bool_arg() {
    let mut executor = Executor::new();
    let sort = Sort::Uninterpreted("U".to_string());
    let b = executor.ctx.terms.mk_var("b", Sort::Bool);
    let u = executor.ctx.terms.mk_var("u", sort.clone());
    let f_b_u = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![b, u], sort);

    let mut model = model_with_sat_assignments(&[(b, false)]);
    let mut term_values = HashMap::default();
    // Regression: placeholder bool atoms from EUF model extraction must
    // not override canonical true/false UF table keys.
    term_values.insert(b, "@?17".to_string());
    term_values.insert(u, "@U!0".to_string());
    let mut function_tables = HashMap::default();
    function_tables.insert(
        "f".to_string(),
        vec![(
            vec!["false".to_string(), "@U!0".to_string()],
            "@U!1".to_string(),
        )],
    );
    model.euf_model = Some(EufModel {
        term_values,
        function_tables,
        ..Default::default()
    });

    assert_eq!(
        executor.evaluate_term(&model, f_b_u),
        EvalValue::Element("@U!1".to_string())
    );
}

#[test]
fn test_evaluate_term_bool_uf_prefers_function_table_over_sat_literal() {
    let mut executor = Executor::new();
    let u = executor
        .ctx
        .terms
        .mk_var("u", Sort::Uninterpreted("U".to_string()));
    let p_u = executor
        .ctx
        .terms
        .mk_app(Symbol::named("p"), vec![u], Sort::Bool);

    // SAT assignment says false, but function table says true.
    // Function-table evaluation must win so congruent applications are interpreted consistently.
    let mut model = model_with_sat_assignments(&[(p_u, false)]);
    let mut term_values = HashMap::default();
    term_values.insert(u, "@U!0".to_string());
    let mut function_tables = HashMap::default();
    function_tables.insert(
        "p".to_string(),
        vec![(vec!["@U!0".to_string()], "true".to_string())],
    );
    model.euf_model = Some(EufModel {
        term_values,
        function_tables,
        ..Default::default()
    });

    assert_eq!(executor.evaluate_term(&model, p_u), EvalValue::Bool(true));
}

#[test]
fn test_total_uf_table_overrides_stale_app_values_and_supplies_default() {
    let mut executor = Executor::new();
    let zero = executor.ctx.terms.mk_int(BigInt::zero());
    let one = executor.ctx.terms.mk_int(BigInt::one());
    let f_zero = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![zero], Sort::Int);
    let f_one = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![one], Sort::Int);
    let plus_one = executor
        .ctx
        .terms
        .mk_app(Symbol::named("+"), vec![f_one, one], Sort::Int);

    let mut model = empty_model();
    let mut euf = EufModel::default();
    // These are values from the pre-completion candidate M. The explicit
    // total interpretation M' must override both sources.
    euf.func_app_const_terms.insert(f_one, one);
    euf.term_values.insert(f_one, "1".to_string());
    model.euf_model = Some(euf);
    let mut lia_values = HashMap::default();
    lia_values.insert(f_one, BigInt::one());
    model.lia_model = Some(LiaModel { values: lia_values });
    // The first row is the certified exception. `f(1)` exercises the typed
    // default; installation derives the printer table from these same values.
    model
        .install_certified_total_uf(
            "f".to_string(),
            vec![Sort::Int],
            Sort::Int,
            vec![(
                vec![EvalValue::Rational(BigRational::zero())],
                EvalValue::Rational(BigRational::one()),
            )],
            EvalValue::Rational(BigRational::zero()),
        )
        .expect("well-typed total table");

    assert_eq!(
        executor.evaluate_term(&model, f_zero),
        EvalValue::Rational(BigRational::one())
    );
    assert_eq!(
        executor.evaluate_term(&model, f_one),
        EvalValue::Rational(BigRational::zero())
    );
    assert_eq!(
        executor.evaluate_term(&model, plus_one),
        EvalValue::Rational(BigRational::one())
    );
}

#[test]
fn test_raw_table_cleanup_preserves_certified_total_interpretation() {
    let mut executor = Executor::new();
    let zero = executor.ctx.terms.mk_int(BigInt::zero());
    let one = executor.ctx.terms.mk_int(BigInt::one());
    let f_zero = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![zero], Sort::Int);
    let f_one = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![one], Sort::Int);

    let mut model = empty_model();
    model
        .install_certified_total_uf(
            "f".to_string(),
            vec![Sort::Int],
            Sort::Int,
            vec![(
                vec![EvalValue::Rational(BigRational::zero())],
                EvalValue::Rational(BigRational::one()),
            )],
            EvalValue::Rational(BigRational::zero()),
        )
        .expect("well-typed total table");
    assert!(model
        .euf_model
        .as_ref()
        .is_some_and(|euf| euf.function_tables.contains_key("f")));

    // DT post-certificate cleanup strips only the stale raw representation.
    // The typed M' remains the sole evaluation and output authority.
    model.remove_raw_uf_table_interpretation("f");

    assert!(model.has_certified_total_uf("f"));
    assert!(model
        .euf_model
        .as_ref()
        .is_some_and(|euf| !euf.function_tables.contains_key("f")));
    assert_eq!(
        executor.evaluate_term(&model, f_zero),
        EvalValue::Rational(BigRational::one())
    );
    assert_eq!(
        executor.evaluate_term(&model, f_one),
        EvalValue::Rational(BigRational::zero())
    );
}

#[test]
fn test_cegqi_model_epoch_is_affine_across_clone_and_table_replacement() {
    let mut model = empty_model();
    model
        .install_certified_total_uf(
            "f".to_string(),
            vec![Sort::Int],
            Sort::Int,
            Vec::new(),
            EvalValue::Rational(BigRational::zero()),
        )
        .expect("well-typed constant total table");
    let epoch = model.seal_cegqi_uf_recompletion();

    assert!(model.carries_cegqi_uf_recompletion(&epoch));
    assert!(
        !model.clone().carries_cegqi_uf_recompletion(&epoch),
        "cloning model values must not duplicate an affine certificate identity"
    );

    model
        .install_certified_total_uf(
            "f".to_string(),
            vec![Sort::Int],
            Sort::Int,
            Vec::new(),
            EvalValue::Rational(BigRational::one()),
        )
        .expect("replacement table is independently well typed");
    assert!(
        !model.carries_cegqi_uf_recompletion(&epoch),
        "changing a certified interpretation must revoke the theorem's model identity"
    );
}

#[test]
fn test_certified_total_uf_rejects_argument_value_of_wrong_kind() {
    let mut executor = Executor::new();
    let malformed_int = executor.ctx.terms.mk_app(
        Symbol::named("malformed_int"),
        Vec::<TermId>::new(),
        Sort::Int,
    );
    let f_malformed = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![malformed_int], Sort::Int);

    let mut model = empty_model();
    let mut euf = EufModel::default();
    // Deliberately malformed model evidence: an Int-sorted term resolves to an
    // element token. The certified evaluator must not interpret that as an
    // unlisted Int point and silently return its default.
    euf.term_values
        .insert(malformed_int, "opaque-element".to_string());
    model.euf_model = Some(euf);
    model
        .install_certified_total_uf(
            "f".to_string(),
            vec![Sort::Int],
            Sort::Int,
            Vec::new(),
            EvalValue::Rational(BigRational::from_integer(BigInt::from(9))),
        )
        .expect("well-typed certified total UF");

    assert_eq!(
        executor.evaluate_term(&model, f_malformed),
        EvalValue::Unknown,
        "wrong-kind model evidence must fail closed before default lookup"
    );
}

#[test]
fn test_certified_real_uf_accepts_exact_algebraic_argument() {
    let mut executor = Executor::new();
    let algebraic_arg = executor.ctx.terms.mk_var("a", Sort::Real);
    let f_algebraic = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![algebraic_arg], Sort::Int);
    let irrational = ay_nra::rcf_api::real_roots(&[
        BigRational::from_integer(BigInt::from(-2)),
        BigRational::zero(),
        BigRational::one(),
    ])
    .expect("x^2 - 2 root isolation")
    .into_iter()
    .find_map(|root| match root {
        ay_nra::RealScalar::Algebraic(value) => Some(value),
        ay_nra::RealScalar::Rational(_) => None,
    })
    .expect("x^2 - 2 has irrational real roots");
    executor
        .nra_algebraic_model
        .insert(algebraic_arg, irrational);

    let mut model = empty_model();
    model
        .install_certified_total_uf(
            "f".to_string(),
            vec![Sort::Real],
            Sort::Int,
            vec![(
                vec![EvalValue::Rational(BigRational::zero())],
                EvalValue::Rational(BigRational::one()),
            )],
            EvalValue::Rational(BigRational::from_integer(BigInt::from(9))),
        )
        .expect("well-typed certified Real UF");

    assert!(matches!(
        executor.evaluate_term(&model, algebraic_arg),
        EvalValue::Algebraic(_)
    ));
    assert_eq!(
        executor.evaluate_term(&model, f_algebraic),
        EvalValue::Rational(BigRational::from_integer(BigInt::from(9))),
        "an exact algebraic is a valid Real argument and differs from the rational exception"
    );
}

#[test]
fn test_certified_dt_uf_rejects_abstract_argument_and_rendered_key_collision() {
    let mut executor = Executor::new();
    let dt_sort = Sort::Uninterpreted("D".to_string());
    let abstract_arg = executor.ctx.terms.mk_var("d", dt_sort.clone());
    let score = executor
        .ctx
        .terms
        .mk_app(Symbol::named("score"), vec![abstract_arg], Sort::Int);

    let mut model = empty_model();
    let mut euf = EufModel::default();
    euf.term_values.insert(abstract_arg, "@D!0".to_string());
    model.euf_model = Some(euf);
    model
        .install_certified_total_dt_uf(
            "score".to_string(),
            vec![dt_sort.clone()],
            Sort::Int,
            Vec::new(),
            Vec::new(),
            EvalValue::Rational(BigRational::from_integer(BigInt::from(7))),
        )
        .expect("well-typed certified datatype UF");
    assert_eq!(
        executor.evaluate_term(&model, score),
        EvalValue::Unknown,
        "an unresolved abstract datatype element may denote an exception row"
    );

    let mut collision = empty_model();
    assert!(
        collision
            .install_certified_total_dt_uf(
                "score".to_string(),
                vec![dt_sort],
                Sort::Int,
                vec![
                    (
                        vec![EvalValue::Element("(C 0)".to_string())],
                        EvalValue::Rational(BigRational::from_integer(BigInt::from(1))),
                    ),
                    (
                        vec![EvalValue::Element("(C 1)".to_string())],
                        EvalValue::Rational(BigRational::from_integer(BigInt::from(2))),
                    ),
                ],
                vec![vec!["(C 0)".to_string()], vec!["(C 0)".to_string()]],
                EvalValue::Rational(BigRational::zero()),
            )
            .is_none(),
        "two typed rows may not collapse to one printed constructor key"
    );
}

#[test]
fn test_total_uf_table_matches_negative_int_and_real_keys_semantically() {
    let mut executor = Executor::new();
    let minus_one_value = BigRational::from_integer(BigInt::from(-1));
    let minus_one = executor.ctx.terms.mk_int(BigInt::from(-1));
    let f_minus_one = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![minus_one], Sort::Int);

    let minus_half_value = BigRational::new(BigInt::from(-1), BigInt::from(2));
    let minus_half = executor.ctx.terms.mk_rational(minus_half_value.clone());
    let g_minus_half = executor
        .ctx
        .terms
        .mk_app(Symbol::named("g"), vec![minus_half], Sort::Real);
    let three_halves = BigRational::new(BigInt::from(3), BigInt::from(2));

    let mut model = empty_model();
    model
        .install_certified_total_uf(
            "f".to_string(),
            vec![Sort::Int],
            Sort::Int,
            vec![(
                vec![EvalValue::Rational(minus_one_value)],
                EvalValue::Rational(BigRational::from_integer(BigInt::from(7))),
            )],
            EvalValue::Rational(BigRational::zero()),
        )
        .expect("well-typed negative Int table");
    model
        .install_certified_total_uf(
            "g".to_string(),
            vec![Sort::Real],
            Sort::Real,
            vec![(
                vec![EvalValue::Rational(minus_half_value)],
                EvalValue::Rational(three_halves.clone()),
            )],
            EvalValue::Rational(BigRational::zero()),
        )
        .expect("well-typed negative Real table");

    let euf = model.euf_model.as_ref().expect("rendered EUF tables");
    assert_eq!(euf.function_tables["f"][0].0, vec!["(- 1)".to_string()]);
    assert_eq!(
        euf.function_tables["g"][0],
        (
            vec!["(- (/ 1.0 2.0))".to_string()],
            "(/ 3.0 2.0)".to_string()
        )
    );

    assert_eq!(
        executor.evaluate_term(&model, f_minus_one),
        EvalValue::Rational(BigRational::from_integer(BigInt::from(7)))
    );
    assert_eq!(
        executor.evaluate_term(&model, g_minus_half),
        EvalValue::Rational(three_halves)
    );
}

/// Regression (#9007): EUF function-table placeholders for arithmetic
/// arguments must not be resolved through arbitrary LIA/LRA model defaults.
/// verification-consumer's persistent-array VC has a positive
/// `(fmap_contains call_43 __uf_int_aux_0)` and negative concrete-key facts;
/// resolving `@?__uf_int_aux_0` to default `0` aliases the symbolic key to
/// concrete key `0` during model validation.
#[test]
fn test_evaluate_term_uf_table_keeps_int_placeholder_args_symbolic_9007() {
    let mut executor = Executor::new();
    let map = executor
        .ctx
        .terms
        .mk_var("call_43", Sort::Uninterpreted("FMap".to_string()));
    let aux = executor.ctx.terms.mk_var("__uf_int_aux_0", Sort::Int);
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let p_aux =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("fmap_contains"), vec![map, aux], Sort::Bool);
    let p_zero =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("fmap_contains"), vec![map, zero], Sort::Bool);

    let mut term_values = HashMap::default();
    term_values.insert(map, "@FMap!0".to_string());
    term_values.insert(aux, "0".to_string());
    let mut int_values = HashMap::default();
    int_values.insert(aux, BigInt::from(1));
    let mut function_tables = HashMap::default();
    function_tables.insert(
        "fmap_contains".to_string(),
        vec![(
            vec!["@FMap!0".to_string(), format!("@?{}", aux.0)],
            "true".to_string(),
        )],
    );

    let mut model = empty_model();
    model.euf_model = Some(EufModel {
        term_values,
        function_tables,
        int_values,
        ..Default::default()
    });

    assert_eq!(executor.evaluate_term(&model, p_aux), EvalValue::Bool(true));
    assert_eq!(executor.evaluate_term(&model, p_zero), EvalValue::Unknown);
}

#[test]
fn test_evaluate_term_uf_app_self_placeholder_falls_back_to_term_values() {
    let mut executor = Executor::new();
    let sort = Sort::Uninterpreted("U".to_string());
    let x = executor.ctx.terms.mk_var("x", sort.clone());
    let id_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("id"), vec![x], sort);

    let mut term_values = HashMap::default();
    term_values.insert(x, "@U!0".to_string());
    term_values.insert(id_x, "@U!0".to_string());
    let mut function_tables = HashMap::default();
    function_tables.insert(
        "id".to_string(),
        vec![(vec!["@U!0".to_string()], format!("@?{}", id_x.0))],
    );

    let mut model = empty_model();
    model.euf_model = Some(EufModel {
        term_values,
        function_tables,
        ..Default::default()
    });

    assert_eq!(
        executor.evaluate_term(&model, id_x),
        EvalValue::Element("@U!0".to_string())
    );
}

#[test]
fn test_evaluate_term_uf_app_const_term_fallback() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let f_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], Sort::Int);
    let const_val = executor.ctx.terms.mk_int(BigInt::from(100));

    let mut func_app_const_terms = HashMap::default();
    func_app_const_terms.insert(f_x, const_val);

    let euf_model = EufModel {
        func_app_const_terms,
        ..Default::default()
    };

    let mut model = empty_model();
    model.euf_model = Some(euf_model);

    assert_eq!(
        executor.evaluate_term(&model, f_x),
        EvalValue::Rational(BigRational::from(BigInt::from(100)))
    );
}

// ==========================================================================
// Self-audit: additional coverage tests
// ==========================================================================

#[test]
fn test_evaluate_term_equality_string() {
    let mut executor = Executor::new();
    let s1 = executor.ctx.terms.mk_string("hello".to_string());
    let s2 = executor.ctx.terms.mk_string("hello".to_string());
    let s3 = executor.ctx.terms.mk_string("world".to_string());

    let eq_same = executor.ctx.terms.mk_eq(s1, s2);
    let eq_diff = executor.ctx.terms.mk_eq(s1, s3);

    let model = empty_model();
    assert_eq!(
        executor.evaluate_term(&model, eq_same),
        EvalValue::Bool(true)
    );
    assert_eq!(
        executor.evaluate_term(&model, eq_diff),
        EvalValue::Bool(false)
    );
}

#[test]
fn test_evaluate_term_subtraction_nary() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let y = executor.ctx.terms.mk_var("y", Sort::Int);
    let z = executor.ctx.terms.mk_var("z", Sort::Int);
    // (- 100 30 28) = 100 - 30 - 28 = 42
    let diff = executor.ctx.terms.mk_sub(vec![x, y, z]);

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(100));
    lia_values.insert(y, BigInt::from(30));
    lia_values.insert(z, BigInt::from(28));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });

    assert_eq!(
        executor.evaluate_term(&model, diff),
        EvalValue::Rational(BigRational::from(BigInt::from(42)))
    );
}

#[test]
fn test_evaluate_term_var_int_lia_precedence_over_lra() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);

    // Both LIA and LRA have values - LIA should take precedence
    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(42));

    let mut lra_values = HashMap::default();
    lra_values.insert(x, BigRational::from(BigInt::from(100)));

    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });
    model.lra_model = Some(LraModel { values: lra_values });

    // LIA value (42) should be used, not LRA value (100)
    assert_eq!(
        executor.evaluate_term(&model, x),
        EvalValue::Rational(BigRational::from(BigInt::from(42)))
    );
}

#[test]
fn test_evaluate_term_int_app_lia_precedence_over_euf_const_fallback() {
    let mut executor = Executor::new();
    let list = Sort::Uninterpreted("List".to_string());
    let x = executor.ctx.terms.mk_var("x", list);
    let depth_x =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("__ay_dt_depth_List"), vec![x], Sort::Int);
    let const_zero = executor.ctx.terms.mk_int(BigInt::from(0));

    let mut lia_values = HashMap::default();
    lia_values.insert(depth_x, BigInt::from(7));

    let mut func_app_const_terms = HashMap::default();
    func_app_const_terms.insert(depth_x, const_zero);

    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });
    model.euf_model = Some(EufModel {
        func_app_const_terms,
        ..Default::default()
    });

    assert_eq!(
        executor.evaluate_term(&model, depth_x),
        EvalValue::Rational(BigRational::from(BigInt::from(7)))
    );
}

#[test]
fn test_evaluate_term_int_app_returns_unknown_when_arith_model_missing_value() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let u = executor
        .ctx
        .terms
        .mk_var("u", Sort::Uninterpreted("U".to_string()));
    let f_u = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![u], Sort::Int);

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(11));

    // Different EUF classes: no equivalent LIA-assigned term for (f u).
    let mut int_values = HashMap::default();
    int_values.insert(x, BigInt::from(3));
    int_values.insert(f_u, BigInt::from(4));

    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });
    model.euf_model = Some(EufModel {
        int_values,
        ..Default::default()
    });

    assert_eq!(executor.evaluate_term(&model, f_u), EvalValue::Unknown);
}

#[test]
fn test_evaluate_term_int_app_uses_euf_term_values_when_arith_model_present() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let u = executor
        .ctx
        .terms
        .mk_var("u", Sort::Uninterpreted("U".to_string()));
    let f_u = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![u], Sort::Int);

    let mut lia_values = HashMap::default();
    lia_values.insert(x, BigInt::from(11));

    let mut term_values = HashMap::default();
    term_values.insert(f_u, "4".to_string());

    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values: lia_values });
    model.euf_model = Some(EufModel {
        term_values,
        ..Default::default()
    });

    assert_eq!(
        executor.evaluate_term(&model, f_u),
        EvalValue::Rational(BigRational::from(BigInt::from(4)))
    );
}

#[test]
fn test_evaluate_array_equality_unknown_when_reconstruction_fails() {
    // When array reconstruction fails for both sides there is NO semantic
    // evidence either way. The old behavior fell back to the SAT model's own
    // truth value for the equality literal — circular self-validation that
    // certified the QF_AX swap/storeinv `_np_nf_` false-SATs
    // (#qf-ax-swap-false-sat). The only honest verdict is Unknown.
    let mut executor = Executor::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);
    let a = executor.ctx.terms.mk_var("a", arr_sort.clone());
    let b = executor.ctx.terms.mk_var("b", arr_sort);
    let eq = executor.ctx.terms.mk_eq(a, b);

    let model = model_with_sat_assignments(&[(eq, false)]);
    assert_eq!(executor.evaluate_term(&model, eq), EvalValue::Unknown);
}

#[test]
fn test_evaluate_term_not_unknown_propagation() {
    // Not applied to non-Bool value should return Unknown
    let mut executor = Executor::new();

    // Create a Bool-typed term that evaluates to Unknown
    let x = executor
        .ctx
        .terms
        .mk_var("x", Sort::Uninterpreted("U".to_string()));
    let y = executor
        .ctx
        .terms
        .mk_var("y", Sort::Uninterpreted("U".to_string()));
    let x_eq_y = executor.ctx.terms.mk_eq(x, y);

    // Not of an Unknown value should be Unknown
    let not_x = executor.ctx.terms.mk_not(x_eq_y);

    let model = empty_model();
    assert_eq!(executor.evaluate_term(&model, not_x), EvalValue::Unknown);
}

#[test]
fn test_evaluate_term_ite_unknown_condition() {
    // ITE with Unknown condition should return Unknown
    let mut executor = Executor::new();

    // Create a Bool-typed condition that evaluates to Unknown
    let x = executor
        .ctx
        .terms
        .mk_var("x", Sort::Uninterpreted("U".to_string()));
    let y = executor
        .ctx
        .terms
        .mk_var("y", Sort::Uninterpreted("U".to_string()));
    let cond = executor.ctx.terms.mk_eq(x, y);
    let then_br = executor.ctx.terms.mk_bool(true);
    let else_br = executor.ctx.terms.mk_bool(false);

    let ite = executor.ctx.terms.mk_ite(cond, then_br, else_br);

    let model = empty_model();
    assert_eq!(executor.evaluate_term(&model, ite), EvalValue::Unknown);
}

#[test]
fn test_evaluate_term_subtraction_empty_args() {
    // Subtraction with empty args should return Unknown
    let mut executor = Executor::new();

    // Build subtraction app with empty args directly
    let empty_sub = executor
        .ctx
        .terms
        .mk_app(Symbol::named("-"), vec![], Sort::Int);

    let model = empty_model();
    assert_eq!(
        executor.evaluate_term(&model, empty_sub),
        EvalValue::Unknown
    );
}

// ==========================================================================
// parse_real_string tests (#3837)
// ==========================================================================

#[test]
fn test_parse_real_string_integer() {
    assert_eq!(
        Executor::parse_real_string("42"),
        EvalValue::Rational(BigRational::from(BigInt::from(42)))
    );
}

#[test]
fn test_parse_real_string_rational_fraction() {
    assert_eq!(
        Executor::parse_real_string("(/ 1 2)"),
        EvalValue::Rational(BigRational::new(BigInt::from(1), BigInt::from(2)))
    );
}

#[test]
fn test_parse_real_string_negative_rational() {
    assert_eq!(
        Executor::parse_real_string("(/ (- 3) 4)"),
        EvalValue::Rational(BigRational::new(BigInt::from(-3), BigInt::from(4)))
    );
}

#[test]
fn test_parse_real_string_negated_fraction() {
    assert_eq!(
        Executor::parse_real_string("(- (/ 1 2))"),
        EvalValue::Rational(BigRational::new(BigInt::from(-1), BigInt::from(2)))
    );
}

#[test]
fn test_parse_real_string_decimal() {
    // "1.5" = 3/2
    assert_eq!(
        Executor::parse_real_string("1.5"),
        EvalValue::Rational(BigRational::new(BigInt::from(15), BigInt::from(10)))
    );
}

#[test]
fn test_parse_real_string_negative_integer() {
    assert_eq!(
        Executor::parse_real_string("(- 7)"),
        EvalValue::Rational(BigRational::from(BigInt::from(-7)))
    );
}

#[test]
fn test_parse_real_string_zero_denominator_returns_unknown() {
    assert_eq!(Executor::parse_real_string("(/ 1 0)"), EvalValue::Unknown);
    // The z3-exact decimal-denominator spelling with a zero denominator is
    // also rejected (#real-fmt).
    assert_eq!(
        Executor::parse_real_string("(/ 1.0 0.0)"),
        EvalValue::Unknown
    );
}

// ==========================================================================
// parse_real_string: z3-exact user-facing spellings (#real-fmt)
// ==========================================================================

#[test]
fn test_parse_real_string_decimal_fraction_components() {
    // The user-facing printer emits `(/ 7.0 2.0)`; the parser accepts it.
    assert_eq!(
        Executor::parse_real_string("(/ 7.0 2.0)"),
        EvalValue::Rational(BigRational::new(BigInt::from(7), BigInt::from(2)))
    );
    assert_eq!(
        Executor::parse_real_string("(- (/ 7.0 2.0))"),
        EvalValue::Rational(BigRational::new(BigInt::from(-7), BigInt::from(2)))
    );
    assert_eq!(
        Executor::parse_real_string("5.0"),
        EvalValue::Rational(BigRational::from(BigInt::from(5)))
    );
}

#[test]
fn test_parse_real_string_negated_denominator() {
    // The recursive denominator grammar admits nested forms: (/ 1 (- 2)) is
    // -1/2, not Unknown (#real-fmt).
    assert_eq!(
        Executor::parse_real_string("(/ 1 (- 2))"),
        EvalValue::Rational(BigRational::new(BigInt::from(-1), BigInt::from(2)))
    );
}

#[test]
fn test_parse_real_string_negative_decimal_sign_applies_to_whole_value() {
    // "-1.5" is -(1 + 5/10) = -3/2. The former decimal arm computed
    // -1*10/10 + 5/10 = -1/2 — silently wrong (#real-fmt).
    assert_eq!(
        Executor::parse_real_string("-1.5"),
        EvalValue::Rational(BigRational::new(BigInt::from(-3), BigInt::from(2)))
    );
    assert_eq!(
        Executor::parse_real_string("-0.5"),
        EvalValue::Rational(BigRational::new(BigInt::from(-1), BigInt::from(2)))
    );
}

#[test]
fn test_parse_model_value_string_bitvec_hex() {
    let executor = Executor::new();
    assert_eq!(
        executor.parse_model_value_string("#x2a", &Some(Sort::bitvec(8))),
        EvalValue::BitVec {
            value: BigInt::from(42),
            width: 8
        }
    );
}

#[test]
fn test_parse_model_value_string_uninterpreted_element() {
    let executor = Executor::new();
    assert_eq!(
        executor.parse_model_value_string("@U!0", &Some(Sort::Uninterpreted("U".to_string()))),
        EvalValue::Element("@U!0".to_string())
    );
}

/// Regression test for #3903 Wave 2: evaluate_select must traverse store
/// chains deeper than 100 without returning Unknown due to a depth cap.
#[test]
fn test_evaluate_select_deep_store_chain_no_depth_cap() {
    let mut executor = Executor::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);
    let base_arr = executor.ctx.terms.mk_var("a", arr_sort.clone());

    // Build a chain of 150 stores: store(store(...store(a, 0, 42)..., 1, 0), 2, 0)...
    // Index 0 is stored at the innermost layer with value 42.
    // All other layers store at indices 1..=149 with value 0.
    let target_idx = executor.ctx.terms.mk_int(BigInt::from(0));
    let target_val = executor.ctx.terms.mk_int(BigInt::from(42));
    let filler_val = executor.ctx.terms.mk_int(BigInt::from(0));

    // Innermost store: store(a, 0, 42)
    let mut current = executor.ctx.terms.mk_app(
        Symbol::named("store"),
        vec![base_arr, target_idx, target_val],
        arr_sort.clone(),
    );

    // 149 more stores at indices 1..=149
    for i in 1..150u32 {
        let idx = executor.ctx.terms.mk_int(BigInt::from(i));
        current = executor.ctx.terms.mk_app(
            Symbol::named("store"),
            vec![current, idx, filler_val],
            arr_sort.clone(),
        );
    }

    // select(chain, 0) should find value 42 at the bottom
    let model = empty_model();
    let result = executor.evaluate_select(&model, current, target_idx);
    assert_eq!(
        result,
        EvalValue::Rational(BigRational::from(BigInt::from(42))),
        "evaluate_select must traverse >100 store layers without depth-cap truncation"
    );
}

/// Regression test for #5737: BV bitwise/shift ops normalize non-canonical inputs.
#[test]
fn test_bv_ops_normalize_non_canonical_inputs() {
    let mut executor = Executor::new();
    let bv8 = Sort::bitvec(8);
    let x = executor.ctx.terms.mk_var("x", bv8.clone());
    let y = executor.ctx.terms.mk_var("y", bv8.clone());
    let mk = |e: &mut Executor, op, args: Vec<TermId>, s: Sort| {
        e.ctx.terms.mk_app(Symbol::named(op), args, s)
    };
    let bvnot = mk(&mut executor, "bvnot", vec![x], bv8.clone());
    let bvand = mk(&mut executor, "bvand", vec![x, y], bv8.clone());
    let bvshl = mk(&mut executor, "bvshl", vec![x, y], bv8);
    let eq_xy = mk(&mut executor, "=", vec![x, y], Sort::Bool);

    // x=-1 (should be 255), y=300 (should be 44) for 8-bit
    let model = bv_model(&[(x, -1), (y, 300)]);
    let bv = |v: i64| EvalValue::BitVec {
        value: BigInt::from(v),
        width: 8,
    };
    assert_eq!(executor.evaluate_term(&model, bvnot), bv(0)); // ~255=0
    assert_eq!(executor.evaluate_term(&model, bvand), bv(44)); // 255&44=44
    assert_eq!(executor.evaluate_term(&model, bvshl), bv(0)); // shift>=8->0
    assert_eq!(
        executor.evaluate_term(&model, eq_xy),
        EvalValue::Bool(false)
    ); // 255!=44

    // -1 and 255 must compare equal after normalization
    let model2 = bv_model(&[(x, -1), (y, 255)]);
    assert_eq!(
        executor.evaluate_term(&model2, eq_xy),
        EvalValue::Bool(true)
    );
}

/// Regression test for #5737 AC6: bvsdiv/bvsrem/bvsmod edge cases.
///
/// Tests: div-by-zero, negative dividends/divisors, sign handling,
/// non-normalized inputs.
#[test]
fn test_bv_signed_div_rem_mod_edge_cases() {
    let mut executor = Executor::new();
    let bv8 = Sort::bitvec(8);
    let x = executor.ctx.terms.mk_var("x", bv8.clone());
    let y = executor.ctx.terms.mk_var("y", bv8.clone());
    let mk =
        |e: &mut Executor, op: &str, s: Sort| e.ctx.terms.mk_app(Symbol::named(op), vec![x, y], s);
    let bvsdiv = mk(&mut executor, "bvsdiv", bv8.clone());
    let bvsrem = mk(&mut executor, "bvsrem", bv8.clone());
    let bvsmod = mk(&mut executor, "bvsmod", bv8);
    let bv = |v: u8| EvalValue::BitVec {
        value: BigInt::from(v),
        width: 8,
    };

    // --- Division by zero ---
    // SMT-LIB: bvsdiv(x, 0) = all 1s if x >= 0, else 1
    // bvsrem(x, 0) = x, bvsmod(x, 0) = x
    // x = 7 (positive), y = 0
    let model = bv_model(&[(x, 7), (y, 0)]);
    assert_eq!(executor.evaluate_term(&model, bvsdiv), bv(255)); // all 1s
    assert_eq!(executor.evaluate_term(&model, bvsrem), bv(7)); // dividend
    assert_eq!(executor.evaluate_term(&model, bvsmod), bv(7)); // dividend

    // x = -3 (= 253 unsigned), y = 0
    let model = bv_model(&[(x, 253), (y, 0)]);
    assert_eq!(executor.evaluate_term(&model, bvsdiv), bv(1)); // 1 for negative
    assert_eq!(executor.evaluate_term(&model, bvsrem), bv(253)); // dividend
    assert_eq!(executor.evaluate_term(&model, bvsmod), bv(253)); // dividend

    // --- Normal signed division ---
    // x = -6 (= 250), y = 3 => sdiv = -2 (= 254), srem = 0, smod = 0
    let model = bv_model(&[(x, 250), (y, 3)]);
    assert_eq!(executor.evaluate_term(&model, bvsdiv), bv(254)); // -2
    assert_eq!(executor.evaluate_term(&model, bvsrem), bv(0));
    assert_eq!(executor.evaluate_term(&model, bvsmod), bv(0));

    // x = -7 (= 249), y = 3 => sdiv = -2 (= 254), srem = -1 (= 255), smod = 2
    // srem: sign follows dividend (-7 % 3 = -1)
    // smod: sign follows divisor  (-7 mod 3 = 2, since -1 + 3 = 2)
    let model = bv_model(&[(x, 249), (y, 3)]);
    assert_eq!(executor.evaluate_term(&model, bvsdiv), bv(254)); // -2 (truncate toward zero: -7/3 = -2.33 -> -2)
    assert_eq!(executor.evaluate_term(&model, bvsrem), bv(255)); // -1 (sign of dividend)
    assert_eq!(executor.evaluate_term(&model, bvsmod), bv(2)); // 2 (sign of divisor, positive)

    // x = 7, y = -3 (= 253) => sdiv = -2 (= 254), srem = 1, smod = -2 (= 254)
    // srem: sign follows dividend (7 % -3 = 1)
    // smod: sign follows divisor  (7 mod -3 = -2, since 1 + (-3) = -2)
    let model = bv_model(&[(x, 7), (y, 253)]);
    assert_eq!(executor.evaluate_term(&model, bvsdiv), bv(254)); // -2
    assert_eq!(executor.evaluate_term(&model, bvsrem), bv(1)); // 1 (sign of dividend, positive)
    assert_eq!(executor.evaluate_term(&model, bvsmod), bv(254)); // -2 (sign of divisor, negative)

    // --- Non-normalized inputs ---
    // x = -1 (should normalize to 255 = -1 signed), y = -1 (= 255)
    // sdiv(-1, -1) = 1, srem(-1, -1) = 0, smod(-1, -1) = 0
    let model = bv_model(&[(x, -1), (y, -1)]);
    assert_eq!(executor.evaluate_term(&model, bvsdiv), bv(1));
    assert_eq!(executor.evaluate_term(&model, bvsrem), bv(0));
    assert_eq!(executor.evaluate_term(&model, bvsmod), bv(0));
}
