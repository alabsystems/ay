// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `tests` to preserve test FQNs.

#[test]
fn uf_collapsed_arguments_refute_strict_inequality() {
    // The uflia89 shape: `(> (f (* 3 i0)) (f i0))` with `i0 = 0`. Both `(* 3 i0)`
    // and `i0` evaluate to 0, so both applications are `f(0)`; the model pins
    // them to different results (0 and -1). The gate collapses them to one value
    // (first-wins), so `(> v v)` is `false` — a caught wrong witness. (Emitting
    // 0 and -1 for the SAME `f(0)` is exactly the internally-inconsistent model
    // z3 rejects when the scalars are pinned.)
    let mut ts = TermStore::new();
    let i0 = ts.mk_var("i0", Sort::Int);
    let three = ts.mk_int(int(3));
    let mul = app(&mut ts, "*", &[three, i0], Sort::Int);
    let f_hi = app(&mut ts, "f", &[mul], Sort::Int); // f(3*i0)
    let f_lo = app(&mut ts, "f", &[i0], Sort::Int); // f(i0)
    let gt = app(&mut ts, ">", &[f_hi, f_lo], Sort::Bool);
    let m = UfStubModel::new()
        .leaf(i0, ModelValue::Int(int(0)))
        .uf(f_hi, ModelValue::Int(int(0)))
        .uf(f_lo, ModelValue::Int(int(-1)));
    assert_violates(&verdict(&ts, &m, &[gt]));
}

#[test]
fn uf_distinct_arguments_confirm_valid_model() {
    // Distinct arguments (a = 5, b = 7): the two applications key differently and
    // keep their own committed values (f(5) = 1 > f(7) = 0), so the witness is
    // confirmed. The UF handling must NOT over-refute genuine models.
    let mut ts = TermStore::new();
    let a = ts.mk_var("a", Sort::Int);
    let b = ts.mk_var("b", Sort::Int);
    let f_a = app(&mut ts, "f", &[a], Sort::Int);
    let f_b = app(&mut ts, "f", &[b], Sort::Int);
    let gt = app(&mut ts, ">", &[f_a, f_b], Sort::Bool);
    let m = UfStubModel::new()
        .leaf(a, ModelValue::Int(int(5)))
        .leaf(b, ModelValue::Int(int(7)))
        .uf(f_a, ModelValue::Int(int(1)))
        .uf(f_b, ModelValue::Int(int(0)));
    assert_confirmed(&verdict(&ts, &m, &[gt]));
}

#[test]
fn uf_congruent_applications_share_one_value() {
    // Two applications with equal arguments (a = b = 5) must denote the same
    // value: `(= (f a) (f b))` holds even though the model pins them to
    // different committed values (the first-seen value, 1, wins for both).
    let mut ts = TermStore::new();
    let a = ts.mk_var("a", Sort::Int);
    let b = ts.mk_var("b", Sort::Int);
    let f_a = app(&mut ts, "f", &[a], Sort::Int);
    let f_b = app(&mut ts, "f", &[b], Sort::Int);
    let eq = app(&mut ts, "=", &[f_a, f_b], Sort::Bool);
    let m = UfStubModel::new()
        .leaf(a, ModelValue::Int(int(5)))
        .leaf(b, ModelValue::Int(int(5)))
        .uf(f_a, ModelValue::Int(int(1)))
        .uf(f_b, ModelValue::Int(int(2)));
    // Congruent apps collapse to one value, so equality is TRUE (not a spurious
    // violation): `(= 1 1)`.
    assert_confirmed(&verdict(&ts, &m, &[eq]));
}

#[test]
fn uf_array_keys_with_finite_domain_coverage_fail_closed() {
    // The two array arguments are extensionally equal over Bool even though
    // their stored defaults differ: the left stores cover both domain values.
    // They therefore denote one UF graph key. Without index-sort evidence the
    // key comparison must remain unresolved, never install two results and
    // confirm the impossible conjunction `f(left) = 7 ∧ f(right) = 8`.
    let mut ts = TermStore::new();
    let array_sort = Sort::array(Sort::Bool, Sort::Int);
    let zero = ts.mk_int(int(0));
    let one = ts.mk_int(int(1));
    let false_index = ts.mk_bool(false);
    let true_index = ts.mk_bool(true);
    let one_default = app(&mut ts, "const-array", &[one], array_sort.clone());
    let with_false = app(
        &mut ts,
        "store",
        &[one_default, false_index, zero],
        array_sort.clone(),
    );
    let fully_covered = app(
        &mut ts,
        "store",
        &[with_false, true_index, zero],
        array_sort.clone(),
    );
    let zero_default = app(&mut ts, "const-array", &[zero], array_sort);
    let left_app = app(&mut ts, "f", &[fully_covered], Sort::Int);
    let right_app = app(&mut ts, "f", &[zero_default], Sort::Int);
    let seven = ts.mk_int(int(7));
    let eight = ts.mk_int(int(8));
    let left_definition = app(&mut ts, "=", &[left_app, seven], Sort::Bool);
    let right_definition = app(&mut ts, "=", &[right_app, eight], Sort::Bool);
    let model = UfStubModel::new()
        .uf(left_app, ModelValue::Int(int(7)))
        .uf(right_app, ModelValue::Int(int(8)));

    assert_cannot(&verdict(&ts, &model, &[left_definition, right_definition]));
}

#[test]
fn congruence_key_definite_difference_overrides_an_unresolved_component() {
    // A multi-argument graph entry is a definite miss when ANY component is
    // proven different, even if another component's equality is undecidable.
    // The matcher must scan past the algebraic gap rather than failing closed
    // too early and needlessly losing a valid, distinct function point.
    let stored = vec![
        sqrt_two_between(
            BigRational::from_integer(int(1)),
            BigRational::from_integer(int(2)),
        ),
        ModelValue::Int(int(1)),
    ];
    let candidate = vec![
        sqrt_two_between(
            BigRational::new(int(4), int(3)),
            BigRational::new(int(3), int(2)),
        ),
        ModelValue::Int(int(2)),
    ];

    assert!(matches!(
        eval::congruence_keys_equal(&stored, &candidate),
        Ok(false)
    ));
}

#[test]
fn selector_graph_key_matcher_fails_closed_on_nested_algebraic_gap() {
    // Selector fallback keys are committed datatype values. Two equal
    // datatype values can carry equal algebraic fields represented in
    // different extensions, so the recursive `value_eq` gap must propagate;
    // it is not evidence that two selector arguments are distinct.
    let stored = ModelValue::Datatype {
        ctor: "WrongConstructor".to_string(),
        args: vec![sqrt_two_between(
            BigRational::from_integer(int(1)),
            BigRational::from_integer(int(2)),
        )],
    };
    let candidate = ModelValue::Datatype {
        ctor: "WrongConstructor".to_string(),
        args: vec![sqrt_two_between(
            BigRational::new(int(4), int(3)),
            BigRational::new(int(3), int(2)),
        )],
    };

    match eval::congruence_keys_equal(
        std::slice::from_ref(&stored),
        std::slice::from_ref(&candidate),
    ) {
        Err(reason) => assert!(reason.contains("algebraic equality across different extensions")),
        other => panic!("selector key equality gap must remain unresolved, got {other:?}"),
    }
}

#[test]
fn selector_graph_equal_cross_extension_arguments_fail_closed() {
    // Make the selector argument itself unevaluable (its array index is
    // unpinned), while supplying the model's committed value for that exact
    // read. This reaches the selector-specific fallback graph. `get` is
    // under-specified on constructor Bad, but it remains a single-valued
    // function: two equal Bad(sqrt(2)) arguments cannot receive 7 and 8.
    let mut ts = TermStore::new();
    let datatype = Sort::Datatype(DatatypeSort::new(
        "Choice",
        vec![
            DatatypeConstructor::new("Good", vec![DatatypeField::new("get", Sort::Int)]),
            DatatypeConstructor::new("Bad", vec![DatatypeField::new("payload", Sort::Real)]),
        ],
    ));
    let array_sort = Sort::array(Sort::Int, datatype.clone());
    let array = ts.mk_var("choices", array_sort);
    let left_index = ts.mk_var("left-index", Sort::Int); // deliberately unpinned
    let right_index = ts.mk_var("right-index", Sort::Int); // deliberately unpinned
    let left_argument = app(&mut ts, "select", &[array, left_index], datatype.clone());
    let right_argument = app(&mut ts, "select", &[array, right_index], datatype);
    let left_selector = app(&mut ts, "get", &[left_argument], Sort::Int);
    let right_selector = app(&mut ts, "get", &[right_argument], Sort::Int);
    let model = UfStubModel::new()
        .sel(
            left_argument,
            ModelValue::Datatype {
                ctor: "Bad".to_string(),
                args: vec![sqrt_two_between(
                    BigRational::from_integer(int(1)),
                    BigRational::from_integer(int(2)),
                )],
            },
        )
        .sel(
            right_argument,
            ModelValue::Datatype {
                ctor: "Bad".to_string(),
                args: vec![sqrt_two_between(
                    BigRational::new(int(4), int(3)),
                    BigRational::new(int(3), int(2)),
                )],
            },
        )
        .uf(left_selector, ModelValue::Int(int(7)))
        .uf(right_selector, ModelValue::Int(int(8)));
    let evaluator = Evaluator::new(&ts, &model);

    assert!(matches!(
        evaluator.evaluate(left_selector),
        EvalOutcome::Value(ModelValue::Int(value)) if value == int(7)
    ));
    assert!(
        matches!(
            evaluator.evaluate(right_selector),
            EvalOutcome::Unevaluable(_)
        ),
        "an unresolved equality with the existing selector key must fail closed"
    );
}

#[test]
fn projection_reuses_outer_value_keyed_uf_graph() {
    // `1` and `(bvadd 0 1)` are the same argument value, so both `g`
    // applications denote one result even though the supplied per-term pins
    // conflict. The projection must evaluate its selected nested application
    // in the existing Evaluator: a fresh evaluator would forget the first
    // `g(1) = #x10`, adopt `g(0+1) = #x20`, and wrongly confirm `distinct`.
    let mut ts = TermStore::new();
    let bv8 = Sort::bitvec(8);
    let zero = ts.mk_bitvec(int(0), 8);
    let one = ts.mk_bitvec(int(1), 8);
    let dummy = ts.mk_bitvec(int(0xaa), 8);
    let equivalent_one = app(&mut ts, "bvadd", &[zero, one], bv8.clone());
    let g_direct = app(&mut ts, "g", &[one], bv8.clone());
    let g_equivalent = app(&mut ts, "g", &[equivalent_one], bv8.clone());
    let projected = app(&mut ts, "projection", &[dummy, g_equivalent], bv8.clone());
    let distinct = app(&mut ts, "distinct", &[g_direct, projected], Sort::Bool);
    let m = UfStubModel::new()
        .uf(g_direct, ModelValue::bitvec(int(0x10), 8))
        .uf(g_equivalent, ModelValue::bitvec(int(0x20), 8))
        .projection(projected, 1);
    assert_violates(&verdict(&ts, &m, &[distinct]));
}

#[test]
fn projection_metadata_is_validated_before_beta_reduction() {
    let mut ts = TermStore::new();
    let one = ts.mk_int(int(1));
    let out_of_bounds = app(&mut ts, "bad_index", &[one], Sort::Int);
    let wrong_sort = app(&mut ts, "bad_sort", &[one], Sort::Bool);
    let m = UfStubModel::new()
        .uf(out_of_bounds, ModelValue::Int(int(9)))
        .uf(wrong_sort, ModelValue::Bool(true))
        .projection(out_of_bounds, 1)
        .projection(wrong_sort, 0);

    match evaluate_term(&ts, &m, out_of_bounds) {
        EvalOutcome::Unevaluable(reason) => assert!(reason.contains("application arity is 1")),
        other => panic!("invalid projection index must fail closed, got {other:?}"),
    }
    match evaluate_term(&ts, &m, wrong_sort) {
        EvalOutcome::Unevaluable(reason) => assert!(reason.contains("does not match result sort")),
        other => panic!("ill-sorted projection must fail closed, got {other:?}"),
    }
}

#[test]
fn projection_lookup_error_precedes_per_application_uf_value() {
    let mut ts = TermStore::new();
    let one = ts.mk_int(int(1));
    let application = app(&mut ts, "conflicting_projection", &[one], Sort::Int);
    let model = UfStubModel::new()
        .uf(application, ModelValue::Int(int(99)))
        .projection_error(application, "installed and observed signatures differ");

    match evaluate_term(&ts, &model, application) {
        EvalOutcome::Unevaluable(reason) => {
            assert!(reason.contains("inconsistent symbolic projection model"));
            assert!(reason.contains("signatures differ"));
        }
        other => panic!("a projection conflict must not fall through to the UF pin, got {other:?}"),
    }
}

#[test]
fn projections_do_not_reset_the_evaluator_depth_budget() {
    let mut ts = TermStore::new();
    let bv8 = Sort::bitvec(8);
    let dummy = ts.mk_bitvec(int(0), 8);
    let mut nested = ts.mk_bitvec(int(1), 8);
    let mut m = UfStubModel::new();
    // Each layer contributes one projection edge and one ordinary interpreted
    // edge. Resetting depth at projection boundaries would evaluate this whole
    // chain; one continuous evaluator must stop once the shared bound is spent.
    for _ in 0..(MAX_EVAL_DEPTH / 2 + 2) {
        let inverted = app(&mut ts, "bvnot", &[nested], bv8.clone());
        nested = app(&mut ts, "depth_projection", &[dummy, inverted], bv8.clone());
        m = m.projection(nested, 1);
    }
    match evaluate_term(&ts, &m, nested) {
        EvalOutcome::Unevaluable(reason) => assert!(reason.contains("recursion depth limit")),
        other => panic!("projection edges must consume the shared depth budget, got {other:?}"),
    }
}

#[test]
fn projection_evaluator_call_depth_is_restored_between_evaluations() {
    let mut ts = TermStore::new();
    let selected = ts.mk_bool(true);
    let dummy = ts.mk_bool(false);
    let projected = app(
        &mut ts,
        "reused_shallow_projection",
        &[dummy, selected],
        Sort::Bool,
    );
    let model = UfStubModel::new().projection(projected, 1);
    let evaluator = Evaluator::new(&ts, &model);

    // This deliberately crosses the projection-specific active-call bound.
    // Every top-level evaluation must restore the counter to zero; a leaked
    // increment would make the 129th call fail closed despite being shallow.
    for attempt in 0..256 {
        assert!(
            matches!(
                evaluator.evaluate(projected),
                EvalOutcome::Value(ModelValue::Bool(true))
            ),
            "shallow projection failed on top-level evaluation {attempt}"
        );
    }
}

#[test]
fn uf_unpinned_application_cannot_confirm() {
    // If the model does not pin an application value, the application is
    // unevaluable and the gate fails closed (never assumed) — CannotConfirm.
    let mut ts = TermStore::new();
    let a = ts.mk_var("a", Sort::Int);
    let f_a = app(&mut ts, "f", &[a], Sort::Int);
    let zero = ts.mk_int(int(0));
    let gt = app(&mut ts, ">", &[f_a, zero], Sort::Bool);
    let m = UfStubModel::new().leaf(a, ModelValue::Int(int(5))); // no uf pin
    assert_cannot(&verdict(&ts, &m, &[gt]));
}
