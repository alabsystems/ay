// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `tests` to preserve test FQNs.

#[test]
fn finite_quantifier_bool_enumeration_overrides_and_restores_ambient_memo() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Bool)], x);
    let exists = terms.mk_exists(vec![("x".to_string(), Sort::Bool)], x);
    let model = StubModel::new().with(x, ModelValue::Bool(true));
    let evaluator = Evaluator::new(&terms, &model);
    assert!(matches!(
        evaluator.evaluate(x),
        EvalOutcome::Value(ModelValue::Bool(true))
    ));
    assert!(matches!(
        evaluator.evaluate(forall),
        EvalOutcome::Value(ModelValue::Bool(false))
    ));
    assert!(matches!(
        evaluator.evaluate(exists),
        EvalOutcome::Value(ModelValue::Bool(true))
    ));
    assert!(matches!(
        evaluator.evaluate(x),
        EvalOutcome::Value(ModelValue::Bool(true))
    ));
    assert_violates(&verdict(&terms, &model, &[forall]));
    assert_confirmed(&verdict(&terms, &model, &[exists]));
}

#[test]
fn finite_quantifier_bitvec_last_assignment_is_not_skipped() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let last = terms.mk_bitvec(BigInt::from(255u16), 8);
    let equal = app(&mut terms, "=", &[x, last], Sort::Bool);
    let not_equal = terms.mk_not(equal);
    let exists = terms.mk_exists(vec![("x".to_string(), Sort::bitvec(8))], equal);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::bitvec(8))], not_equal);
    assert_confirmed(&verdict(&terms, &StubModel::new(), &[exists]));
    assert_violates(&verdict(&terms, &StubModel::new(), &[forall]));
}

#[test]
fn finite_quantifier_nested_alternation_and_cartesian_domains() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(2));
    let y = terms.mk_var("y", Sort::bitvec(2));
    let equal = app(&mut terms, "=", &[x, y], Sort::Bool);
    let some_y = terms.mk_exists(vec![("y".to_string(), Sort::bitvec(2))], equal);
    let every_x = terms.mk_forall(vec![("x".to_string(), Sort::bitvec(2))], some_y);
    let every_y = terms.mk_forall(vec![("y".to_string(), Sort::bitvec(2))], equal);
    let some_x = terms.mk_exists(vec![("x".to_string(), Sort::bitvec(2))], every_y);
    let all_pairs = terms.mk_forall(
        vec![
            ("x".to_string(), Sort::bitvec(2)),
            ("y".to_string(), Sort::bitvec(2)),
        ],
        equal,
    );
    assert_confirmed(&verdict(&terms, &StubModel::new(), &[every_x]));
    assert_violates(&verdict(&terms, &StubModel::new(), &[some_x]));
    assert_violates(&verdict(&terms, &StubModel::new(), &[all_pairs]));
}

#[test]
fn finite_quantifier_shadowing_handles_same_name_and_different_sorts() {
    let mut terms = TermStore::new();
    let outer = terms.mk_var("x", Sort::Bool);
    let inner = terms.mk_fresh_named_var("x", Sort::bitvec(1));
    let one = terms.mk_bitvec(BigInt::from(1), 1);
    let eq_one = app(&mut terms, "=", &[inner, one], Sort::Bool);
    let inner_exists = terms.mk_exists(vec![("x".to_string(), Sort::bitvec(1))], eq_one);
    let same = app(&mut terms, "=", &[outer, inner_exists], Sort::Bool);
    let all = terms.mk_forall(vec![("x".to_string(), Sort::Bool)], same);
    // The inner existential is true; it must not replace outer x=false.
    assert_violates(&verdict(&terms, &StubModel::new(), &[all]));

    let inner_all = terms.mk_forall(vec![("x".to_string(), Sort::Bool)], outer);
    let implies = app(&mut terms, "=>", &[outer, inner_all], Sort::Bool);
    let outer_all = terms.mk_forall(vec![("x".to_string(), Sort::Bool)], implies);
    assert_violates(&verdict(&terms, &StubModel::new(), &[outer_all]));
}

#[test]
fn finite_quantifier_and_lambda_bindings_shadow_in_both_orders() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let no = terms.mk_bool(false);
    let yes = terms.mk_bool(true);
    let identity = terms.mk_lambda_array(x, x);
    let read_false = app(&mut terms, "select", &[identity, no], Sort::Bool);
    let not_read = terms.mk_not(read_false);
    let outside = terms.mk_forall(vec![("x".to_string(), Sort::Bool)], not_read);
    assert_confirmed(&verdict(&terms, &StubModel::new(), &[outside]));

    let inside = terms.mk_forall(vec![("x".to_string(), Sort::Bool)], x);
    let lambda = terms.mk_lambda_array(x, inside);
    let read_true = app(&mut terms, "select", &[lambda, yes], Sort::Bool);
    let not_read = terms.mk_not(read_true);
    assert_confirmed(&verdict(&terms, &StubModel::new(), &[not_read]));
}

#[test]
fn finite_quantifier_unknown_instances_do_not_hide_decisive_later_values() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let unknown = terms.mk_var("unknown", Sort::Bool);
    let yes = terms.mk_bool(true);
    let no = terms.mk_bool(false);
    let some_body = terms.mk_ite(x, yes, unknown);
    let all_body = terms.mk_ite(x, no, unknown);
    let exists = terms.mk_exists(vec![("x".to_string(), Sort::Bool)], some_body);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Bool)], all_body);
    let incomplete = terms.mk_forall(vec![("x".to_string(), Sort::Bool)], some_body);
    assert_confirmed(&verdict(&terms, &StubModel::new(), &[exists]));
    assert_violates(&verdict(&terms, &StubModel::new(), &[forall]));
    assert_cannot(&verdict(&terms, &StubModel::new(), &[incomplete]));
    // An unevaluable inner quantifier must restore x before the next assertion.
    let model = StubModel::new().with(x, ModelValue::Bool(false));
    let evaluator = Evaluator::new(&terms, &model);
    assert!(matches!(
        evaluator.evaluate(incomplete),
        EvalOutcome::Unevaluable(_)
    ));
    assert!(matches!(
        evaluator.evaluate(x),
        EvalOutcome::Value(ModelValue::Bool(false))
    ));
}

#[test]
fn finite_quantifier_checks_concrete_array_cells_and_rejects_ambient_read_pins() {
    let mut terms = TermStore::new();
    let index = terms.mk_var("index", Sort::bitvec(2));
    let array = terms.mk_var("array", Sort::array(Sort::bitvec(2), Sort::Int));
    let read = app(&mut terms, "select", &[array, index], Sort::Int);
    let seven = terms.mk_int(int(7));
    let eq = app(&mut terms, "=", &[read, seven], Sort::Bool);
    let all = terms.mk_forall(vec![("index".to_string(), Sort::bitvec(2))], eq);
    let good = StubModel::new().with(
        array,
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Int(int(7)),
            store: vec![],
        })),
    );
    let bad = StubModel::new().with(
        array,
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Int(int(7)),
            store: vec![(ModelValue::bitvec(int(3), 2), ModelValue::Int(int(8)))],
        })),
    );
    assert_confirmed(&verdict(&terms, &good, &[all]));
    assert_violates(&verdict(&terms, &bad, &[all]));
    let ambient_pin = UfStubModel::new().sel(read, ModelValue::Int(int(7)));
    assert_cannot(&verdict(&terms, &ambient_pin, &[all]));
}

#[test]
fn finite_quantifier_uses_only_value_keyed_uf_observations_for_bound_applications() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let no = terms.mk_bool(false);
    let yes = terms.mk_bool(true);
    let f_no = app(&mut terms, "f", &[no], Sort::Bool);
    let f_yes = app(&mut terms, "f", &[yes], Sort::Bool);
    let f_x = app(&mut terms, "f", &[x], Sort::Bool);
    let eq = app(&mut terms, "=", &[f_x, x], Sort::Bool);
    let all = terms.mk_forall(vec![("x".to_string(), Sort::Bool)], eq);
    let model = UfStubModel::new()
        .uf(f_no, ModelValue::Bool(false))
        .uf(f_yes, ModelValue::Bool(true))
        .uf(f_x, ModelValue::Bool(false));
    let evaluator = Evaluator::new(&terms, &model);
    assert!(matches!(
        evaluator.evaluate(all),
        EvalOutcome::Unevaluable(_)
    ));
    assert!(matches!(
        evaluator.evaluate(f_no),
        EvalOutcome::Value(ModelValue::Bool(false))
    ));
    assert!(matches!(
        evaluator.evaluate(f_yes),
        EvalOutcome::Value(ModelValue::Bool(true))
    ));
    assert!(matches!(
        evaluator.evaluate(all),
        EvalOutcome::Value(ModelValue::Bool(true))
    ));

    let wrong = UfStubModel::new()
        .uf(f_no, ModelValue::Bool(false))
        .uf(f_yes, ModelValue::Bool(false));
    let evaluator = Evaluator::new(&terms, &wrong);
    let _ = evaluator.evaluate(f_no);
    let _ = evaluator.evaluate(f_yes);
    assert!(matches!(
        evaluator.evaluate(all),
        EvalOutcome::Value(ModelValue::Bool(false))
    ));
}

#[test]
fn finite_quantifier_refuses_unsupported_malformed_and_over_budget_domains() {
    let mut terms = TermStore::new();
    let yes = terms.mk_bool(true);
    let sorts = [Sort::bitvec(0), Sort::bitvec(17), Sort::bitvec(u32::MAX)];
    for sort in sorts {
        let all = terms.mk_forall(vec![("unused".to_string(), sort)], yes);
        assert_cannot(&verdict(&terms, &StubModel::new(), &[all]));
    }
    // An UNUSED Int/Real binder is trivially equality-only: the planner
    // (#eq-only-quantifier-eval) evaluates the body at one fresh value, which
    // over a non-empty carrier is exact (`∀x. φ ≡ φ` when `x` is not free).
    for sort in [Sort::Int, Sort::Real] {
        let all = terms.mk_forall(vec![("unused".to_string(), sort)], yes);
        assert_confirmed(&verdict(&terms, &StubModel::new(), &[all]));
    }
    // An unbounded Int/Real binder used outside an equality stays refused.
    let y = terms.mk_var("y", Sort::Real);
    let reflexive = app(&mut terms, "<=", &[y, y], Sort::Bool);
    let ordered = terms.mk_forall(vec![("y".to_string(), Sort::Real)], reflexive);
    assert_cannot(&verdict(&terms, &StubModel::new(), &[ordered]));
    let duplicate = terms.mk_forall(
        vec![("x".to_string(), Sort::Bool), ("x".to_string(), Sort::Bool)],
        yes,
    );
    assert_cannot(&verdict(&terms, &StubModel::new(), &[duplicate]));
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(int(0));
    let eq = app(&mut terms, "=", &[x, zero], Sort::Bool);
    let wrong_sort = terms.mk_forall(vec![("x".to_string(), Sort::Bool)], eq);
    assert_cannot(&verdict(
        &terms,
        &StubModel::new().with(x, ModelValue::Int(int(0))),
        &[wrong_sort],
    ));
}

#[test]
fn finite_quantifier_assignment_budget_is_shared_across_assertion_roots() {
    let mut terms = TermStore::new();
    let yes = terms.mk_bool(true);
    let roots: Vec<_> = (0..257)
        .map(|index| terms.mk_forall(vec![(format!("unused_{index}"), Sort::bitvec(8))], yes))
        .collect();
    let model = StubModel::new();
    let evaluator = Evaluator::new(&terms, &model);
    for &root in &roots[..256] {
        assert!(matches!(
            evaluator.evaluate(root),
            EvalOutcome::Value(ModelValue::Bool(true))
        ));
    }
    assert!(
        matches!(evaluator.evaluate(roots[256]), EvalOutcome::Unevaluable(reason) if reason.contains("assignment budget"))
    );
    assert!(matches!(
        Evaluator::new(&terms, &model).evaluate(roots[256]),
        EvalOutcome::Value(ModelValue::Bool(true))
    ));
}

#[test]
fn finite_quantifier_nested_enumeration_and_large_bodies_share_work_budget() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let same = app(&mut terms, "=", &[x, x], Sort::Bool);
    let inner = terms.mk_forall(vec![("y".to_string(), Sort::bitvec(8))], same);
    let outer = terms.mk_forall(vec![("x".to_string(), Sort::bitvec(8))], inner);
    assert!(
        matches!(evaluate_term(&terms, &StubModel::new(), outer), EvalOutcome::Unevaluable(reason) if reason.contains("budget"))
    );

    let repeated = app(&mut terms, "and", &vec![same; 1024], Sort::Bool);
    let expensive = terms.mk_forall(vec![("x".to_string(), Sort::bitvec(8))], repeated);
    assert!(
        matches!(evaluate_term(&terms, &StubModel::new(), expensive), EvalOutcome::Unevaluable(reason) if reason.contains("evaluation work budget"))
    );
}

#[test]
fn finite_quantifier_cannot_reuse_an_opaque_array_default_pin() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);
    let body = app(&mut terms, "xor", &[x, y], Sort::Bool);
    let array = terms.mk_lambda_array(y, body);
    let default = terms.mk_array_default(array);
    let all = terms.mk_forall(vec![("x".to_string(), Sort::Bool)], default);
    let model = UfStubModel::new().uf(default, ModelValue::Bool(true));
    assert_cannot(&verdict(&terms, &model, &[all]));
}

#[test]
fn finite_quantifier_distinct_pairs_consume_the_shared_work_budget() {
    let mut terms = TermStore::new();
    let constants: Vec<_> = (0..1600).map(|value| terms.mk_int(int(value))).collect();
    let distinct = app(&mut terms, "distinct", &constants, Sort::Bool);
    let all = terms.mk_forall(vec![("unused".to_string(), Sort::Bool)], distinct);
    // Each comparison is locally tiny, but together the pairs exceed the
    // one quantifier-wide envelope before either valuation may be accepted.
    assert!(
        matches!(evaluate_term(&terms, &StubModel::new(), all), EvalOutcome::Unevaluable(reason) if reason.contains("evaluation work budget"))
    );
}

#[test]
fn finite_quantifier_observations_constrain_residual_array_completion() {
    let mut terms = TermStore::new();
    let array_sort = Sort::array(Sort::Bool, struct_sort());
    let a = terms.mk_var("a", array_sort.clone());
    let b = terms.mk_var("b", array_sort);
    let index = terms.mk_bool(false);
    let a_read = app(&mut terms, "select", &[a, index], struct_sort());
    let a_field = app(&mut terms, "f", &[a_read], Sort::Int);
    let six = terms.mk_int(int(6));
    let five = terms.mk_int(int(5));
    let a_is_six = app(&mut terms, "=", &[a_field, six], Sort::Bool);
    let quantified = terms.mk_forall(vec![("unused".to_string(), Sort::Bool)], a_is_six);
    let aliases = app(&mut terms, "=", &[a, b], Sort::Bool);
    let b_is_five = field_read_eq(&mut terms, "f", b, index, five);
    let model = UfStubModel::new().uf(a_field, ModelValue::Int(int(6)));
    // The quantified assertion can adopt this binder-independent pin. A
    // residual witness must not overwrite it with b[false].f = 5 afterward.
    assert_confirmed(&verdict(&terms, &model, &[quantified]));
    assert_cannot(&verdict(&terms, &model, &[quantified, aliases, b_is_five]));
}

include!("finite_quantifier_boundaries.rs");
include!("guarded_quantifier_ranges.rs");
include!("compound_quantifier_endpoints.rs");
include!("joint_quantifier_ranges.rs");
