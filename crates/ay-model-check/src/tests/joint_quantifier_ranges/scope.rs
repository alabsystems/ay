// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#[test]
fn joint_bound_names_ignore_ambient_pins_and_restore_them_after_evaluation() {
    let mut terms = TermStore::new();
    let fixture = matrix(&mut terms);
    let model = StubModel::new()
        .with(fixture.outer, matrix_value(false))
        .with(fixture.r, bv(99))
        .with(fixture.c, bv(98));
    let evaluator = Evaluator::new(&terms, &model);
    assert_bv(evaluator.evaluate(fixture.r), 99);
    assert_bv(evaluator.evaluate(fixture.c), 98);
    assert!(matches!(
        evaluator.evaluate(fixture.all),
        EvalOutcome::Value(ModelValue::Bool(true))
    ));
    assert_bv(evaluator.evaluate(fixture.r), 99);
    assert_bv(evaluator.evaluate(fixture.c), 98);
}

#[test]
fn joint_reverse_dependency_refuses_even_when_future_name_has_a_model_value() {
    let mut terms = TermStore::new();
    let fixture = matrix(&mut terms);
    let body = app(&mut terms, "=>", &[fixture.guard, fixture.read], Sort::Bool);
    let mut reversed = bindings();
    reversed.reverse();
    let all = terms.mk_forall(reversed, body);
    let model = StubModel::new()
        .with(fixture.outer, matrix_value(false))
        .with(fixture.r, bv(0))
        .with(fixture.c, bv(0));
    let evaluator = Evaluator::new(&terms, &model);
    assert_bv(evaluator.evaluate(fixture.r), 0);
    assert!(matches!(
        evaluator.evaluate(all),
        EvalOutcome::Unevaluable(_)
    ));
    assert_bv(evaluator.evaluate(fixture.r), 0);
    // The ordered source is supported on that same evaluator after refusal;
    // no placeholder/future binding leaks out of failed planning.
    assert!(matches!(
        evaluator.evaluate(fixture.all),
        EvalOutcome::Value(ModelValue::Bool(true))
    ));
}

#[test]
fn joint_self_and_future_endpoints_do_not_use_placeholder_zeroes_or_model_pins() {
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", Sort::bitvec(64));
    let c = terms.mk_var("c", Sort::bitvec(64));
    let alias = terms.mk_fresh_named_var("r", Sort::bitvec(64));
    let one = terms.mk_bitvec(int(1), 64);
    let two = terms.mk_bitvec(int(2), 64);
    let self_bound = app(&mut terms, "bvadd", &[alias, one], Sort::bitvec(64));
    let c_bound = app(&mut terms, "bvult", &[c, two], Sort::Bool);
    let property = terms.mk_var("property", Sort::Bool);
    let model = StubModel::new()
        .with(r, bv(0))
        .with(alias, bv(0))
        .with(c, bv(0))
        .with(property, ModelValue::Bool(false));
    for endpoint in [c, self_bound] {
        let r_bound = app(&mut terms, "bvult", &[r, endpoint], Sort::Bool);
        let guard = app(&mut terms, "and", &[r_bound, c_bound], Sort::Bool);
        let (all, some_bad) = quantified_pair(&mut terms, guard, property);
        assert_cannot(&verdict(&terms, &model, &[all]));
        assert_cannot(&verdict(&terms, &model, &[some_bad]));
    }
}

#[test]
fn joint_mixed_small_bool_carrier_and_wide_guarded_range_remain_supported() {
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", Sort::bitvec(64));
    let flag = terms.mk_var("flag", Sort::Bool);
    let two = terms.mk_bitvec(int(2), 64);
    let guard = app(&mut terms, "bvult", &[r, two], Sort::Bool);
    let not_flag = terms.mk_not(flag);
    let tautology = app(&mut terms, "or", &[flag, not_flag], Sort::Bool);
    let all = app(&mut terms, "=>", &[guard, tautology], Sort::Bool);
    let some = app(&mut terms, "and", &[guard, flag], Sort::Bool);
    let names = vec![
        ("r".to_string(), Sort::bitvec(64)),
        ("flag".to_string(), Sort::Bool),
    ];
    let all = terms.mk_forall(names.clone(), all);
    let some = terms.mk_exists(names, some);
    assert_confirmed(&verdict(&terms, &StubModel::new(), &[all, some]));
}

#[test]
fn joint_uf_endpoints_and_opaque_receivers_do_not_gain_structural_authority() {
    let mut terms = TermStore::new();
    let fixture = matrix(&mut terms);
    assert_cannot(&verdict(&terms, &StubModel::new(), &[fixture.all]));
    let two = terms.mk_bitvec(int(2), 64);
    let r_bound = app(&mut terms, "bvult", &[fixture.r, two], Sort::Bool);
    let opaque_len = app(&mut terms, "unknown_length", &[fixture.r], Sort::bitvec(64));
    let c_bound = app(&mut terms, "bvult", &[fixture.c, opaque_len], Sort::Bool);
    let guard = app(&mut terms, "and", &[r_bound, c_bound], Sort::Bool);
    let property = terms.mk_var("property", Sort::Bool);
    let (all, some_bad) = quantified_pair(&mut terms, guard, property);
    let model = UfStubModel::new()
        .uf(opaque_len, bv(0))
        .leaf(fixture.r, bv(0))
        .leaf(property, ModelValue::Bool(false));
    assert_cannot(&verdict(&terms, &model, &[all]));
    assert_cannot(&verdict(&terms, &model, &[some_bad]));
}

#[test]
fn joint_duplicate_wide_binders_are_rejected_before_empty_support_can_win() {
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", Sort::bitvec(64));
    let zero = terms.mk_bitvec(int(0), 64);
    let empty = app(&mut terms, "bvult", &[r, zero], Sort::Bool);
    let no = terms.mk_bool(false);
    let body = app(&mut terms, "=>", &[empty, no], Sort::Bool);
    let all = terms.mk_forall(
        vec![
            ("r".to_string(), Sort::bitvec(64)),
            ("r".to_string(), Sort::bitvec(64)),
        ],
        body,
    );
    assert!(matches!(
        evaluate_term(&terms, &StubModel::new(), all),
        EvalOutcome::Unevaluable(reason) if reason.contains("duplicate name")
    ));
}
