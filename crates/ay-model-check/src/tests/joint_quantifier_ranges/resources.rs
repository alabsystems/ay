// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#[test]
fn joint_plans_later_rows_before_accepting_an_early_counterexample_or_witness() {
    let mut terms = TermStore::new();
    let fixture = matrix(&mut terms);
    let value = outer(
        2,
        row(0, cells(false, &[])),
        vec![
            (0, row(1, cells(false, &[]))),
            (1, row(65_537, cells(true, &[]))),
        ],
    );
    let model = StubModel::new().with(fixture.outer, value);
    // (0,0) already falsifies forall and witnesses exists. But the full
    // required plan exceeds its shared cap at row 1, before any body runs.
    for quantified in [fixture.all, fixture.some_bad] {
        assert!(matches!(
            evaluate_term(&terms, &model, quantified),
            EvalOutcome::Unevaluable(reason) if reason.contains("assignment budget")
        ));
    }
    let small = StubModel::new().with(
        fixture.outer,
        outer(
            2,
            row(1, cells(true, &[])),
            vec![(0, row(1, cells(false, &[])))],
        ),
    );
    assert_violates(&verdict(&terms, &small, &[fixture.all]));
    assert_confirmed(&verdict(&terms, &small, &[fixture.some_bad]));
}

#[test]
fn joint_support_work_is_shared_between_roots_but_a_fresh_evaluator_recovers() {
    let mut terms = TermStore::new();
    let fixture = matrix(&mut terms);
    let zero = terms.mk_bitvec(int(0), 64);
    let mut repeated = app(&mut terms, "bvuge", &[fixture.r, zero], Sort::Bool);
    // Twenty distinct nodes, but repeated occurrence traversal exceeds the
    // source-support work allowance; this does not enumerate 65K tuples.
    for _ in 0..20 {
        repeated = app(&mut terms, "and", &[repeated, repeated], Sort::Bool);
    }
    let exhausted = terms.mk_forall(bindings(), repeated);
    let model = StubModel::new().with(fixture.outer, matrix_value(false));
    let evaluator = Evaluator::new(&terms, &model);
    assert!(matches!(
        evaluator.evaluate(exhausted),
        EvalOutcome::Unevaluable(reason) if reason.contains("evaluation work budget")
    ));
    assert!(matches!(
        evaluator.evaluate(fixture.all),
        EvalOutcome::Unevaluable(reason) if reason.contains("evaluation work budget")
    ));
    assert!(matches!(
        Evaluator::new(&terms, &model).evaluate(fixture.all),
        EvalOutcome::Value(ModelValue::Bool(true))
    ));
}
