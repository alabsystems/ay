// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used)]
use super::*;
use crate::ChcOp;
fn make_counter_loop() -> (ChcExpr, Vec<ChcVar>) {
    // Loop: x' = x + 1
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);

    let loop_body = ChcExpr::eq(
        ChcExpr::var(x_next),
        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
    );

    (loop_body, vec![x])
}

#[test]
fn test_trp_creation() {
    let x = ChcVar::new("x", ChcSort::Int);
    let trp = Trp::new(vec![x]);

    assert_eq!(trp.state_vars.len(), 1);
    assert_eq!(trp.n_var.name, "__trp_n");
}

#[test]
fn test_trp_compute_constant_delta() {
    let (loop_body, state_vars) = make_counter_loop();
    let trp = Trp::new(state_vars);

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    model.insert("x_next".to_string(), SmtValue::Int(6));

    let result = trp
        .compute(&loop_body, &model)
        .expect("constant-delta counter loop must produce TRP constraints");

    // The TRP result should be a non-trivial constraint.
    assert!(
        !matches!(result, ChcExpr::Bool(true)),
        "TRP constraint should not be trivially true"
    );
    assert!(
        !matches!(result, ChcExpr::Bool(false)),
        "TRP constraint should not be trivially false"
    );
    // Should reference state variables AND the iteration count __trp_n.
    // After the TRL n-retention fix, TRP keeps __trp_n as a free variable
    // so learned relations can represent n > 0 loop iterations.
    let vars = result.vars();
    let var_names: Vec<&str> = vars.iter().map(|v| v.name.as_str()).collect();
    assert!(
        !var_names.is_empty(),
        "TRP constraint should reference variables, got: {result:?}"
    );
    assert!(
        var_names.contains(&"__trp_n"),
        "TRP should keep __trp_n as a free variable: {result:?}"
    );
    // For a counter loop x' = x + 1 with model x=5, x_next=6, at least
    // one of x or x_next must appear (the constraint summarizes the
    // relationship between pre/post state).
    assert!(
        var_names.contains(&"x") || var_names.contains(&"x_next"),
        "TRP constraint should reference x or x_next, got: {var_names:?}"
    );
    assert_eq!(
        trp.accelerated_summary_accelerated_row_candidates(),
        1,
        "constant-delta TRP should record one accelerated-summary accelerated-row candidate"
    );
    assert_eq!(
        trp.accelerated_summary_family_summary_candidates(),
        1,
        "constant-delta TRP should record one accelerated-summary family-summary candidate"
    );
    assert_eq!(
        trp.accelerated_summary_family_summary_kind_candidates(
            AcceleratedSummaryFamilySummaryKind::AffineConstantDelta
        ),
        1,
        "constant-delta TRP should distinguish the affine constant-delta summary family"
    );
    let family_stats = trp.accelerated_summary_family_summary_statistics();
    assert_eq!(family_stats.family_summary_candidates, 1);
    assert_eq!(family_stats.affine_constant_delta_family_summaries, 1);
    assert_eq!(family_stats.polynomial_closed_form_family_summaries, 0);
    assert_eq!(family_stats.affine_preserved_difference_family_summaries, 0);
    let records = trp.accelerated_summary_accelerated_row_candidate_records();
    assert_eq!(
        records.len(),
        1,
        "constant-delta TRP should preserve the accelerated-summary candidate row"
    );
    assert_eq!(
        records[0].schema,
        ACCELERATED_SUMMARY_TRP_ACCELERATED_ROW_CANDIDATE_SCHEMA
    );
    assert_eq!(records[0].local_index, 0);
    assert_eq!(
        records[0].kind,
        AcceleratedSummaryAcceleratedRowKind::ConstantDelta
    );
    assert_eq!(
        records[0].row,
        ChcExpr::eq(
            ChcExpr::sub(
                ChcExpr::var(ChcVar::new("x_next", ChcSort::Int)),
                ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
            ),
            ChcExpr::var(ChcVar::new("__trp_n", ChcSort::Int)),
        )
    );
    let summary_records = trp.accelerated_summary_family_summary_candidate_records();
    assert_eq!(summary_records.len(), 1);
    assert_eq!(
        summary_records[0].schema,
        ACCELERATED_SUMMARY_TRP_FAMILY_SUMMARY_CANDIDATE_SCHEMA
    );
    assert_eq!(summary_records[0].local_index, 0);
    assert_eq!(
        summary_records[0].kind,
        AcceleratedSummaryFamilySummaryKind::AffineConstantDelta
    );
    assert_eq!(summary_records[0].source_row, records[0].row);
}

#[test]
fn test_trp_recurrent_constant_delta() {
    let (loop_body, state_vars) = make_counter_loop();
    let trp = Trp::new(state_vars);

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(0));
    model.insert("x_next".to_string(), SmtValue::Int(1));

    let result = trp.recurrent(&loop_body, &model);

    // Should produce recurrence constraints with n > 0
    assert!(
        !matches!(result, ChcExpr::Bool(true)),
        "recurrent should produce non-trivial constraint for constant-delta loop"
    );
    // The recurrence formula must reference the n_var (__trp_n) for iteration count
    let vars = result.vars();
    let var_names: Vec<&str> = vars.iter().map(|v| v.name.as_str()).collect();
    assert!(
        var_names.contains(&"__trp_n"),
        "recurrence constraint should reference __trp_n, got: {var_names:?}"
    );
}

#[test]
fn test_extract_delta() {
    let x = ChcVar::new("x", ChcSort::Int);
    let trp = Trp::new(vec![x.clone()]);

    // x + 3
    let expr1 = ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(3));
    assert_eq!(trp.extract_delta(&expr1, &x), Some(3));

    // x - 2
    let expr2 = ChcExpr::sub(ChcExpr::var(x.clone()), ChcExpr::int(2));
    assert_eq!(trp.extract_delta(&expr2, &x), Some(-2));

    // x
    let expr3 = ChcExpr::var(x.clone());
    assert_eq!(trp.extract_delta(&expr3, &x), Some(0));
}

#[test]
fn test_is_constant_delta_pattern() {
    let (loop_body, state_vars) = make_counter_loop();
    let trp = Trp::new(state_vars.clone());
    let x = &state_vars[0];

    assert!(trp.is_constant_delta_pattern(&loop_body, x, 1));
    assert!(!trp.is_constant_delta_pattern(&loop_body, x, 2));
}

#[test]
fn test_collect_conjuncts() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let expr = ChcExpr::and(
        ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(0)),
        ChcExpr::lt(ChcExpr::var(y), ChcExpr::int(10)),
    );

    let conjuncts = expr.conjuncts();
    assert_eq!(conjuncts.len(), 2);
}

#[test]
fn test_and_all() {
    let x = ChcVar::new("x", ChcSort::Int);

    // Empty
    let empty: Vec<ChcExpr> = vec![];
    assert_eq!(ChcExpr::and_all(empty), ChcExpr::Bool(true));

    // Single
    let single = vec![ChcExpr::var(x.clone())];
    assert!(matches!(ChcExpr::and_all(single), ChcExpr::Var(_)));

    // Multiple
    let multi = vec![
        ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(10)),
    ];
    assert!(matches!(
        ChcExpr::and_all(multi),
        ChcExpr::Op(ChcOp::And, _)
    ));
}

/// Test recurrent_bounds with a constant positive delta (x' = x + 2).
/// This exercises the recurrent_bounds method directly, which was previously
/// untested and has unwrap_or(0) defaults that could mask bugs.
#[test]
fn test_recurrent_bounds_positive_delta() {
    let x = ChcVar::new("x", ChcSort::Int);
    let trp = Trp::new(vec![x.clone()]);

    // Loop body: x_next = x + 2
    let loop_body = ChcExpr::eq(
        ChcExpr::var(ChcVar::new("x_next", ChcSort::Int)),
        ChcExpr::add(ChcExpr::var(x), ChcExpr::int(2)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(3));
    model.insert("x_next".to_string(), SmtValue::Int(5));

    let handled = FxHashSet::default();
    let mut result = Vec::new();
    trp.recurrent_bounds(&loop_body, &model, &mut result, &handled);

    // With delta=+2, should emit x_next >= x + 2*n bound
    assert!(
        !result.is_empty(),
        "recurrent_bounds should emit constraints for positive delta"
    );
    // The bound should reference x_next
    let all_vars: FxHashSet<String> = result
        .iter()
        .flat_map(|e| e.vars().into_iter().map(|v| v.name))
        .collect();
    assert!(
        all_vars.contains("x_next"),
        "recurrent_bounds result should reference x_next: {all_vars:?}"
    );
}

/// Test recurrent_bounds with a constant negative delta (x' = x - 1).
#[test]
fn test_recurrent_bounds_negative_delta() {
    let x = ChcVar::new("x", ChcSort::Int);
    let trp = Trp::new(vec![x.clone()]);

    // Loop body: x_next = x - 1
    let loop_body = ChcExpr::eq(
        ChcExpr::var(ChcVar::new("x_next", ChcSort::Int)),
        ChcExpr::sub(ChcExpr::var(x), ChcExpr::int(1)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(10));
    model.insert("x_next".to_string(), SmtValue::Int(9));

    let handled = FxHashSet::default();
    let mut result = Vec::new();
    trp.recurrent_bounds(&loop_body, &model, &mut result, &handled);

    assert!(
        !result.is_empty(),
        "recurrent_bounds should emit constraints for negative delta"
    );
    // The bound should reference x_next (same structural check as positive delta)
    let all_vars: FxHashSet<String> = result
        .iter()
        .flat_map(|e| e.vars().into_iter().map(|v| v.name))
        .collect();
    assert!(
        all_vars.contains("x_next"),
        "recurrent_bounds result for negative delta should reference x_next: {all_vars:?}"
    );
}

/// Test recurrent_bounds skips already-handled variables.
#[test]
fn test_recurrent_bounds_skips_handled() {
    let x = ChcVar::new("x", ChcSort::Int);
    let trp = Trp::new(vec![x.clone()]);

    let loop_body = ChcExpr::eq(
        ChcExpr::var(ChcVar::new("x_next", ChcSort::Int)),
        ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(0));
    model.insert("x_next".to_string(), SmtValue::Int(1));

    let mut handled = FxHashSet::default();
    handled.insert("x".to_string());
    let mut result = Vec::new();
    trp.recurrent_bounds(&loop_body, &model, &mut result, &handled);

    assert!(
        result.is_empty(),
        "recurrent_bounds should skip handled vars, got: {result:?}"
    );
}

/// Test recurrent_bounds with missing model values (unwrap_or(0) path).
#[test]
fn test_recurrent_bounds_missing_model_values() {
    let x = ChcVar::new("x", ChcSort::Int);
    let trp = Trp::new(vec![x.clone()]);

    // Loop body has the pattern, but model is empty
    let loop_body = ChcExpr::eq(
        ChcExpr::var(ChcVar::new("x_next", ChcSort::Int)),
        ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1)),
    );

    // Empty model - both pre and post default to 0, so delta = 0
    let model = FxHashMap::default();
    let handled = FxHashSet::default();
    let mut result = Vec::new();
    trp.recurrent_bounds(&loop_body, &model, &mut result, &handled);

    // With both values defaulting to 0, delta=0, so no constraints emitted
    assert!(
        result.is_empty(),
        "recurrent_bounds with zero delta from missing model should emit nothing"
    );
}

/// Test recurrent_exps with x' = 2*x (exponential growth, positive x).
#[test]
fn test_recurrent_exps_doubling_positive() {
    let x = ChcVar::new("x", ChcSort::Int);
    let trp = Trp::new(vec![x.clone()]);

    // Loop body: x_next = 2 * x
    let loop_body = ChcExpr::eq(
        ChcExpr::var(ChcVar::new("x_next", ChcSort::Int)),
        ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(x)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(3));
    model.insert("x_next".to_string(), SmtValue::Int(6));

    let mut result = Vec::new();
    trp.recurrent_exps(&loop_body, &model, &mut result);

    // For coeff=2 and x >= 0: should emit x >= 0 and x_next >= x
    assert!(
        result.len() >= 2,
        "recurrent_exps should emit sign preservation + growth bound, got {}: {result:?}",
        result.len()
    );
    // Verify constraints reference both x and x_next (sign preservation + monotonicity)
    let all_vars: FxHashSet<String> = result
        .iter()
        .flat_map(|e| e.vars().into_iter().map(|v| v.name))
        .collect();
    assert!(
        all_vars.contains("x"),
        "recurrent_exps should reference x for sign preservation: {all_vars:?}"
    );
    assert!(
        all_vars.contains("x_next"),
        "recurrent_exps should reference x_next for growth bound: {all_vars:?}"
    );
}

/// Test recurrent_exps with x' = 2*x (exponential growth, negative x).
#[test]
fn test_recurrent_exps_doubling_negative() {
    let x = ChcVar::new("x", ChcSort::Int);
    let trp = Trp::new(vec![x.clone()]);

    // Loop body: x_next = 2 * x
    let loop_body = ChcExpr::eq(
        ChcExpr::var(ChcVar::new("x_next", ChcSort::Int)),
        ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(x)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(-3));
    model.insert("x_next".to_string(), SmtValue::Int(-6));

    let mut result = Vec::new();
    trp.recurrent_exps(&loop_body, &model, &mut result);

    // For coeff=2 and x < 0: should emit x < 0 and x_next <= x
    assert!(
        result.len() >= 2,
        "recurrent_exps with negative x should emit sign preservation + decay bound, got {}: {result:?}",
        result.len()
    );
    // Verify constraints reference both x and x_next
    let all_vars: FxHashSet<String> = result
        .iter()
        .flat_map(|e| e.vars().into_iter().map(|v| v.name))
        .collect();
    assert!(
        all_vars.contains("x"),
        "recurrent_exps (negative) should reference x for sign preservation: {all_vars:?}"
    );
    assert!(
        all_vars.contains("x_next"),
        "recurrent_exps (negative) should reference x_next for decay bound: {all_vars:?}"
    );
}

/// Test recurrent_exps with x' = x (coeff=1, no exponential pattern).
#[test]
fn test_recurrent_exps_identity_no_emit() {
    let x = ChcVar::new("x", ChcSort::Int);
    let trp = Trp::new(vec![x.clone()]);

    // Loop body: x_next = 1 * x (identity, coeff == 1)
    let loop_body = ChcExpr::eq(
        ChcExpr::var(ChcVar::new("x_next", ChcSort::Int)),
        ChcExpr::mul(ChcExpr::int(1), ChcExpr::var(x)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    model.insert("x_next".to_string(), SmtValue::Int(5));

    let mut result = Vec::new();
    trp.recurrent_exps(&loop_body, &model, &mut result);

    // coeff=1 is excluded from exponential handling
    assert!(
        result.is_empty(),
        "recurrent_exps should not emit for identity (coeff=1): {result:?}"
    );
}

/// Test extract_linear_coeff recognizes c*x patterns.
#[test]
fn test_extract_linear_coeff() {
    let x = ChcVar::new("x", ChcSort::Int);
    let trp = Trp::new(vec![x.clone()]);

    // 3 * x
    let expr1 = ChcExpr::mul(ChcExpr::int(3), ChcExpr::var(x.clone()));
    assert_eq!(trp.extract_linear_coeff(&expr1, &x), Some(3));

    // x (bare variable, implicit coeff=1)
    let expr2 = ChcExpr::var(x.clone());
    assert_eq!(trp.extract_linear_coeff(&expr2, &x), Some(1));
}

/// Test for #4730: TRP should retain n_var as a free variable.
#[test]
fn test_trp_retains_n_var() {
    let x = ChcVar::new("x", ChcSort::Int);
    let trp = Trp::new(vec![x.clone()]);

    // Loop: x' = x + 1
    let loop_body = ChcExpr::eq(
        ChcExpr::var(ChcVar::new("x_next", ChcSort::Int)),
        ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(0));
    model.insert("x_next".to_string(), SmtValue::Int(1));

    let result = trp.compute(&loop_body, &model);

    // After the TRL n-retention fix, TRP keeps __trp_n as a free variable.
    if let Some(ref formula) = result {
        let vars = formula.vars();
        assert!(
            vars.iter().any(|v| v.name == "__trp_n"),
            "TRP result should contain iteration variable __trp_n: {vars:?}"
        );
    }
}

/// Test polynomial closed-form lowering for quadratic accumulation.
///
/// Loop: i' = i + 1, s' = s + i'
/// Recurrence analysis produces:
///   i -> ConstantDelta { delta: 1 }
///   s -> Polynomial { coeffs: [{s: 1}, {i: 1, "": -1/2}, {"": 1/2}] }
///
/// The polynomial constraint should be:
///   2 * s_next = 2*s + 2*n*i + n^2 - n
/// (denominator-cleared form of s_next = s + n*i + n*(n-1)/2)
///
/// Part of #7335.
#[test]
fn test_emit_recurrence_polynomial_quadratic_sum() {
    use crate::recurrence::ClosedForm;
    use num_rational::Rational64;

    let i_var = ChcVar::new("i", ChcSort::Int);
    let s_var = ChcVar::new("s", ChcSort::Int);
    let trp = Trp::new(vec![i_var, s_var]);

    // Build a TriangularSystem with both solutions
    let mut system = TriangularSystem {
        solutions: FxHashMap::default(),
        order: vec!["i".to_string(), "s".to_string()],
    };
    system
        .solutions
        .insert("i".to_string(), ClosedForm::ConstantDelta { delta: 1 });
    // s_n = s_0 + n*i_0 + (1/2)*n^2 - (1/2)*n
    let mut coeff_0 = FxHashMap::default();
    coeff_0.insert("s".to_string(), Rational64::from_integer(1));
    let mut coeff_1 = FxHashMap::default();
    coeff_1.insert("i".to_string(), Rational64::from_integer(1));
    coeff_1.insert(String::new(), Rational64::new(-1, 2));
    let mut coeff_2 = FxHashMap::default();
    coeff_2.insert(String::new(), Rational64::new(1, 2));
    system.solutions.insert(
        "s".to_string(),
        ClosedForm::Polynomial {
            coeffs: vec![coeff_0, coeff_1, coeff_2],
        },
    );

    let model = FxHashMap::default();
    let mut result = Vec::new();
    let mut handled_vars = FxHashSet::default();
    trp.emit_recurrence_constraints(&system, &model, &mut result, &mut handled_vars);
    assert_eq!(
        trp.accelerated_summary_accelerated_row_candidates(),
        2,
        "one constant-delta row and one polynomial row should be accelerated-summary candidates"
    );
    let records = trp.accelerated_summary_accelerated_row_candidate_records();
    assert_eq!(
        records.len(),
        2,
        "TRP should preserve constant-delta and polynomial candidate rows"
    );
    assert_eq!(records[0].local_index, 0);
    assert_eq!(records[1].local_index, 1);
    assert_eq!(
        records[0].kind,
        AcceleratedSummaryAcceleratedRowKind::ConstantDelta
    );
    assert_eq!(
        records[1].kind,
        AcceleratedSummaryAcceleratedRowKind::PolynomialClosedForm
    );
    assert_eq!(
        trp.accelerated_summary_family_summary_candidates(),
        2,
        "TRP should record matching family summaries for emitted accelerated-summary rows"
    );
    assert_eq!(
        trp.accelerated_summary_family_summary_kind_candidates(
            AcceleratedSummaryFamilySummaryKind::AffineConstantDelta
        ),
        1
    );
    assert_eq!(
        trp.accelerated_summary_family_summary_kind_candidates(
            AcceleratedSummaryFamilySummaryKind::PolynomialClosedForm
        ),
        1
    );
    let summary_records = trp.accelerated_summary_family_summary_candidate_records();
    assert_eq!(summary_records.len(), 2);
    assert_eq!(
        summary_records[0].kind,
        AcceleratedSummaryFamilySummaryKind::AffineConstantDelta
    );
    assert_eq!(
        summary_records[1].kind,
        AcceleratedSummaryFamilySummaryKind::PolynomialClosedForm
    );

    // Both i and s should be handled
    assert!(
        handled_vars.contains("i"),
        "ConstantDelta var 'i' should be handled: {handled_vars:?}"
    );
    assert!(
        handled_vars.contains("s"),
        "Polynomial var 's' should be handled: {handled_vars:?}"
    );

    // Find the polynomial constraint for s
    let s_constraint = result.iter().find(|c| {
        let vars = c.vars();
        vars.iter().any(|v| v.name == "s_next")
    });
    assert!(
        s_constraint.is_some(),
        "Should emit a constraint referencing s_next: {result:?}"
    );
    let s_constraint = s_constraint.unwrap();
    assert_eq!(
        records[1].row, *s_constraint,
        "polynomial accelerated-summary record should preserve the emitted row"
    );

    // The constraint should reference s, i, s_next, and __trp_n
    let vars = s_constraint.vars();
    let var_names: FxHashSet<&str> = vars.iter().map(|v| v.name.as_str()).collect();
    assert!(
        var_names.contains("s"),
        "Polynomial constraint should reference pre-state s: {var_names:?}"
    );
    assert!(
        var_names.contains("i"),
        "Polynomial constraint should reference pre-state i: {var_names:?}"
    );
    assert!(
        var_names.contains("s_next"),
        "Polynomial constraint should reference s_next: {var_names:?}"
    );
    assert!(
        var_names.contains("__trp_n"),
        "Polynomial constraint should reference __trp_n: {var_names:?}"
    );
}

#[test]
fn test_emit_recurrence_records_preserved_difference_candidate() {
    use crate::recurrence::ClosedForm;

    let a_var = ChcVar::new("a", ChcSort::Int);
    let b_var = ChcVar::new("b", ChcSort::Int);
    let trp = Trp::new(vec![a_var, b_var]);

    let mut system = TriangularSystem {
        solutions: FxHashMap::default(),
        order: vec!["a".to_string(), "b".to_string()],
    };
    system
        .solutions
        .insert("a".to_string(), ClosedForm::ConstantDelta { delta: 2 });
    system
        .solutions
        .insert("b".to_string(), ClosedForm::ConstantDelta { delta: 2 });

    let mut model = FxHashMap::default();
    model.insert("a".to_string(), SmtValue::Int(1));
    model.insert("b".to_string(), SmtValue::Int(3));

    let mut result = Vec::new();
    let mut handled_vars = FxHashSet::default();
    trp.emit_recurrence_constraints(&system, &model, &mut result, &mut handled_vars);

    let records = trp.accelerated_summary_accelerated_row_candidate_records();
    assert_eq!(
        records.len(),
        3,
        "two constant-delta rows and one preserved difference should be recorded"
    );
    for (index, record) in records.iter().enumerate() {
        assert_eq!(
            record.local_index, index,
            "accelerated-summary candidate record indexes should follow emission order"
        );
    }
    assert_eq!(
        records[0].kind,
        AcceleratedSummaryAcceleratedRowKind::ConstantDelta
    );
    assert_eq!(
        records[1].kind,
        AcceleratedSummaryAcceleratedRowKind::ConstantDelta
    );
    assert_eq!(
        records[2].kind,
        AcceleratedSummaryAcceleratedRowKind::PreservedDifference
    );
    assert_eq!(
        trp.accelerated_summary_family_summary_candidates(),
        3,
        "two constant-delta rows and one preserved-difference summary should be recorded"
    );
    assert_eq!(
        trp.accelerated_summary_family_summary_kind_candidates(
            AcceleratedSummaryFamilySummaryKind::AffineConstantDelta
        ),
        2
    );
    assert_eq!(
        trp.accelerated_summary_family_summary_kind_candidates(
            AcceleratedSummaryFamilySummaryKind::AffinePreservedDifference
        ),
        1
    );
    let summary_records = trp.accelerated_summary_family_summary_candidate_records();
    assert_eq!(summary_records.len(), 3);
    assert_eq!(
        summary_records[2].kind,
        AcceleratedSummaryFamilySummaryKind::AffinePreservedDifference
    );
    assert_eq!(summary_records[2].source_row, records[2].row);
    assert!(
        result.contains(&records[2].row),
        "preserved-difference accelerated-summary record should preserve the emitted row"
    );

    let vars = records[2].row.vars();
    let var_names: FxHashSet<&str> = vars.iter().map(|v| v.name.as_str()).collect();
    assert!(
        var_names.contains("a"),
        "preserved-difference row should mention a: {var_names:?}"
    );
    assert!(
        var_names.contains("b"),
        "preserved-difference row should mention b: {var_names:?}"
    );
    assert!(
        var_names.contains("a_next"),
        "preserved-difference row should mention a_next: {var_names:?}"
    );
    assert!(
        var_names.contains("b_next"),
        "preserved-difference row should mention b_next: {var_names:?}"
    );
}

/// Test lower_polynomial_constraint with a degree-0 (constant) polynomial.
///
/// Constant reset: x' = 42. This has coeffs = [{"": 42}].
/// Should emit: x_next = 42 (no n dependence).
///
/// Part of #7335.
#[test]
fn test_lower_polynomial_constant_reset() {
    use num_rational::Rational64;

    let x = ChcVar::new("x", ChcSort::Int);
    let trp = Trp::new(vec![x.clone()]);

    let mut coeff_0 = FxHashMap::default();
    coeff_0.insert(String::new(), Rational64::from_integer(42));
    let coeffs = vec![coeff_0];

    let constraint = trp.lower_polynomial_constraint(&x, &coeffs);
    assert!(
        constraint.is_some(),
        "Constant polynomial should produce a constraint"
    );
    let constraint = constraint.unwrap();

    // Should be: x_next = 42
    let vars = constraint.vars();
    let var_names: FxHashSet<&str> = vars.iter().map(|v| v.name.as_str()).collect();
    assert!(
        var_names.contains("x_next"),
        "Constant polynomial constraint should reference x_next"
    );
    // Should NOT reference __trp_n (no iteration dependence)
    assert!(
        !var_names.contains("__trp_n"),
        "Constant polynomial should not reference __trp_n: {var_names:?}"
    );
}
