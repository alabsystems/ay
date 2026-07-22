// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the MaxSMT API (#8300).

use crate::api::{BitVecSort, Logic, MaxSmtStatus, Solver, Sort};

/// Basic: three soft LIA constraints, verify maximum satisfaction.
#[test]
fn test_maxsmt_basic_lia_three_softs() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let ten = solver.int_const(10);

    // Hard: 0 <= x <= 10
    let x_ge_0 = solver.try_ge(x, zero).unwrap();
    solver.try_assert_term(x_ge_0).unwrap();
    let x_le_10 = solver.try_le(x, ten).unwrap();
    solver.try_assert_term(x_le_10).unwrap();

    // Soft: x > 5 (weight 1)
    let five = solver.int_const(5);
    let x_gt_5 = solver.try_gt(x, five).unwrap();
    let s0 = solver.assert_soft(x_gt_5, 1, None).unwrap();
    assert_eq!(s0, 0);

    // Soft: x < 3 (weight 1)
    let three = solver.int_const(3);
    let x_lt_3 = solver.try_lt(x, three).unwrap();
    let s1 = solver.assert_soft(x_lt_3, 1, None).unwrap();
    assert_eq!(s1, 1);

    // Soft: x == 7 (weight 1)
    let seven = solver.int_const(7);
    let x_eq_7 = solver.try_eq(x, seven).unwrap();
    let s2 = solver.assert_soft(x_eq_7, 1, None).unwrap();
    assert_eq!(s2, 2);

    // x > 5 and x == 7 are compatible; x < 3 conflicts with both.
    // Optimal: satisfy s0 and s2 (weight 2), violate s1.
    let result = solver.check_sat_max().unwrap();
    assert_eq!(
        result.status,
        MaxSmtStatus::Optimal,
        "reason={:?}, error={:?}",
        solver.unknown_reason(),
        solver.executor_error()
    );
    assert_eq!(result.satisfied_weight, 2, "should satisfy 2 of 3 softs");
    assert_eq!(result.violated_weight, 1);
    assert_eq!(result.violated_weight(), 1);
    assert_eq!(result.violated_softs, vec![1], "x < 3 should be violated");
}

/// Regression: `check_sat_max` must minimize total VIOLATED WEIGHT, not
/// violation count. Hard: `a => (not b and not c)`. Softs a:5, b:1, c:1.
/// Weight-optimal = satisfy a, violate b and c (violated weight 2); a
/// count-first optimizer wrongly violates a alone (violated weight 5).
#[test]
fn test_maxsmt_weight_optimal_not_count_optimal() {
    let mut solver = Solver::try_new(Logic::QfUf).unwrap();
    let a = solver.declare_const("a", Sort::Bool);
    let b = solver.declare_const("b", Sort::Bool);
    let c = solver.declare_const("c", Sort::Bool);

    // Hard: (or (not a) (and (not b) (not c)))  ==  a => (not b and not c).
    let not_a = solver.try_not(a).unwrap();
    let not_b = solver.try_not(b).unwrap();
    let not_c = solver.try_not(c).unwrap();
    let nb_and_nc = solver.try_and(not_b, not_c).unwrap();
    let hard = solver.try_or(not_a, nb_and_nc).unwrap();
    solver.try_assert_term(hard).unwrap();

    solver.assert_soft(a, 5, None).unwrap();
    solver.assert_soft(b, 1, None).unwrap();
    solver.assert_soft(c, 1, None).unwrap();

    let result = solver.check_sat_max().unwrap();
    assert_eq!(
        result.status,
        MaxSmtStatus::Optimal,
        "reason={:?}, error={:?}",
        solver.unknown_reason(),
        solver.executor_error()
    );
    // Weight-optimal: satisfy a (5), violate b and c (violated weight 2).
    assert_eq!(
        result.satisfied_weight, 5,
        "must minimize violated WEIGHT (violate b,c=2), not count (violate a=5)"
    );
    assert_eq!(result.violated_weight(), 2);
    assert_eq!(result.violated_softs, vec![1, 2], "b and c violated");
}

/// Weighted: different weights, verify weight-optimal solution.
#[test]
fn test_maxsmt_weighted_lia() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let hundred = solver.int_const(100);

    // Hard: 0 <= x <= 100
    let x_ge_0 = solver.try_ge(x, zero).unwrap();
    solver.try_assert_term(x_ge_0).unwrap();
    let x_le_100 = solver.try_le(x, hundred).unwrap();
    solver.try_assert_term(x_le_100).unwrap();

    // Soft: x > 50 (weight 10 — high priority)
    let fifty = solver.int_const(50);
    let x_gt_50 = solver.try_gt(x, fifty).unwrap();
    solver.assert_soft(x_gt_50, 10, None).unwrap();

    // Soft: x < 10 (weight 1 — low priority, conflicts with x > 50)
    let ten = solver.int_const(10);
    let x_lt_10 = solver.try_lt(x, ten).unwrap();
    solver.assert_soft(x_lt_10, 1, None).unwrap();

    let result = solver.check_sat_max().unwrap();
    assert_eq!(
        result.status,
        MaxSmtStatus::Optimal,
        "reason={:?}, error={:?}",
        solver.unknown_reason(),
        solver.executor_error()
    );
    // The solver should prefer satisfying the weight-10 soft over the weight-1 soft.
    assert!(
        result.satisfied_weight >= 10,
        "should satisfy the high-weight soft: satisfied_weight={}",
        result.satisfied_weight
    );
    assert!(
        result.violated_softs.contains(&1),
        "low-weight soft (x < 10) should be violated: {:?}",
        result.violated_softs
    );
}

/// Group labels are semantic independent objectives in SMT-LIB/Z3, while the
/// current native result can represent only one flat weighted objective. The
/// solver must not silently flatten them and claim a false optimum.
#[test]
fn test_maxsmt_groups_are_honest_unknown_until_semantics_are_representable() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let twenty = solver.int_const(20);

    // Hard: 0 <= x <= 20
    let x_ge_0 = solver.try_ge(x, zero).unwrap();
    solver.try_assert_term(x_ge_0).unwrap();
    let x_le_20 = solver.try_le(x, twenty).unwrap();
    solver.try_assert_term(x_le_20).unwrap();

    // Group "vuln": x >= 10 (compatible with x <= 15)
    let ten = solver.int_const(10);
    let x_ge_10 = solver.try_ge(x, ten).unwrap();
    solver.assert_soft(x_ge_10, 1, Some("vuln")).unwrap();

    // Group "vuln": x <= 15 (compatible with x >= 10)
    let fifteen = solver.int_const(15);
    let x_le_15 = solver.try_le(x, fifteen).unwrap();
    solver.assert_soft(x_le_15, 1, Some("vuln")).unwrap();

    // Group "patch": x < 5 (conflicts with x >= 10)
    let five = solver.int_const(5);
    let x_lt_5 = solver.try_lt(x, five).unwrap();
    solver.assert_soft(x_lt_5, 1, Some("patch")).unwrap();

    let result = solver.check_sat_max().unwrap();
    assert!(result.is_unknown());
    assert_eq!(
        solver.unknown_reason(),
        Some(crate::UnknownReason::Unsupported)
    );
    assert!(solver.model().is_none());
    assert!(solver.model_for_consumer().is_none());
}

/// Hard constraints unsatisfiable.
#[test]
fn test_maxsmt_hard_unsat() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);

    // Hard: x > 0 AND x < 0 — contradictory
    let x_gt_0 = solver.try_gt(x, zero).unwrap();
    solver.try_assert_term(x_gt_0).unwrap();
    let x_lt_0 = solver.try_lt(x, zero).unwrap();
    solver.try_assert_term(x_lt_0).unwrap();

    // Soft: x == 1 (irrelevant — hard is UNSAT)
    let x_eq_1 = solver.try_eq(x, one).unwrap();
    solver.assert_soft(x_eq_1, 1, None).unwrap();

    let result = solver.check_sat_max().unwrap();
    assert_eq!(result.status, MaxSmtStatus::HardUnsatisfiable);
    assert_eq!(result.satisfied_weight, 0);
}

/// Trivial: all softs satisfiable.
#[test]
fn test_maxsmt_all_softs_satisfiable() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let hundred = solver.int_const(100);

    // Hard: 0 <= x <= 100
    let x_ge_0 = solver.try_ge(x, zero).unwrap();
    solver.try_assert_term(x_ge_0).unwrap();
    let x_le_100 = solver.try_le(x, hundred).unwrap();
    solver.try_assert_term(x_le_100).unwrap();

    // All soft constraints are compatible:
    let ten = solver.int_const(10);
    let fifty = solver.int_const(50);

    // x >= 10
    let x_ge_10 = solver.try_ge(x, ten).unwrap();
    solver.assert_soft(x_ge_10, 5, None).unwrap();

    // x <= 50
    let x_le_50 = solver.try_le(x, fifty).unwrap();
    solver.assert_soft(x_le_50, 3, None).unwrap();

    let result = solver.check_sat_max().unwrap();
    assert_eq!(result.status, MaxSmtStatus::Optimal);
    assert_eq!(result.satisfied_weight, 8, "all softs should be satisfied");
    assert!(
        result.violated_softs.is_empty(),
        "no softs should be violated"
    );
}

/// No soft constraints: just hard constraints.
#[test]
fn test_maxsmt_no_softs() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_ge_0 = solver.try_ge(x, zero).unwrap();
    solver.try_assert_term(x_ge_0).unwrap();

    let result = solver.check_sat_max().unwrap();
    assert_eq!(result.status, MaxSmtStatus::Optimal);
    assert_eq!(result.satisfied_weight, 0);
    assert!(result.violated_softs.is_empty());
}

/// Sort mismatch: assert_soft with non-Bool term.
#[test]
fn test_maxsmt_assert_soft_sort_check() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let x = solver.declare_const("x", Sort::Int);
    match solver.assert_soft(x, 1, None) {
        Err(crate::api::SolverError::SortMismatch { operation, .. }) => {
            assert_eq!(operation, "assert_soft");
        }
        other => panic!("expected SortMismatch, got {other:?}"),
    }
}

/// BV constraints: three soft bitvector constraints.
#[test]
fn test_maxsmt_bv_constraints() {
    let mut solver = Solver::try_new(Logic::QfBv).unwrap();
    let bv8 = Sort::BitVec(BitVecSort { width: 8 });
    let x = solver.declare_const("x", bv8);

    // Hard: none (any 8-bit value is valid)

    // Soft: x == 0xFF (weight 1)
    let ff = solver.try_bv_const(0xFF_i64, 8).unwrap();
    let x_eq_ff = solver.try_eq(x, ff).unwrap();
    solver.assert_soft(x_eq_ff, 1, None).unwrap();

    // Soft: x == 0x00 (weight 1, conflicts with 0xFF)
    let zero = solver.try_bv_const(0_i64, 8).unwrap();
    let x_eq_0 = solver.try_eq(x, zero).unwrap();
    solver.assert_soft(x_eq_0, 1, None).unwrap();

    // Soft: x == 0x42 (weight 1, conflicts with both)
    let val42 = solver.try_bv_const(0x42_i64, 8).unwrap();
    let x_eq_42 = solver.try_eq(x, val42).unwrap();
    solver.assert_soft(x_eq_42, 1, None).unwrap();

    let result = solver.check_sat_max().unwrap();
    assert_eq!(
        result.status,
        MaxSmtStatus::Optimal,
        "reason={:?}, error={:?}",
        solver.unknown_reason(),
        solver.executor_error()
    );
    // x can only equal one value, so exactly 1 soft satisfied, 2 violated.
    assert_eq!(
        result.satisfied_weight, 1,
        "only one equality can be satisfied"
    );
    assert_eq!(
        result.violated_softs.len(),
        2,
        "two of three equalities must be violated"
    );
}

/// Soundness regression (#maxsmt-unevaluable-soft): a soft constraint whose
/// Boolean term the model cannot fully evaluate must NOT be force-counted as
/// violated when it is in fact satisfiable.
///
/// A Bool-valued uninterpreted predicate `p(a)` over an uninterpreted sort can
/// fail to resolve in the term-level model evaluator (`value` may return `None`
/// or the default `Bool(false)`) even when the constraint is satisfiable (a
/// valid model may interpret `p(a) = true`). The previous implementation read
/// any non-`true` evaluation as "violated", which would understate
/// `satisfied_weight` and corrupt the violated set. The fix decides violation
/// from the always-evaluable relaxation variable instead.
///
/// Here `p(a)` is the only soft and has no conflicting hard constraints, so the
/// optimum keeps it satisfied (its relax variable is false). It must be reported
/// satisfied, not violated.
#[test]
fn test_maxsmt_unevaluable_bool_soft_not_force_violated() {
    let mut solver = Solver::try_new(Logic::QfUf).unwrap();
    let s = Sort::Uninterpreted("S".into());
    let a = solver.declare_const("a", s.clone());

    // Soft: p(a) — a Bool-valued UF the model evaluator defaults to false,
    // yet it is satisfiable (model may set p(a) = true).
    let p = solver.declare_fun("p", &[s], Sort::Bool);
    let pa = solver.apply(&p, &[a]);
    solver.assert_soft(pa, 1, None).unwrap();

    let result = solver.check_sat_max().unwrap();
    assert_eq!(
        result.status,
        MaxSmtStatus::Optimal,
        "reason={:?}, error={:?}",
        solver.unknown_reason(),
        solver.executor_error()
    );
    assert_eq!(
        result.satisfied_weight, 1,
        "satisfiable unevaluable Bool soft must be counted satisfied, not violated"
    );
    assert!(
        result.violated_softs.is_empty(),
        "no soft should be violated: {:?}",
        result.violated_softs
    );
}

/// Soundness regression (mixed): an unevaluable-but-satisfiable Bool soft plus
/// an ordinary soft that genuinely conflicts with a hard constraint. The
/// unevaluable soft must be kept satisfied; only the genuinely-violated soft is
/// reported, and `satisfied_weight` must reflect the kept soft's weight.
#[test]
fn test_maxsmt_unevaluable_bool_soft_mixed_with_real_violation() {
    let mut solver = Solver::try_new(Logic::QfUflia).unwrap();
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let ten = solver.int_const(10);

    // Hard: 0 <= x <= 10
    let x_ge_0 = solver.try_ge(x, zero).unwrap();
    solver.try_assert_term(x_ge_0).unwrap();
    let x_le_10 = solver.try_le(x, ten).unwrap();
    solver.try_assert_term(x_le_10).unwrap();

    // Soft 0: p(x) — Bool-valued UF, satisfiable, but the model evaluator
    // defaults its value to false (unevaluable at the term level), weight 5.
    let p = solver.declare_fun("p", &[Sort::Int], Sort::Bool);
    let px = solver.apply(&p, &[x]);
    solver.assert_soft(px, 5, None).unwrap();

    // Soft 1: x > 100 — impossible given hard 0 <= x <= 10, weight 1.
    let hundred = solver.int_const(100);
    let x_gt_100 = solver.try_gt(x, hundred).unwrap();
    solver.assert_soft(x_gt_100, 1, None).unwrap();

    let result = solver.check_sat_max().unwrap();
    assert_eq!(result.status, MaxSmtStatus::Optimal);
    assert_eq!(
        result.satisfied_weight, 5,
        "the satisfiable unevaluable soft (weight 5) must be satisfied"
    );
    assert_eq!(
        result.violated_softs,
        vec![1],
        "only the impossible soft (x > 100) should be violated"
    );
}

/// Vulnerability analysis use case: maximum exploitability.
/// Hard constraints encode program semantics; soft constraints encode
/// individual vulnerability conditions.
#[test]
fn test_maxsmt_vulnerability_exploitability() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();

    // Program input
    let input = solver.declare_const("input", Sort::Int);
    let zero = solver.int_const(0);
    let hundred = solver.int_const(100);

    // Hard: input is in valid range [0, 100]
    let in_range_lo = solver.try_ge(input, zero).unwrap();
    solver.try_assert_term(in_range_lo).unwrap();
    let in_range_hi = solver.try_le(input, hundred).unwrap();
    solver.try_assert_term(in_range_hi).unwrap();

    // Vuln 1: buffer overflow when input > 80
    let eighty = solver.int_const(80);
    let vuln1 = solver.try_gt(input, eighty).unwrap();
    solver.assert_soft(vuln1, 1, None).unwrap();

    // Vuln 2: integer overflow when input > 90
    let ninety = solver.int_const(90);
    let vuln2 = solver.try_gt(input, ninety).unwrap();
    solver.assert_soft(vuln2, 1, None).unwrap();

    // Vuln 3: null deref when input < 10
    let ten = solver.int_const(10);
    let vuln3 = solver.try_lt(input, ten).unwrap();
    solver.assert_soft(vuln3, 1, None).unwrap();

    let result = solver.check_sat_max().unwrap();
    assert_eq!(result.status, MaxSmtStatus::Optimal);
    // Vulns 1 and 2 are compatible (input > 90 satisfies both).
    // Vuln 3 conflicts with vulns 1 and 2.
    // Optimal: satisfy vulns 1+2, violate vuln 3.
    assert_eq!(
        result.satisfied_weight, 2,
        "should trigger 2 vulns simultaneously"
    );
    assert_eq!(
        result.violated_softs,
        vec![2],
        "vuln 3 (input < 10) should be the one violated"
    );
}

/// A MaxSMT call is a transaction over the existing hard assertion/scope state,
/// and a repeated call must rebuild only transient internals while retaining a
/// newly revalidated optimal model.
#[test]
fn test_maxsmt_repeated_calls_do_not_leak_assertions_scopes_or_symbols() {
    let mut solver = Solver::try_new(Logic::QfUf).unwrap();
    let a = solver.declare_const("a", Sort::Bool);
    let b = solver.declare_const("b", Sort::Bool);
    let hard = solver.try_or(a, b).unwrap();
    solver.try_assert_term(hard).unwrap();
    let not_a = solver.try_not(a).unwrap();
    let not_b = solver.try_not(b).unwrap();
    solver.assert_soft(not_a, 1, None).unwrap();
    solver.assert_soft(not_b, 1, None).unwrap();

    solver.try_push().unwrap();
    let assertions_before = solver.assertions();
    let scopes_before = solver.num_scopes();

    for round in 0..2 {
        let result = solver.check_sat_max().unwrap();
        assert!(result.is_optimal(), "round {round}: {result}");
        assert_eq!(result.satisfied_weight, 1);
        assert_eq!(result.violated_weight(), 1);
        assert_eq!(solver.assertions(), assertions_before, "round {round}");
        assert_eq!(solver.num_scopes(), scopes_before, "round {round}");
        assert!(
            solver.model_for_consumer().is_some(),
            "round {round}: optimal witness must be revalidated"
        );
        let model = solver.model_str().expect("optimal model remains queryable");
        assert!(
            !model.contains("__ay_soft_"),
            "round {round}: internal MaxSMT symbols leaked into model: {model}"
        );
    }

    solver.try_pop().unwrap();
}

/// Parsed SMT-LIB softs and native API softs have different owners and index
/// spaces. Until a joint result can represent both, `check_sat_max` must reject
/// the mix instead of temporarily hiding the parsed set.
#[test]
fn test_maxsmt_rejects_parsed_and_native_soft_mix_without_state_loss() {
    let mut solver = Solver::try_new(Logic::QfUf).unwrap();
    solver
        .parse_smtlib2("(assert-soft true :weight 7 :id parsed)")
        .unwrap();
    assert_eq!(solver.num_parsed_soft_constraints(), 1);

    let a = solver.declare_const("a", Sort::Bool);
    solver.assert_soft(a, 1, None).unwrap();

    for route in 0..3 {
        let result = match route {
            0 => solver.check_sat(),
            1 => solver.check_sat_assuming(&[]),
            _ => solver.check_sat_interruptible(|| false),
        };
        assert!(result.is_unknown(), "unexpected result: {result}");
        assert_eq!(
            solver.unknown_reason(),
            Some(crate::UnknownReason::Unsupported)
        );
        assert!(solver.model().is_none());
        assert!(solver.model_for_consumer().is_none());
    }

    let optimized = solver.optimize_check();
    assert!(optimized.is_unknown(), "unexpected result: {optimized}");
    assert_eq!(
        solver.unknown_reason(),
        Some(crate::UnknownReason::Unsupported)
    );

    for _ in 0..2 {
        let result = solver.check_sat_max().unwrap();
        assert!(result.is_unknown(), "unexpected result: {result}");
        assert_eq!(
            solver.unknown_reason(),
            Some(crate::UnknownReason::Unsupported)
        );
        assert_eq!(solver.num_parsed_soft_constraints(), 1);
        assert_eq!(solver.num_soft_constraints(), 1);
        assert!(solver.model().is_none());
        assert!(solver.model_for_consumer().is_none());
    }
}

/// An executor error can occur after internal MaxSMT probes have populated
/// state. It must retire all probe/prior witness state before reaching the
/// caller.
#[test]
fn test_maxsmt_executor_error_revokes_model() {
    let mut solver = Solver::try_new(Logic::QfUf).unwrap();
    let a = solver.declare_const("a", Sort::Bool);
    solver.assert_soft(a, 1, None).unwrap();
    let seeded = solver.check_sat_max().unwrap();
    assert!(
        seeded.is_optimal(),
        "result={seeded}, reason={:?}, error={:?}",
        solver.unknown_reason(),
        solver.executor_error()
    );
    assert!(solver.model_for_consumer().is_some());

    solver.set_option(":ay-maxsmt-engine", "invalid");
    let assertions_before = solver.assertions();
    let scopes_before = solver.num_scopes();
    let error = solver
        .check_sat_max()
        .expect_err("unknown MaxSMT engine must be rejected");
    assert!(error.to_string().contains("ay-maxsmt-engine"));
    assert_eq!(solver.assertions(), assertions_before);
    assert_eq!(solver.num_scopes(), scopes_before);
    assert_eq!(solver.num_parsed_soft_constraints(), 0);
    assert!(solver.model().is_none());
    assert!(solver.model_for_consumer().is_none());
    assert_eq!(
        solver.unknown_reason(),
        Some(crate::UnknownReason::InternalError)
    );
}

/// `check_sat_max` is the API-soft entrypoint. Parsed-only softs must not be
/// solved and then misreported as an empty native optimum.
#[test]
fn test_maxsmt_rejects_parsed_softs_even_without_native_softs() {
    let mut solver = Solver::try_new(Logic::QfUf).unwrap();
    solver
        .parse_smtlib2("(assert-soft false :weight 9)")
        .unwrap();

    let result = solver.check_sat_max().unwrap();
    assert!(result.is_unknown());
    assert_eq!(
        solver.unknown_reason(),
        Some(crate::UnknownReason::Unsupported)
    );
    assert_eq!(solver.num_parsed_soft_constraints(), 1);
    assert!(solver.model().is_none());
    assert!(solver.model_for_consumer().is_none());
}

/// Neither native optimization entrypoint may silently drop the other
/// objective class while presenting a non-joint model value as optimal.
#[test]
fn test_native_objective_and_soft_mix_is_honest_unknown_everywhere() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let ten = solver.int_const(10);
    let lo = solver.try_ge(x, zero).unwrap();
    let hi = solver.try_le(x, ten).unwrap();
    solver.try_assert_term(lo).unwrap();
    solver.try_assert_term(hi).unwrap();
    let is_zero = solver.try_eq(x, zero).unwrap();
    solver.assert_soft(is_zero, 3, None).unwrap();
    let objective = solver.maximize(x);

    let optimized = solver.optimize_check();
    assert!(optimized.is_unknown());
    assert_eq!(
        solver.unknown_reason(),
        Some(crate::UnknownReason::Unsupported)
    );
    assert_eq!(solver.get_objective_value(objective), None);
    assert!(solver.model().is_none());
    assert!(solver.model_for_consumer().is_none());
    assert!(solver.executor.take_sat_certificate().is_none());

    let maxsmt = solver.check_sat_max().unwrap();
    assert!(maxsmt.is_unknown());
    assert_eq!(
        solver.unknown_reason(),
        Some(crate::UnknownReason::Unsupported)
    );
    assert_eq!(solver.get_objective_value(objective), None);
    assert!(solver.model().is_none());
    assert!(solver.model_for_consumer().is_none());
    assert!(solver.executor.take_sat_certificate().is_none());
}

/// Release builds must authenticate the full executor-installed soft set, not
/// merely assert its length in debug builds. The hook substitutes equal-length
/// accounting input after execution; publication must fail closed.
#[test]
fn test_maxsmt_native_soft_transaction_corruption_is_rejected() {
    let mut solver = Solver::try_new(Logic::QfUf).unwrap();
    let a = solver.declare_const("a", Sort::Bool);
    solver.assert_soft(a, 1, None).unwrap();
    solver.corrupt_native_soft_transaction_for_test();

    let result = solver.check_sat_max().unwrap();
    assert!(result.is_unknown());
    assert_eq!(
        solver.unknown_reason(),
        Some(crate::UnknownReason::InternalError)
    );
    assert!(solver
        .executor_error()
        .is_some_and(|detail| detail.contains("mutated or reordered")));
    assert!(solver.model().is_none());
    assert!(solver.model_for_consumer().is_none());
    assert_eq!(solver.num_soft_constraints(), 1);
}

/// The native result has no "approximate" state, so instances outside the
/// exact weighted encoding bound (or whose total overflows) must be Unknown and
/// must not expose the executor's feasible greedy fallback as an optimum/model.
#[test]
fn test_maxsmt_large_and_overflowing_weights_are_honest_unknown() {
    for weights in [vec![4097], vec![u64::MAX, 1]] {
        let mut solver = Solver::try_new(Logic::QfUf).unwrap();
        let a = solver.declare_const("a", Sort::Bool);
        let assertions_before = solver.assertions();
        let scopes_before = solver.num_scopes();
        for weight in weights {
            solver.assert_soft(a, weight, None).unwrap();
        }

        let result = solver.check_sat_max().unwrap();
        assert!(result.is_unknown(), "unexpected result: {result}");
        assert!(!result.is_optimal());
        assert_eq!(result.satisfied_weight, 0);
        assert_eq!(result.violated_weight(), 0);
        assert!(result.violated_softs.is_empty());
        assert_eq!(solver.assertions(), assertions_before);
        assert_eq!(solver.num_scopes(), scopes_before);
        assert!(solver.model().is_none());
        assert!(solver.model_for_consumer().is_none());
        assert_eq!(
            solver.unknown_reason(),
            Some(crate::UnknownReason::Incomplete)
        );
    }
}

/// Soft-set mutations supersede the preceding query just like hard assertion
/// mutations: stale models/certificates/optima are never queryable afterward.
#[test]
fn test_maxsmt_soft_mutations_invalidate_prior_query_artifacts() {
    let mut solver = Solver::try_new(Logic::QfUf).unwrap();
    let a = solver.declare_const("a", Sort::Bool);
    solver.try_assert_term(a).unwrap();
    assert!(solver.check_sat().is_sat());
    assert!(solver.model_for_consumer().is_some());
    let incremental_before_soft_mutation = solver.executor.incremental_mode;

    solver.assert_soft(a, 1, None).unwrap();
    assert!(solver.model().is_none());
    assert!(solver.model_for_consumer().is_none());
    assert_eq!(
        solver.executor.incremental_mode, incremental_before_soft_mutation,
        "soft registration must not masquerade as a hard-assertion mutation"
    );

    let not_a = solver.try_not(a).unwrap();
    solver.assert_soft(not_a, 1, None).unwrap();
    assert!(solver.check_sat_max().unwrap().is_optimal());
    assert!(solver.model_for_consumer().is_some());
    let incremental_before_truncate = solver.executor.incremental_mode;

    solver.truncate_soft_constraints(1);
    assert_eq!(solver.num_soft_constraints(), 1);
    assert!(solver.model().is_none());
    assert!(solver.model_for_consumer().is_none());
    assert_eq!(
        solver.executor.incremental_mode, incremental_before_truncate,
        "soft truncation must not masquerade as a hard-assertion mutation"
    );
}
