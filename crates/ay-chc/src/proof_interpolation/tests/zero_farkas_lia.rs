// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_zero_farkas_fm_elimination_counter_increments_without_synthetic() {
    // Build a zero-Farkas scenario where:
    // - direct IUC is skipped (no shared-only B-core conjuncts),
    // - A-side equalities are unavailable,
    // - FM elimination can project A-local vars and produce a Craig-valid interpolant.
    let x = ChcVar::new("x", ChcSort::Int);
    let a_local = ChcVar::new("a_local", ChcSort::Int);
    let b_local = ChcVar::new("b_local", ChcSort::Int);

    // A implies x <= 0 via:
    //   a_local <= 0
    //   x - a_local <= 0
    let a_constraints = vec![
        ChcExpr::le(ChcExpr::var(a_local.clone()), ChcExpr::int(0)),
        ChcExpr::le(
            ChcExpr::sub(ChcExpr::var(x.clone()), ChcExpr::var(a_local)),
            ChcExpr::int(0),
        ),
    ];

    // B implies x >= 1 via:
    //   b_local >= 1
    //   x - b_local >= 0
    // Both B conjuncts mention non-shared vars, so direct IUC shared-B fast path is skipped.
    let b_constraints = vec![
        ChcExpr::ge(ChcExpr::var(b_local.clone()), ChcExpr::int(1)),
        ChcExpr::ge(
            ChcExpr::sub(ChcExpr::var(x.clone()), ChcExpr::var(b_local)),
            ChcExpr::int(0),
        ),
    ];

    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name]);

    let before_fm = ZERO_FARKAS_FM_ELIMINATION_SUCCESSES.load(Ordering::Relaxed);
    let mut smt = SmtContext::new();

    let candidate = try_zero_farkas_interpolant_candidate(
        &mut smt,
        &a_constraints,
        &b_constraints,
        &shared,
        false,
    )
    .expect("expected FM elimination interpolant");
    let interpolant = candidate.expr;

    let after_fm = ZERO_FARKAS_FM_ELIMINATION_SUCCESSES.load(Ordering::Relaxed);

    assert_eq!(candidate.kind, InterpolantKind::FourierMotzkin);
    assert!(
        after_fm > before_fm,
        "expected FM elimination counter to increment (before={before_fm}, after={after_fm})"
    );

    let interp_vars: FxHashSet<String> = interpolant.vars().into_iter().map(|v| v.name).collect();
    assert!(
        interp_vars.iter().all(|v| shared.contains(v)),
        "interpolant must only mention shared vars: {interpolant}"
    );

    let mut check_smt = SmtContext::new();
    let a_implies_i = ChcExpr::and(and_slice(&a_constraints), ChcExpr::not(interpolant.clone()));
    assert!(
        matches!(
            check_smt.check_sat(&a_implies_i),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "A does not imply interpolant: {interpolant}"
    );

    check_smt.reset();
    let i_and_b = and_with_tail(interpolant.clone(), &b_constraints);
    assert!(
        matches!(
            check_smt.check_sat(&i_and_b),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "interpolant does not block B: {interpolant}"
    );
}

#[test]
fn test_zero_farkas_b_side_fm_projection_with_reversed_shared_var() {
    // This scenario has B-local var y with shared x. B-side FM projection
    // eliminates y from {x - y >= 1, y >= 0} to get x >= 1, then returns
    // I = NOT(x >= 1) = (x <= 0). This is the same fallback path as the
    // companion test but with x as shared (instead of y).
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let a_constraints = vec![ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(0))];
    let b_constraints = vec![
        ChcExpr::ge(
            ChcExpr::sub(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
            ChcExpr::int(1),
        ),
        ChcExpr::ge(ChcExpr::var(y.clone()), ChcExpr::int(0)),
    ];
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name]);

    let before_b_fm = ZERO_FARKAS_B_SIDE_FM_PROJECTION_SUCCESSES.load(Ordering::Relaxed);

    let mut smt = SmtContext::new();
    let candidate = try_zero_farkas_interpolant_candidate(
        &mut smt,
        &a_constraints,
        &b_constraints,
        &shared,
        false,
    )
    .expect("expected B-side FM projection interpolant");
    let interpolant = candidate.expr;

    let after_b_fm = ZERO_FARKAS_B_SIDE_FM_PROJECTION_SUCCESSES.load(Ordering::Relaxed);

    assert_eq!(candidate.kind, InterpolantKind::BSideFourierMotzkin);
    assert!(
        after_b_fm > before_b_fm,
        "expected B-side FM projection counter to increment (before={before_b_fm}, after={after_b_fm})"
    );

    let interp_vars: FxHashSet<String> = interpolant.vars().into_iter().map(|v| v.name).collect();
    assert!(
        interp_vars.iter().all(|v| shared.contains(v)),
        "interpolant must only mention shared vars: {interpolant}"
    );
    assert!(
        !interp_vars.contains(&y.name),
        "interpolant should not mention y: {interpolant}"
    );

    let mut check_smt = SmtContext::new();
    let a_implies_i = ChcExpr::and(and_slice(&a_constraints), ChcExpr::not(interpolant.clone()));
    assert!(
        matches!(
            check_smt.check_sat(&a_implies_i),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "A does not imply interpolant: {interpolant}"
    );

    check_smt.reset();
    let i_and_b = and_with_tail(interpolant.clone(), &b_constraints);
    assert!(
        matches!(
            check_smt.check_sat(&i_and_b),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "interpolant does not block B: {interpolant}"
    );
}

#[test]
fn test_zero_farkas_b_side_fm_projection_counter_increments_before_lia() {
    // Build a zero-Farkas scenario where:
    // - direct IUC is skipped (no shared-only B-core conjuncts),
    // - A-side equality fallback is unavailable,
    // - A-side FM elimination is skipped (A has only shared vars),
    // - B-side FM projection derives a shared summary J and uses I = ¬J.
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let a_constraints = vec![ChcExpr::ge(ChcExpr::var(y.clone()), ChcExpr::int(0))];
    let b_constraints = vec![
        // x >= y
        ChcExpr::ge(
            ChcExpr::sub(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
            ChcExpr::int(0),
        ),
        // x <= -1
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(-1)),
    ];
    let shared: FxHashSet<String> = FxHashSet::from_iter([y.name]);

    let before_b_fm = ZERO_FARKAS_B_SIDE_FM_PROJECTION_SUCCESSES.load(Ordering::Relaxed);

    let mut smt = SmtContext::new();
    let candidate = try_zero_farkas_interpolant_candidate(
        &mut smt,
        &a_constraints,
        &b_constraints,
        &shared,
        false,
    )
    .expect("expected B-side FM projection interpolant");
    let interpolant = candidate.expr;

    let after_b_fm = ZERO_FARKAS_B_SIDE_FM_PROJECTION_SUCCESSES.load(Ordering::Relaxed);

    assert_eq!(candidate.kind, InterpolantKind::BSideFourierMotzkin);
    assert!(
        after_b_fm > before_b_fm,
        "expected B-side FM projection counter to increment (before={before_b_fm}, after={after_b_fm})"
    );

    let interp_vars: FxHashSet<String> = interpolant.vars().into_iter().map(|v| v.name).collect();
    assert!(
        interp_vars.iter().all(|v| shared.contains(v)),
        "interpolant must only mention shared vars: {interpolant}"
    );
    assert!(
        !interp_vars.contains(&x.name),
        "interpolant should not mention x: {interpolant}"
    );

    let mut check_smt = SmtContext::new();
    let a_implies_i = ChcExpr::and(and_slice(&a_constraints), ChcExpr::not(interpolant.clone()));
    assert!(
        matches!(
            check_smt.check_sat(&a_implies_i),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "A does not imply interpolant: {interpolant}"
    );

    check_smt.reset();
    let i_and_b = and_with_tail(interpolant.clone(), &b_constraints);
    assert!(
        matches!(
            check_smt.check_sat(&i_and_b),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "interpolant does not block B: {interpolant}"
    );
}

#[test]
fn test_zero_farkas_lia_attempt_counter_increments_on_non_linear_fallback() {
    // Construct a Boolean (non-atom) A-constraint so the LIA fallback is
    // attempted but rejected by the linear-atom precondition check.
    let x = ChcVar::new("x", ChcSort::Int);
    let a_constraints = vec![ChcExpr::or_all(vec![
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(0)),
    ])];
    let b_constraints = vec![ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(-1))];
    let shared: FxHashSet<String> = FxHashSet::default();

    let before_attempts = ZERO_FARKAS_LIA_FARKAS_ATTEMPTS.load(Ordering::Relaxed);
    let before_precond = ZERO_FARKAS_LIA_FARKAS_PRECONDITION_FAILURES.load(Ordering::Relaxed);

    let mut smt = SmtContext::new();
    let interpolant =
        try_zero_farkas_interpolant(&mut smt, &a_constraints, &b_constraints, &shared);

    let after_attempts = ZERO_FARKAS_LIA_FARKAS_ATTEMPTS.load(Ordering::Relaxed);
    let after_precond = ZERO_FARKAS_LIA_FARKAS_PRECONDITION_FAILURES.load(Ordering::Relaxed);

    assert!(
        interpolant.is_none(),
        "expected no interpolant for non-atom A-constraint case"
    );
    assert!(
        after_attempts > before_attempts,
        "expected LIA fallback attempt counter to increment (before={before_attempts}, after={after_attempts})"
    );
    assert!(
        after_precond > before_precond,
        "expected at least one LIA precondition failure to be recorded (before={before_precond}, after={after_precond})"
    );
}

#[test]
fn test_lia_farkas_precondition_rejects_integer_division_atoms() {
    // `div` is not linear arithmetic and should be rejected before LIA-Farkas.
    let x = ChcVar::new("x", ChcSort::Int);
    let a_constraints = vec![ChcExpr::eq(
        ChcExpr::Op(
            ChcOp::Div,
            vec![Arc::new(ChcExpr::var(x.clone())), Arc::new(ChcExpr::int(2))],
        ),
        ChcExpr::int(0),
    )];
    let b_constraints = vec![ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(1))];
    let shared: FxHashSet<String> = FxHashSet::default();

    let before_precond = ZERO_FARKAS_LIA_FARKAS_PRECONDITION_FAILURES.load(Ordering::Relaxed);
    let mut smt = SmtContext::new();
    let interpolant =
        compute_interpolant_from_lia_farkas(&mut smt, &a_constraints, &b_constraints, &shared);
    let after_precond = ZERO_FARKAS_LIA_FARKAS_PRECONDITION_FAILURES.load(Ordering::Relaxed);

    assert!(
        interpolant.is_none(),
        "LIA-Farkas should reject atoms that contain integer division"
    );
    assert!(
        after_precond > before_precond,
        "expected precondition failure counter to increase (before={before_precond}, after={after_precond})"
    );
}

#[test]
fn test_zero_farkas_direct_iuc_core_exact_fast_path_counter_increments() {
    // Single shared B-core conjunct gives a core-exact direct IUC candidate.
    // This should use the no-revalidation fast path and still return
    // a Craig-valid interpolant.
    let x = ChcVar::new("x", ChcSort::Int);
    let a_constraints = vec![ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))];
    let b_constraints = vec![ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(1))];
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name]);

    let before = ZERO_FARKAS_DIRECT_IUC_CORE_EXACT_SUCCESSES.load(Ordering::Relaxed);
    let mut smt = SmtContext::new();
    let candidate = compute_interpolant_candidate_from_smt_farkas_history(
        &mut smt,
        &a_constraints,
        &b_constraints,
        &shared,
        false,
    )
    .expect("expected core-exact direct IUC interpolant");
    let after = ZERO_FARKAS_DIRECT_IUC_CORE_EXACT_SUCCESSES.load(Ordering::Relaxed);

    assert!(
        after > before,
        "expected core-exact direct IUC counter to increment (before={before}, after={after})"
    );
    assert_eq!(candidate.kind, InterpolantKind::DirectIucCoreExact);
    assert!(
        !candidate.has_farkas_conflicts,
        "zero-Farkas direct IUC should record has_farkas_conflicts=false"
    );
    let interpolant = candidate.expr;

    let interp_vars: FxHashSet<String> = interpolant.vars().into_iter().map(|v| v.name).collect();
    assert!(
        interp_vars.iter().all(|v| shared.contains(v)),
        "interpolant must only mention shared vars: {interpolant}"
    );

    let mut check_smt = SmtContext::new();
    let a_implies_i = ChcExpr::and(and_slice(&a_constraints), ChcExpr::not(interpolant.clone()));
    assert!(
        matches!(
            check_smt.check_sat(&a_implies_i),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "A does not imply interpolant: {interpolant}"
    );

    check_smt.reset();
    let i_and_b = and_with_tail(interpolant.clone(), &b_constraints);
    assert!(
        matches!(
            check_smt.check_sat(&i_and_b),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "interpolant does not block B: {interpolant}"
    );
}

fn nested4_style_bv_vars() -> (
    ChcVar,
    ChcVar,
    ChcVar,
    ChcVar,
    ChcVar,
    ChcVar,
    ChcVar,
    ChcVar,
) {
    (
        ChcVar::new("A", ChcSort::BitVec(32)),
        ChcVar::new("B", ChcSort::BitVec(32)),
        ChcVar::new("C", ChcSort::BitVec(32)),
        ChcVar::new("D", ChcSort::BitVec(32)),
        ChcVar::new("E", ChcSort::BitVec(32)),
        ChcVar::new("F", ChcSort::Bool),
        ChcVar::new("G", ChcSort::Bool),
        ChcVar::new("H", ChcSort::Bool),
    )
}

fn nested4_style_direct_iuc_inputs() -> (Vec<ChcExpr>, Vec<ChcExpr>, FxHashSet<String>) {
    let (a_bv, b_bv, c_bv, d_bv, e_bv, f, g, h) = nested4_style_bv_vars();
    let a_constraints = vec![
        ChcExpr::not(ChcExpr::var(f.clone())),
        ChcExpr::not(ChcExpr::var(g.clone())),
        ChcExpr::not(ChcExpr::var(h.clone())),
    ];
    let b_constraints = vec![ChcExpr::or_all(vec![
        ChcExpr::and_all(vec![
            ChcExpr::var(f.clone()),
            ChcExpr::not(ChcExpr::var(g.clone())),
            ChcExpr::var(h.clone()),
            ChcExpr::eq(
                ChcExpr::BitVec(3_221_225_472, 32),
                ChcExpr::var(e_bv.clone()),
            ),
            ChcExpr::eq(
                ChcExpr::BitVec(4_294_967_295, 32),
                ChcExpr::var(d_bv.clone()),
            ),
            ChcExpr::eq(
                ChcExpr::var(a_bv.clone()),
                ChcExpr::BitVec(3_221_225_472, 32),
            ),
            ChcExpr::eq(
                ChcExpr::BitVec(4_294_967_293, 32),
                ChcExpr::var(c_bv.clone()),
            ),
            ChcExpr::eq(
                ChcExpr::var(b_bv.clone()),
                ChcExpr::BitVec(4_294_967_295, 32),
            ),
        ]),
        ChcExpr::and_all(vec![
            ChcExpr::var(f.clone()),
            ChcExpr::var(g.clone()),
            ChcExpr::not(ChcExpr::var(h.clone())),
        ]),
    ])];
    let shared = FxHashSet::from_iter([
        a_bv.name, b_bv.name, c_bv.name, d_bv.name, e_bv.name, f.name, g.name, h.name,
    ]);
    (a_constraints, b_constraints, shared)
}

fn nested4_style_direct_iuc_expected() -> ChcExpr {
    let (a_bv, b_bv, c_bv, d_bv, e_bv, f, g, h) = nested4_style_bv_vars();
    ChcExpr::and_all(vec![
        ChcExpr::or_all(vec![
            ChcExpr::not(ChcExpr::var(f.clone())),
            ChcExpr::var(g.clone()),
            ChcExpr::not(ChcExpr::var(h.clone())),
            ChcExpr::ne(ChcExpr::BitVec(3_221_225_472, 32), ChcExpr::var(e_bv)),
            ChcExpr::ne(ChcExpr::BitVec(4_294_967_295, 32), ChcExpr::var(d_bv)),
            ChcExpr::ne(ChcExpr::var(a_bv), ChcExpr::BitVec(3_221_225_472, 32)),
            ChcExpr::ne(ChcExpr::BitVec(4_294_967_293, 32), ChcExpr::var(c_bv)),
            ChcExpr::ne(ChcExpr::var(b_bv), ChcExpr::BitVec(4_294_967_295, 32)),
        ]),
        ChcExpr::or_all(vec![
            ChcExpr::not(ChcExpr::var(f)),
            ChcExpr::not(ChcExpr::var(g)),
            ChcExpr::var(h),
        ]),
    ])
}

#[test]
fn test_zero_farkas_direct_iuc_core_exact_preserves_nested4_style_bv_clauses() {
    // Release `nested4` traces for #5877 hit a direct-IUC exact-core fast path
    // where one shared B-side disjunction negates into a conjunction of two BV
    // clauses. Keep that shape intact so clause-splitting/push packets can rely
    // on it instead of reasoning from a stale scalar-only candidate.
    let (a_constraints, b_constraints, shared) = nested4_style_direct_iuc_inputs();

    let mut smt = SmtContext::new();
    let candidate = compute_interpolant_candidate_from_smt_farkas_history(
        &mut smt,
        &a_constraints,
        &b_constraints,
        &shared,
        false,
    )
    .expect("expected nested4-style direct-IUC interpolant");

    assert_eq!(candidate.kind, InterpolantKind::DirectIucCoreExact);
    assert!(
        !candidate.has_farkas_conflicts,
        "expected zero-Farkas candidate for nested4-style BV clause"
    );

    let expected = nested4_style_direct_iuc_expected();

    assert_eq!(
        candidate.expr, expected,
        "expected nested4-style direct-IUC fast path to preserve the raw BV clause conjunction"
    );
    assert_eq!(
        candidate.expr.collect_conjuncts().len(),
        2,
        "expected the direct-IUC candidate to stay as a two-clause conjunction"
    );
}

#[test]
fn test_zero_farkas_direct_iuc_core_exact_skips_b_local_bv_candidate_7701() {
    let p = ChcVar::new("p", ChcSort::Bool);
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let a_constraints = vec![ChcExpr::not(ChcExpr::var(p.clone()))];
    let b_constraints = vec![
        ChcExpr::or_all(vec![
            ChcExpr::var(p.clone()),
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(0, 8)),
        ]),
        ChcExpr::ne(ChcExpr::var(x), ChcExpr::BitVec(0, 8)),
    ];
    let shared = FxHashSet::from_iter([p.name]);

    let mut smt = SmtContext::new();
    let candidate = compute_interpolant_candidate_from_smt_farkas_history(
        &mut smt,
        &a_constraints,
        &b_constraints,
        &shared,
        false,
    );

    assert_ne!(
        candidate.as_ref().map(|candidate| candidate.kind),
        Some(InterpolantKind::DirectIucCoreExact),
        "core-exact fast path must not accept candidates with B-local BV vars"
    );

    if let Some(candidate) = candidate {
        let a_conj = and_slice(&a_constraints);
        let b_conj = and_slice(&b_constraints);
        let mut check_smt = SmtContext::new();
        assert!(
            verify_craig_properties(
                &candidate.expr,
                &a_conj,
                &b_conj,
                &shared,
                &mut check_smt,
                "test_zero_farkas_direct_iuc_core_exact_skips_b_local_bv_candidate_7701",
            ),
            "fallback candidate must satisfy Craig properties: {:?}",
            candidate
        );
    }
}

#[test]
fn test_smt_term_to_chc_expr_roundtrip_gt_ge() {
    let x = ChcVar::new("x", ChcSort::Int);
    let mut smt = SmtContext::new();

    let gt_expr = ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let gt_term = smt.convert_expr(&gt_expr);
    let gt_back = smt.term_to_chc_expr(gt_term);
    assert!(
        gt_back == Some(gt_expr.clone())
            || gt_back == Some(ChcExpr::lt(ChcExpr::int(0), ChcExpr::var(x.clone()))),
        "unexpected gt roundtrip {gt_back:?}"
    );

    let ge_expr = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));
    let ge_term = smt.convert_expr(&ge_expr);
    let ge_back = smt.term_to_chc_expr(ge_term);
    assert!(
        ge_back == Some(ge_expr.clone())
            || ge_back
                == Some(ChcExpr::le(
                    ChcExpr::int(0),
                    ChcExpr::var(ChcVar::new("x", ChcSort::Int))
                )),
        "unexpected ge roundtrip {ge_back:?}"
    );
}

#[test]
fn test_smt_farkas_history_with_branch_split_returns_valid_interpolant() {
    // A: x != 0 (requires integer branching)
    // B: x = 0
    //
    // With IucSolver proxy literals tracking partition membership accurately,
    // we can now return `x != 0` as a valid interpolant:
    // - A ⊨ (x != 0) trivially (it IS A)
    // - (x != 0) ∧ (x = 0) is UNSAT (blocks B)
    //
    // Previously this test expected None because branch splits like (x <= -1)
    // polluted the B-partition classification.
    let x = ChcVar::new("x", ChcSort::Int);

    let a = vec![ChcExpr::ne(ChcExpr::var(x.clone()), ChcExpr::int(0))];
    let b = vec![ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))];
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name]);

    let mut smt = SmtContext::new();
    let interpolant = compute_interpolant_from_smt_farkas_history(&mut smt, &a, &b, &shared, false);

    // Now we expect a valid interpolant (x != 0)
    assert!(
        interpolant.is_some(),
        "expected valid interpolant with IucSolver; got None"
    );

    let interp = interpolant.unwrap();
    // Verify it's the expected (x != 0)
    assert!(
        matches!(&interp, ChcExpr::Op(ChcOp::Ne, args) if args.len() == 2),
        "expected x != 0 interpolant; got {interp:?}"
    );

    // Verify all three Craig conditions:
    // 1) shared-variable locality
    // 2) A |= I
    // 3) I /\ B is UNSAT
    let a_expr = and_slice(&a);
    let b_expr = and_slice(&b);
    let mut check_smt = SmtContext::new();
    assert!(
        crate::interpolant_validation::is_valid_interpolant_with_check_sat(
            &a_expr,
            &b_expr,
            &interp,
            &shared,
            |expr| check_smt.check_sat(expr),
        ),
        "branch-split interpolant must satisfy Craig conditions, got {interp}"
    );
}
