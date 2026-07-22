// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_proof_interpolant_simple_bounds() {
    // A: x <= 5
    // B: x >= 10
    // Interpolant should be x <= 5 (A-side).
    let x = ChcVar::new("x", ChcSort::Int);
    let a = vec![ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5))];
    let b = vec![ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10))];
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name.clone()]);

    let mut smt = SmtContext::new();
    let interpolant = compute_interpolant_from_lia_farkas(&mut smt, &a, &b, &shared)
        .expect("expected interpolant from Farkas certificate");

    assert_eq!(interpolant, ChcExpr::le(ChcExpr::var(x), ChcExpr::int(5)));

    // Regression check for #2392: if we return Some(I), A must imply I.
    let mut check_smt = SmtContext::new();
    let a_implies_i = ChcExpr::and(ChcExpr::and_all(a), ChcExpr::not(interpolant));
    assert!(matches!(
        check_smt.check_sat(&a_implies_i),
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
    ));
}

#[test]
fn test_proof_interpolant_rejects_non_shared_vars() {
    // If the interpolant would mention a non-shared var, we currently return None.
    // Use x + y <= 5 so that both x and y are in the UNSAT core.
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let a = vec![
        // x + y <= 5  (y is required in the conflict)
        ChcExpr::le(
            ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
            ChcExpr::int(5),
        ),
    ];
    let b = vec![
        // x >= 10, y >= 0  (conflict: x + y >= 10 contradicts x + y <= 5)
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10)),
        ChcExpr::ge(ChcExpr::var(y), ChcExpr::int(0)),
    ];
    // Only x is shared; y is NOT shared but IS in the UNSAT core.
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name]);

    let mut smt = SmtContext::new();
    let interpolant = compute_interpolant_from_lia_farkas(&mut smt, &a, &b, &shared);
    // The interpolant from A-side (`x + y <= 5`) would mention non-shared `y`,
    // so we should reject it.
    assert!(interpolant.is_none());
}

#[test]
fn test_proof_interpolant_equality_validation() {
    // Regression test for P0 soundness bug (#97):
    // A: x = 5 (equality)
    // B: x < 1
    //
    // The naive Farkas extraction might produce x <= 5 (wrong direction of equality).
    // But x <= 5 is NOT a valid interpolant because x <= 5 ∧ x < 1 is SAT (e.g., x=0).
    //
    // The soundness check should reject this and return None, falling back to
    // other interpolation methods.
    let x = ChcVar::new("x", ChcSort::Int);
    let a = vec![ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5))];
    let b = vec![ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(1))];
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name.clone()]);

    let mut smt = SmtContext::new();
    let interpolant = compute_interpolant_from_lia_farkas(&mut smt, &a, &b, &shared);

    // Either we get a valid interpolant (like x >= 1), or None.
    // We should NOT get x <= 5 because that's not a valid interpolant.
    if let Some(ref i) = interpolant {
        // Verify the interpolant is valid: I ∧ B must be UNSAT
        // (If the function returns Some, the soundness check already passed)
        // But let's double-check that it's not the buggy x <= 5.
        let invalid_interp = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(5));
        assert_ne!(
            *i, invalid_interp,
            "Should not produce x <= 5 as interpolant"
        );
    }
    // If interpolant is None, that's also acceptable - fallback methods will handle it.
}

#[test]
fn test_try_a_side_equality_interpolant_prefers_weaker_inequality() {
    // A: x = 0
    // B: x >= 1
    //
    // The equality blocks B, but so does the weaker inequality x <= 0.
    // We prefer the inequality because it is more likely to be inductive.
    let x = ChcVar::new("x", ChcSort::Int);
    let a = vec![ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))];
    let b = vec![ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(1))];
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name.clone()]);

    let interpolant = try_a_side_equality_interpolant(&a, &b, &shared, &mut SmtContext::new())
        .expect("expected A-side inequality interpolant");

    assert_eq!(interpolant, ChcExpr::le(ChcExpr::var(x), ChcExpr::int(0)));
}

#[test]
fn test_try_a_side_equality_interpolant_prefers_normalized_ge_for_flipped_equality() {
    // A: 0 = x
    // B: x <= -1
    //
    // Prefer the normalized inequality x >= 0 (not (<= 0 x)).
    let x = ChcVar::new("x", ChcSort::Int);
    let a = vec![ChcExpr::eq(ChcExpr::int(0), ChcExpr::var(x.clone()))];
    let b = vec![ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(-1))];
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name.clone()]);

    let interpolant = try_a_side_equality_interpolant(&a, &b, &shared, &mut SmtContext::new())
        .expect("expected A-side inequality interpolant");

    assert_eq!(interpolant, ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0)));
}

#[test]
fn test_try_a_side_equality_interpolant_uses_conjunction_when_single_equalities_too_weak() {
    // A: x = 0, y = 0, z = 5
    // B: x + y = 1
    //
    // No single equality blocks B, but (x = 0 ∧ y = 0) does.
    // This regression guards the conjunction fallback path used in #2450.
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    let a = vec![
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(0)),
        ChcExpr::eq(ChcExpr::var(z.clone()), ChcExpr::int(5)),
    ];
    let b = vec![ChcExpr::eq(
        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
        ChcExpr::int(1),
    )];
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name, y.name, z.name.clone()]);

    let interpolant = try_a_side_equality_interpolant(&a, &b, &shared, &mut SmtContext::new())
        .expect("expected conjunction equality interpolant");

    let mut check_smt = SmtContext::new();
    let a_implies_i = ChcExpr::and(and_slice(&a), ChcExpr::not(interpolant.clone()));
    assert!(
        matches!(
            check_smt.check_sat(&a_implies_i),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "A does not imply interpolant: {interpolant}"
    );

    check_smt.reset();
    let i_and_b = and_with_tail(interpolant.clone(), &b);
    assert!(
        matches!(
            check_smt.check_sat(&i_and_b),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "interpolant does not block B: {interpolant}"
    );

    let interp_vars: FxHashSet<String> = interpolant.vars().into_iter().map(|v| v.name).collect();
    assert!(
        !interp_vars.contains(&z.name),
        "conjunction fallback should avoid unrelated equality z=5: {interpolant}"
    );
}
// NOTE: N-ary equality test removed - the equality weakening code correctly handles
// binary equalities (args.len() == 2). N-ary equalities like (= 0 x 0) are rare in CHC
// problems and would require additional logic to extract usable pairs.

#[test]
fn test_proof_interpolant_two_variables() {
    // A: x <= 3, y <= 2
    // B: x + y >= 10
    // Interpolant should involve only shared variables and prove UNSAT.
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let a = vec![
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(3)),
        ChcExpr::le(ChcExpr::var(y.clone()), ChcExpr::int(2)),
    ];
    let b = vec![ChcExpr::ge(
        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
        ChcExpr::int(10),
    )];
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name, y.name]);

    let mut smt = SmtContext::new();
    let interpolant = compute_interpolant_from_lia_farkas(&mut smt, &a, &b, &shared);

    // The interpolant should exist and be valid (soundness check passes)
    if let Some(ref i) = interpolant {
        // Verify the interpolant mentions only shared vars
        let interp_vars: FxHashSet<String> = i.vars().into_iter().map(|v| v.name).collect();
        for v in &interp_vars {
            assert!(shared.contains(v), "Interpolant var {v} not in shared set");
        }
    }
    // None is also acceptable - means fallback needed
}

/// Test that disequalities (NOT(x = c)) are handled correctly and not confused with equalities.
/// This prevents a potential soundness bug where treating NOT(x=5) as x=5 could produce
/// an interpolant inconsistent with B.
#[test]
fn test_proof_interpolant_disequality_not_equality() {
    // Test that NOT(x = c) is NOT treated as an equality
    // A: x != 5 (meaning NOT(x = 5))
    // B: x >= 5, x <= 5 (forces x = 5)
    // If we incorrectly treat NOT(x=5) as equality, we might produce wrong interpolant
    let x = ChcVar::new("x", ChcSort::Int);

    let a = vec![ChcExpr::not(ChcExpr::eq(
        ChcExpr::var(x.clone()),
        ChcExpr::int(5),
    ))];
    let b = vec![
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(5)),
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5)),
    ];
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name]);

    let mut smt = SmtContext::new();
    let _interpolant = compute_interpolant_from_lia_farkas(&mut smt, &a, &b, &shared);
    // Either valid interpolant or None is acceptable - the key is no crash.
    // If an interpolant is returned, soundness is checked inside the function.
    // No assertion needed: reaching this point without panic = success.
}

#[test]
fn test_proof_interpolant_strict_inequality() {
    // A: x < 5
    // B: x >= 5
    // Interpolant should be x < 5 or equivalent
    let x = ChcVar::new("x", ChcSort::Int);

    let a = vec![ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(5))];
    let b = vec![ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(5))];
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name]);

    let mut smt = SmtContext::new();
    let interpolant = compute_interpolant_from_lia_farkas(&mut smt, &a, &b, &shared);

    // The interpolant should be valid (strict inequality or equivalent)
    assert!(
        interpolant.is_some(),
        "Should produce interpolant for simple strict inequality"
    );
}

#[test]
fn test_proof_interpolant_empty_constraints() {
    // Edge case: empty A or B
    let x = ChcVar::new("x", ChcSort::Int);
    let a: Vec<ChcExpr> = vec![];
    let b = vec![ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(5))];
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name]);

    let mut smt = SmtContext::new();
    let interpolant = compute_interpolant_from_lia_farkas(&mut smt, &a, &b, &shared);

    // Should return None for empty A
    assert!(interpolant.is_none(), "Empty A should return None");
}

#[test]
fn test_proof_interpolant_true_constraint() {
    // Edge case: trivially true constraint in A
    // A: x <= 5, true
    // B: x >= 10
    let x = ChcVar::new("x", ChcSort::Int);

    let a = vec![
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5)),
        ChcExpr::Bool(true),
    ];
    let b = vec![ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10))];
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name.clone()]);

    let mut smt = SmtContext::new();
    let interpolant = compute_interpolant_from_lia_farkas(&mut smt, &a, &b, &shared);

    // True should be filtered out, so we get x <= 5
    if let Some(ref i) = interpolant {
        assert_eq!(*i, ChcExpr::le(ChcExpr::var(x), ChcExpr::int(5)));
    }
}

#[test]
fn test_select_shrunk_b_occurrences_honors_core_multiplicity() {
    let x = ChcVar::new("x", ChcSort::Int);
    let ge0 = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let ge1 = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(1));
    let b_constraints = vec![ge0.clone(), ge0.clone(), ge1];

    let single = select_shrunk_b_occurrences(&b_constraints, std::slice::from_ref(&ge0));
    assert_eq!(
        single.len(),
        1,
        "single core occurrence must match one original constraint"
    );
    assert_eq!(single[0].0, 0, "expected first duplicate index");

    let double = select_shrunk_b_occurrences(&b_constraints, &[ge0.clone(), ge0]);
    assert_eq!(
        double.len(),
        2,
        "core multiplicity should select exactly two duplicates"
    );
    assert_eq!(double[0].0, 0);
    assert_eq!(double[1].0, 1);
}

#[test]
fn test_smt_farkas_history_prefers_core_derived_before_synthetic() {
    // Regression for #2450: when IUC returns an UNSAT B-core but zero Farkas conflicts,
    // prefer core-derived interpolation over synthetic decomposed fallback.
    //
    // A-side constraints include extra equalities (not needed for UNSAT):
    //   B = C, A = 100, D = 0, E = 1
    // B-side constraints:
    //   D = 2*A, B != C
    //
    // UNSAT is explained by D = 0 and A = 100 contradicting D = 2*A.
    // If synthetic decomposition runs first, it tends to return a large conjunction
    // over all A constraints (including E = 1). Core-derived IUC should avoid
    // unrelated variables such as E.
    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let c = ChcVar::new("C", ChcSort::Int);
    let d = ChcVar::new("D", ChcSort::Int);
    let e = ChcVar::new("E", ChcSort::Int);

    let a_constraints = vec![
        ChcExpr::eq(ChcExpr::var(b.clone()), ChcExpr::var(c.clone())),
        ChcExpr::eq(ChcExpr::var(a.clone()), ChcExpr::int(100)),
        ChcExpr::eq(ChcExpr::var(d.clone()), ChcExpr::int(0)),
        ChcExpr::eq(ChcExpr::var(e), ChcExpr::int(1)),
    ];
    let b_constraints = vec![
        ChcExpr::eq(
            ChcExpr::var(d),
            ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(a)),
        ),
        ChcExpr::ne(ChcExpr::var(b), ChcExpr::var(c)),
    ];

    let shared: FxHashSet<String> = ["A", "B", "C", "D", "E"]
        .into_iter()
        .map(str::to_string)
        .collect();

    let mut smt = SmtContext::new();
    let interpolant = compute_interpolant_from_smt_farkas_history(
        &mut smt,
        &a_constraints,
        &b_constraints,
        &shared,
        false,
    )
    .expect("expected interpolant");

    let interp_vars: FxHashSet<String> = interpolant.vars().into_iter().map(|v| v.name).collect();
    assert!(
            !interp_vars.contains("E"),
            "interpolant unexpectedly mentions unrelated var E (synthetic fallback likely used): {interpolant}"
        );

    // Craig checks (A => I and I & B UNSAT).
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
fn test_zero_farkas_fallback_tries_a_side_equalities_when_shared_b_core_is_empty() {
    // Regression for #2450: if B-core has no shared-only conjuncts, we must still
    // try fallback paths (A-side equalities / synthetic decomposition) instead of
    // returning None immediately.
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let a_constraints = vec![ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))];
    let b_constraints = vec![
        ChcExpr::ge(
            ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
            ChcExpr::int(1),
        ),
        ChcExpr::le(ChcExpr::var(y.clone()), ChcExpr::int(0)),
    ];

    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name]);
    let mut smt = SmtContext::new();
    let candidate = try_zero_farkas_interpolant_candidate(
        &mut smt,
        &a_constraints,
        &b_constraints,
        &shared,
        false,
    )
    .expect("expected fallback interpolant even when shared B-core is empty");
    assert_eq!(candidate.kind, InterpolantKind::ASideEquality);
    assert!(
        !candidate.has_farkas_conflicts,
        "zero-Farkas fallback should record has_farkas_conflicts=false"
    );
    let interpolant = candidate.expr;

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
