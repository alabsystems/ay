// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_i64_gcd_with_i64_min_no_panic() {
    // i64::MIN = -2^63; unsigned_abs gives correct u64 value
    assert_eq!(i64_gcd(i64::MIN, 4), 4);
    assert_eq!(i64_gcd(6, i64::MIN), 2);
    assert_eq!(i64_gcd(i64::MIN, i64::MIN), i64::MAX); // 2^63 clamped to i64::MAX
    assert_eq!(i64_gcd(i64::MIN, 2), 2);
}

#[test]
fn test_rational64_abs_i64_min_numer_no_panic() {
    // Rational64 with i64::MIN numerator must not panic in abs
    let r = Rational64::new_raw(i64::MIN, 1);
    let result = rational64_abs(r);
    assert!(result > Rational64::from_integer(0));
}

#[test]
fn test_try_a_side_farkas_projection_shared_vars_only() {
    // A-origin: x >= 3 (coeff=1)
    // B-origin: x <= 0 (coeff=1)
    // shared: {x}
    //
    // The A-sum with weight 1 on (x >= 3) gives x >= 3.
    // All vars are shared, so it should return directly.
    let x = ChcVar::new("x", ChcSort::Int);
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name.clone()]);

    let a_atom = TermId(200);
    let b_atom = TermId(201);

    let conflict_terms = vec![a_atom, b_atom];
    let origins = vec![Partition::A, Partition::B];
    let polarities = vec![true, true]; // both appear positive
    let coefficients = vec![Rational64::from_integer(1), Rational64::from_integer(1)];

    let mut atom_to_expr: FxHashMap<TermId, ChcExpr> = FxHashMap::default();
    atom_to_expr.insert(
        a_atom,
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(3)),
    );
    atom_to_expr.insert(
        b_atom,
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(0)),
    );

    let a_atoms_in_a: FxHashSet<TermId> = FxHashSet::from_iter([a_atom]);

    let result = try_a_side_farkas_projection(
        &conflict_terms,
        &origins,
        &polarities,
        &coefficients,
        &atom_to_expr,
        &shared,
        &a_atoms_in_a,
    );

    assert!(
        result.is_some(),
        "expected A-side Farkas projection to produce a candidate"
    );
    let interp = result.unwrap();

    // Verify it uses only shared vars
    let vars = interp.vars();
    for v in &vars {
        assert!(
            shared.contains(&v.name),
            "interpolant mentions non-shared var {}",
            v.name
        );
    }

    // Verify soundness: A |= I (A ∧ ¬I should be UNSAT)
    let a_expr = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(3));
    let a_and_not_i = ChcExpr::and(a_expr, ChcExpr::not(interp.clone()));
    let mut smt = SmtContext::new();
    assert!(
        matches!(
            smt.check_sat(&a_and_not_i),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "A does not imply interpolant: {interp}"
    );
}

#[test]
fn test_try_a_side_farkas_projection_returns_none_for_b_only_conflict() {
    // All conflict literals are B-origin: should return None.
    let x = ChcVar::new("x", ChcSort::Int);
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name.clone()]);

    let b1 = TermId(300);
    let b2 = TermId(301);

    let conflict_terms = vec![b1, b2];
    let origins = vec![Partition::B, Partition::B];
    let polarities = vec![true, true];
    let coefficients = vec![Rational64::from_integer(1), Rational64::from_integer(1)];

    let mut atom_to_expr: FxHashMap<TermId, ChcExpr> = FxHashMap::default();
    atom_to_expr.insert(b1, ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(5)));
    atom_to_expr.insert(b2, ChcExpr::le(ChcExpr::var(x), ChcExpr::int(0)));

    let a_atoms_in_a: FxHashSet<TermId> = FxHashSet::default();

    let result = try_a_side_farkas_projection(
        &conflict_terms,
        &origins,
        &polarities,
        &coefficients,
        &atom_to_expr,
        &shared,
        &a_atoms_in_a,
    );

    assert!(
        result.is_none(),
        "B-only conflict should not produce A-side Farkas projection"
    );
}

#[test]
fn test_try_a_side_farkas_projection_ab_partition_uses_a_atoms() {
    // AB-origin literal that is in a_atoms_in_a should be treated as A-side.
    // This tests the IUC origin fallback logic introduced in W5's fix.
    let x = ChcVar::new("x", ChcSort::Int);
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name.clone()]);

    let ab_atom = TermId(400);
    let b_atom = TermId(401);

    let conflict_terms = vec![ab_atom, b_atom];
    let origins = vec![Partition::AB, Partition::B];
    let polarities = vec![true, true];
    let coefficients = vec![Rational64::from_integer(1), Rational64::from_integer(1)];

    let mut atom_to_expr: FxHashMap<TermId, ChcExpr> = FxHashMap::default();
    atom_to_expr.insert(
        ab_atom,
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(7)),
    );
    atom_to_expr.insert(b_atom, ChcExpr::le(ChcExpr::var(x), ChcExpr::int(0)));

    // Mark the AB atom as in the A-side term set
    let a_atoms_in_a: FxHashSet<TermId> = FxHashSet::from_iter([ab_atom]);

    let result = try_a_side_farkas_projection(
        &conflict_terms,
        &origins,
        &polarities,
        &coefficients,
        &atom_to_expr,
        &shared,
        &a_atoms_in_a,
    );

    assert!(
        result.is_some(),
        "AB-origin atom in a_atoms_in_a should be treated as A-side"
    );
    let interp = result.unwrap();

    // Verify shared-var-only
    let vars = interp.vars();
    for v in &vars {
        assert!(
            shared.contains(&v.name),
            "interpolant mentions non-shared var {}",
            v.name
        );
    }
}

// ================================================================
// Edge case tests for i64_gcd / i64_lcm arithmetic
// ================================================================

#[test]
fn test_i64_gcd_normal_cases() {
    assert_eq!(i64_gcd(12, 8), 4);
    assert_eq!(i64_gcd(7, 13), 1);
    assert_eq!(i64_gcd(0, 5), 5);
    assert_eq!(i64_gcd(5, 0), 5);
    assert_eq!(i64_gcd(0, 0), 0);
    assert_eq!(i64_gcd(-12, 8), 4);
    assert_eq!(i64_gcd(12, -8), 4);
    assert_eq!(i64_gcd(-12, -8), 4);
}

#[test]
fn test_i64_lcm_normal_cases() {
    assert_eq!(i64_lcm(4, 6), Some(12));
    assert_eq!(i64_lcm(0, 5), Some(0));
    assert_eq!(i64_lcm(5, 0), Some(0));
    assert_eq!(i64_lcm(1, 1), Some(1));
}

#[test]
fn test_i64_lcm_overflow_returns_none() {
    // Large values should return None on overflow
    assert_eq!(i64_lcm(i64::MAX, i64::MAX - 1), None);
}

// ================================================================
// verify_craig_properties shared-variable locality check
// ================================================================

/// verify_craig_properties now checks all three Craig conditions including
/// shared-variable locality (condition 3).
#[test]
fn test_verify_craig_properties_rejects_non_shared_var_interpolant() {
    // A: x <= 5, y = 3  (y is A-only)
    // B: x >= 10         (only mentions x)
    // shared: {x}
    // candidate I: (x <= 5 AND y = 3)  -- mentions y which is NOT shared
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let a_conj = ChcExpr::and(
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5)),
        ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(3)),
    );
    let b_conj = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10));
    let candidate = ChcExpr::and(
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5)),
        ChcExpr::eq(ChcExpr::var(y), ChcExpr::int(3)),
    );

    // Only x is shared; y is not
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name]);
    let mut smt = SmtContext::new();
    // verify_craig_properties now rejects because candidate mentions non-shared y
    let result = verify_craig_properties(
        &candidate,
        &a_conj,
        &b_conj,
        &shared,
        &mut smt,
        "reject-test",
    );
    assert!(
        !result,
        "verify_craig_properties must reject interpolant with non-shared variable y"
    );
}

/// verify_craig_properties accepts a valid interpolant when all vars are shared.
#[test]
fn test_verify_craig_properties_accepts_shared_var_interpolant() {
    let x = ChcVar::new("x", ChcSort::Int);

    let a_conj = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let b_conj = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10));
    let candidate = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5));

    // x is shared
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name]);
    let mut smt = SmtContext::new();
    let result = verify_craig_properties(
        &candidate,
        &a_conj,
        &b_conj,
        &shared,
        &mut smt,
        "accept-test",
    );
    assert!(
        result,
        "verify_craig_properties must accept interpolant with only shared variables"
    );
}

// --- is_linear_atom / is_linear_term tests (#3062) ---

#[test]
fn is_linear_atom_accepts_simple_comparison() {
    // x <= 5
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let expr = ChcExpr::le(x, ChcExpr::int(5));
    assert!(is_linear_atom(&expr));
}

#[test]
fn is_linear_atom_accepts_linear_mul() {
    // 2*x >= 0  (constant * variable is linear)
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let expr = ChcExpr::ge(ChcExpr::mul(ChcExpr::int(2), x), ChcExpr::int(0));
    assert!(is_linear_atom(&expr));
}

#[test]
fn is_linear_atom_rejects_nonlinear_mul() {
    // x*x >= 0  (variable * variable is non-linear)
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let expr = ChcExpr::ge(ChcExpr::mul(x.clone(), x), ChcExpr::int(0));
    assert!(!is_linear_atom(&expr));
}

#[test]
fn is_linear_atom_rejects_nested_nonlinear() {
    // x + y*y <= 10  (y*y nested in Add)
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    let expr = ChcExpr::le(
        ChcExpr::add(x, ChcExpr::mul(y.clone(), y)),
        ChcExpr::int(10),
    );
    assert!(!is_linear_atom(&expr));
}

#[test]
fn is_linear_atom_rejects_div() {
    // x / y <= 1  (Div is non-linear for Farkas)
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    let expr = ChcExpr::le(
        ChcExpr::Op(ChcOp::Div, vec![Arc::new(x), Arc::new(y)]),
        ChcExpr::int(1),
    );
    assert!(!is_linear_atom(&expr));
}

#[test]
fn is_linear_atom_rejects_mod() {
    // x mod 2 = 0  (Mod is non-linear for Farkas)
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let expr = ChcExpr::eq(
        ChcExpr::Op(ChcOp::Mod, vec![Arc::new(x), Arc::new(ChcExpr::int(2))]),
        ChcExpr::int(0),
    );
    assert!(!is_linear_atom(&expr));
}

#[test]
fn is_linear_atom_accepts_negation_of_linear() {
    // NOT(x <= 5) is a linear atom
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let expr = ChcExpr::not(ChcExpr::le(x, ChcExpr::int(5)));
    assert!(is_linear_atom(&expr));
}

#[test]
fn is_linear_atom_rejects_negation_of_nonlinear() {
    // NOT(x*x >= 0) should be rejected
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let expr = ChcExpr::not(ChcExpr::ge(ChcExpr::mul(x.clone(), x), ChcExpr::int(0)));
    assert!(!is_linear_atom(&expr));
}

#[test]
fn is_linear_atom_accepts_add_sub_chain() {
    // x + y - 3 <= z  (all linear operations)
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    let z = ChcExpr::var(ChcVar::new("z", ChcSort::Int));
    let expr = ChcExpr::le(ChcExpr::sub(ChcExpr::add(x, y), ChcExpr::int(3)), z);
    assert!(is_linear_atom(&expr));
}

#[test]
fn farkas_returns_none_for_nonlinear_input() {
    // A: x*x >= 0 (non-linear)
    // B: x <= -1
    // Farkas should reject and return None
    let x = ChcVar::new("x", ChcSort::Int);
    let a = vec![ChcExpr::ge(
        ChcExpr::mul(ChcExpr::var(x.clone()), ChcExpr::var(x.clone())),
        ChcExpr::int(0),
    )];
    let b = vec![ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(-1))];
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name]);

    let mut smt = SmtContext::new();
    let result = compute_interpolant_from_lia_farkas(&mut smt, &a, &b, &shared);
    assert!(
        result.is_none(),
        "Farkas must return None for non-linear input, got: {result:?}"
    );
}
