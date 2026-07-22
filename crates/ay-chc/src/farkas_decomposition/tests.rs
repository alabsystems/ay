// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used)]
use super::matrix::{
    ensure_non_negative_decomposition, gaussian_elimination, get_alphas, get_null_basis,
    get_pivot_cols_bitmap, is_decomposition, matrix_nullity, to_reduced_row_echelon_form, Matrix,
};
use super::*;
use crate::farkas::parse_linear_constraint;
use crate::proof_interpolation::strengthen_strict_lia_constraint;
use crate::smt::{SmtContext, SmtResult};
use crate::{ChcSort, ChcVar};

#[test]
fn test_decomposed_farkas_matrix_ops_null_basis() {
    let mut matrix = vec![vec![
        Rational64::from_integer(2),
        Rational64::from_integer(-1),
        Rational64::from_integer(1),
    ]];

    gaussian_elimination(&mut matrix);
    assert_eq!(matrix_nullity(&matrix), 2);

    to_reduced_row_echelon_form(&mut matrix);
    let pivot_cols = get_pivot_cols_bitmap(&matrix);
    assert_eq!(pivot_cols, vec![true, false, false]);

    let basis = get_null_basis(&matrix);
    assert_eq!(basis.len(), 2);

    for base_vec in basis {
        let dot = matrix[0]
            .iter()
            .zip(base_vec.iter())
            .fold(Rational64::from_integer(0), |acc, (a, b)| acc + (*a * *b));
        assert_eq!(dot, Rational64::from_integer(0));
    }
}

#[test]
fn test_ensure_non_negative_decomposition_adjusts_basis() {
    let mut basis = vec![vec![
        Rational64::from_integer(-1),
        Rational64::from_integer(1),
        Rational64::from_integer(0),
    ]];
    let mut coordinates = vec![Rational64::from_integer(1)];
    let original = vec![
        Rational64::from_integer(2),
        Rational64::from_integer(1),
        Rational64::from_integer(1),
    ];

    assert!(ensure_non_negative_decomposition(
        &mut basis,
        &mut coordinates,
        &original
    ));
    assert!(
        basis[0].iter().all(|c| *c >= Rational64::from_integer(0)),
        "basis should be non-negative after adjustment: {:?}",
        basis[0]
    );
    assert!(coordinates[0] > Rational64::from_integer(0));
}

#[test]
fn test_decomposed_farkas_interpolant_satisfies_craig_properties() {
    fn is_unsat(result: &SmtResult) -> bool {
        matches!(
            result,
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        )
    }

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // A constraints:
    //   x <= 0
    //   y - x <= 0
    //   x - y <= 1
    // Together they imply y <= 0.
    let a_constraints = vec![
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::le(
            ChcExpr::sub(ChcExpr::var(y.clone()), ChcExpr::var(x.clone())),
            ChcExpr::int(0),
        ),
        ChcExpr::le(
            ChcExpr::sub(ChcExpr::var(x), ChcExpr::var(y.clone())),
            ChcExpr::int(1),
        ),
    ];

    let mut linear: Vec<LinearConstraint> = Vec::new();
    for expr in &a_constraints {
        let parsed = parse_linear_constraint(expr).expect("expected linear constraint");
        linear.push(strengthen_strict_lia_constraint(parsed));
    }

    // Coefficients correspond to local-variable matrix [1, -1, 1] over x.
    // Nullity is 2, enabling decomposed interpolant generation.
    let coeffs = vec![
        Rational64::from_integer(1),
        Rational64::from_integer(1),
        Rational64::from_integer(0),
    ];
    let shared: FxHashSet<String> = FxHashSet::from_iter([y.name.clone()]);

    let interpolant = decomposed_farkas_interpolant(&linear, &coeffs, &shared)
        .expect("expected decomposed interpolant");
    let interpolant_vars: FxHashSet<String> =
        interpolant.vars().into_iter().map(|v| v.name).collect();
    assert!(
        interpolant_vars.iter().all(|v| shared.contains(v)),
        "interpolant mentions non-shared vars: {interpolant}"
    );

    let a = ChcExpr::and_all(a_constraints);
    let b = ChcExpr::ge(ChcExpr::var(y), ChcExpr::int(1));

    let mut smt = SmtContext::new();
    let a_implies_i = ChcExpr::and(a, ChcExpr::not(interpolant.clone()));
    assert!(is_unsat(&smt.check_sat(&a_implies_i)), "A does not imply I");

    smt.reset();
    let i_and_b = ChcExpr::and(interpolant, b);
    assert!(is_unsat(&smt.check_sat(&i_and_b)), "I does not block B");
}

#[test]
fn test_decomposition_identity_holds_after_non_negative_repair() {
    // The decomposition identity holds when the weight vector lies in the null
    // space of the local-variable coefficient matrix. This mirrors real usage:
    // Farkas coefficients satisfy the constraint matrix, so local vars cancel.
    //
    // Local-var matrix M = [[1, -1, 1]] (one local var x, three constraints).
    // Null space (after RREF) has basis vectors for free cols 1, 2.
    // Weights must satisfy M*w = 0: w[0] - w[1] + w[2] = 0.
    // Choose w = [1, 2, 1]: 1 - 2 + 1 = 0. ✓
    let mut matrix = vec![vec![
        Rational64::from_integer(1),
        Rational64::from_integer(-1),
        Rational64::from_integer(1),
    ]];
    gaussian_elimination(&mut matrix);
    to_reduced_row_echelon_form(&mut matrix);

    let original_weights = vec![
        Rational64::from_integer(1),
        Rational64::from_integer(2),
        Rational64::from_integer(1),
    ];
    let pivot_cols = get_pivot_cols_bitmap(&matrix);
    let mut basis = get_null_basis(&matrix);
    let mut alphas = get_alphas(&original_weights, &pivot_cols);

    // Checkpoint 1: identity before repair
    assert!(
        is_decomposition(&basis, &alphas, &original_weights),
        "identity must hold after alpha extraction"
    );

    // Repair
    let ok = ensure_non_negative_decomposition(&mut basis, &mut alphas, &original_weights);
    assert!(ok, "non-negative repair should succeed");

    // Checkpoint 2: identity after repair
    assert!(
        is_decomposition(&basis, &alphas, &original_weights),
        "identity must hold after non-negative repair"
    );
}

#[test]
fn test_nullity_one_falls_back_to_standard_sum() {
    // When the local-variable coefficient matrix has nullity <= 1,
    // decomposed_farkas_interpolant should use the standard weighted sum
    // (no basis decomposition).
    //
    // Setup: 2 constraints with 1 local var, nullity = 1 (not > 1).
    //   x + y <= 5   (x is local, y is shared)
    //   x - y <= 3   (x is local, y is shared)
    // With weights [1, 1], standard sum = 2*x <= 8, still has local x.
    // With shared = {y}, the standard sum after elimination should produce
    // something or return None if the sum still mentions locals.
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let c1 = ChcExpr::le(
        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
        ChcExpr::int(5),
    );
    let c2 = ChcExpr::le(
        ChcExpr::sub(ChcExpr::var(x), ChcExpr::var(y.clone())),
        ChcExpr::int(3),
    );

    let mut linear = Vec::new();
    for expr in [&c1, &c2] {
        if let Some(lc) = parse_linear_constraint(expr) {
            linear.push(strengthen_strict_lia_constraint(lc));
        }
    }
    assert_eq!(linear.len(), 2);

    let weights = vec![Rational64::from_integer(1), Rational64::from_integer(1)];
    let shared: FxHashSet<String> = FxHashSet::from_iter([y.name]);

    // The local-variable matrix is [[1], [1]] for x, rank=1, nullity=cols-rank=2-1=1.
    // So this should take the nullity<=1 path (standard weighted sum).
    // The sum 2*x <= 8 mentions local x, so final shared-var filtering rejects it.
    let result = decomposed_farkas_interpolant(&linear, &weights, &shared);
    assert!(
        result.is_none(),
        "nullity<=1 fallback should be rejected when standard sum keeps local vars"
    );
}

#[test]
fn test_nullity_one_produces_shared_only_interpolant() {
    // Positive companion to test_nullity_one_falls_back_to_standard_sum.
    // When the standard weighted sum eliminates local variables, the
    // nullity<=1 path should return Some(interpolant) with shared vars only.
    //
    // Setup: 2 constraints with 1 local var x, nullity = 1:
    //   x + y <= 5   (x local, y shared)
    //  -x + y <= 3   (x local, y shared)
    // With weights [1, 1], sum = 2*y <= 8, which only mentions shared y.
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let c1 = ChcExpr::le(
        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
        ChcExpr::int(5),
    );
    let c2 = ChcExpr::le(
        ChcExpr::add(ChcExpr::neg(ChcExpr::var(x)), ChcExpr::var(y.clone())),
        ChcExpr::int(3),
    );

    let mut linear = Vec::new();
    for expr in [&c1, &c2] {
        if let Some(lc) = parse_linear_constraint(expr) {
            linear.push(strengthen_strict_lia_constraint(lc));
        }
    }
    assert_eq!(linear.len(), 2);

    let weights = vec![Rational64::from_integer(1), Rational64::from_integer(1)];
    let shared: FxHashSet<String> = FxHashSet::from_iter([y.name]);

    let result = decomposed_farkas_interpolant(&linear, &weights, &shared);
    assert!(
        result.is_some(),
        "nullity<=1 with shared-only sum should produce an interpolant"
    );
    // Verify the interpolant mentions at least one variable and only shared ones.
    let interp = result.unwrap();
    let vars = interp.vars();
    assert!(
        !vars.is_empty(),
        "interpolant must mention at least one shared variable (not a trivial constant)"
    );
    assert!(
        vars.iter().all(|v| shared.contains(&v.name)),
        "interpolant should only contain shared variables, got: {:?}",
        vars.iter().map(|v| &v.name).collect::<Vec<_>>()
    );
}

#[test]
fn test_gaussian_elimination_consistent_row_lengths() {
    // Verify gaussian_elimination preserves consistent row lengths
    let mut matrix = vec![
        vec![
            Rational64::from_integer(1),
            Rational64::from_integer(2),
            Rational64::from_integer(3),
        ],
        vec![
            Rational64::from_integer(4),
            Rational64::from_integer(5),
            Rational64::from_integer(6),
        ],
    ];
    let cols = matrix[0].len();
    gaussian_elimination(&mut matrix);
    assert!(
        matrix.iter().all(|row| row.len() == cols),
        "row lengths must remain consistent after elimination"
    );
}

#[test]
fn test_get_alphas_length_invariant() {
    // get_alphas must produce one alpha per non-pivot column
    let coeffs = vec![
        Rational64::from_integer(3),
        Rational64::from_integer(5),
        Rational64::from_integer(7),
    ];
    let pivot_cols = vec![true, false, false];
    let alphas = get_alphas(&coeffs, &pivot_cols);
    let expected_free = pivot_cols.iter().filter(|&&is_pivot| !is_pivot).count();
    assert_eq!(
        alphas.len(),
        expected_free,
        "alphas count must equal number of free (non-pivot) columns"
    );
    assert_eq!(alphas[0], Rational64::from_integer(5));
    assert_eq!(alphas[1], Rational64::from_integer(7));
}

#[test]
fn test_empty_matrix_operations_are_no_ops() {
    // Empty matrix should be handled without panic
    let mut empty: Matrix = vec![];
    gaussian_elimination(&mut empty);
    assert!(empty.is_empty());

    to_reduced_row_echelon_form(&mut empty);
    assert!(empty.is_empty());

    assert_eq!(matrix_nullity(&empty), 0);

    // Single empty row
    let mut single_empty: Matrix = vec![vec![]];
    gaussian_elimination(&mut single_empty);
    to_reduced_row_echelon_form(&mut single_empty);
}

#[test]
fn test_ensure_non_negative_fails_on_impossible_repair() {
    // When a basis vector has a negative entry that cannot be repaired
    // (coordinate is zero and original weight doesn't help), return false.
    let mut basis = vec![vec![
        Rational64::from_integer(-1),
        Rational64::from_integer(0),
    ]];
    let mut coordinates = vec![Rational64::from_integer(0)];
    let original = vec![Rational64::from_integer(0), Rational64::from_integer(0)];

    let ok = ensure_non_negative_decomposition(&mut basis, &mut coordinates, &original);
    assert!(!ok, "repair must fail when denominator is non-positive");
}

#[test]
fn test_shared_only_constraints_become_standalone_conjuncts() {
    // Constraints that mention only shared variables should appear directly
    // in the interpolant without matrix decomposition.
    let y = ChcVar::new("y", ChcSort::Int);

    // y <= 5 (shared-only)
    let c1 = ChcExpr::le(ChcExpr::var(y.clone()), ChcExpr::int(5));
    let lc = parse_linear_constraint(&c1).unwrap();
    let linear = vec![strengthen_strict_lia_constraint(lc)];
    let weights = vec![Rational64::from_integer(1)];
    let shared: FxHashSet<String> = FxHashSet::from_iter([y.name]);

    let result = decomposed_farkas_interpolant(&linear, &weights, &shared);
    assert!(
        result.is_some(),
        "shared-only constraint should produce interpolant"
    );
}

#[test]
fn test_invalid_alpha_decomposition_falls_back_without_panic() {
    // Matrix for local var x has coefficients [1, -1, 1], so nullity = 2 and
    // decomposition branch is taken. Weights [1, 1, 1] violate x-cancellation
    // (1 - 1 + 1 != 0), so alpha extraction is not a valid decomposition.
    // This must not panic in debug builds.
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let constraints = vec![
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::le(
            ChcExpr::sub(ChcExpr::var(y.clone()), ChcExpr::var(x.clone())),
            ChcExpr::int(0),
        ),
        ChcExpr::le(
            ChcExpr::sub(ChcExpr::var(x), ChcExpr::var(y.clone())),
            ChcExpr::int(1),
        ),
    ];
    let mut linear = Vec::new();
    for expr in &constraints {
        let parsed = parse_linear_constraint(expr).expect("expected linear constraint");
        linear.push(strengthen_strict_lia_constraint(parsed));
    }
    let invalid_weights = vec![
        Rational64::from_integer(1),
        Rational64::from_integer(1),
        Rational64::from_integer(1),
    ];
    let shared: FxHashSet<String> = FxHashSet::from_iter([y.name]);

    let result = decomposed_farkas_interpolant(&linear, &invalid_weights, &shared);
    assert!(
        result.is_none(),
        "invalid decomposition should fall back and be rejected as non-shared"
    );
}

#[test]
fn test_invalid_decomposition_preserves_standalone_shared_parts() {
    fn is_unsat(result: &SmtResult) -> bool {
        matches!(
            result,
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        )
    }

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // First constraint is shared-only and should survive.
    // Remaining constraints force a nullity>1 decomposition path with invalid
    // local-cancellation weights, so fallback standard sum keeps local x.
    let constraints = vec![
        ChcExpr::le(ChcExpr::var(y.clone()), ChcExpr::int(5)),
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::le(
            ChcExpr::sub(ChcExpr::var(y.clone()), ChcExpr::var(x.clone())),
            ChcExpr::int(0),
        ),
        ChcExpr::le(
            ChcExpr::sub(ChcExpr::var(x), ChcExpr::var(y.clone())),
            ChcExpr::int(1),
        ),
    ];
    let mut linear = Vec::new();
    for expr in &constraints {
        let parsed = parse_linear_constraint(expr).expect("expected linear constraint");
        linear.push(strengthen_strict_lia_constraint(parsed));
    }
    let weights = vec![
        Rational64::from_integer(1),
        Rational64::from_integer(1),
        Rational64::from_integer(1),
        Rational64::from_integer(1),
    ];
    let shared: FxHashSet<String> = FxHashSet::from_iter([y.name.clone()]);

    let interpolant = decomposed_farkas_interpolant(&linear, &weights, &shared)
        .expect("standalone shared part should not be dropped");
    let vars: FxHashSet<String> = interpolant.vars().into_iter().map(|v| v.name).collect();
    assert!(
        vars.iter().all(|v| shared.contains(v)),
        "interpolant must only mention shared vars: {interpolant}"
    );

    let mut smt = SmtContext::new();
    let violates_shared_bound = ChcExpr::and(
        interpolant.clone(),
        ChcExpr::ge(ChcExpr::var(y), ChcExpr::int(6)),
    );
    assert!(
        is_unsat(&smt.check_sat(&violates_shared_bound)),
        "standalone shared conjunct y <= 5 should be preserved: {interpolant}"
    );
}

#[test]
fn test_decomposition_stats_increment_on_non_trivial_basis_success() {
    let before = decomp_stats_snapshot();

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // Three constraints involving local var x and shared var y, all with
    // nonzero weight. The local-var coefficient matrix for x is [1, 1, -1]
    // (1×3), giving rank=1 and nullity=2 > 1 — the non-trivial-basis path.
    //
    // Null-space basis: {(1,0,1), (0,1,1)} with alphas (1,1).
    //   Basis[0] applied: (x+y≤5) + (-x≤0) = y≤5  (shared-only)
    //   Basis[1] applied: (x-y≤3) + (-x≤0) = -y≤3  (shared-only)
    let constraints = vec![
        // c0: x + y ≤ 5  (x-coeff: +1)
        ChcExpr::le(
            ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
            ChcExpr::int(5),
        ),
        // c1: x - y ≤ 3  (x-coeff: +1)
        ChcExpr::le(
            ChcExpr::sub(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
            ChcExpr::int(3),
        ),
        // c2: -x ≤ 0  (x-coeff: -1)
        ChcExpr::le(ChcExpr::neg(ChcExpr::var(x)), ChcExpr::int(0)),
    ];

    let mut linear = Vec::new();
    for expr in &constraints {
        let parsed = parse_linear_constraint(expr).expect("expected linear constraint");
        linear.push(strengthen_strict_lia_constraint(parsed));
    }

    let weights = vec![
        Rational64::from_integer(1),
        Rational64::from_integer(1),
        Rational64::from_integer(2),
    ];
    let shared: FxHashSet<String> = FxHashSet::from_iter([y.name]);

    let result = decomposed_farkas_interpolant(&linear, &weights, &shared);
    assert!(
        result.is_some(),
        "expected non-trivial decomposition success"
    );

    let after = decomp_stats_snapshot();
    assert!(
        after.opportunities > before.opportunities,
        "expected opportunities to increase (before={before:?}, after={after:?})"
    );
    assert!(
        after.non_trivial_basis > before.non_trivial_basis,
        "expected non_trivial_basis to increase (before={before:?}, after={after:?})"
    );
    assert!(
        after.decomposed > before.decomposed,
        "expected decomposed count to increase (before={before:?}, after={after:?})"
    );
}

#[test]
fn test_decomposition_stats_increment_on_standard_fallback() {
    let before = decomp_stats_snapshot();

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let c1 = ChcExpr::le(
        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
        ChcExpr::int(5),
    );
    let c2 = ChcExpr::le(
        ChcExpr::sub(ChcExpr::var(x), ChcExpr::var(y.clone())),
        ChcExpr::int(3),
    );

    let mut linear = Vec::new();
    for expr in [&c1, &c2] {
        if let Some(lc) = parse_linear_constraint(expr) {
            linear.push(strengthen_strict_lia_constraint(lc));
        }
    }

    let weights = vec![Rational64::from_integer(1), Rational64::from_integer(1)];
    let shared: FxHashSet<String> = FxHashSet::from_iter([y.name]);

    let result = decomposed_farkas_interpolant(&linear, &weights, &shared);
    assert!(
        result.is_none(),
        "nullity<=1 fallback keeps local vars and should be rejected"
    );

    let after = decomp_stats_snapshot();
    assert!(
        after.opportunities > before.opportunities,
        "expected opportunities to increase (before={before:?}, after={after:?})"
    );
    assert!(
        after.fallback_to_standard > before.fallback_to_standard,
        "expected fallback_to_standard to increase (before={before:?}, after={after:?})"
    );
}
