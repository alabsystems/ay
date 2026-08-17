// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Farkas-decomposition statistics regressions.

use super::*;

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
