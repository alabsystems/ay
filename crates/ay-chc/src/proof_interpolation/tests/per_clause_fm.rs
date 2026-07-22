// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_per_clause_interpolation_basic() {
    // Test per-clause interpolation directly.
    //
    // Setup: B contains x >= 10 (shared var, B-origin)
    //
    // Per-clause should collect B-origin + shared-var literals and negate them.
    // The negation of (x >= 10) is (x < 10), which normalizes to (x <= 9).

    let x = ChcVar::new("x", ChcSort::Int);
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name.clone()]);

    // Use a dummy TermId - we only need it as a key for the atom_to_expr map
    let ge_atom = TermId(42);

    let conflict_terms = vec![ge_atom];
    let origins = vec![Partition::B];
    let polarities = vec![true]; // x >= 10 appears positive in conflict

    let mut atom_to_expr: FxHashMap<TermId, ChcExpr> = FxHashMap::default();
    atom_to_expr.insert(
        ge_atom,
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10)),
    );

    // Call per-clause interpolation
    let candidate = try_per_clause_interpolation(
        &conflict_terms,
        &origins,
        &polarities,
        &atom_to_expr,
        &shared,
    );

    // Should produce an interpolant (negation of x >= 10)
    assert!(
        candidate.is_some(),
        "expected per-clause interpolation to produce a candidate"
    );

    let interp = candidate.unwrap();
    safe_eprintln!("per-clause interpolant: {}", interp);

    // Verify it mentions only shared vars
    let vars = interp.vars();
    for v in &vars {
        assert!(
            shared.contains(&v.name),
            "interpolant mentions non-shared var {}",
            v.name
        );
    }

    // Verify soundness: I ∧ B should be UNSAT
    let mut smt = SmtContext::new();
    let b = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10));
    let i_and_b = ChcExpr::and(interp, b);
    let result = smt.check_sat(&i_and_b);
    assert!(
        matches!(
            result,
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "I ∧ B should be UNSAT, got {result:?}"
    );
}

#[test]
fn test_per_clause_interpolation_multiple_literals() {
    // Test per-clause with multiple B-origin literals.
    //
    // B: x >= 10 AND y >= 5 (both shared vars, B-origin)
    //
    // Per-clause should produce (x < 10) OR (y < 5) as the interpolant.

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name.clone(), y.name.clone()]);

    // Use dummy TermIds
    let ge_x = TermId(100);
    let ge_y = TermId(101);

    let conflict_terms = vec![ge_x, ge_y];
    let origins = vec![Partition::B, Partition::B];
    let polarities = vec![true, true];

    let mut atom_to_expr: FxHashMap<TermId, ChcExpr> = FxHashMap::default();
    atom_to_expr.insert(ge_x, ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10)));
    atom_to_expr.insert(ge_y, ChcExpr::ge(ChcExpr::var(y), ChcExpr::int(5)));

    let candidate = try_per_clause_interpolation(
        &conflict_terms,
        &origins,
        &polarities,
        &atom_to_expr,
        &shared,
    );

    assert!(
        candidate.is_some(),
        "expected per-clause interpolation to produce a candidate"
    );

    let interp = candidate.unwrap();
    safe_eprintln!("per-clause interpolant (multi): {}", interp);

    // Should be a disjunction (ChcExpr::Op with Or)
    assert!(
        matches!(interp, ChcExpr::Op(ChcOp::Or, _)),
        "expected disjunction, got: {interp}"
    );
}

#[test]
fn test_fourier_motzkin_elimination_basic() {
    // Test Fourier-Motzkin bound elimination.
    //
    // Conjuncts: y >= x, y <= 10  (y is non-shared, x is shared)
    // After eliminating y: x <= 10
    //
    // y >= x means: -y + x <= 0  (so y appears with -1, lower bound)
    // y <= 10 means: y <= 10     (so y appears with +1, upper bound)
    // Combining: x <= 10

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let conjuncts = vec![
        ChcExpr::ge(ChcExpr::var(y.clone()), ChcExpr::var(x.clone())),
        ChcExpr::le(ChcExpr::var(y.clone()), ChcExpr::int(10)),
    ];

    let vars_to_eliminate: FxHashSet<String> = FxHashSet::from_iter([y.name.clone()]);
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name.clone()]);

    let vars_to_eliminate_names: FxHashSet<&str> =
        vars_to_eliminate.iter().map(String::as_str).collect();
    let result = try_fourier_motzkin_elimination(&conjuncts, &vars_to_eliminate_names);

    assert!(
        result.is_some(),
        "F-M elimination should succeed for basic bounds"
    );

    let projected = result.unwrap();
    safe_eprintln!("F-M projected: {}", projected);

    // Verify projected mentions only x
    let vars = projected.vars();
    for v in &vars {
        assert!(
            shared.contains(&v.name),
            "projected should mention only shared vars, found {}",
            v.name
        );
    }

    // Soundness: the original implies the projected
    // y >= x AND y <= 10 implies x <= 10
    let mut smt = SmtContext::new();
    let original = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(y.clone()), ChcExpr::var(x)),
        ChcExpr::le(ChcExpr::var(y), ChcExpr::int(10)),
    );
    let implication_check = ChcExpr::and(original, ChcExpr::not(projected));
    let result = smt.check_sat(&implication_check);
    assert!(
        matches!(
            result,
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "original should imply projected"
    );
}

#[test]
fn test_fourier_motzkin_unbounded() {
    // Test unbounded variable elimination.
    //
    // Conjuncts: y >= 0, x <= 5  (y is non-shared but only has lower bound)
    // After eliminating y: x <= 5 (y's constraint drops)

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let conjuncts = vec![
        ChcExpr::ge(ChcExpr::var(y.clone()), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5)),
    ];

    let vars_to_eliminate: FxHashSet<String> = FxHashSet::from_iter([y.name]);
    let vars_to_eliminate_names: FxHashSet<&str> =
        vars_to_eliminate.iter().map(String::as_str).collect();
    let result = try_fourier_motzkin_elimination(&conjuncts, &vars_to_eliminate_names);

    assert!(
        result.is_some(),
        "F-M elimination should succeed for unbounded vars"
    );

    let projected = result.unwrap();
    safe_eprintln!("F-M projected (unbounded): {}", projected);

    // Should be x <= 5
    let vars = projected.vars();
    assert!(
        vars.iter().all(|v| v.name == "x"),
        "projected should only mention x"
    );
}

#[test]
fn test_fourier_motzkin_nonlinear_with_ite() {
    // Regression test for #985: F-M should skip elimination when variable
    // appears in a non-linear constraint (like ITE).
    //
    // ITE(true, y, 0) >= 0 - this won't parse as linear constraint

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // ITE(true, y, 0) >= 0 - non-linear, contains y
    let ite_expr = ChcExpr::ge(
        ChcExpr::ite(
            ChcExpr::Bool(true),
            ChcExpr::var(y.clone()),
            ChcExpr::int(0),
        ),
        ChcExpr::int(0),
    );

    let conjuncts = vec![
        ite_expr,
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5)),
    ];

    let vars_to_eliminate: FxHashSet<String> = FxHashSet::from_iter([y.name]);
    let vars_to_eliminate_names: FxHashSet<&str> =
        vars_to_eliminate.iter().map(String::as_str).collect();
    let result = try_fourier_motzkin_elimination(&conjuncts, &vars_to_eliminate_names);

    // F-M should either:
    // 1. Return None (y couldn't be eliminated)
    // 2. Return result that does NOT contain y
    if let Some(projected) = result {
        let vars = projected.vars();
        assert!(
            !vars.iter().any(|v| v.name == "y"),
            "projected should NOT contain y after elimination, but got: {projected}"
        );
    }
    // None is acceptable - means y couldn't be eliminated due to non-linear constraint
}

/// Test that MAX_ELIMINATIONS guard limits Fourier-Motzkin iterations.
///
/// When more than 5 variables need elimination, the algorithm should stop
/// after MAX_ELIMINATIONS to prevent exponential blowup.
#[test]
fn test_fourier_motzkin_max_eliminations_guard() {
    // Create constraints with 10 variables to eliminate, exceeding MAX_ELIMINATIONS=5.
    // All variables are non-shared and have simple bounds.
    let x = ChcVar::new("x", ChcSort::Int);
    let v0 = ChcVar::new("v0", ChcSort::Int);
    let v1 = ChcVar::new("v1", ChcSort::Int);
    let v2 = ChcVar::new("v2", ChcSort::Int);
    let v3 = ChcVar::new("v3", ChcSort::Int);
    let v4 = ChcVar::new("v4", ChcSort::Int);
    let v5 = ChcVar::new("v5", ChcSort::Int);
    let v6 = ChcVar::new("v6", ChcSort::Int);
    let v7 = ChcVar::new("v7", ChcSort::Int);
    let v8 = ChcVar::new("v8", ChcSort::Int);

    // Create chain: x <= v0 <= v1 <= ... <= v8 <= 100
    // Eliminating all v_i should give x <= 100, but after MAX_ELIMINATIONS
    // the algorithm should stop (possibly returning None or a partial result).
    let conjuncts = vec![
        // x <= v0
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::var(v0.clone())),
        // v0 <= v1
        ChcExpr::le(ChcExpr::var(v0.clone()), ChcExpr::var(v1.clone())),
        // v1 <= v2
        ChcExpr::le(ChcExpr::var(v1.clone()), ChcExpr::var(v2.clone())),
        // v2 <= v3
        ChcExpr::le(ChcExpr::var(v2.clone()), ChcExpr::var(v3.clone())),
        // v3 <= v4
        ChcExpr::le(ChcExpr::var(v3.clone()), ChcExpr::var(v4.clone())),
        // v4 <= v5
        ChcExpr::le(ChcExpr::var(v4.clone()), ChcExpr::var(v5.clone())),
        // v5 <= v6
        ChcExpr::le(ChcExpr::var(v5.clone()), ChcExpr::var(v6.clone())),
        // v6 <= v7
        ChcExpr::le(ChcExpr::var(v6.clone()), ChcExpr::var(v7.clone())),
        // v7 <= v8
        ChcExpr::le(ChcExpr::var(v7.clone()), ChcExpr::var(v8.clone())),
        // v8 <= 100
        ChcExpr::le(ChcExpr::var(v8.clone()), ChcExpr::int(100)),
    ];

    let vars_to_eliminate: FxHashSet<String> = FxHashSet::from_iter([
        v0.name, v1.name, v2.name, v3.name, v4.name, v5.name, v6.name, v7.name, v8.name,
    ]);
    let shared: FxHashSet<String> = FxHashSet::from_iter([x.name]);

    // Call the function - it should not hang and should return eventually.
    // The MAX_ELIMINATIONS=5 guard limits the number of variables eliminated.
    let vars_to_eliminate_names: FxHashSet<&str> =
        vars_to_eliminate.iter().map(String::as_str).collect();
    let result = try_fourier_motzkin_elimination(&conjuncts, &vars_to_eliminate_names);

    // The function may return None (couldn't fully eliminate all vars) or
    // Some(expr) with a partial projection. Either is acceptable as long as
    // it doesn't hang.
    //
    // If Some, verify the result doesn't contain shared vars beyond x.
    if let Some(projected) = result {
        let vars = projected.vars();
        for v in &vars {
            assert!(
                shared.contains(&v.name),
                "projected should only contain shared vars, found non-shared: {}",
                v.name
            );
        }
    }
    // If None, that's also acceptable - the guard limited iterations.
}
