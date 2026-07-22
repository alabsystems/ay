// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_normalize_cube_flattens_and_sorts() {
    let cube = make_and(
        make_and(
            make_gt(make_var("y"), ChcExpr::Int(10)),
            make_gt(make_var("x"), ChcExpr::Int(5)),
        ),
        ChcExpr::Bool(true),
    );

    let normalized = normalize_cube(&cube);
    assert_eq!(normalized.to_string(), "(and (> x 5) (> y 10))");
}

#[test]
fn test_normalize_cube_swaps_simple_comparisons() {
    // (<= 5 x) should become (>= x 5)
    let cube = ChcExpr::Op(
        ChcOp::Le,
        vec![Arc::new(ChcExpr::Int(5)), Arc::new(make_var("x"))],
    );

    let normalized = normalize_cube(&cube);
    assert_eq!(normalized.to_string(), "(>= x 5)");
}

#[test]
fn test_extract_pattern_single_constant() {
    // x > 5
    let cube = make_gt(make_var("x"), ChcExpr::Int(5));
    let result = extract_pattern(&cube);

    assert_eq!(result.pattern_vars.len(), 1);
    assert_eq!(result.pattern_vars[0].name, "__gg_k0");
    assert_eq!(result.subst_values, vec![5]);
}

#[test]
fn test_extract_pattern_multiple_constants() {
    // x > 5 ∧ y > 10
    let cube = make_and(
        make_gt(make_var("x"), ChcExpr::Int(5)),
        make_gt(make_var("y"), ChcExpr::Int(10)),
    );
    let result = extract_pattern(&cube);

    assert_eq!(result.pattern_vars.len(), 2);
    assert_eq!(result.subst_values, vec![5, 10]);
}

#[test]
fn test_extract_pattern_duplicate_constants() {
    // x > 5 ∧ y > 5 (same constant 5 used twice)
    let cube = make_and(
        make_gt(make_var("x"), ChcExpr::Int(5)),
        make_gt(make_var("y"), ChcExpr::Int(5)),
    );
    let result = extract_pattern(&cube);

    // Each occurrence gets its own pattern variable (MVP)
    assert_eq!(result.pattern_vars.len(), 2);
    assert_eq!(result.subst_values, vec![5, 5]);
}

#[test]
fn test_extract_pattern_abstracts_constants_inside_mul() {
    // (* 2 x) > 5
    let cube = make_gt(
        ChcExpr::mul(ChcExpr::Int(2), make_var("x")),
        ChcExpr::Int(5),
    );
    let result = extract_pattern(&cube);

    assert_eq!(result.pattern_vars.len(), 2);
    assert_eq!(result.pattern_vars[0].name, "__gg_k0");
    assert_eq!(result.pattern_vars[1].name, "__gg_k1");
    assert_eq!(result.subst_values, vec![2, 5]);

    let expected_pattern = make_gt(
        ChcExpr::mul(ChcExpr::var(result.pattern_vars[0].clone()), make_var("x")),
        ChcExpr::var(result.pattern_vars[1].clone()),
    );
    assert_eq!(result.pattern.to_string(), expected_pattern.to_string());
}

#[test]
fn test_match_pattern_success() {
    // Pattern: x > __gg_k0
    let pattern_var = ChcVar::new("__gg_k0", ChcSort::Int);
    let pattern = make_gt(make_var("x"), ChcExpr::Var(pattern_var.clone()));
    let pattern_vars = vec![pattern_var];

    // Cube: x > 5
    let cube = make_gt(make_var("x"), ChcExpr::Int(5));

    let result = match_pattern(&pattern, &pattern_vars, &cube);
    assert_eq!(result, Some(vec![5]));
}

#[test]
fn test_match_pattern_semantic_equivalence_le_not_gt() {
    // Pattern: x <= __gg_k0
    let pattern_var = ChcVar::new("__gg_k0", ChcSort::Int);
    let pattern = ChcExpr::le(make_var("x"), ChcExpr::Var(pattern_var.clone()));
    let pattern_vars = vec![pattern_var];

    // Cube: !(x > 5)
    let cube = ChcExpr::not(make_gt(make_var("x"), ChcExpr::Int(5)));

    let result = match_pattern(&pattern, &pattern_vars, &cube);
    assert_eq!(result, Some(vec![5]));
}

#[test]
fn test_match_pattern_rejects_top_level_signed_match() {
    // Pattern: !(x > __gg_k0), Cube: (x > 5) should be a *signed* match only.
    // Clustering uses positive matches only.
    let pattern_var = ChcVar::new("__gg_k0", ChcSort::Int);
    let pattern = ChcExpr::not(make_gt(make_var("x"), ChcExpr::Var(pattern_var.clone())));
    let pattern_vars = vec![pattern_var];

    let cube = make_gt(make_var("x"), ChcExpr::Int(5));

    let result = match_pattern(&pattern, &pattern_vars, &cube);
    assert_eq!(result, None);
}

#[test]
fn test_match_pattern_failure_wrong_structure() {
    // Pattern: x > __gg_k0
    let pattern_var = ChcVar::new("__gg_k0", ChcSort::Int);
    let pattern = make_gt(make_var("x"), ChcExpr::Var(pattern_var.clone()));
    let pattern_vars = vec![pattern_var];

    // Cube: y > 5 (different variable)
    let cube = make_gt(make_var("y"), ChcExpr::Int(5));

    let result = match_pattern(&pattern, &pattern_vars, &cube);
    assert_eq!(result, None);
}

/// Test that pattern variables avoid collision with existing cube variables (#1317)
#[test]
fn test_extract_pattern_avoids_name_collision() {
    // Create a cube with a variable named __gg_k0 (same as pattern var prefix)
    // __gg_k0 > 5 ∧ x > 10
    let cube = make_and(
        make_gt(make_var("__gg_k0"), ChcExpr::Int(5)),
        make_gt(make_var("x"), ChcExpr::Int(10)),
    );
    let result = extract_pattern(&cube);

    // Should have 2 pattern variables for the two constants
    assert_eq!(result.pattern_vars.len(), 2);

    // Neither pattern var should be named __gg_k0 (it's already taken by user var)
    for pv in &result.pattern_vars {
        assert_ne!(
            pv.name, "__gg_k0",
            "pattern var should not collide with existing var name"
        );
    }

    // Verify pattern vars have unique names
    let pv_names: FxHashSet<_> = result.pattern_vars.iter().map(|v| &v.name).collect();
    assert_eq!(pv_names.len(), 2, "pattern vars should have unique names");

    // Verify substitution values are correct
    assert_eq!(result.subst_values, vec![5, 10]);

    // Verify the pattern still has __gg_k0 as a Var (not abstracted)
    assert!(
        result.pattern.to_string().contains("__gg_k0"),
        "user variable __gg_k0 should still be present in pattern"
    );
}

/// Test that match_pattern works correctly when cube has vars named like pattern vars (#1317)
#[test]
fn test_match_pattern_with_colliding_var_names() {
    // Extract pattern from cube containing __gg_k0 variable
    let original_cube = make_and(
        make_gt(make_var("__gg_k0"), ChcExpr::Int(5)),
        make_gt(make_var("x"), ChcExpr::Int(10)),
    );
    let result = extract_pattern(&original_cube);

    // Create a different instance with same pattern structure but different values
    let instance_cube = make_and(
        make_gt(make_var("__gg_k0"), ChcExpr::Int(7)),
        make_gt(make_var("x"), ChcExpr::Int(20)),
    );
    let instance_normalized = normalize_cube(&instance_cube);

    // Should match and extract the new values
    let match_result = match_pattern(&result.pattern, &result.pattern_vars, &instance_normalized);
    assert!(
        match_result.is_some(),
        "should match instance with same structure"
    );
    let values = match_result.unwrap();
    assert_eq!(values, vec![7, 20]);
}
