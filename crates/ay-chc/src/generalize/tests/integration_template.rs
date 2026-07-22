// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// TemplateGeneralizer tests
#[test]
fn test_template_generalizer_name() {
    let g = TemplateGeneralizer::new();
    assert_eq!(g.name(), "template");
}

#[test]
fn test_template_generalizer_default() {
    let g = TemplateGeneralizer::default();
    assert_eq!(g.name(), "template");
}

#[test]
fn test_template_is_point_constraint_equality() {
    // x = 5 is a point constraint
    let x = ChcVar::new("x", ChcSort::Int);
    let eq = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5));
    assert!(TemplateGeneralizer::is_point_constraint(&eq));

    // 5 = x is also a point constraint
    let eq_rev = ChcExpr::eq(ChcExpr::int(5), ChcExpr::var(x));
    assert!(TemplateGeneralizer::is_point_constraint(&eq_rev));
}

#[test]
fn test_template_is_point_constraint_disequality() {
    // x != 5 is a point constraint
    let x = ChcVar::new("x", ChcSort::Int);
    let ne = ChcExpr::ne(ChcExpr::var(x), ChcExpr::int(5));
    assert!(TemplateGeneralizer::is_point_constraint(&ne));
}

#[test]
fn test_template_is_point_constraint_conjunction() {
    // x = 5 AND y = 3 is a conjunction of point constraints
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let conj = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(5)),
        ChcExpr::eq(ChcExpr::var(y), ChcExpr::int(3)),
    );
    assert!(TemplateGeneralizer::is_point_constraint(&conj));
}

#[test]
fn test_template_is_not_point_constraint_range() {
    // x >= 5 is NOT a point constraint
    let x = ChcVar::new("x", ChcSort::Int);
    let ge = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5));
    assert!(!TemplateGeneralizer::is_point_constraint(&ge));
}

#[test]
fn test_template_generate_init_bound_templates() {
    let x = ChcVar::new("x", ChcSort::Int);
    let bounds = InitBounds::exact(0);

    let templates = TemplateGeneralizer::generate_init_bound_templates(&x, &bounds);

    // Should generate: x >= 0, x <= 0, x = 0, x > 0, x < 0
    assert!(
        templates.len() >= 3,
        "expected at least 3 templates, got {}",
        templates.len()
    );

    // Check that x >= 0 is present
    let x_ge_0 = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0));
    assert!(templates.contains(&x_ge_0), "expected x >= 0 in templates");

    // Check that x <= 0 is present
    let x_le_0 = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(0));
    assert!(templates.contains(&x_le_0), "expected x <= 0 in templates");
}

#[test]
fn test_template_generate_relational_templates() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let templates = TemplateGeneralizer::generate_relational_templates(&x, &y);

    // Should generate: x <= y, x >= y, x = y, x + y >= 0, x + y <= 0
    assert_eq!(
        templates.len(),
        5,
        "expected 5 relational templates (3 comparison + 2 sum)"
    );

    let x_le_y = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::var(y.clone()));
    let x_ge_y = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::var(y.clone()));
    let x_eq_y = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::var(y.clone()));
    let sum_ge_0 = ChcExpr::ge(
        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
        ChcExpr::Int(0),
    );
    let sum_le_0 = ChcExpr::le(
        ChcExpr::add(ChcExpr::var(x), ChcExpr::var(y)),
        ChcExpr::Int(0),
    );

    assert!(templates.contains(&x_le_y), "expected x <= y");
    assert!(templates.contains(&x_ge_y), "expected x >= y");
    assert!(templates.contains(&x_eq_y), "expected x = y");
    assert!(templates.contains(&sum_ge_0), "expected x + y >= 0");
    assert!(templates.contains(&sum_le_0), "expected x + y <= 0");
}

#[test]
fn test_template_generalizer_skips_non_point() {
    let g = TemplateGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    // x >= 5 is already a range constraint, not a point constraint
    let x = ChcVar::new("x", ChcSort::Int);
    let lemma = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5));

    let result = g.generalize(&lemma, 1, &mut ts);

    // Should return unchanged since it's not a point constraint
    assert_eq!(result, lemma);
}

#[test]
fn test_template_generalizer_with_init_bounds() {
    let g = TemplateGeneralizer::new();

    // Set up init bounds: x starts at 0
    let mut bounds = HashMap::default();
    bounds.insert("x".to_string(), InitBounds::exact(0));
    let mut ts = MockTransitionSystem::new().with_init_bounds(bounds);

    // Point constraint: x = 5
    let x = ChcVar::new("x", ChcSort::Int);
    let lemma = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5));

    // Mark x >= 0 as inductive (the template we want)
    let template = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));
    ts.mark_inductive(&format!("{template:?}"));

    let result = g.generalize(&lemma, 1, &mut ts);

    // Should have tried templates and found x >= 0
    assert_eq!(result, template);
}

// Tests for extract_point_values (Fix #966)
#[test]
fn test_extract_point_values_single() {
    let x = ChcVar::new("x", ChcSort::Int);
    let lemma = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(4));

    let result = TemplateGeneralizer::extract_point_values(&lemma);
    assert!(result.is_some());
    let values = result.unwrap();
    assert_eq!(values.get("x"), Some(&4));
}

#[test]
fn test_extract_point_values_conjunction() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let lemma = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(4)),
        ChcExpr::eq(ChcExpr::var(y), ChcExpr::int(3)),
    );

    let result = TemplateGeneralizer::extract_point_values(&lemma);
    assert!(result.is_some());
    let values = result.unwrap();
    assert_eq!(values.get("x"), Some(&4));
    assert_eq!(values.get("y"), Some(&3));
}

#[test]
fn test_extract_point_values_with_disequality() {
    // Disequalities should not contribute values but shouldn't fail
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let lemma = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(4)),
        ChcExpr::ne(ChcExpr::var(y), ChcExpr::int(0)),
    );

    let result = TemplateGeneralizer::extract_point_values(&lemma);
    assert!(result.is_some());
    let values = result.unwrap();
    assert_eq!(values.get("x"), Some(&4));
    assert_eq!(values.get("y"), None); // Disequality doesn't give a value
}

// Tests for template_covers_point (Fix #966)
#[test]
fn test_template_covers_point_le_true() {
    // Point: x = 4
    // Template: x <= 5 (should cover point since 4 <= 5)
    let mut point_values = HashMap::default();
    point_values.insert("x".to_string(), 4i128);

    let x = ChcVar::new("x", ChcSort::Int);
    let template = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(5));

    assert!(TemplateGeneralizer::template_covers_point(
        &template,
        &point_values
    ));
}

#[test]
fn test_template_covers_point_le_false() {
    // Point: x = 4
    // Template: x <= 1 (should NOT cover point since 4 > 1)
    // This is the exact bug from issue #966!
    let mut point_values = HashMap::default();
    point_values.insert("x".to_string(), 4i128);

    let x = ChcVar::new("x", ChcSort::Int);
    let template = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(1));

    assert!(!TemplateGeneralizer::template_covers_point(
        &template,
        &point_values
    ));
}

#[test]
fn test_template_covers_point_ge_true() {
    // Point: x = 4
    // Template: x >= 0 (should cover point since 4 >= 0)
    let mut point_values = HashMap::default();
    point_values.insert("x".to_string(), 4i128);

    let x = ChcVar::new("x", ChcSort::Int);
    let template = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));

    assert!(TemplateGeneralizer::template_covers_point(
        &template,
        &point_values
    ));
}

#[test]
fn test_template_covers_point_ge_false() {
    // Point: x = 4
    // Template: x >= 10 (should NOT cover point since 4 < 10)
    let mut point_values = HashMap::default();
    point_values.insert("x".to_string(), 4i128);

    let x = ChcVar::new("x", ChcSort::Int);
    let template = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10));

    assert!(!TemplateGeneralizer::template_covers_point(
        &template,
        &point_values
    ));
}

#[test]
fn test_template_covers_point_eq_true() {
    // Point: x = 4
    // Template: x = 4 (should cover point)
    let mut point_values = HashMap::default();
    point_values.insert("x".to_string(), 4i128);

    let x = ChcVar::new("x", ChcSort::Int);
    let template = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(4));

    assert!(TemplateGeneralizer::template_covers_point(
        &template,
        &point_values
    ));
}

#[test]
fn test_template_covers_point_eq_false() {
    // Point: x = 4
    // Template: x = 0 (should NOT cover point since 4 != 0)
    let mut point_values = HashMap::default();
    point_values.insert("x".to_string(), 4i128);

    let x = ChcVar::new("x", ChcSort::Int);
    let template = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(0));

    assert!(!TemplateGeneralizer::template_covers_point(
        &template,
        &point_values
    ));
}

#[test]
fn test_template_covers_point_relational() {
    // Point: x = 4, y = 3
    // Template: x >= y (should cover point since 4 >= 3)
    let mut point_values = HashMap::default();
    point_values.insert("x".to_string(), 4i128);
    point_values.insert("y".to_string(), 3i128);

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let template = ChcExpr::ge(ChcExpr::var(x), ChcExpr::var(y));

    assert!(TemplateGeneralizer::template_covers_point(
        &template,
        &point_values
    ));
}

#[test]
fn test_template_covers_point_relational_false() {
    // Point: x = 3, y = 4
    // Template: x >= y (should NOT cover point since 3 < 4)
    let mut point_values = HashMap::default();
    point_values.insert("x".to_string(), 3i128);
    point_values.insert("y".to_string(), 4i128);

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let template = ChcExpr::ge(ChcExpr::var(x), ChcExpr::var(y));

    assert!(!TemplateGeneralizer::template_covers_point(
        &template,
        &point_values
    ));
}
