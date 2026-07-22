// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{ChcSort, SmtContext, SmtResult};

#[test]
fn test_sip_extracts_conjunction() {
    // Formula: x > 0 AND y < 10
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let formula = ChcExpr::and(
        ChcExpr::gt(ChcExpr::var(x), ChcExpr::Int(0)),
        ChcExpr::lt(ChcExpr::var(y), ChcExpr::Int(10)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    model.insert("y".to_string(), SmtValue::Int(3));

    let result = sip(&formula, &model);

    // Result should be a conjunction (And)
    assert!(matches!(result, ChcExpr::Op(ChcOp::And, _)));
}

#[test]
fn test_sip_picks_satisfied_branch() {
    // Formula: (x > 0) OR (y < 0)
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let formula = ChcExpr::or(
        ChcExpr::gt(ChcExpr::var(x), ChcExpr::Int(0)),
        ChcExpr::lt(ChcExpr::var(y), ChcExpr::Int(0)),
    );

    // Model where x > 0 is true but y < 0 is false
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    model.insert("y".to_string(), SmtValue::Int(3));

    let result = sip(&formula, &model);

    // Should pick x > 0 (the satisfied branch)
    let vars = result.vars();
    assert!(vars.iter().any(|v| v.name == "x"));
}

#[test]
fn test_cvp_filters_variables() {
    // Formula: x > 0 AND y < 10
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let formula = ChcExpr::and(
        ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
        ChcExpr::lt(ChcExpr::var(y), ChcExpr::Int(10)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    model.insert("y".to_string(), SmtValue::Int(3));

    // Only keep x
    let mut vars_to_keep = FxHashSet::default();
    vars_to_keep.insert(x);

    let result = cvp(&formula, &model, &vars_to_keep);

    // Result should only mention x
    let vars = result.vars();
    assert!(vars.iter().all(|v| v.name == "x"));
    assert!(!vars.iter().any(|v| v.name == "y"));
}

#[test]
fn test_cvp_empty_vars_to_keep() {
    // Formula: x > 0 AND y < 10
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let formula = ChcExpr::and(
        ChcExpr::gt(ChcExpr::var(x), ChcExpr::Int(0)),
        ChcExpr::lt(ChcExpr::var(y), ChcExpr::Int(10)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    model.insert("y".to_string(), SmtValue::Int(3));

    // Empty vars_to_keep
    let vars_to_keep = FxHashSet::default();

    let result = cvp(&formula, &model, &vars_to_keep);

    // Result should be true (empty conjunction)
    assert_eq!(result, ChcExpr::Bool(true));
}

#[test]
fn test_cvp_refines_disequality_to_less_than() {
    // Formula: x != 5
    let x = ChcVar::new("x", ChcSort::Int);

    let formula = ChcExpr::ne(ChcExpr::var(x.clone()), ChcExpr::Int(5));

    // Model where x = 3 (so x < 5 is true)
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(3));

    let mut vars_to_keep = FxHashSet::default();
    vars_to_keep.insert(x);

    let result = cvp(&formula, &model, &vars_to_keep);

    // Should refine to x < 5
    assert!(matches!(result, ChcExpr::Op(ChcOp::Lt, _)));
}

#[test]
fn test_cvp_refines_disequality_to_greater_than() {
    // Formula: x != 5
    let x = ChcVar::new("x", ChcSort::Int);

    let formula = ChcExpr::ne(ChcExpr::var(x.clone()), ChcExpr::Int(5));

    // Model where x = 10 (so x > 5 is true)
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(10));

    let mut vars_to_keep = FxHashSet::default();
    vars_to_keep.insert(x);

    let result = cvp(&formula, &model, &vars_to_keep);

    // Should refine to x > 5
    assert!(matches!(result, ChcExpr::Op(ChcOp::Gt, _)));
}

#[test]
fn test_cvp_model_satisfies_both_formula_and_result() {
    // Property: σ |= cvp(τ, σ, X) AND σ |= τ (Def.2 property 1)
    // This checks model satisfaction, NOT implication.
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let formula = ChcExpr::and(
        ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
        ChcExpr::lt(ChcExpr::var(y), ChcExpr::Int(10)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    model.insert("y".to_string(), SmtValue::Int(3));

    let mut vars_to_keep = FxHashSet::default();
    vars_to_keep.insert(x);

    let result = cvp(&formula, &model, &vars_to_keep);

    // Both formula and result should be satisfied by model
    let mbp = Mbp::new();
    assert_eq!(mbp.eval_bool(&formula, &model), Some(true));
    assert_eq!(mbp.eval_bool(&result, &model), Some(true));
}

#[test]
fn test_cvp_with_nested_and() {
    // Formula: (x > 0 AND y > 0) AND z > 0
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    let formula = ChcExpr::and(
        ChcExpr::and(
            ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
            ChcExpr::gt(ChcExpr::var(y), ChcExpr::Int(0)),
        ),
        ChcExpr::gt(ChcExpr::var(z.clone()), ChcExpr::Int(0)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(1));
    model.insert("y".to_string(), SmtValue::Int(2));
    model.insert("z".to_string(), SmtValue::Int(3));

    // Keep only x and z
    let mut vars_to_keep = FxHashSet::default();
    vars_to_keep.insert(x);
    vars_to_keep.insert(z);

    let result = cvp(&formula, &model, &vars_to_keep);

    // Result should mention x and z but not y
    let vars = result.vars();
    assert!(vars.iter().any(|v| v.name == "x"));
    assert!(vars.iter().any(|v| v.name == "z"));
    assert!(!vars.iter().any(|v| v.name == "y"));
}

#[test]
fn test_collect_vars() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let expr = ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::var(y.clone()));
    let vars = expr.vars();

    assert!(vars.iter().any(|v| v == &x));
    assert!(vars.iter().any(|v| v == &y));
    assert_eq!(vars.len(), 2);
}

/// Test implication property: cvp(τ, σ, X) |= ∃(V(τ)\X). τ
///
/// Per TRL paper Definition 2(2), the CVP result should imply the original
/// formula under existential projection of eliminated variables.
///
/// Solver-backed test: checks (cvp ∧ ¬∃V\X.τ) is UNSAT.
#[test]
fn test_cvp_implies_existentially_projected_formula() {
    // Formula: x > 0 AND y > 0
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let formula = ChcExpr::and(
        ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
        ChcExpr::gt(ChcExpr::var(y), ChcExpr::Int(0)),
    );

    // Model: x=5, y=3
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    model.insert("y".to_string(), SmtValue::Int(3));

    // Keep only x - this eliminates y
    let mut vars_to_keep = FxHashSet::default();
    vars_to_keep.insert(x.clone());

    let cvp_result = cvp(&formula, &model, &vars_to_keep);

    // CVP should return x > 0 (y > 0 filtered out)
    assert!(cvp_result.vars().iter().all(|v| v.name == "x"));

    // Check implication: cvp |= ∃y. (x > 0 ∧ y > 0)
    //
    // ∃y. (x > 0 ∧ y > 0) ≡ x > 0 ∧ ∃y. y > 0
    //                     ≡ x > 0 ∧ true  (since y > 0 is satisfiable)
    //                     ≡ x > 0
    //
    // In this case, CVP returns x > 0, and ∃y.formula = x > 0,
    // so cvp |= ∃y.formula trivially holds.
    //
    // Test: (cvp ∧ ¬(x > 0)) should be UNSAT
    let existential_projection = ChcExpr::gt(ChcExpr::var(x), ChcExpr::Int(0));
    let implication_check = ChcExpr::and(cvp_result, ChcExpr::not(existential_projection));

    let mut smt = SmtContext::new();
    let result = smt.check_sat(&implication_check);
    assert!(
        matches!(result, SmtResult::Unsat),
        "cvp should imply existentially projected formula, but got {result:?}"
    );
}

/// Test that SIP (no variable filtering) implies the original formula.
///
/// SIP extracts a syntactic implicant - a conjunction of literals from the
/// formula that are true under the model. This SHOULD imply the original
/// formula (unlike CVP which may weaken via variable filtering).
#[test]
fn test_sip_implies_formula() {
    // Formula: (x > 0 AND y < 10) OR (z > 100)
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    let formula = ChcExpr::or(
        ChcExpr::and(
            ChcExpr::gt(ChcExpr::var(x), ChcExpr::Int(0)),
            ChcExpr::lt(ChcExpr::var(y), ChcExpr::Int(10)),
        ),
        ChcExpr::gt(ChcExpr::var(z), ChcExpr::Int(100)),
    );

    // Model: x=5, y=3, z=50 (satisfies first branch)
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    model.insert("y".to_string(), SmtValue::Int(3));
    model.insert("z".to_string(), SmtValue::Int(50));

    let sip_result = sip(&formula, &model);

    // SIP should pick the satisfied branch: x > 0 AND y < 10
    let sip_vars = sip_result.vars();
    assert!(sip_vars.iter().any(|v| v.name == "x"));
    assert!(sip_vars.iter().any(|v| v.name == "y"));

    // Check implication: sip |= formula
    // Test: (sip ∧ ¬formula) should be UNSAT
    let implication_check = ChcExpr::and(sip_result, ChcExpr::not(formula));

    let mut smt = SmtContext::new();
    let result = smt.check_sat(&implication_check);
    assert!(
        matches!(
            result,
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "sip should imply original formula, but got {result:?}"
    );
}

/// Test CVP behavior with mixed-variable literals.
///
/// CVP keeps literals that mention ANY vars_to_keep variable.
/// If a literal like "x > y" mentions both a kept variable (x) and
/// an eliminated variable (y), it is KEPT because it mentions x.
///
/// This is intentional - full MBP-style projection would be needed to
/// properly eliminate y from such mixed literals, which CVP doesn't do.
///
/// The property `V(cvp) ⊆ X ∩ V(τ)` from TRL Def.2(4) is thus NOT
/// always satisfied by our current implementation when literals
/// mention both kept and eliminated variables.
#[test]
fn test_cvp_keeps_mixed_variable_literals() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // Formula: x > y AND y > 0 AND y < 10
    let formula = ChcExpr::and(
        ChcExpr::and(
            ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
            ChcExpr::gt(ChcExpr::var(y.clone()), ChcExpr::Int(0)),
        ),
        ChcExpr::lt(ChcExpr::var(y), ChcExpr::Int(10)),
    );

    // Model: x=5, y=3 (satisfies formula: 5>3, 3>0, 3<10)
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    model.insert("y".to_string(), SmtValue::Int(3));

    // Keep only x - but "x > y" will be kept because it mentions x
    let mut vars_to_keep = FxHashSet::default();
    vars_to_keep.insert(x);

    let cvp_result = cvp(&formula, &model, &vars_to_keep);

    // CVP keeps "x > y" because it mentions x
    // So result still contains y (this is current behavior, not ideal)
    let cvp_vars = cvp_result.vars();
    assert!(
        cvp_vars.iter().any(|v| v.name == "x"),
        "CVP result should contain x"
    );

    // Document that y is also present due to mixed literal
    let has_y = cvp_vars.iter().any(|v| v.name == "y");
    assert!(
        has_y,
        "CVP result contains y from mixed literal 'x > y' - this is known limitation"
    );

    // CVP drops y-only constraints, so cvp_result does NOT imply the original formula.
    // Demonstrate with a concrete counterexample model.
    let mbp = Mbp::new();

    assert_eq!(mbp.eval_bool(&formula, &model), Some(true));
    assert_eq!(mbp.eval_bool(&cvp_result, &model), Some(true));

    // x > y is satisfied, but y is outside (0, 10)
    let mut counterexample = FxHashMap::default();
    counterexample.insert("x".to_string(), SmtValue::Int(0));
    counterexample.insert("y".to_string(), SmtValue::Int(-1));

    assert_eq!(mbp.eval_bool(&cvp_result, &counterexample), Some(true));
    assert_eq!(mbp.eval_bool(&formula, &counterexample), Some(false));
}

/// Demonstrates that CVP does NOT directly imply the original formula.
///
/// This is by design per TRL paper: CVP implies the *existentially projected*
/// formula, not the original. Variable filtering removes constraints on
/// eliminated variables.
///
/// This test documents the expected behavior - it's NOT a bug.
#[test]
fn test_cvp_does_not_directly_imply_formula_after_filtering() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // Formula: x > 0 AND y = 100
    let formula = ChcExpr::and(
        ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
        ChcExpr::eq(ChcExpr::var(y), ChcExpr::Int(100)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    model.insert("y".to_string(), SmtValue::Int(100));

    // Keep only x - y is filtered out
    let mut vars_to_keep = FxHashSet::default();
    vars_to_keep.insert(x);

    let cvp_result = cvp(&formula, &model, &vars_to_keep);

    // CVP returns only x constraints (e.g., x > 0)
    assert!(cvp_result.vars().iter().all(|v| v.name == "x"));

    // Direct implication check: cvp_result |= formula?
    // This should be SAT (i.e., implication fails) because:
    // cvp_result = "x > 0" does NOT imply "x > 0 AND y = 100"
    // (there exist x > 0 with y ≠ 100)
    let direct_impl_check = ChcExpr::and(cvp_result, ChcExpr::not(formula));

    let mut smt = SmtContext::new();
    let result = smt.check_sat(&direct_impl_check);

    // Expected: SAT (direct implication does NOT hold)
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "Expected direct implication to FAIL (SAT), got {result:?}.\n\
         This is expected behavior per TRL paper Def.2(2): CVP implies the \
         existentially projected formula ∃y.τ, not the original τ."
    );
}
