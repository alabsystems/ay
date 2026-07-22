// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn deep_int_ite_chain(cond: &ChcExpr, depth: usize) -> ChcExpr {
    let mut expr = ChcExpr::Int(0);
    for _ in 0..depth {
        expr = ChcExpr::ite(cond.clone(), expr, ChcExpr::Int(1));
    }
    expr
}

fn deep_bool_ite_chain(cond: &ChcExpr, depth: usize, leaf: ChcExpr) -> ChcExpr {
    let mut expr = leaf;
    for _ in 0..depth {
        expr = ChcExpr::ite(cond.clone(), expr, ChcExpr::Bool(false));
    }
    expr
}

#[test]
fn test_mbp_boolean_projection() {
    let mbp = Mbp::new();

    // Formula: x = 1 AND b
    let x = ChcVar::new("x", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Bool);

    let formula = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(1)),
        ChcExpr::var(b.clone()),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(1));
    model.insert("b".to_string(), SmtValue::Bool(true));

    // Project out b - should get x = 1
    let result = mbp.project(&formula, &[b], &model);
    assert!(matches!(result, ChcExpr::Op(ChcOp::Eq, _)));
}

#[test]
fn test_mbp_integer_equality() {
    let mbp = Mbp::new();

    // Formula: x = y + 1 AND x > 0
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let formula = ChcExpr::and(
        ChcExpr::eq(
            ChcExpr::var(x.clone()),
            ChcExpr::add(ChcExpr::var(y), ChcExpr::Int(1)),
        ),
        ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    model.insert("y".to_string(), SmtValue::Int(4));

    // Project out x - should get constraints on y
    let result = mbp.project(&formula, &[x], &model);

    // Result should not contain x
    let vars = result.vars();
    assert!(!vars.iter().any(|v| v.name == "x"));
}

#[test]
fn test_mbp_bounds_resolution() {
    let mbp = Mbp::new();

    // Formula: x >= 0 AND x <= 10 AND y = x + 1
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let formula = ChcExpr::and(
        ChcExpr::and(
            ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
            ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::Int(10)),
        ),
        ChcExpr::eq(
            ChcExpr::var(y),
            ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::Int(1)),
        ),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    model.insert("y".to_string(), SmtValue::Int(6));

    // Project out x
    let result = mbp.project(&formula, &[x], &model);

    // Result should constrain y based on the elimination
    let vars = result.vars();
    assert!(!vars.iter().any(|v| v.name == "x"));
}

#[test]
fn test_implicant_extraction() {
    let mbp = Mbp::new();

    // Formula: (a AND b) OR c
    let a = ChcVar::new("a", ChcSort::Bool);
    let b = ChcVar::new("b", ChcSort::Bool);
    let c = ChcVar::new("c", ChcSort::Bool);

    let formula = ChcExpr::or(
        ChcExpr::and(ChcExpr::var(a), ChcExpr::var(b)),
        ChcExpr::var(c),
    );

    let mut model = FxHashMap::default();
    model.insert("a".to_string(), SmtValue::Bool(true));
    model.insert("b".to_string(), SmtValue::Bool(true));
    model.insert("c".to_string(), SmtValue::Bool(false));

    let implicant = mbp.get_implicant(&formula, &model);

    // Should pick (a AND b) branch since a=true, b=true, c=false
    assert_eq!(implicant.len(), 2, "implicant should have 2 literals");
    // Verify the implicant contains variables a and b (not c)
    let implicant_vars: Vec<String> = implicant
        .iter()
        .flat_map(|lit| lit.atom.vars())
        .map(|v| v.name)
        .collect();
    assert!(
        implicant_vars.contains(&"a".to_string()),
        "implicant should contain variable a, got: {implicant_vars:?}"
    );
    assert!(
        implicant_vars.contains(&"b".to_string()),
        "implicant should contain variable b, got: {implicant_vars:?}"
    );
}

#[test]
fn test_implicant_preserves_positive_bv_comparison_atom() {
    let mbp = Mbp::new();

    let bv_x = ChcVar::new("bv_x", ChcSort::BitVec(32));
    let bv_y = ChcVar::new("bv_y", ChcSort::BitVec(32));
    let signed_le = ChcExpr::bv_sle(ChcExpr::var(bv_x), ChcExpr::var(bv_y.clone()));
    let formula = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(bv_y), ChcExpr::BitVec(10, 32)),
        signed_le.clone(),
    );

    let mut model = FxHashMap::default();
    model.insert("bv_x".to_string(), SmtValue::BitVec(5, 32));
    model.insert("bv_y".to_string(), SmtValue::BitVec(10, 32));

    let implicant = mbp.get_implicant(&formula, &model);

    assert_eq!(
        implicant.len(),
        2,
        "positive BV comparison atoms must remain in the implicant: {implicant:?}"
    );
    assert!(
        implicant
            .iter()
            .any(|lit| lit.positive && lit.atom == signed_le),
        "implicant must preserve the positive bvsle atom: {implicant:?}"
    );
}

#[test]
fn test_simplify_via_simplify_constants() {
    // 0 + x = x
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::add(ChcExpr::Int(0), ChcExpr::var(x));
    let result = expr.simplify_constants();
    assert!(matches!(result, ChcExpr::Var(_)));

    // 5 <= 10 = true
    let expr2 = ChcExpr::le(ChcExpr::Int(5), ChcExpr::Int(10));
    let result2 = expr2.simplify_constants();
    assert_eq!(result2, ChcExpr::Bool(true));

    // true AND x = x (where x is boolean)
    let b = ChcVar::new("b", ChcSort::Bool);
    let expr3 = ChcExpr::and(ChcExpr::Bool(true), ChcExpr::var(b));
    let result3 = expr3.simplify_constants();
    assert!(matches!(result3, ChcExpr::Var(_)));
}

/// Test for #720: eval_bool should return None (not Some(false)) for Or
/// when no disjunct is provably true but at least one is unknown.
#[test]
fn test_eval_bool_or_partial_model() {
    let mbp = Mbp::new();

    // Formula: (x > 0) OR (y > 0)
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let or_formula = ChcExpr::or(
        ChcExpr::gt(ChcExpr::var(x), ChcExpr::Int(0)),
        ChcExpr::gt(ChcExpr::var(y), ChcExpr::Int(0)),
    );

    // Partial model: x is known (= 0, so x > 0 is false), but y is unknown
    let mut partial_model = FxHashMap::default();
    partial_model.insert("x".to_string(), SmtValue::Int(0));
    // y is NOT in model - partial/unknown

    // eval_bool should return None (unknown), not Some(false)
    // because y > 0 cannot be evaluated
    let result = mbp.eval_bool(&or_formula, &partial_model);
    assert_eq!(
        result, None,
        "Or with unknown disjunct should return None, not Some(false)"
    );

    // Also test: if one disjunct is true, should return true even with unknowns
    partial_model.insert("x".to_string(), SmtValue::Int(5));
    let result_true = mbp.eval_bool(&or_formula, &partial_model);
    assert_eq!(
        result_true,
        Some(true),
        "Or with true disjunct should return Some(true)"
    );

    // And: if all disjuncts are provably false, should return Some(false)
    let mut full_model = FxHashMap::default();
    full_model.insert("x".to_string(), SmtValue::Int(0));
    full_model.insert("y".to_string(), SmtValue::Int(-1));
    let result_false = mbp.eval_bool(&or_formula, &full_model);
    assert_eq!(
        result_false,
        Some(false),
        "Or with all false disjuncts should return Some(false)"
    );
}

/// Test for #720: collect_implicant should not drop Or when no branch is provably true
#[test]
fn test_implicant_or_partial_model_preserves_or() {
    let mbp = Mbp::new();

    // Formula: z = 1 AND ((x > 0) OR (y > 0))
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    let or_part = ChcExpr::or(
        ChcExpr::gt(ChcExpr::var(x), ChcExpr::Int(0)),
        ChcExpr::gt(ChcExpr::var(y), ChcExpr::Int(0)),
    );
    let formula = ChcExpr::and(ChcExpr::eq(ChcExpr::var(z), ChcExpr::Int(1)), or_part);

    // Partial model: z=1, x=0, y unknown
    let mut partial_model = FxHashMap::default();
    partial_model.insert("z".to_string(), SmtValue::Int(1));
    partial_model.insert("x".to_string(), SmtValue::Int(0));
    // y is unknown

    let implicant = mbp.get_implicant(&formula, &partial_model);

    // Implicant should have 2 literals: (z = 1) and the Or
    // Previously it would drop the Or, leaving just (z = 1)
    assert_eq!(
        implicant.len(),
        2,
        "Implicant should contain both z=1 and the Or"
    );

    // Convert to formula and check the Or is preserved
    let implicant_formula = mbp.implicant_to_formula(&implicant);

    // Check that the Or is in the result (not dropped)
    fn contains_or(e: &ChcExpr) -> bool {
        match e {
            ChcExpr::Op(ChcOp::Or, _) => true,
            ChcExpr::Op(_, args) => args.iter().any(|a| contains_or(a)),
            _ => false,
        }
    }
    assert!(
        contains_or(&implicant_formula),
        "Implicant should preserve Or constraint"
    );
}

#[test]
fn test_eval_bool_handles_ite_in_arith_atom() {
    let mbp = Mbp::new();

    // Formula: (= (ite c 1 0) 1) OR (= x 0)
    // With c=true, the first disjunct is true and Or should evaluate to true.
    let c = ChcVar::new("c", ChcSort::Bool);
    let x = ChcVar::new("x", ChcSort::Int);

    let ite = ChcExpr::ite(ChcExpr::var(c), ChcExpr::int(1), ChcExpr::int(0));
    let disj1 = ChcExpr::eq(ite, ChcExpr::int(1));
    let disj2 = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(0));
    let formula = ChcExpr::or(disj1, disj2);

    let mut model = FxHashMap::default();
    model.insert("c".to_string(), SmtValue::Bool(true));

    assert_eq!(mbp.eval_bool(&formula, &model), Some(true));
}

#[test]
fn test_eval_bool_deep_mutual_recursion_with_eval_arith() {
    let mbp = Mbp::new();
    // Depth 4096 exceeds MAX_EXPR_RECURSION_DEPTH (500).
    // After #3031 depth guards, eval_bool returns None at the limit
    // instead of overflowing the stack.
    const DEPTH: usize = 4096;

    let x = ChcVar::new("x", ChcSort::Int);
    let cond = ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(0));
    let deep_int = deep_int_ite_chain(&cond, DEPTH);
    let formula = ChcExpr::eq(deep_int, ChcExpr::Int(0));

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(0));

    // At depth 4096, the depth guard bails out — eval_bool returns None.
    // The key property: no stack overflow.
    let result = mbp.eval_bool(&formula, &model);
    assert!(
        result.is_none(),
        "depth-bounded eval_bool should return None on expressions deeper than 500"
    );

    // Verify a shallow chain still evaluates correctly
    let shallow_int = deep_int_ite_chain(&cond, 50);
    let shallow_formula = ChcExpr::eq(shallow_int, ChcExpr::Int(0));
    assert_eq!(mbp.eval_bool(&shallow_formula, &model), Some(true));
}

#[test]
fn test_collect_implicant_deep_mutual_recursion_with_eval_bool() {
    let mbp = Mbp::new();
    // Depth 4096 exceeds MAX_EXPR_RECURSION_DEPTH (500).
    // collect_implicant stops collecting at the depth limit instead of
    // overflowing the stack.
    const DEPTH: usize = 4096;

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let cond = ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(0));
    let terminal = ChcExpr::eq(ChcExpr::var(y), ChcExpr::Int(1));
    let formula = deep_bool_ite_chain(&cond, DEPTH, terminal.clone());

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(0));
    model.insert("y".to_string(), SmtValue::Int(1));

    // The key property: no stack overflow. The implicant may be incomplete
    // because the depth guard truncates deep traversals.
    let _implicant = mbp.get_implicant(&formula, &model);

    // Verify a shallow chain still works correctly
    let shallow_formula = deep_bool_ite_chain(&cond, 50, terminal.clone());
    let shallow_implicant = mbp.get_implicant(&shallow_formula, &model);
    assert!(
        shallow_implicant
            .iter()
            .any(|lit| lit.positive && lit.atom == terminal),
        "shallow implicant should retain the terminal satisfied atom"
    );
}

#[test]
fn test_eval_bool_handles_bool_eq_and_ne() {
    let mbp = Mbp::new();

    let a = ChcVar::new("a", ChcSort::Bool);
    let b = ChcVar::new("b", ChcSort::Bool);

    let a_is_true = ChcExpr::eq(ChcExpr::var(a.clone()), ChcExpr::Bool(true));
    let b_is_true = ChcExpr::eq(ChcExpr::var(b.clone()), ChcExpr::Bool(true));
    let formula = ChcExpr::or(a_is_true, b_is_true);

    let mut model = FxHashMap::default();
    model.insert("a".to_string(), SmtValue::Bool(false));
    model.insert("b".to_string(), SmtValue::Bool(true));

    assert_eq!(mbp.eval_bool(&formula, &model), Some(true));

    let neq = ChcExpr::ne(ChcExpr::var(a), ChcExpr::var(b));
    assert_eq!(mbp.eval_bool(&neq, &model), Some(true));
}

#[test]
fn test_implicant_picks_bool_eq_disjunct() {
    let mbp = Mbp::new();

    let a = ChcVar::new("a", ChcSort::Bool);
    let b = ChcVar::new("b", ChcSort::Bool);

    let a_is_true = ChcExpr::eq(ChcExpr::var(a), ChcExpr::Bool(true));
    let b_is_true = ChcExpr::eq(ChcExpr::var(b), ChcExpr::Bool(true));
    let formula = ChcExpr::or(a_is_true, b_is_true);

    let mut model = FxHashMap::default();
    model.insert("a".to_string(), SmtValue::Bool(false));
    model.insert("b".to_string(), SmtValue::Bool(true));

    let implicant = mbp.get_implicant(&formula, &model);
    assert_eq!(implicant.len(), 1);

    let implicant_formula = mbp.implicant_to_formula(&implicant);
    assert!(
        !matches!(implicant_formula, ChcExpr::Op(ChcOp::Or, _)),
        "Implicant should pick a satisfied disjunct instead of preserving the Or"
    );
}

#[test]
fn test_implicant_handles_implies() {
    let mbp = Mbp::new();

    // (x = 0) => (y = 0), with x != 0 in the model.
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let formula = ChcExpr::implies(
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(0)),
        ChcExpr::eq(ChcExpr::var(y), ChcExpr::Int(0)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(1));

    let implicant = mbp.get_implicant(&formula, &model);
    assert_eq!(implicant.len(), 1);
    assert!(!implicant[0].positive);
    assert!(matches!(implicant[0].atom, ChcExpr::Op(ChcOp::Eq, _)));
}

#[test]
fn test_implicant_handles_bool_ite() {
    let mbp = Mbp::new();

    // (ite c (x > 0) (y > 0))
    let c = ChcVar::new("c", ChcSort::Bool);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let formula = ChcExpr::ite(
        ChcExpr::var(c),
        ChcExpr::gt(ChcExpr::var(x), ChcExpr::Int(0)),
        ChcExpr::gt(ChcExpr::var(y), ChcExpr::Int(0)),
    );

    let mut model = FxHashMap::default();
    model.insert("c".to_string(), SmtValue::Bool(true));
    model.insert("x".to_string(), SmtValue::Int(1));

    let implicant = mbp.get_implicant(&formula, &model);
    assert_eq!(
        implicant.len(),
        2,
        "Implicant should include guard and selected branch"
    );
}

/// Test for #720: project should bail out when implicant contains unprojectable Or
#[test]
fn test_project_bails_on_unprojectable_or() {
    let mbp = Mbp::new();

    // Formula: ((x > 0) OR (y > 0)) AND z = 1
    // Try to project out x with partial model
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    let or_part = ChcExpr::or(
        ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
        ChcExpr::gt(ChcExpr::var(y), ChcExpr::Int(0)),
    );
    let formula = ChcExpr::and(or_part, ChcExpr::eq(ChcExpr::var(z), ChcExpr::Int(1)));

    // Partial model: x=0 (so x>0 is false), y unknown, z=1
    let mut partial_model = FxHashMap::default();
    partial_model.insert("x".to_string(), SmtValue::Int(0));
    partial_model.insert("z".to_string(), SmtValue::Int(1));
    // y is unknown

    // Project out x
    let result = mbp.project(&formula, std::slice::from_ref(&x), &partial_model);

    // The Or contains x but cannot be projected (not a simple bound).
    // MBP should bail out and return the simplified formula, still containing the Or.
    // It should NOT silently drop the Or.
    fn contains_or(e: &ChcExpr) -> bool {
        match e {
            ChcExpr::Op(ChcOp::Or, _) => true,
            ChcExpr::Op(_, args) => args.iter().any(|a| contains_or(a)),
            _ => false,
        }
    }
    assert!(
        contains_or(&result),
        "Projection should preserve Or when it can't be projected"
    );
}

/// Test for #720: Not(And) should also preserve constraint under partial models
#[test]
fn test_implicant_not_and_partial_model_preserves_constraint() {
    let mbp = Mbp::new();

    // Formula: z = 1 AND NOT((x > 0) AND (y > 0))
    // Under partial model, if we can't find a definitely-false conjunct,
    // we should keep the whole Not(And(...))
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    let not_and_part = ChcExpr::not(ChcExpr::and(
        ChcExpr::gt(ChcExpr::var(x), ChcExpr::Int(0)),
        ChcExpr::gt(ChcExpr::var(y), ChcExpr::Int(0)),
    ));
    let formula = ChcExpr::and(ChcExpr::eq(ChcExpr::var(z), ChcExpr::Int(1)), not_and_part);

    // Partial model: z=1, x=5 (so x>0 is true), y unknown
    // For NOT(And(x>0, y>0)) to be true, we need one false conjunct.
    // x>0 is true, so we need y>0 to be false or unknown.
    // With y unknown, we can't confirm y>0 is false, so we should keep Not(And(...))
    let mut partial_model = FxHashMap::default();
    partial_model.insert("z".to_string(), SmtValue::Int(1));
    partial_model.insert("x".to_string(), SmtValue::Int(5));
    // y is unknown

    let implicant = mbp.get_implicant(&formula, &partial_model);

    // Implicant should have 2 literals: (z = 1) and the Not(And(...))
    assert_eq!(
        implicant.len(),
        2,
        "Implicant should contain both z=1 and Not(And(...))"
    );
}

/// Test for #892: MBQI-style term substitution finds equivalent terms
#[test]
fn test_mbqi_find_equivalent_term() {
    let mbp = Mbp::new();

    // Formula: x = y + 1 AND z = 2
    // With model x=3, y=2, z=2
    // When eliminating x, we should find that y+1 evaluates to 3 (same as x)
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    let y_plus_1 = ChcExpr::add(ChcExpr::var(y), ChcExpr::Int(1));
    let formula = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x.clone()), y_plus_1),
        ChcExpr::eq(ChcExpr::var(z), ChcExpr::Int(2)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(3));
    model.insert("y".to_string(), SmtValue::Int(2));
    model.insert("z".to_string(), SmtValue::Int(2));

    // Collect candidate terms from formula
    let candidates = Mbp::collect_candidate_terms(&formula);

    // Should find y+1 as an equivalent term for x
    let equiv = mbp.find_equivalent_term(&x, &candidates, &model);
    assert!(equiv.is_some(), "Should find equivalent term for x");

    // The equivalent term should be y+1
    let equiv_term = equiv.unwrap();
    assert_eq!(
        mbp.eval_arith(&equiv_term, &model),
        Some(3),
        "Equivalent term should evaluate to 3"
    );
    assert!(
        !equiv_term.contains_var_name(&x.name),
        "Equivalent term should not contain x"
    );
}

/// Test for #892: MBQI fallback in project() produces more general results
#[test]
fn test_mbqi_project_uses_equivalent_term() {
    let mbp = Mbp::new();

    // Formula: x = y + 1 AND x < 10 AND z = 2
    // Project out y (unprojectable due to being on RHS of =).
    // With model x=3, y=2, z=2
    //
    // Without MBQI: would substitute y with 2, getting x = 3 AND x < 10 AND z = 2
    // With MBQI: should find x - 1 as equivalent to y, getting x < 10 AND z = 2
    // (Or substitute with equivalent term if possible)
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    let y_plus_1 = ChcExpr::add(ChcExpr::var(y.clone()), ChcExpr::Int(1));
    let formula = ChcExpr::and(
        ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(x.clone()), y_plus_1),
            ChcExpr::lt(ChcExpr::var(x), ChcExpr::Int(10)),
        ),
        ChcExpr::eq(ChcExpr::var(z), ChcExpr::Int(2)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(3));
    model.insert("y".to_string(), SmtValue::Int(2));
    model.insert("z".to_string(), SmtValue::Int(2));

    // Project out y
    let result = mbp.project(&formula, std::slice::from_ref(&y), &model);

    // Result should not contain y
    assert!(
        !result.contains_var_name(&y.name),
        "Projected result should not contain y"
    );

    // Result should still be valid under the model
    // (The exact form depends on whether MBQI found an equivalent term)
}

/// Test for #892: collect_candidate_terms extracts arithmetic subterms
#[test]
fn test_collect_candidate_terms() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // Formula: x = y + 1
    let formula = ChcExpr::eq(
        ChcExpr::var(x.clone()),
        ChcExpr::add(ChcExpr::var(y.clone()), ChcExpr::Int(1)),
    );

    let candidates = Mbp::collect_candidate_terms(&formula);

    // Should contain: x, y+1, y
    assert!(
        candidates.iter().any(|t| *t == ChcExpr::var(x.clone())),
        "Should contain x"
    );
    assert!(
        candidates.iter().any(|t| *t == ChcExpr::var(y.clone())),
        "Should contain y"
    );
    // Should contain the addition term
    let y_plus_1 = ChcExpr::add(ChcExpr::var(y), ChcExpr::Int(1));
    assert!(candidates.contains(&y_plus_1), "Should contain y+1");
}

#[test]
fn test_project_with_residuals_full_projection() {
    let mbp = Mbp::new();

    // Formula: x = y + 1 AND x > 0
    // Project out x — equality allows full substitution, no residuals
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let formula = ChcExpr::and(
        ChcExpr::eq(
            ChcExpr::var(x.clone()),
            ChcExpr::add(ChcExpr::var(y), ChcExpr::Int(1)),
        ),
        ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    model.insert("y".to_string(), SmtValue::Int(4));

    let result = mbp.project_with_residuals(&formula, std::slice::from_ref(&x), &model);

    assert!(
        result.residual_vars.is_empty(),
        "Full projection should have no residuals"
    );
    assert!(
        !result.formula.contains_var_name(&x.name),
        "Projected formula should not contain x"
    );
}

#[test]
fn test_project_with_residuals_partial_projection() {
    let mbp = Mbp::new();

    // Formula: ((x > 0) OR (y > 0)) AND z = 1
    // Project out x AND y:
    // - x is inside an Or (unprojectable) → residual
    // - y is inside the same Or (unprojectable) → residual
    // - z is not being eliminated
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    let formula = ChcExpr::and(
        ChcExpr::or(
            ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
            ChcExpr::gt(ChcExpr::var(y.clone()), ChcExpr::Int(0)),
        ),
        ChcExpr::eq(ChcExpr::var(z.clone()), ChcExpr::Int(1)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(3));
    model.insert("y".to_string(), SmtValue::Int(0));
    model.insert("z".to_string(), SmtValue::Int(1));

    let result = mbp.project_with_residuals(&formula, &[x.clone(), y.clone()], &model);

    // z is not being eliminated, so z = 1 must be preserved in the result.
    assert!(
        result.formula.contains_var_name(&z.name),
        "z should be retained in the projected formula: {}",
        result.formula
    );

    // z should NOT appear as a residual (it's not a projection target).
    assert!(
        !result.residual_vars.iter().any(|r| r.name == "z"),
        "z should not be in residuals"
    );

    // The result formula, with residual vars set to model values, must
    // evaluate to true under the model (soundness: underapproximation).
    assert_eq!(
        mbp.eval_bool(&result.formula, &model),
        Some(true),
        "projected formula must be satisfied by the original model"
    );

    // x and y are inside an Or and are unprojectable. They should either
    // be in residuals or fully resolved by MBQI (not silently dropped).
    let x_resolved = !result.formula.contains_var_name(&x.name);
    let y_resolved = !result.formula.contains_var_name(&y.name);
    let x_residual = result.residual_vars.iter().any(|r| r.name == "x");
    let y_residual = result.residual_vars.iter().any(|r| r.name == "y");
    assert!(
        (x_resolved || x_residual) && (y_resolved || y_residual),
        "Each projection target must be either resolved or tracked as residual.\n\
             x: resolved={}, residual={}. y: resolved={}, residual={}.\n\
             residuals: {:?}, formula: {}",
        x_resolved,
        x_residual,
        y_resolved,
        y_residual,
        result
            .residual_vars
            .iter()
            .map(|v| &v.name)
            .collect::<Vec<_>>(),
        result.formula
    );
}

#[test]
fn test_project_with_residuals_empty_vars() {
    let mbp = Mbp::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let formula = ChcExpr::gt(ChcExpr::var(x), ChcExpr::Int(0));
    let model = FxHashMap::default();

    let result = mbp.project_with_residuals(&formula, &[], &model);

    assert!(result.residual_vars.is_empty());
    assert_eq!(result.formula, formula);
}

#[test]
fn test_project_with_residuals_tracks_bool_residual_when_model_value_missing() {
    let mbp = Mbp::new();

    let b = ChcVar::new("b", ChcSort::Bool);
    let x = ChcVar::new("x", ChcSort::Int);
    let formula = ChcExpr::and(
        ChcExpr::var(b.clone()),
        ChcExpr::gt(ChcExpr::var(x), ChcExpr::Int(0)),
    );

    // Deliberately omit `b` from the model to simulate a partial model.
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));

    let result = mbp.project_with_residuals(&formula, std::slice::from_ref(&b), &model);

    assert!(
        result.residual_vars.iter().any(|v| v == &b),
        "missing Bool model value must be tracked as a residual"
    );
    assert!(
        result.formula.contains_var_name(&b.name),
        "uneliminated Bool var should remain in formula for caller handling"
    );
}

#[test]
fn test_project_with_residuals_preserves_projected_generalization() {
    let mbp = Mbp::new();

    // Formula: x = y + 1 AND ((z > 5) OR (w > 5)) AND y > 0
    // Project out x and z:
    // - x can be projected via equality (x = y + 1) → substituted away
    // - z is in an Or (unprojectable) → residual
    // Result: y + 1 > 0 AND ((z > 5) OR (w > 5)) with z as residual
    // Key: the y constraint should remain generalized (not collapsed to y=4)
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);
    let w = ChcVar::new("w", ChcSort::Int);

    let formula = ChcExpr::and(
        ChcExpr::and(
            ChcExpr::eq(
                ChcExpr::var(x.clone()),
                ChcExpr::add(ChcExpr::var(y.clone()), ChcExpr::Int(1)),
            ),
            ChcExpr::or(
                ChcExpr::gt(ChcExpr::var(z.clone()), ChcExpr::Int(5)),
                ChcExpr::gt(ChcExpr::var(w), ChcExpr::Int(5)),
            ),
        ),
        ChcExpr::gt(ChcExpr::var(y.clone()), ChcExpr::Int(0)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    model.insert("y".to_string(), SmtValue::Int(4));
    model.insert("z".to_string(), SmtValue::Int(10));
    model.insert("w".to_string(), SmtValue::Int(3));

    let result = mbp.project_with_residuals(&formula, &[x.clone(), z.clone()], &model);

    // x should be fully projected (via equality)
    assert!(
        !result.formula.contains_var_name(&x.name),
        "x should be projected away via equality"
    );
    // z should be a residual (inside Or, not projectable)
    // Unless MBQI found a term equivalent to z
    if result.formula.contains_var_name(&z.name) {
        assert!(
            result.residual_vars.iter().any(|v| v == &z),
            "z should be in residuals if still in formula"
        );
    }
    // y should still be in the formula (not being eliminated)
    assert!(
        result.formula.contains_var_name(&y.name),
        "y (not being eliminated) should remain in formula"
    );
}

#[test]
fn test_project_with_mode_distinguishes_force_and_allow_residual() {
    let mbp = Mbp::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // x*x = 4 is non-linear for x, so it cannot be projected with bound extraction.
    let formula = ChcExpr::and(
        ChcExpr::eq(
            ChcExpr::mul(ChcExpr::var(x.clone()), ChcExpr::var(x.clone())),
            ChcExpr::Int(4),
        ),
        ChcExpr::gt(ChcExpr::var(y), ChcExpr::Int(0)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(2));
    model.insert("y".to_string(), SmtValue::Int(5));

    let allow = mbp.project_with_mode(
        &formula,
        std::slice::from_ref(&x),
        &model,
        MbpMode::AllowResidual,
    );
    assert!(
        allow.residual_vars.iter().any(|v| v == &x),
        "allow-residual mode should report x as residual for non-linear atom"
    );
    assert!(
        allow.formula.contains_var_name(&x.name),
        "allow-residual mode should preserve unresolved vars in formula"
    );

    let force = mbp.project_with_mode(
        &formula,
        std::slice::from_ref(&x),
        &model,
        MbpMode::ForceSubstitute,
    );
    assert!(
        force.residual_vars.is_empty(),
        "force mode should not report residual vars"
    );
    assert!(
        !force.formula.contains_var_name(&x.name),
        "force mode should eliminate target vars via substitution fallback"
    );
    assert_eq!(
        mbp.eval_bool(&force.formula, &model),
        Some(true),
        "force mode result must remain satisfied by source model"
    );
}
