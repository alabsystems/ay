// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_extract_conjuncts() {
    // Use non-trivial expressions; and_all simplifies Bool(true)/Bool(false) away.
    let a = ChcExpr::ge(ChcExpr::int(1), ChcExpr::int(0));
    let b = ChcExpr::le(ChcExpr::int(5), ChcExpr::int(10));
    let conj = ChcExpr::and(a, b);

    let conjuncts = conj.collect_conjuncts();
    assert_eq!(conjuncts.len(), 2);
}

#[test]
fn test_build_conjunction_empty() {
    let result = ChcExpr::and_all(Vec::<ChcExpr>::new());
    assert_eq!(result, ChcExpr::Bool(true));
}

#[test]
fn test_build_conjunction_single() {
    let lit = ChcExpr::Bool(false);
    let result = ChcExpr::and_all(std::iter::once(lit.clone()));
    assert_eq!(result, lit);
}

#[test]
fn test_pipeline_empty() {
    let pipeline = GeneralizerPipeline::new();
    assert!(pipeline.generalizers.is_empty());
}

#[test]
fn test_unsat_core_extract_conjuncts() {
    // Use non-trivial expressions; and_all simplifies Bool(true)/Bool(false) away.
    let a = ChcExpr::ge(ChcExpr::int(1), ChcExpr::int(0));
    let b = ChcExpr::le(ChcExpr::int(5), ChcExpr::int(10));
    let conj = ChcExpr::and(a, b);

    let conjuncts = conj.collect_conjuncts();
    assert_eq!(conjuncts.len(), 2);
}

#[test]
fn test_unsat_core_build_conjunction_empty() {
    let result = ChcExpr::and_all(Vec::<ChcExpr>::new());
    assert_eq!(result, ChcExpr::Bool(true));
}

#[test]
fn test_unsat_core_build_conjunction_single() {
    let lit = ChcExpr::Bool(false);
    let result = ChcExpr::and_all(std::iter::once(lit.clone()));
    assert_eq!(result, lit);
}

#[test]
fn test_unsat_core_generalizer_name() {
    let g = UnsatCoreGeneralizer::new();
    assert_eq!(g.name(), "unsat-core");
}

#[test]
fn test_relevant_variable_projection_generalizer_name() {
    let g = RelevantVariableProjectionGeneralizer::new();
    assert_eq!(g.name(), "relevant-variable-projection");
}

#[test]
fn test_relevant_variable_is_point_assignment() {
    use crate::expr::{ChcSort, ChcVar};

    // x = 5 is a point assignment
    let x = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
    let eq = ChcExpr::eq(x.clone(), ChcExpr::int(5));
    assert!(RelevantVariableProjectionGeneralizer::is_point_assignment(
        &eq
    ));

    // 5 = x is also a point assignment (reversed)
    let eq_rev = ChcExpr::eq(ChcExpr::int(5), x.clone());
    assert!(RelevantVariableProjectionGeneralizer::is_point_assignment(
        &eq_rev
    ));

    // x < 5 is NOT a point assignment
    let lt = ChcExpr::lt(x.clone(), ChcExpr::int(5));
    assert!(!RelevantVariableProjectionGeneralizer::is_point_assignment(
        &lt
    ));

    // x = y is NOT a point assignment (both sides are variables)
    let y = ChcExpr::Var(ChcVar::new("y", ChcSort::Int));
    let eq_vars = ChcExpr::eq(x, y);
    assert!(!RelevantVariableProjectionGeneralizer::is_point_assignment(
        &eq_vars
    ));

    // Boolean variable is a point assignment
    let b = ChcExpr::Var(ChcVar::new("b", ChcSort::Bool));
    assert!(RelevantVariableProjectionGeneralizer::is_point_assignment(
        &b
    ));

    // NOT(boolean variable) is a point assignment
    let not_b = ChcExpr::not(b);
    assert!(RelevantVariableProjectionGeneralizer::is_point_assignment(
        &not_b
    ));
}

#[test]
fn test_relevant_variable_is_constant() {
    use crate::expr::{ChcSort, ChcVar};

    // Literals are constants
    assert!(RelevantVariableProjectionGeneralizer::is_constant(
        &ChcExpr::int(5)
    ));
    assert!(RelevantVariableProjectionGeneralizer::is_constant(
        &ChcExpr::Bool(true)
    ));

    // Variables are not constants
    let x = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
    assert!(!RelevantVariableProjectionGeneralizer::is_constant(&x));

    // Expressions with variables are not constants
    let add = ChcExpr::add(x, ChcExpr::int(1));
    assert!(!RelevantVariableProjectionGeneralizer::is_constant(&add));

    // Expressions with only literals are constants
    let add_lit = ChcExpr::add(ChcExpr::int(1), ChcExpr::int(2));
    assert!(RelevantVariableProjectionGeneralizer::is_constant(&add_lit));
}

#[test]
fn test_relevant_variable_extract_conjuncts() {
    use crate::expr::{ChcSort, ChcVar};

    let x = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::Var(ChcVar::new("y", ChcSort::Int));
    let x_eq_5 = ChcExpr::eq(x, ChcExpr::int(5));
    let y_eq_3 = ChcExpr::eq(y, ChcExpr::int(3));
    let conj = ChcExpr::and(x_eq_5.clone(), y_eq_3.clone());

    let conjuncts = conj.collect_conjuncts();
    assert_eq!(conjuncts.len(), 2);
    assert!(conjuncts.contains(&x_eq_5));
    assert!(conjuncts.contains(&y_eq_3));
}

#[test]
fn test_literal_weakening_generalizer_name() {
    let g = LiteralWeakeningGeneralizer::new();
    assert_eq!(g.name(), "literal-weakening");
}

#[test]
fn test_literal_weakening_is_arithmetic() {
    use crate::expr::{ChcSort, ChcVar};

    // Int variable is arithmetic
    let x = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
    assert!(LiteralWeakeningGeneralizer::is_arithmetic(&x));

    // Real variable is arithmetic
    let y = ChcExpr::Var(ChcVar::new("y", ChcSort::Real));
    assert!(LiteralWeakeningGeneralizer::is_arithmetic(&y));

    // Bool variable is not arithmetic
    let b = ChcExpr::Var(ChcVar::new("b", ChcSort::Bool));
    assert!(!LiteralWeakeningGeneralizer::is_arithmetic(&b));

    // Arithmetic operations are arithmetic
    let add = ChcExpr::add(x, ChcExpr::int(1));
    assert!(LiteralWeakeningGeneralizer::is_arithmetic(&add));
}

#[test]
fn test_literal_weakening_generate_weakenings_equality() {
    use crate::expr::{ChcSort, ChcVar};

    let g = LiteralWeakeningGeneralizer::new();

    // x = 5 (arithmetic equality)
    let x = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
    let five = ChcExpr::int(5);
    let eq = ChcExpr::eq(x.clone(), five.clone());

    let weakenings = g.generate_weakenings(&eq);
    assert_eq!(weakenings.len(), 2);

    // Should produce x <= 5 and 5 <= x
    let x_le_5 = ChcExpr::le(x.clone(), five.clone());
    let five_le_x = ChcExpr::le(five, x);

    assert!(weakenings.contains(&x_le_5));
    assert!(weakenings.contains(&five_le_x));
}

#[test]
fn test_literal_weakening_no_weakening_for_bool() {
    use crate::expr::{ChcSort, ChcVar};

    let g = LiteralWeakeningGeneralizer::new();

    // b = true (boolean equality, should not weaken)
    let b = ChcExpr::Var(ChcVar::new("b", ChcSort::Bool));
    let t = ChcExpr::Bool(true);
    let eq = ChcExpr::eq(b, t);

    let weakenings = g.generate_weakenings(&eq);
    assert!(weakenings.is_empty());
}

#[test]
fn test_literal_weakening_no_weakening_for_inequality() {
    use crate::expr::{ChcSort, ChcVar};

    let g = LiteralWeakeningGeneralizer::new();

    // x < 5 (already an inequality, no weakening needed)
    let x = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
    let five = ChcExpr::int(5);
    let lt = ChcExpr::lt(x, five);

    let weakenings = g.generate_weakenings(&lt);
    assert!(weakenings.is_empty());
}

#[test]
fn test_literal_weakening_no_weakening_for_modulo() {
    use crate::expr::{ChcSort, ChcVar};

    let g = LiteralWeakeningGeneralizer::new();

    // (x mod 3) = 0 - should NOT weaken (per Z3's expand_literals, #169)
    let x = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
    let mod_expr = ChcExpr::mod_op(x.clone(), ChcExpr::int(3));
    let eq_mod = ChcExpr::eq(mod_expr, ChcExpr::int(0));

    let weakenings = g.generate_weakenings(&eq_mod);
    assert!(
        weakenings.is_empty(),
        "modulo equalities should not be weakened"
    );

    // Also test: x = (y mod 2) - RHS is modulo
    let y = ChcExpr::Var(ChcVar::new("y", ChcSort::Int));
    let mod_y = ChcExpr::mod_op(y, ChcExpr::int(2));
    let eq_mod_rhs = ChcExpr::eq(x, mod_y);

    let weakenings_rhs = g.generate_weakenings(&eq_mod_rhs);
    assert!(
        weakenings_rhs.is_empty(),
        "equalities with modulo on RHS should not be weakened"
    );
}

#[test]
fn test_literal_weakening_is_modulo() {
    use crate::expr::{ChcSort, ChcVar};

    let x = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));

    // x mod 3 is a modulo expression
    let mod_expr = ChcExpr::mod_op(x.clone(), ChcExpr::int(3));
    assert!(LiteralWeakeningGeneralizer::is_modulo(&mod_expr));

    // x + 3 is NOT a modulo expression
    let add_expr = ChcExpr::add(x.clone(), ChcExpr::int(3));
    assert!(!LiteralWeakeningGeneralizer::is_modulo(&add_expr));

    // variable is NOT a modulo expression
    assert!(!LiteralWeakeningGeneralizer::is_modulo(&x));
}

#[test]
fn test_literal_weakening_extract_conjuncts() {
    use crate::expr::{ChcSort, ChcVar};

    let x = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::Var(ChcVar::new("y", ChcSort::Int));

    // x >= 0 AND y >= 0
    let x_ge_0 = ChcExpr::ge(x, ChcExpr::int(0));
    let y_ge_0 = ChcExpr::ge(y, ChcExpr::int(0));
    let conj = ChcExpr::and(x_ge_0.clone(), y_ge_0.clone());

    let conjuncts = conj.collect_conjuncts();
    assert_eq!(conjuncts.len(), 2);
    assert!(conjuncts.contains(&x_ge_0));
    assert!(conjuncts.contains(&y_ge_0));
}

#[test]
fn test_literal_weakening_build_conjunction() {
    use crate::expr::{ChcSort, ChcVar};

    let x = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
    let x_ge_0 = ChcExpr::ge(x.clone(), ChcExpr::int(0));
    let x_le_10 = ChcExpr::le(x, ChcExpr::int(10));

    // Empty
    let empty = ChcExpr::and_all(Vec::<ChcExpr>::new());
    assert_eq!(empty, ChcExpr::Bool(true));

    // Single
    let single = ChcExpr::and_all(std::iter::once(x_ge_0.clone()));
    assert_eq!(single, x_ge_0);

    // Multiple
    let multi = ChcExpr::and_all([x_ge_0.clone(), x_le_10.clone()]);
    let expected = ChcExpr::and(x_ge_0, x_le_10);
    assert_eq!(multi, expected);
}

#[test]
fn test_bound_expansion_generalizer_name() {
    let g = BoundExpansionGeneralizer::new();
    assert_eq!(g.name(), "bound-expansion");
}

#[test]
fn test_bound_expansion_default_max_distance() {
    let g = BoundExpansionGeneralizer::new();
    assert_eq!(g.max_search_distance, 1000);
}

#[test]
fn test_bound_expansion_extract_conjuncts() {
    use crate::expr::{ChcSort, ChcVar};

    let x = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::Var(ChcVar::new("y", ChcSort::Int));

    // x < 5 AND y > 3
    let x_lt_5 = ChcExpr::lt(x, ChcExpr::int(5));
    let y_gt_3 = ChcExpr::gt(y, ChcExpr::int(3));
    let conj = ChcExpr::and(x_lt_5.clone(), y_gt_3.clone());

    let conjuncts = conj.collect_conjuncts();
    assert_eq!(conjuncts.len(), 2);
    assert!(conjuncts.contains(&x_lt_5));
    assert!(conjuncts.contains(&y_gt_3));
}

#[test]
fn test_bound_expansion_build_conjunction() {
    use crate::expr::{ChcSort, ChcVar};

    let x = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
    let x_lt_5 = ChcExpr::lt(x.clone(), ChcExpr::int(5));
    let x_gt_0 = ChcExpr::gt(x, ChcExpr::int(0));

    // Empty
    let empty = ChcExpr::and_all(Vec::<ChcExpr>::new());
    assert_eq!(empty, ChcExpr::Bool(true));

    // Single
    let single = ChcExpr::and_all(std::iter::once(x_lt_5.clone()));
    assert_eq!(single, x_lt_5);

    // Multiple
    let multi = ChcExpr::and_all([x_lt_5.clone(), x_gt_0.clone()]);
    let expected = ChcExpr::and(x_lt_5, x_gt_0);
    assert_eq!(multi, expected);
}

#[test]
fn test_bound_expansion_default() {
    let g = BoundExpansionGeneralizer::default();
    assert_eq!(g.max_search_distance, 1000);
}

#[test]
fn test_init_bounds_exact() {
    let b = InitBounds::exact(42);
    assert_eq!(b.min, 42);
    assert_eq!(b.max, 42);
    assert!(b.is_exact());
    assert!(b.contains(42));
    assert!(!b.contains(41));
    assert!(!b.contains(43));
}

#[test]
fn test_init_bounds_range() {
    let b = InitBounds::range(10, 20);
    assert_eq!(b.min, 10);
    assert_eq!(b.max, 20);
    assert!(!b.is_exact());
    assert!(b.contains(10));
    assert!(b.contains(15));
    assert!(b.contains(20));
    assert!(!b.contains(9));
    assert!(!b.contains(21));
}

#[test]
fn test_init_bounds_unbounded() {
    let b = InitBounds::unbounded();
    assert_eq!(b.min, i64::MIN);
    assert_eq!(b.max, i64::MAX);
    assert!(b.contains(0));
    assert!(b.contains(i64::MAX));
    assert!(b.contains(i64::MIN));
}

#[test]
fn test_init_bound_weakening_generalizer_name() {
    let g = InitBoundWeakeningGeneralizer::new();
    assert_eq!(g.name(), "init-bound-weakening");
}

#[test]
fn test_init_bound_weakening_extract_equality() {
    use crate::expr::{ChcSort, ChcVar};

    // x = 5
    let x = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
    let eq = ChcExpr::eq(x.clone(), ChcExpr::int(5));
    let result = eq.extract_var_int_equality().map(|(v, c)| (v.name, c));
    assert_eq!(result, Some(("x".to_string(), 5)));

    // 5 = x (reversed order)
    let eq_rev = ChcExpr::eq(ChcExpr::int(5), x.clone());
    let result_rev = eq_rev.extract_var_int_equality().map(|(v, c)| (v.name, c));
    assert_eq!(result_rev, Some(("x".to_string(), 5)));

    // x < 5 (not an equality)
    let lt = ChcExpr::lt(x, ChcExpr::int(5));
    let result_lt = lt.extract_var_int_equality();
    assert_eq!(result_lt, None);
}

#[test]
fn test_init_bound_weakening_try_weaken() {
    use crate::expr::{ChcSort, ChcVar};

    let g = InitBoundWeakeningGeneralizer::new();
    let mut init_bounds = HashMap::default();
    init_bounds.insert("x".to_string(), InitBounds::exact(0));

    // x = -5 (below init) should weaken to x < 0
    let x = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
    let eq_below = ChcExpr::eq(x.clone(), ChcExpr::int(-5));
    let weakened = g.try_weaken(&eq_below, &init_bounds);
    assert!(weakened.is_some());
    let expected = ChcExpr::lt(x.clone(), ChcExpr::int(0));
    assert_eq!(weakened.unwrap(), expected);

    // x = 5 (above init) should NOT be weakened
    let eq_above = ChcExpr::eq(x.clone(), ChcExpr::int(5));
    let not_weakened = g.try_weaken(&eq_above, &init_bounds);
    assert!(not_weakened.is_none());

    // x = 0 (at init) should NOT be weakened
    let eq_at = ChcExpr::eq(x, ChcExpr::int(0));
    let not_weakened_at = g.try_weaken(&eq_at, &init_bounds);
    assert!(not_weakened_at.is_none());
}

#[test]
fn test_init_bound_weakening_default() {
    let g = InitBoundWeakeningGeneralizer;
    assert_eq!(g.name(), "init-bound-weakening");
}

#[test]
fn test_single_variable_range_generalizer_name() {
    let g = SingleVariableRangeGeneralizer::new();
    assert_eq!(g.name(), "single-variable-range");
}

#[test]
fn test_single_variable_range_default() {
    let g = SingleVariableRangeGeneralizer;
    assert_eq!(g.name(), "single-variable-range");
}

#[test]
fn test_single_variable_range_extract_equality() {
    use crate::expr::{ChcSort, ChcVar};

    // x = 5
    let x = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
    let eq = ChcExpr::eq(x.clone(), ChcExpr::int(5));
    let result = eq.extract_var_int_equality().map(|(v, c)| (v.name, c));
    assert_eq!(result, Some(("x".to_string(), 5)));

    // x < 5 (not an equality)
    let lt = ChcExpr::lt(x, ChcExpr::int(5));
    let result_lt = lt.extract_var_int_equality();
    assert_eq!(result_lt, None);
}

#[test]
fn test_farkas_generalizer_name() {
    let g = FarkasGeneralizer::new();
    assert_eq!(g.name(), "farkas-combination");
}

#[test]
fn test_farkas_generalizer_default() {
    let g = FarkasGeneralizer;
    assert_eq!(g.name(), "farkas-combination");
}

#[test]
fn test_denominator_simplification_generalizer_name() {
    let g = DenominatorSimplificationGeneralizer::new();
    assert_eq!(g.name(), "denominator-simplification");
}

#[test]
fn test_farkas_generalizer_extract_conjuncts() {
    use crate::expr::{ChcSort, ChcVar};

    let x = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::Var(ChcVar::new("y", ChcSort::Int));

    // x <= 5 AND y >= 3
    let x_le_5 = ChcExpr::le(x, ChcExpr::int(5));
    let y_ge_3 = ChcExpr::ge(y, ChcExpr::int(3));
    let conj = ChcExpr::and(x_le_5.clone(), y_ge_3.clone());

    let conjuncts = conj.collect_conjuncts();
    assert_eq!(conjuncts.len(), 2);
    assert!(conjuncts.contains(&x_le_5));
    assert!(conjuncts.contains(&y_ge_3));
}
use crate::expr::{ChcSort, ChcVar};

// ConstantSumGeneralizer tests
#[test]
fn test_constant_sum_generalizer_name() {
    let g = ConstantSumGeneralizer::new();
    assert_eq!(g.name(), "constant-sum");
}

#[test]
fn test_constant_sum_generalizer_default() {
    let g = ConstantSumGeneralizer;
    assert_eq!(g.name(), "constant-sum");
}

#[test]
fn test_constant_sum_extract_equality() {
    // x = 5
    let x = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
    let eq = ChcExpr::eq(x.clone(), ChcExpr::int(5));
    let result = eq.extract_var_int_equality().map(|(v, c)| (v.name, c));
    assert_eq!(result, Some(("x".to_string(), 5)));

    // 5 = x (reversed order)
    let eq_rev = ChcExpr::eq(ChcExpr::int(5), x.clone());
    let result_rev = eq_rev.extract_var_int_equality().map(|(v, c)| (v.name, c));
    assert_eq!(result_rev, Some(("x".to_string(), 5)));

    // x < 5 (not an equality)
    let lt = ChcExpr::lt(x, ChcExpr::int(5));
    let result_lt = lt.extract_var_int_equality();
    assert_eq!(result_lt, None);
}

#[test]
fn test_constant_sum_extract_conjuncts() {
    let x = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::Var(ChcVar::new("y", ChcSort::Int));

    // x = 5 AND y = 3
    let x_eq_5 = ChcExpr::eq(x, ChcExpr::int(5));
    let y_eq_3 = ChcExpr::eq(y, ChcExpr::int(3));
    let conj = ChcExpr::and(x_eq_5.clone(), y_eq_3.clone());

    let conjuncts = conj.collect_conjuncts();
    assert_eq!(conjuncts.len(), 2);
    assert!(conjuncts.contains(&x_eq_5));
    assert!(conjuncts.contains(&y_eq_3));
}

// RelationalEqualityGeneralizer tests
#[test]
fn test_relational_equality_generalizer_name() {
    let g = RelationalEqualityGeneralizer::new();
    assert_eq!(g.name(), "relational-equality");
}

#[test]
fn test_relational_equality_generalizer_default() {
    let g = RelationalEqualityGeneralizer::default();
    assert_eq!(g.name(), "relational-equality");
}

#[test]
fn test_relational_equality_extract_equality() {
    // x = 5
    let x = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
    let eq = ChcExpr::eq(x.clone(), ChcExpr::int(5));
    let result = eq.extract_var_int_equality().map(|(v, c)| (v.name, c));
    assert_eq!(result, Some(("x".to_string(), 5)));

    // x < 5 (not an equality)
    let lt = ChcExpr::lt(x, ChcExpr::int(5));
    let result_lt = lt.extract_var_int_equality();
    assert_eq!(result_lt, None);
}

#[test]
fn test_relational_equality_extract_conjuncts() {
    let x = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::Var(ChcVar::new("y", ChcSort::Int));

    // x = 5 AND y = 3
    let x_eq_5 = ChcExpr::eq(x, ChcExpr::int(5));
    let y_eq_3 = ChcExpr::eq(y, ChcExpr::int(3));
    let conj = ChcExpr::and(x_eq_5, y_eq_3);

    let conjuncts = conj.collect_conjuncts();
    assert_eq!(conjuncts.len(), 2);
}

#[test]
fn test_relational_equality_build_conjunction() {
    let x = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
    let x_ge_0 = ChcExpr::ge(x.clone(), ChcExpr::int(0));
    let x_le_10 = ChcExpr::le(x, ChcExpr::int(10));

    // Empty
    let empty = ChcExpr::and_all(Vec::<ChcExpr>::new());
    assert_eq!(empty, ChcExpr::Bool(true));

    // Single
    let single = ChcExpr::and_all(std::iter::once(x_ge_0.clone()));
    assert_eq!(single, x_ge_0);

    // Multiple
    let multi = ChcExpr::and_all([x_ge_0.clone(), x_le_10.clone()]);
    let expected = ChcExpr::and(x_ge_0, x_le_10);
    assert_eq!(multi, expected);
}

// ImplicationGeneralizer tests
#[test]
fn test_implication_generalizer_name() {
    let g = ImplicationGeneralizer::new();
    assert_eq!(g.name(), "implication");
}

#[test]
fn test_implication_generalizer_default() {
    let g = ImplicationGeneralizer::default();
    assert_eq!(g.name(), "implication");
    assert_eq!(g.min_range_gap, 3);
}

#[test]
fn test_implication_extract_equality() {
    // pc = 2
    let pc = ChcExpr::Var(ChcVar::new("pc", ChcSort::Int));
    let eq = ChcExpr::eq(pc.clone(), ChcExpr::int(2));
    let result = eq.extract_var_int_equality().map(|(v, c)| (v.name, c));
    assert_eq!(result, Some(("pc".to_string(), 2)));

    // lock != 0 (not an equality)
    let ne = ChcExpr::ne(pc, ChcExpr::int(0));
    let result_ne = ne.extract_var_int_equality();
    assert_eq!(result_ne, None);
}

#[test]
fn test_implication_extract_conjuncts() {
    let pc = ChcExpr::Var(ChcVar::new("pc", ChcSort::Int));
    let lock = ChcExpr::Var(ChcVar::new("lock", ChcSort::Int));

    // pc = 2 AND lock = 0
    let pc_eq_2 = ChcExpr::eq(pc, ChcExpr::int(2));
    let lock_eq_0 = ChcExpr::eq(lock, ChcExpr::int(0));
    let conj = ChcExpr::and(pc_eq_2.clone(), lock_eq_0.clone());

    let conjuncts = conj.collect_conjuncts();
    assert_eq!(conjuncts.len(), 2);
    assert!(conjuncts.contains(&pc_eq_2));
    assert!(conjuncts.contains(&lock_eq_0));
}

#[test]
fn test_implication_build_conjunction() {
    let pc = ChcExpr::Var(ChcVar::new("pc", ChcSort::Int));
    let pc_eq_2 = ChcExpr::eq(pc.clone(), ChcExpr::int(2));
    let pc_eq_1 = ChcExpr::eq(pc, ChcExpr::int(1));

    // Empty
    let empty = ChcExpr::and_all(Vec::<ChcExpr>::new());
    assert_eq!(empty, ChcExpr::Bool(true));

    // Single
    let single = ChcExpr::and_all(std::iter::once(pc_eq_2.clone()));
    assert_eq!(single, pc_eq_2);

    // Multiple
    let multi = ChcExpr::and_all([pc_eq_2.clone(), pc_eq_1.clone()]);
    let expected = ChcExpr::and(pc_eq_2, pc_eq_1);
    assert_eq!(multi, expected);
}
