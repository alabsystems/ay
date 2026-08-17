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

include!("unit_tests/bounds_and_specialized_generalizers.rs");
