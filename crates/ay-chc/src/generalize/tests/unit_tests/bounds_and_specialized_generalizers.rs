// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `generalize::tests::unit_tests` to preserve test FQNs.

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
