// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Array store projection and array equality dropping generalizers for CHC PDR lemmas.
//!
//! Two complementary generalizers for array-heavy CHC problems:
//!
//! ## `ArrayStoreProjectionGeneralizer`
//!
//! Weakens `(= arr (store arr' i v))` conjuncts to `(= (select arr i) v)`,
//! a "point projection" that retains the key semantic information (the value
//! written at index `i`) while eliminating the full array equality constraint.
//!
//! Full array equality is much harder for PDR to generalize because it
//! constrains every element of the array simultaneously. Point projection
//! reduces this to a scalar constraint on a single element.
//!
//! Reference: Z3 Spacer's quantifier generalizer pattern where array stores
//! are projected to selects for lemma weakening.
//! `reference/z3/src/muz/spacer/spacer_quant_generalizer.cpp`
//!
//! ## `ArrayEqualityDropGeneralizer`
//!
//! Aggressively drops any conjunct that contains an array-sorted equality
//! (either `(= arr1 arr2)` where both sides have Array sort, or `(= arr (store ...))`),
//! checking inductiveness after each removal. This is more aggressive than
//! `ArraySelectIndexGeneralizer` which only targets `select(arr, idx) = val`
//! patterns.
//!
//! For problems with >=2 Array-sorted parameters, array equalities are often
//! the main obstacle to lemma generalization. Removing them (when inductiveness
//! is preserved) dramatically reduces the search space.

use std::sync::Arc;

use super::{LemmaGeneralizer, TransitionSystemRef};
use crate::expr::{ChcExpr, ChcOp, ChcSort};

/// Weakens `(= arr (store arr' i v))` to `(= (select arr i) v)`.
///
/// This "point projection" retains only the specific element written by the
/// store operation, discarding the full array equality constraint. The weaker
/// conjunct is kept only if the resulting lemma is still inductive.
///
/// # Algorithm
///
/// For each conjunct of the form `(= arr (store arr' i v))` or
/// `(= (store arr' i v) arr)`:
/// 1. Construct the weakened conjunct: `(= (select arr i) v)`
/// 2. Replace the original conjunct with the weakened version
/// 3. Check inductiveness
/// 4. If inductive, keep the weaker version; otherwise restore the original
///
/// # Why This Helps
///
/// model-checker-consumer (Rust verification tool) generates CHC problems where heap operations
/// become `store` chains. A typical lemma might contain:
/// ```text
/// (and (= heap' (store heap 42 7))
///      (= x 5)
///      (>= y 0))
/// ```
/// The full array equality `(= heap' (store heap 42 7))` prevents generalization
/// because it constrains ALL indices of heap'. After point projection:
/// ```text
/// (and (= (select heap' 42) 7)
///      (= x 5)
///      (>= y 0))
/// ```
/// Now only index 42 is constrained, and the drop-literal generalizer can
/// potentially remove even that if it's not needed for inductiveness.
pub(crate) struct ArrayStoreProjectionGeneralizer;

impl Default for ArrayStoreProjectionGeneralizer {
    fn default() -> Self {
        Self::new()
    }
}

impl ArrayStoreProjectionGeneralizer {
    pub(crate) fn new() -> Self {
        Self
    }

    /// Check if an expression is `(= arr (store arr' i v))` or `(= (store arr' i v) arr)`.
    ///
    /// Returns `Some((arr, idx, val))` where:
    /// - `arr` is the LHS of the equality (the result array)
    /// - `idx` is the store index
    /// - `val` is the stored value
    fn extract_store_equality(expr: &ChcExpr) -> Option<(ChcExpr, ChcExpr, ChcExpr)> {
        let ChcExpr::Op(ChcOp::Eq, args) = expr else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }

        let lhs = args[0].as_ref();
        let rhs = args[1].as_ref();

        // Pattern: (= arr (store arr' i v))
        if let Some((arr, idx, val)) = Self::extract_store(rhs) {
            if matches!(lhs.sort(), ChcSort::Array(_, _)) {
                return Some((lhs.clone(), idx, val));
            }
            // LHS array might be the store target itself
            return Some((arr, idx, val));
        }

        // Pattern: (= (store arr' i v) arr)
        if let Some((arr, idx, val)) = Self::extract_store(lhs) {
            if matches!(rhs.sort(), ChcSort::Array(_, _)) {
                return Some((rhs.clone(), idx, val));
            }
            return Some((arr, idx, val));
        }

        None
    }

    /// Extract `(store arr idx val)` components.
    fn extract_store(expr: &ChcExpr) -> Option<(ChcExpr, ChcExpr, ChcExpr)> {
        let ChcExpr::Op(ChcOp::Store, args) = expr else {
            return None;
        };
        if args.len() != 3 {
            return None;
        }
        Some((
            args[0].as_ref().clone(),
            args[1].as_ref().clone(),
            args[2].as_ref().clone(),
        ))
    }

    /// Create a point projection: `(= (select arr idx) val)`.
    fn make_point_select(arr: &ChcExpr, idx: &ChcExpr, val: &ChcExpr) -> ChcExpr {
        ChcExpr::eq(ChcExpr::select(arr.clone(), idx.clone()), val.clone())
    }
}

impl LemmaGeneralizer for ArrayStoreProjectionGeneralizer {
    fn generalize(
        &self,
        formula: &ChcExpr,
        level: u32,
        system: &mut dyn TransitionSystemRef,
    ) -> ChcExpr {
        if !formula.contains_array_ops() {
            return formula.clone();
        }

        let conjuncts = formula.collect_conjuncts();
        if conjuncts.len() <= 1 {
            return formula.clone();
        }

        // Find store equality conjuncts and try to weaken them
        let mut result_conjuncts = conjuncts.clone();
        let mut changed = false;

        for (i, conjunct) in conjuncts.iter().enumerate() {
            if let Some((arr, idx, val)) = Self::extract_store_equality(conjunct) {
                let weakened = Self::make_point_select(&arr, &idx, &val);

                // Build candidate with weakened conjunct
                let mut candidate: Vec<ChcExpr> = result_conjuncts
                    .iter()
                    .enumerate()
                    .map(|(j, c)| if j == i { weakened.clone() } else { c.clone() })
                    .collect();

                let candidate_expr = ChcExpr::and_all(candidate.iter().cloned());
                if system.check_inductive(&candidate_expr, level) {
                    result_conjuncts[i] = weakened;
                    changed = true;
                } else {
                    // Try dropping the conjunct entirely instead
                    candidate = result_conjuncts
                        .iter()
                        .enumerate()
                        .filter(|(j, _)| *j != i)
                        .map(|(_, c)| c.clone())
                        .collect();

                    if !candidate.is_empty() {
                        let drop_expr = ChcExpr::and_all(candidate.iter().cloned());
                        if system.check_inductive(&drop_expr, level) {
                            // Mark as dropped by replacing with Bool(true)
                            result_conjuncts[i] = ChcExpr::Bool(true);
                            changed = true;
                        }
                    }
                }
            }
        }

        if !changed {
            return formula.clone();
        }

        // Filter out Bool(true) placeholders and rebuild
        let final_conjuncts: Vec<ChcExpr> = result_conjuncts
            .into_iter()
            .filter(|c| !matches!(c, ChcExpr::Bool(true)))
            .collect();

        if final_conjuncts.is_empty() {
            formula.clone()
        } else {
            ChcExpr::and_all(final_conjuncts)
        }
    }

    fn name(&self) -> &'static str {
        "array-store-projection"
    }
}

/// Drops conjuncts containing array-sorted equalities when inductiveness holds.
///
/// This is more aggressive than `ArraySelectIndexGeneralizer`: it targets ANY
/// conjunct where both sides of an equality have Array sort, not just
/// `select(arr, idx) = val` patterns.
///
/// # Patterns Matched
///
/// - `(= arr1 arr2)` where both arr1, arr2 have Array sort
/// - `(= arr (store ...))` — full array equality from store operations
/// - `(= (store ...) arr)` — same, reversed
/// - `(= arr (const_array ...))` — equality with constant array
///
/// # Algorithm
///
/// 1. First try dropping ALL array equality conjuncts at once
/// 2. If that fails, try dropping them one at a time (greedy)
///
/// This mirrors the strategy in `ArraySelectIndexGeneralizer` but for a
/// broader class of array constraints.
pub(crate) struct ArrayEqualityDropGeneralizer;

impl Default for ArrayEqualityDropGeneralizer {
    fn default() -> Self {
        Self::new()
    }
}

impl ArrayEqualityDropGeneralizer {
    pub(crate) fn new() -> Self {
        Self
    }

    /// Check if a conjunct is an array-sorted equality.
    ///
    /// Returns true for `(= e1 e2)` where either side has Array sort,
    /// or where either side is a store/const-array expression.
    fn is_array_equality(expr: &ChcExpr) -> bool {
        let ChcExpr::Op(ChcOp::Eq, args) = expr else {
            return false;
        };
        if args.len() != 2 {
            return false;
        }

        let lhs = args[0].as_ref();
        let rhs = args[1].as_ref();

        // Check if either side has Array sort
        matches!(lhs.sort(), ChcSort::Array(_, _)) || matches!(rhs.sort(), ChcSort::Array(_, _))
    }

    /// Check if a conjunct references array operations (store, select, const-array)
    /// but is NOT a simple select equality (those are handled by ArraySelectIndexGeneralizer).
    fn is_complex_array_conjunct(expr: &ChcExpr) -> bool {
        // First check for array equality
        if Self::is_array_equality(expr) {
            return true;
        }

        // Also check for negated array equalities: (not (= arr1 arr2))
        if let ChcExpr::Op(ChcOp::Not, args) = expr {
            if args.len() == 1 && Self::is_array_equality(args[0].as_ref()) {
                return true;
            }
        }

        // Check for distinct with array args: (not (= arr1 arr2))
        if let ChcExpr::Op(ChcOp::Ne, args) = expr {
            if args.len() == 2 {
                let lhs = args[0].as_ref();
                let rhs = args[1].as_ref();
                if matches!(lhs.sort(), ChcSort::Array(_, _))
                    || matches!(rhs.sort(), ChcSort::Array(_, _))
                {
                    return true;
                }
            }
        }

        false
    }
}

impl LemmaGeneralizer for ArrayEqualityDropGeneralizer {
    fn generalize(
        &self,
        formula: &ChcExpr,
        level: u32,
        system: &mut dyn TransitionSystemRef,
    ) -> ChcExpr {
        if !formula.contains_array_ops() {
            return formula.clone();
        }

        let conjuncts = formula.collect_conjuncts();
        if conjuncts.len() <= 1 {
            return formula.clone();
        }

        // Identify array equality conjuncts
        let array_eq_indices: Vec<usize> = conjuncts
            .iter()
            .enumerate()
            .filter_map(|(i, c)| Self::is_complex_array_conjunct(c).then_some(i))
            .collect();

        if array_eq_indices.is_empty() {
            return formula.clone();
        }

        // Strategy 1: Try dropping ALL array equality conjuncts at once
        let non_array_conjuncts: Vec<ChcExpr> = conjuncts
            .iter()
            .enumerate()
            .filter(|(i, _)| !array_eq_indices.contains(i))
            .map(|(_, c)| c.clone())
            .collect();

        if !non_array_conjuncts.is_empty() {
            let candidate = ChcExpr::and_all(non_array_conjuncts.iter().cloned());
            if system.check_inductive(&candidate, level) {
                return candidate;
            }
        }

        // Strategy 2: Try dropping array equality conjuncts one at a time (greedy)
        let mut kept = vec![true; conjuncts.len()];
        let mut changed = false;

        for &idx in &array_eq_indices {
            let candidate: Vec<ChcExpr> = conjuncts
                .iter()
                .enumerate()
                .filter(|(j, _)| kept[*j] && *j != idx)
                .map(|(_, c)| c.clone())
                .collect();

            if candidate.is_empty() {
                continue;
            }

            let candidate_expr = ChcExpr::and_all(candidate.iter().cloned());
            if system.check_inductive(&candidate_expr, level) {
                kept[idx] = false;
                changed = true;
            }
        }

        if !changed {
            return formula.clone();
        }

        let result: Vec<ChcExpr> = conjuncts
            .iter()
            .enumerate()
            .filter(|(i, _)| kept[*i])
            .map(|(_, c)| c.clone())
            .collect();

        if result.is_empty() {
            formula.clone()
        } else {
            ChcExpr::and_all(result)
        }
    }

    fn name(&self) -> &'static str {
        "array-equality-drop"
    }
}

/// Select value weakening generalizer: weakens `(= (select arr i) c)` to
/// range constraints like `(>= (select arr i) lo)` and `(<= (select arr i) hi)`.
///
/// When a point select equality `(= (select arr i) 42)` is not needed for
/// inductiveness, but a bound on the value is, this generalizer finds the
/// weakest inductive bound.
///
/// # Algorithm
///
/// For each `(= (select arr i) c)` conjunct where c is a constant:
/// 1. Try dropping it entirely (handled by ArraySelectIndexGeneralizer)
/// 2. If that fails, try weakening to `(>= (select arr i) c)` (lower bound)
/// 3. If that fails, try weakening to `(<= (select arr i) c)` (upper bound)
///
/// This bridges the gap between "must keep exact value" and "can drop entirely".
pub(crate) struct ArraySelectValueWeakeningGeneralizer;

impl Default for ArraySelectValueWeakeningGeneralizer {
    fn default() -> Self {
        Self::new()
    }
}

impl ArraySelectValueWeakeningGeneralizer {
    pub(crate) fn new() -> Self {
        Self
    }

    /// Extract `(= (select arr i) c)` or `(= c (select arr i))` where c is a constant.
    ///
    /// Returns `Some((select_expr, constant_value))`.
    fn extract_select_const_equality(expr: &ChcExpr) -> Option<(ChcExpr, i64)> {
        let ChcExpr::Op(ChcOp::Eq, args) = expr else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }

        let lhs = args[0].as_ref();
        let rhs = args[1].as_ref();

        // Pattern: (= (select arr i) c)
        if Self::is_select(lhs) {
            if let Some(c) = rhs.as_i64() {
                return Some((lhs.clone(), c));
            }
        }

        // Pattern: (= c (select arr i))
        if Self::is_select(rhs) {
            if let Some(c) = lhs.as_i64() {
                return Some((rhs.clone(), c));
            }
        }

        None
    }

    fn is_select(expr: &ChcExpr) -> bool {
        matches!(expr, ChcExpr::Op(ChcOp::Select, args) if args.len() == 2)
    }
}

impl LemmaGeneralizer for ArraySelectValueWeakeningGeneralizer {
    fn generalize(
        &self,
        formula: &ChcExpr,
        level: u32,
        system: &mut dyn TransitionSystemRef,
    ) -> ChcExpr {
        if !formula.contains_array_ops() {
            return formula.clone();
        }

        let conjuncts = formula.collect_conjuncts();
        if conjuncts.len() <= 1 {
            return formula.clone();
        }

        let mut result_conjuncts = conjuncts.clone();
        let mut changed = false;

        for (i, conjunct) in conjuncts.iter().enumerate() {
            if let Some((select_expr, _const_val)) = Self::extract_select_const_equality(conjunct) {
                // Try weakening to lower bound: (>= (select arr i) c)
                let lower_bound = ChcExpr::Op(
                    ChcOp::Ge,
                    vec![Arc::new(select_expr.clone()), args_rhs(conjunct)],
                );
                let mut candidate = result_conjuncts.clone();
                candidate[i] = lower_bound.clone();
                let candidate_expr = ChcExpr::and_all(candidate.iter().cloned());
                if system.check_inductive(&candidate_expr, level) {
                    result_conjuncts[i] = lower_bound;
                    changed = true;
                    continue;
                }

                // Try weakening to upper bound: (<= (select arr i) c)
                let upper_bound = ChcExpr::Op(
                    ChcOp::Le,
                    vec![Arc::new(select_expr.clone()), args_rhs(conjunct)],
                );
                let mut candidate = result_conjuncts.clone();
                candidate[i] = upper_bound.clone();
                let candidate_expr = ChcExpr::and_all(candidate.iter().cloned());
                if system.check_inductive(&candidate_expr, level) {
                    result_conjuncts[i] = upper_bound;
                    changed = true;
                    continue;
                }

                // Try weakening to non-negative: (>= (select arr i) 0)
                // This is common for array indices and counters
                if _const_val > 0 {
                    let non_neg = ChcExpr::ge(select_expr.clone(), ChcExpr::int(0));
                    let mut candidate = result_conjuncts.clone();
                    candidate[i] = non_neg.clone();
                    let candidate_expr = ChcExpr::and_all(candidate.iter().cloned());
                    if system.check_inductive(&candidate_expr, level) {
                        result_conjuncts[i] = non_neg;
                        changed = true;
                    }
                }
            }
        }

        if !changed {
            return formula.clone();
        }

        ChcExpr::and_all(result_conjuncts)
    }

    fn name(&self) -> &'static str {
        "array-select-value-weakening"
    }
}

/// Helper: extract the RHS Arc from an equality conjunct.
fn args_rhs(expr: &ChcExpr) -> Arc<ChcExpr> {
    if let ChcExpr::Op(ChcOp::Eq, args) = expr {
        if args.len() == 2 {
            // If LHS is select, RHS is the constant
            if matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Select, _)) {
                return Arc::clone(&args[1]);
            }
            // If RHS is select, LHS is the constant
            return Arc::clone(&args[0]);
        }
    }
    Arc::new(ChcExpr::int(0)) // fallback, should not happen
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{ChcSort, ChcVar};
    use crate::generalize::tests::MockTransitionSystem;

    fn arr_sort() -> ChcSort {
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int))
    }

    fn arr_var(name: &str) -> ChcExpr {
        ChcExpr::Var(ChcVar::new(name, arr_sort()))
    }

    fn int_var(name: &str) -> ChcExpr {
        ChcExpr::Var(ChcVar::new(name, ChcSort::Int))
    }

    // ---- ArrayStoreProjectionGeneralizer tests ----

    #[test]
    fn test_store_projection_name() {
        let g = ArrayStoreProjectionGeneralizer::new();
        assert_eq!(g.name(), "array-store-projection");
    }

    #[test]
    fn test_store_projection_extract_store_equality() {
        let arr = arr_var("heap");
        let arr2 = arr_var("heap2");
        let idx = ChcExpr::int(42);
        let val = ChcExpr::int(7);

        // (= heap (store heap2 42 7))
        let store = ChcExpr::store(arr2.clone(), idx.clone(), val.clone());
        let eq = ChcExpr::eq(arr.clone(), store);

        let result = ArrayStoreProjectionGeneralizer::extract_store_equality(&eq);
        assert!(result.is_some());
        let (a, i, v) = result.expect("should extract store equality");
        assert_eq!(a, arr);
        assert_eq!(i, idx);
        assert_eq!(v, val);
    }

    #[test]
    fn test_store_projection_extract_reversed() {
        let arr = arr_var("heap");
        let arr2 = arr_var("heap2");
        let idx = ChcExpr::int(42);
        let val = ChcExpr::int(7);

        // (= (store heap2 42 7) heap)
        let store = ChcExpr::store(arr2.clone(), idx.clone(), val.clone());
        let eq = ChcExpr::eq(store, arr.clone());

        let result = ArrayStoreProjectionGeneralizer::extract_store_equality(&eq);
        assert!(result.is_some());
    }

    #[test]
    fn test_store_projection_no_match_on_non_store() {
        let x = int_var("x");
        let eq = ChcExpr::eq(x, ChcExpr::int(5));
        assert!(ArrayStoreProjectionGeneralizer::extract_store_equality(&eq).is_none());
    }

    #[test]
    fn test_store_projection_generalizes_when_inductive() {
        let arr = arr_var("heap");
        let arr2 = arr_var("heap2");
        let idx = ChcExpr::int(42);
        let val = ChcExpr::int(7);
        let x = int_var("x");

        // Lemma: (and (= heap (store heap2 42 7)) (= x 5))
        let store_eq = ChcExpr::eq(
            arr.clone(),
            ChcExpr::store(arr2.clone(), idx.clone(), val.clone()),
        );
        let scalar_eq = ChcExpr::eq(x.clone(), ChcExpr::int(5));
        let lemma = ChcExpr::and(store_eq, scalar_eq.clone());

        let g = ArrayStoreProjectionGeneralizer::new();
        let mut ts = MockTransitionSystem::new();

        // Mark the weakened version as inductive
        let weakened_point = ChcExpr::eq(ChcExpr::select(arr.clone(), idx.clone()), val.clone());
        let weakened_lemma = ChcExpr::and(weakened_point.clone(), scalar_eq.clone());
        ts.mark_inductive(&format!("{weakened_lemma:?}"));

        let result = g.generalize(&lemma, 0, &mut ts);
        // Should have replaced the store equality with a select equality
        let result_conjuncts = result.collect_conjuncts();
        assert_eq!(result_conjuncts.len(), 2, "should still have 2 conjuncts");
        // One of them should be the point select
        let has_select = result_conjuncts.iter().any(|c| {
            matches!(c, ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 &&
                matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Select, _)))
        });
        assert!(
            has_select,
            "should contain a select equality after projection"
        );
    }

    #[test]
    fn test_store_projection_preserves_when_not_inductive() {
        let arr = arr_var("heap");
        let arr2 = arr_var("heap2");
        let idx = ChcExpr::int(42);
        let val = ChcExpr::int(7);
        let x = int_var("x");

        let store_eq = ChcExpr::eq(arr.clone(), ChcExpr::store(arr2, idx, val));
        let scalar_eq = ChcExpr::eq(x, ChcExpr::int(5));
        let lemma = ChcExpr::and(store_eq, scalar_eq);

        let g = ArrayStoreProjectionGeneralizer::new();
        let mut ts = MockTransitionSystem::new();
        // Nothing is marked inductive

        let result = g.generalize(&lemma, 0, &mut ts);
        assert_eq!(
            result, lemma,
            "should return original when nothing is inductive"
        );
    }

    #[test]
    fn test_store_projection_skips_non_array_formulas() {
        let x = int_var("x");
        let lemma = ChcExpr::eq(x, ChcExpr::int(5));
        let g = ArrayStoreProjectionGeneralizer::new();
        let mut ts = MockTransitionSystem::new();

        let result = g.generalize(&lemma, 0, &mut ts);
        assert_eq!(result, lemma);
    }

    // ---- ArrayEqualityDropGeneralizer tests ----

    #[test]
    fn test_array_equality_drop_name() {
        let g = ArrayEqualityDropGeneralizer::new();
        assert_eq!(g.name(), "array-equality-drop");
    }

    #[test]
    fn test_is_array_equality() {
        let arr1 = arr_var("a");
        let arr2 = arr_var("b");
        let eq = ChcExpr::eq(arr1, arr2);
        assert!(ArrayEqualityDropGeneralizer::is_array_equality(&eq));

        // Non-array equality should not match
        let x = int_var("x");
        let non_arr_eq = ChcExpr::eq(x, ChcExpr::int(5));
        assert!(!ArrayEqualityDropGeneralizer::is_array_equality(
            &non_arr_eq
        ));
    }

    #[test]
    fn test_array_equality_drop_all_at_once() {
        let arr1 = arr_var("a");
        let arr2 = arr_var("b");
        let x = int_var("x");
        let y = int_var("y");

        let arr_eq = ChcExpr::eq(arr1, arr2);
        let scalar1 = ChcExpr::ge(x, ChcExpr::int(0));
        let scalar2 = ChcExpr::le(y.clone(), ChcExpr::int(10));
        let lemma = ChcExpr::and_all([arr_eq, scalar1.clone(), scalar2.clone()]);

        let g = ArrayEqualityDropGeneralizer::new();
        let mut ts = MockTransitionSystem::new();

        // Mark the scalar-only version as inductive
        let scalar_only = ChcExpr::and(scalar1.clone(), scalar2.clone());
        ts.mark_inductive(&format!("{scalar_only:?}"));

        let result = g.generalize(&lemma, 0, &mut ts);
        let result_conjuncts = result.collect_conjuncts();
        assert_eq!(
            result_conjuncts.len(),
            2,
            "should have dropped array equality"
        );
        // Verify no array equalities remain
        for c in &result_conjuncts {
            assert!(!ArrayEqualityDropGeneralizer::is_array_equality(c));
        }
    }

    #[test]
    fn test_array_equality_drop_greedy() {
        let arr1 = arr_var("a");
        let arr2 = arr_var("b");
        let arr3 = arr_var("c");
        let arr4 = arr_var("d");
        let x = int_var("x");

        let arr_eq1 = ChcExpr::eq(arr1.clone(), arr2.clone());
        let arr_eq2 = ChcExpr::eq(arr3.clone(), arr4.clone());
        let scalar = ChcExpr::ge(x, ChcExpr::int(0));
        let lemma = ChcExpr::and_all([arr_eq1.clone(), arr_eq2.clone(), scalar.clone()]);

        let g = ArrayEqualityDropGeneralizer::new();
        let mut ts = MockTransitionSystem::new();

        // Only dropping arr_eq2 (not arr_eq1) preserves inductiveness
        let partial = ChcExpr::and(arr_eq1.clone(), scalar.clone());
        ts.mark_inductive(&format!("{partial:?}"));

        let result = g.generalize(&lemma, 0, &mut ts);
        let result_conjuncts = result.collect_conjuncts();
        assert_eq!(
            result_conjuncts.len(),
            2,
            "should have dropped one array equality"
        );
    }

    // ---- ArraySelectValueWeakeningGeneralizer tests ----

    #[test]
    fn test_select_value_weakening_name() {
        let g = ArraySelectValueWeakeningGeneralizer::new();
        assert_eq!(g.name(), "array-select-value-weakening");
    }

    #[test]
    fn test_extract_select_const_equality() {
        let arr = arr_var("heap");
        let idx = ChcExpr::int(3);
        let val = ChcExpr::int(42);

        // (= (select heap 3) 42)
        let sel = ChcExpr::select(arr.clone(), idx.clone());
        let eq = ChcExpr::eq(sel.clone(), val.clone());

        let result = ArraySelectValueWeakeningGeneralizer::extract_select_const_equality(&eq);
        assert!(result.is_some());
        let (s, c) = result.expect("should extract");
        assert_eq!(s, sel);
        assert_eq!(c, 42);
    }

    #[test]
    fn test_extract_select_const_equality_reversed() {
        let arr = arr_var("heap");
        let idx = ChcExpr::int(3);
        let val = ChcExpr::int(42);

        // (= 42 (select heap 3))
        let sel = ChcExpr::select(arr, idx);
        let eq = ChcExpr::eq(val, sel.clone());

        let result = ArraySelectValueWeakeningGeneralizer::extract_select_const_equality(&eq);
        assert!(result.is_some());
        let (s, c) = result.expect("should extract reversed");
        assert_eq!(s, sel);
        assert_eq!(c, 42);
    }

    #[test]
    fn test_select_value_weakening_to_ge() {
        let arr = arr_var("heap");
        let idx = ChcExpr::int(3);
        let val = ChcExpr::int(42);
        let x = int_var("x");

        // Lemma: (and (= (select heap 3) 42) (= x 5))
        let sel_eq = ChcExpr::eq(ChcExpr::select(arr.clone(), idx.clone()), val.clone());
        let scalar_eq = ChcExpr::eq(x.clone(), ChcExpr::int(5));
        let lemma = ChcExpr::and(sel_eq, scalar_eq.clone());

        let g = ArraySelectValueWeakeningGeneralizer::new();
        let mut ts = MockTransitionSystem::new();

        // Mark the lower-bound weakened version as inductive
        let lower_bound = ChcExpr::ge(ChcExpr::select(arr.clone(), idx.clone()), val.clone());
        let weakened = ChcExpr::and(lower_bound.clone(), scalar_eq.clone());
        ts.mark_inductive(&format!("{weakened:?}"));

        let result = g.generalize(&lemma, 0, &mut ts);
        let result_conjuncts = result.collect_conjuncts();
        assert_eq!(result_conjuncts.len(), 2);
        // Should have replaced equality with >= constraint
        let has_ge = result_conjuncts
            .iter()
            .any(|c| matches!(c, ChcExpr::Op(ChcOp::Ge, _)));
        assert!(has_ge, "should contain a >= constraint after weakening");
    }

    #[test]
    fn test_select_value_weakening_skips_non_array() {
        let x = int_var("x");
        let lemma = ChcExpr::eq(x, ChcExpr::int(5));
        let g = ArraySelectValueWeakeningGeneralizer::new();
        let mut ts = MockTransitionSystem::new();

        let result = g.generalize(&lemma, 0, &mut ts);
        assert_eq!(result, lemma);
    }
}
