// Copyright 2026 Andrew Yates
// Author: Andrew Yates
//
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

/// Literal weakening generalizer: weakens literals that cannot be dropped.
///
/// Z3 equivalent: `lemma_inductive_generalizer::weaken1` in
/// `spacer_ind_lemma_generalizer.cpp:185-226`
///
/// When [`DropLiteralGeneralizer`] cannot drop a literal, this generalizer
/// tries weakening it instead:
/// - `x = y` → `x ≤ y` or `y ≤ x`
///
/// The generalizer attempts each weakening and keeps the first one that
/// maintains inductiveness.
///
/// Reference: `reference/z3/src/muz/spacer/spacer_ind_lemma_generalizer.cpp:185-226`
/// Design: the development design notes
pub(crate) struct LiteralWeakeningGeneralizer;

impl Default for LiteralWeakeningGeneralizer {
    fn default() -> Self {
        Self::new()
    }
}

impl LiteralWeakeningGeneralizer {
    /// Create a new literal weakening generalizer.
    pub(crate) fn new() -> Self {
        Self
    }

    /// Generate weakening candidates for a literal.
    ///
    /// Returns a vector of candidate literals that are weaker than the original.
    ///
    /// # Modulo exclusion
    ///
    /// Per Z3's `expand_literals` in `spacer_util.cpp`, equalities involving
    /// modulo operations are NOT weakened. This prevents wasted SMT time since
    /// modulo equalities typically cannot be relaxed to inequalities usefully.
    /// Reference: `!arith.is_mod(e1) && !arith.is_mod(e2)` check in Z3.
    /// Issue: #169
    pub(super) fn generate_weakenings(&self, lit: &ChcExpr) -> Vec<ChcExpr> {
        use crate::expr::ChcOp;

        let mut candidates = Vec::new();

        match lit {
            // Arithmetic equality: x = y → x ≤ y or y ≤ x
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                let lhs = &args[0];
                let rhs = &args[1];

                // Only weaken arithmetic equalities, excluding modulo operations (#169)
                // Z3 skips weakening when either operand is a mod expression
                if Self::is_arithmetic(lhs) && !Self::is_modulo(lhs) && !Self::is_modulo(rhs) {
                    // x = y → x ≤ y (weaker: loses x ≥ y constraint)
                    candidates.push(ChcExpr::le((**lhs).clone(), (**rhs).clone()));
                    // x = y → y ≤ x (weaker: loses x ≤ y constraint)
                    candidates.push(ChcExpr::le((**rhs).clone(), (**lhs).clone()));
                }

                // #5877: BV MSB extract equality → signed inequality.
                // (= (extract 31 31 x) #b1) → (bvslt x 0) (signed negative)
                // (= (extract 31 31 x) #b0) → (bvsle 0 x) (signed non-negative)
                // This takes priority over general BV weakening since extract
                // results are 1-bit BV, and bvsle on 1-bit is trivially true.
                if Self::is_msb_extract(lhs) && matches!(rhs.as_ref(), ChcExpr::BitVec(_, 1)) {
                    if let Some((var, width)) = Self::extract_msb_var(lhs) {
                        let val = match rhs.as_ref() {
                            ChcExpr::BitVec(v, _) => *v,
                            _ => return candidates,
                        };
                        let zero = ChcExpr::BitVec(0, width);
                        let var_expr = ChcExpr::Var(var);
                        if val == 1 {
                            // MSB=1 means signed negative: weaken to bvslt(x, 0)
                            candidates.push(ChcExpr::Op(
                                ChcOp::BvSLt,
                                vec![Arc::new(var_expr), Arc::new(zero)],
                            ));
                        } else {
                            // MSB=0 means signed non-negative: weaken to bvsle(0, x)
                            candidates.push(ChcExpr::Op(
                                ChcOp::BvSLe,
                                vec![Arc::new(zero), Arc::new(var_expr)],
                            ));
                        }
                    }
                } else if Self::is_bitvec(lhs) || Self::is_bitvec(rhs) {
                    // #5877: BV equality weakening to signed/unsigned inequalities.
                    // (= x #xK) → (bvsle x #xK) or (bvsle #xK x)
                    // This enables PDR to generalize BV point lemmas into range
                    // lemmas, matching Z3 Spacer's BV invariant pattern.

                    // x = y → bvsle(x, y) (signed: x <= y)
                    candidates.push(ChcExpr::Op(
                        ChcOp::BvSLe,
                        vec![Arc::new((**lhs).clone()), Arc::new((**rhs).clone())],
                    ));
                    // x = y → bvsle(y, x) (signed: y <= x, i.e., x >= y)
                    candidates.push(ChcExpr::Op(
                        ChcOp::BvSLe,
                        vec![Arc::new((**rhs).clone()), Arc::new((**lhs).clone())],
                    ));
                    // Also try unsigned: bvule(x, y) and bvule(y, x)
                    candidates.push(ChcExpr::Op(
                        ChcOp::BvULe,
                        vec![Arc::new((**lhs).clone()), Arc::new((**rhs).clone())],
                    ));
                    candidates.push(ChcExpr::Op(
                        ChcOp::BvULe,
                        vec![Arc::new((**rhs).clone()), Arc::new((**lhs).clone())],
                    ));
                }
            }
            _ => {}
        }

        candidates
    }

    /// Check if an expression is a modulo operation.
    ///
    /// Used to exclude modulo equalities from weakening per Z3's approach.
    /// See #169.
    pub(super) fn is_modulo(expr: &ChcExpr) -> bool {
        matches!(expr, ChcExpr::Op(crate::expr::ChcOp::Mod, _))
    }

    /// Check if an expression is arithmetic (Int or Real sort).
    pub(super) fn is_arithmetic(expr: &ChcExpr) -> bool {
        use crate::expr::ChcSort;

        match expr.sort() {
            ChcSort::Int | ChcSort::Real => true,
            _ => {
                // Also check for arithmetic operations
                matches!(
                    expr,
                    ChcExpr::Op(
                        crate::expr::ChcOp::Add
                            | crate::expr::ChcOp::Sub
                            | crate::expr::ChcOp::Mul
                            | crate::expr::ChcOp::Div
                            | crate::expr::ChcOp::Mod
                            | crate::expr::ChcOp::Neg,
                        _
                    )
                )
            }
        }
    }

    /// Check if an expression is bitvector sort (#5877).
    fn is_bitvec(expr: &ChcExpr) -> bool {
        matches!(expr.sort(), crate::expr::ChcSort::BitVec(_))
    }

    /// Check if an expression is an MSB extract: `((_ extract (w-1) (w-1)) x)` (#5877).
    fn is_msb_extract(expr: &ChcExpr) -> bool {
        matches!(
            expr,
            ChcExpr::Op(crate::expr::ChcOp::BvExtract(hi, lo), _) if hi == lo
        )
    }

    /// Extract variable and width from MSB extract: `((_ extract (w-1) (w-1)) x)` (#5877).
    fn extract_msb_var(expr: &ChcExpr) -> Option<(crate::expr::ChcVar, u32)> {
        match expr {
            ChcExpr::Op(crate::expr::ChcOp::BvExtract(hi, _lo), args) if args.len() == 1 => {
                match args[0].as_ref() {
                    ChcExpr::Var(v) => {
                        if let crate::expr::ChcSort::BitVec(w) = v.sort {
                            if *hi == w - 1 {
                                return Some((v.clone(), w));
                            }
                        }
                        None
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

impl LemmaGeneralizer for LiteralWeakeningGeneralizer {
    fn generalize(&self, lemma: &ChcExpr, level: u32, ts: &mut dyn TransitionSystemRef) -> ChcExpr {
        let conjuncts = lemma.collect_conjuncts();

        if conjuncts.is_empty() {
            return lemma.clone();
        }

        let mut result_conjuncts = conjuncts.clone();
        let mut any_changed = false;

        for i in 0..conjuncts.len() {
            // Generate weakening candidates for this conjunct
            let candidates = self.generate_weakenings(&conjuncts[i]);
            if candidates.is_empty() {
                continue;
            }

            // Try each weakening
            for candidate in candidates {
                // Build test expression with weakening applied
                let test_conjuncts: Vec<ChcExpr> = result_conjuncts
                    .iter()
                    .enumerate()
                    .map(|(j, c)| if j == i { candidate.clone() } else { c.clone() })
                    .collect();

                let test_expr = ChcExpr::and_all(test_conjuncts.iter().cloned());

                // Check if weakened version is still inductive
                if ts.check_inductive(&test_expr, level) {
                    // Weakening succeeded - apply it
                    result_conjuncts[i] = candidate;
                    any_changed = true;
                    break; // Move to next conjunct
                }
            }
        }

        if any_changed {
            ChcExpr::and_all(result_conjuncts.iter().cloned())
        } else {
            lemma.clone()
        }
    }

    fn name(&self) -> &'static str {
        "literal-weakening"
    }
}

/// Init-bound weakening generalizer: weakens equalities based on init bounds.
///
/// For constraints like `x = 5` where 5 is outside the initial bounds,
/// tries weakening to `x < init_min` or `x > init_max` (depending on direction).
///
/// This is a key generalization technique from Z3 Spacer's PDR algorithm.
/// It uses information about initial state bounds to generalize point
/// constraints into range constraints.
///
/// # Examples
///
/// If `init(x) = 0`:
/// - `x = -5` → `x < 0` (value is below init)
/// - `x = 10` is not weakened (value is above init, typically reachable)
///
/// # Design Note
///
/// This generalizer only weakens when the observed value is BELOW init bounds.
/// Values above init max are typically reachable via loop iterations,
/// so weakening them would produce incorrect invariants.
///
/// Reference: PDR's Phase 1a (lines 7249-7320 in pdr.rs)
pub(crate) struct InitBoundWeakeningGeneralizer;

impl Default for InitBoundWeakeningGeneralizer {
    fn default() -> Self {
        Self::new()
    }
}

impl InitBoundWeakeningGeneralizer {
    /// Create a new init-bound weakening generalizer.
    pub(crate) fn new() -> Self {
        Self
    }

    /// Try to weaken an equality based on init bounds.
    pub(super) fn try_weaken(
        &self,
        expr: &ChcExpr,
        init_bounds: &HashMap<String, InitBounds>,
    ) -> Option<ChcExpr> {
        let (var, val) = expr.extract_var_int_equality()?;
        let var_name = var.name;
        let bounds = init_bounds.get(&var_name)?;

        // Only weaken if value is below init minimum
        // (values above init are typically reachable via iteration)
        if val < i128::from(bounds.min) {
            // val < init_min: weaken (var = val) to (var < init_min)
            // This blocks all values below init_min, not just `val`
            Some(ChcExpr::lt(
                ChcExpr::var(crate::expr::ChcVar::new(
                    &var_name,
                    crate::expr::ChcSort::Int,
                )),
                ChcExpr::int(bounds.min),
            ))
        } else {
            None
        }
    }
}

impl LemmaGeneralizer for InitBoundWeakeningGeneralizer {
    fn generalize(&self, lemma: &ChcExpr, level: u32, ts: &mut dyn TransitionSystemRef) -> ChcExpr {
        let conjuncts = lemma.collect_conjuncts();

        if conjuncts.is_empty() {
            return lemma.clone();
        }

        // Get init bounds from transition system
        let init_bounds = ts.init_bounds();
        if init_bounds.is_empty() {
            return lemma.clone();
        }

        let mut result_conjuncts = conjuncts.clone();
        let mut any_changed = false;

        for i in 0..conjuncts.len() {
            // Try to weaken this equality based on init bounds
            if let Some(weakened) = self.try_weaken(&result_conjuncts[i], &init_bounds) {
                // Verify the weakened formula is still inductive
                let mut test_conjuncts = result_conjuncts.clone();
                test_conjuncts[i] = weakened.clone();
                let test_expr = ChcExpr::and_all(test_conjuncts.iter().cloned());

                if ts.check_inductive(&test_expr, level) {
                    result_conjuncts[i] = weakened;
                    any_changed = true;
                }
            }
        }

        if any_changed {
            ChcExpr::and_all(result_conjuncts.iter().cloned())
        } else {
            lemma.clone()
        }
    }

    fn name(&self) -> &'static str {
        "init-bound-weakening"
    }
}

/// Single-variable range generalizer: aggressively generalizes to range constraints.
///
/// For lemmas with equalities like `x = val` where val is outside init bounds,
/// this generalizer tries to replace the ENTIRE lemma with a single range constraint
/// like `x < init_min`. This is more aggressive than [`InitBoundWeakeningGeneralizer`]
/// which preserves other conjuncts.
///
/// # When to Use
///
/// Use this generalizer early in the pipeline (before DropLiteralGeneralizer) when
/// you want to discover strong single-variable invariants. If a single range
/// constraint is inductive, it blocks an infinite set of bad states.
///
/// # Examples
///
/// If `init(x) = [0, 10]` and lemma is `x = -5 AND y = 3`:
/// - Tries `x < 0` as a replacement for the entire lemma
/// - If inductive, returns `x < 0` (dropping the `y = 3` conjunct entirely)
///
/// # Design Note
///
/// This is PDR's Phase 0a generalization. It short-circuits other phases
/// when a strong single-variable invariant is found.
///
/// Reference: PDR's Phase 0a (lines 6951-6996 in pdr.rs)
pub(crate) struct SingleVariableRangeGeneralizer;

impl Default for SingleVariableRangeGeneralizer {
    fn default() -> Self {
        Self::new()
    }
}

impl SingleVariableRangeGeneralizer {
    /// Create a new single-variable range generalizer.
    pub(crate) fn new() -> Self {
        Self
    }
}

impl LemmaGeneralizer for SingleVariableRangeGeneralizer {
    fn generalize(&self, lemma: &ChcExpr, level: u32, ts: &mut dyn TransitionSystemRef) -> ChcExpr {
        let conjuncts = lemma.collect_conjuncts();

        if conjuncts.is_empty() {
            return lemma.clone();
        }

        // Get init bounds from transition system
        let init_bounds = ts.init_bounds();
        if init_bounds.is_empty() {
            return lemma.clone();
        }

        // Try each equality to see if we can generalize to a range constraint
        for conjunct in &conjuncts {
            if let Some((var, val)) = conjunct.extract_var_int_equality() {
                let var_name = var.name;
                if let Some(bounds) = init_bounds.get(&var_name) {
                    // Only generalize LOWER bounds based on init
                    // (values above init are typically reachable via iteration)
                    if val < i128::from(bounds.min) {
                        // Try blocking (var < init_min) as the ENTIRE lemma
                        let range_formula = ChcExpr::lt(
                            ChcExpr::var(crate::expr::ChcVar::new(
                                &var_name,
                                crate::expr::ChcSort::Int,
                            )),
                            ChcExpr::int(bounds.min),
                        );

                        if ts.check_inductive(&range_formula, level) {
                            // Found a strong single-variable range invariant
                            return range_formula;
                        }
                    }
                }
            }
        }

        // No single-variable range generalization found
        lemma.clone()
    }

    fn name(&self) -> &'static str {
        "single-variable-range"
    }
}
