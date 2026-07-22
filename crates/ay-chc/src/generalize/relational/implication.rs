// Copyright 2026 Andrew Yates
// Author: Andrew Yates
//
// Licensed under the Apache License, Version 2.0

//! Implication generalizer: discovers conditional invariants like `(pc = 2) => (lock = 1)`.

use crate::expr::{ChcExpr, ChcOp, ChcSort, ChcVar};
use crate::generalize::{LemmaGeneralizer, TransitionSystemRef};

/// Implication generalizer: discovers conditional invariants like `(pc = 2) => (lock = 1)`.
///
/// For state formula (v1 = c1 AND v2 = c2), tries to learn implicative lemmas:
/// - Point implications: `(v1 = c1) => (v2 != c2)`
/// - Range implications: `(v1 = c1) => (v2 < bound)` when bound is far from init
///
/// # When to Use
///
/// Use this generalizer for mutex protocols, state machines, and programs with
/// control flow dependencies. It discovers invariants like:
/// - `(pc = 2) => (lock = 1)` (critical section protection)
/// - `(phase = COMMIT) => (prepared = true)` (2PC protocol)
///
/// # Algorithm
///
/// For each pair of equalities (v1 = c1) and (v2 = c2):
/// 1. Try range implications if c2 is significantly outside init bounds:
///    - `(v1 = c1) => (v2 < c2)` when c2 >> init_max
///    - `(v1 = c1) => (v2 > c2)` when c2 << init_min
/// 2. Try point implication: `(v1 = c1) => (v2 != c2)`
/// 3. Check inductiveness at level 1 for global invariants
///
/// # Design Notes
///
/// - Large-magnitude range implications (|c2| >= 5) are returned immediately
/// - Small-domain variables (like pc) use point implications to avoid overgeneralization
/// - MIN_RANGE_GAP prevents false positives on bounded-domain variables
///
/// Reference: PDR's Phase 0b (lines 6998-7244 in pdr.rs)
pub(crate) struct ImplicationGeneralizer {
    /// Minimum gap from init bounds to use range implications.
    /// Smaller gaps risk overgeneralization on bounded-domain variables.
    pub(crate) min_range_gap: i64,
}

impl Default for ImplicationGeneralizer {
    fn default() -> Self {
        Self::new()
    }
}

impl ImplicationGeneralizer {
    /// Create a new implication generalizer with default settings.
    pub(crate) fn new() -> Self {
        Self { min_range_gap: 3 }
    }

    /// Check if an expression is already a range constraint (not a point constraint).
    fn is_range_constraint(expr: &ChcExpr) -> bool {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Op(ChcOp::Ge | ChcOp::Le | ChcOp::Gt | ChcOp::Lt, _) => true,
            ChcExpr::Op(ChcOp::And, args) => args.iter().all(|a| Self::is_range_constraint(a)),
            ChcExpr::Op(ChcOp::Or, args) => args.iter().any(|a| Self::is_range_constraint(a)),
            _ => false,
        })
    }
}

impl LemmaGeneralizer for ImplicationGeneralizer {
    fn generalize(&self, lemma: &ChcExpr, level: u32, ts: &mut dyn TransitionSystemRef) -> ChcExpr {
        let conjuncts = lemma.collect_conjuncts();

        // Skip if lemma is already a template (range constraint)
        if Self::is_range_constraint(lemma) {
            return lemma.clone();
        }

        // Need at least 2 equalities for implication patterns
        if conjuncts.len() < 2 {
            return lemma.clone();
        }

        // Extract all (var_name, value) pairs from equalities
        let equalities: Vec<(String, i128)> = conjuncts
            .iter()
            .filter_map(|e| e.extract_var_int_equality().map(|(v, c)| (v.name, c)))
            .collect();

        if equalities.len() < 2 {
            return lemma.clone();
        }

        // Get init bounds for range-based implications
        let init_bounds = ts.init_bounds();

        let mut implication_lemmas: Vec<ChcExpr> = Vec::new();
        let mut small_range_blocking: Vec<ChcExpr> = Vec::new();

        // Try each pair of equalities for implication pattern
        for i in 0..equalities.len() {
            for j in 0..equalities.len() {
                if i == j {
                    continue;
                }

                let (var_ant, val_ant) = &equalities[i];
                let (var_cons, val_cons) = &equalities[j];

                // First, try range consequent if value is far from init bounds
                if let Some(bounds) = init_bounds.get(var_cons) {
                    // Try: (v1 = c1) => (v2 < c2) when c2 >> init_max
                    // (i64 bounds + i64 gap always fit in i128, so the sum is exact)
                    if *val_cons > i128::from(bounds.max) + i128::from(self.min_range_gap) {
                        let blocking_formula = ChcExpr::and(
                            ChcExpr::eq(
                                ChcExpr::var(ChcVar::new(var_ant, ChcSort::Int)),
                                ChcExpr::Int(*val_ant),
                            ),
                            ChcExpr::ge(
                                ChcExpr::var(ChcVar::new(var_cons, ChcSort::Int)),
                                ChcExpr::Int(*val_cons),
                            ),
                        );

                        if ts.check_inductive(&blocking_formula, 1) {
                            if val_cons.unsigned_abs() >= 5 {
                                return blocking_formula;
                            }
                            small_range_blocking.push(blocking_formula);
                        }
                    }

                    // Try: (v1 = c1) => (v2 > c2) when c2 << init_min
                    // (i64 bounds - i64 gap always fit in i128, so the difference is exact)
                    if *val_cons < i128::from(bounds.min) - i128::from(self.min_range_gap) {
                        let blocking_formula = ChcExpr::and(
                            ChcExpr::eq(
                                ChcExpr::var(ChcVar::new(var_ant, ChcSort::Int)),
                                ChcExpr::Int(*val_ant),
                            ),
                            ChcExpr::le(
                                ChcExpr::var(ChcVar::new(var_cons, ChcSort::Int)),
                                ChcExpr::Int(*val_cons),
                            ),
                        );

                        if ts.check_inductive(&blocking_formula, 1) {
                            if val_cons.unsigned_abs() >= 5 {
                                return blocking_formula;
                            }
                            small_range_blocking.push(blocking_formula);
                        }
                    }
                }

                // Try point implication: (v1 = c1) => (v2 != c2)
                let blocking_formula = ChcExpr::and(
                    ChcExpr::eq(
                        ChcExpr::var(ChcVar::new(var_ant, ChcSort::Int)),
                        ChcExpr::Int(*val_ant),
                    ),
                    ChcExpr::eq(
                        ChcExpr::var(ChcVar::new(var_cons, ChcSort::Int)),
                        ChcExpr::Int(*val_cons),
                    ),
                );

                // Check at level 1 for global invariants, then at current level
                let is_inductive_at_1 = ts.check_inductive(&blocking_formula, 1);
                let is_inductive = is_inductive_at_1
                    || (level > 1 && ts.check_inductive(&blocking_formula, level));

                if is_inductive {
                    let not_ant = ChcExpr::ne(
                        ChcExpr::var(ChcVar::new(var_ant, ChcSort::Int)),
                        ChcExpr::Int(*val_ant),
                    );
                    let not_cons = ChcExpr::ne(
                        ChcExpr::var(ChcVar::new(var_cons, ChcSort::Int)),
                        ChcExpr::Int(*val_cons),
                    );
                    implication_lemmas.push(ChcExpr::or(not_ant, not_cons));
                }
            }
        }

        // Priority: range implications over point implications
        if !small_range_blocking.is_empty() {
            return small_range_blocking[0].clone();
        }

        // Select best point implication
        if !implication_lemmas.is_empty() {
            let mut best_blocking: Option<(String, i128, String, i128)> = None;

            for i in 0..equalities.len() {
                for j in 0..equalities.len() {
                    if i == j {
                        continue;
                    }

                    let (var_i, val_i) = &equalities[i];
                    let (var_j, val_j) = &equalities[j];

                    let blocking_2var = ChcExpr::and(
                        ChcExpr::eq(
                            ChcExpr::var(ChcVar::new(var_i, ChcSort::Int)),
                            ChcExpr::Int(*val_i),
                        ),
                        ChcExpr::eq(
                            ChcExpr::var(ChcVar::new(var_j, ChcSort::Int)),
                            ChcExpr::Int(*val_j),
                        ),
                    );

                    if ts.check_inductive(&blocking_2var, 1) {
                        let is_better = best_blocking.is_none()
                            || var_j.contains("lock")
                            || var_j.contains("a2")
                            || var_j.contains("_p0_a2");

                        if is_better {
                            best_blocking = Some((var_i.clone(), *val_i, var_j.clone(), *val_j));
                        }
                    }
                }
            }

            if let Some((var_i, val_i, var_j, val_j)) = best_blocking {
                return ChcExpr::and_all([
                    ChcExpr::eq(
                        ChcExpr::var(ChcVar::new(&var_i, ChcSort::Int)),
                        ChcExpr::Int(val_i),
                    ),
                    ChcExpr::eq(
                        ChcExpr::var(ChcVar::new(&var_j, ChcSort::Int)),
                        ChcExpr::Int(val_j),
                    ),
                ]);
            }
        }

        lemma.clone()
    }

    fn name(&self) -> &'static str {
        "implication"
    }
}
