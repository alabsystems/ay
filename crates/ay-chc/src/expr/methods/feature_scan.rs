// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Preprocessing feature detection and normalization routing.

use super::{
    maybe_grow_expr_stack, ChcExpr, ChcOp, ChcSort, ExprFeatures, MAX_EXPR_RECURSION_DEPTH,
};

impl ExprFeatures {
    /// Returns true if all feature flags are set (early-exit optimization).
    fn all_set(&self) -> bool {
        self.has_array_ops
            && self.has_bv
            && self.has_uf_apps
            && self.has_dt
            && self.has_mixed_sort_eq
            && self.has_ite
            && self.has_mod_or_div
            && self.has_negation
            && self.has_strict_int_comparison
    }

    /// Returns true if the expression needs normalization passes.
    /// When false, `core_normalize_pre_rename` and `core_normalize_post_rename`
    /// are identity functions and can be skipped (#6358 performance).
    pub(crate) fn needs_normalization(&self) -> bool {
        self.has_mixed_sort_eq
            || self.has_ite
            || self.has_mod_or_div
            || self.has_negation
            || self.has_strict_int_comparison
    }

    /// Close the feature set under preprocessing-side implications.
    ///
    /// `scan_features()` walks the original expression only once, but later
    /// preprocessing passes can introduce new nodes that still require
    /// follow-up passes:
    /// - mixed-sort equality rewriting introduces arithmetic ITEs
    /// - arithmetic ITE elimination introduces a negated else-branch guard
    /// - mod/div elimination introduces a strict `<` remainder bound
    /// - negation normalization can rewrite `not(<= ...)` / `not(>= ...)` into
    ///   strict `<` / `>` comparisons
    ///
    /// Conservatively marking these downstream features preserves the behavior
    /// of the old stage-by-stage `contains_*` checks.
    fn close_under_preprocessing(&mut self) {
        if self.has_mixed_sort_eq {
            self.has_ite = true;
            self.has_negation = true;
        }
        if self.has_mod_or_div || self.has_negation {
            self.has_strict_int_comparison = true;
        }
    }

    /// Core normalization chain shared by all three preprocessing pipelines
    /// (#6360): mixed-sort eq → ITE → mod → negation → strict comparison.
    ///
    /// This replaces the duplicated 5-step transformation sequence in
    /// `check_sat_internal`, `preprocess()`, and
    /// `preprocess_incremental_assumption()`.
    pub(crate) fn core_normalize(&self, expr: ChcExpr) -> ChcExpr {
        let after_mod = self.core_normalize_pre_rename(expr);
        self.core_normalize_post_rename(after_mod)
    }

    /// First half of core normalization: mixed-sort eq → ITE → mod.
    ///
    /// Pipeline 3 (`preprocess_incremental_assumption`) inserts a rename
    /// step between this and `core_normalize_post_rename`.
    pub(crate) fn core_normalize_pre_rename(&self, expr: ChcExpr) -> ChcExpr {
        let mixed_fixed = if self.has_mixed_sort_eq {
            expr.eliminate_mixed_sort_eq()
        } else {
            expr
        };
        // #5970: Eliminate mod/div BEFORE ITE. When mod appears inside an ITE
        // condition like `(ite (= (mod x 2) 1) a b)`, ITE elimination creates
        // two implications that each contain the condition. If mod is eliminated
        // after ITE, each implication gets its own fresh mod variables — the SAT
        // solver can assign them inconsistently, producing models that violate
        // the original formula. Eliminating mod first replaces `(mod x 2)` with
        // a single fresh variable `_mod_r`, so both ITE branches share the same
        // condition variable.
        let mod_eliminated = if self.has_mod_or_div {
            mixed_fixed.eliminate_mod()
        } else {
            mixed_fixed
        };
        let has_ite = self.has_ite || self.has_mixed_sort_eq;
        if has_ite {
            mod_eliminated.eliminate_ite()
        } else {
            mod_eliminated
        }
    }

    /// Second half of core normalization: negation → strict comparison.
    pub(crate) fn core_normalize_post_rename(&self, expr: ChcExpr) -> ChcExpr {
        let normalized = if self.has_negation {
            expr.normalize_negations()
        } else {
            expr
        };
        if self.has_strict_int_comparison {
            normalized.normalize_strict_int_comparisons()
        } else {
            normalized
        }
    }
}

impl ChcExpr {
    /// Single-pass feature scan: detect all preprocessing-relevant features
    /// in one tree walk instead of 6-8 individual `contains_*` calls (#6360).
    ///
    /// The returned `ExprFeatures` indicates which preprocessing transformations
    /// are needed, allowing callers to skip both the detection walk and the
    /// transformation walk for features that are absent.
    pub(crate) fn scan_features(&self) -> ExprFeatures {
        fn inner(expr: &ChcExpr, features: &mut ExprFeatures, depth: usize) {
            if depth >= MAX_EXPR_RECURSION_DEPTH {
                // Conservative: mark everything present if too deep.
                features.has_array_ops = true;
                features.has_bv = true;
                features.has_uf_apps = true;
                features.has_dt = true;
                features.has_mixed_sort_eq = true;
                features.has_ite = true;
                features.has_mod_or_div = true;
                features.has_negation = true;
                features.has_strict_int_comparison = true;
                return;
            }
            // Early exit: if all features are already found, no need to keep walking.
            if features.all_set() {
                return;
            }
            maybe_grow_expr_stack(|| match expr {
                ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::Real(_, _)
                | ChcExpr::ConstArrayMarker(_)
                | ChcExpr::IsTesterMarker(_) => {}
                ChcExpr::BitVec(_, _) => {
                    features.has_bv = true;
                }
                ChcExpr::Var(v) => {
                    if matches!(v.sort, ChcSort::Array(_, _)) {
                        features.has_array_ops = true;
                    }
                    if matches!(v.sort, ChcSort::BitVec(_)) {
                        features.has_bv = true;
                    }
                    if matches!(v.sort, ChcSort::Datatype { .. }) {
                        features.has_dt = true;
                    }
                }
                ChcExpr::ConstArray(_, val) => {
                    features.has_array_ops = true;
                    inner(val, features, depth + 1);
                }
                ChcExpr::FuncApp(_, sort, args) => {
                    features.has_uf_apps = true;
                    if matches!(sort, ChcSort::Array(_, _)) {
                        features.has_array_ops = true;
                    }
                    if matches!(sort, ChcSort::BitVec(_)) {
                        features.has_bv = true;
                    }
                    if matches!(sort, ChcSort::Datatype { .. }) {
                        features.has_dt = true;
                    }
                    for a in args {
                        inner(a, features, depth + 1);
                    }
                }
                ChcExpr::PredicateApp(_, _, args) => {
                    for a in args {
                        inner(a, features, depth + 1);
                    }
                }
                ChcExpr::Op(op, args) => {
                    match op {
                        ChcOp::Select | ChcOp::Store => features.has_array_ops = true,
                        ChcOp::BvAdd
                        | ChcOp::BvSub
                        | ChcOp::BvMul
                        | ChcOp::BvUDiv
                        | ChcOp::BvURem
                        | ChcOp::BvSDiv
                        | ChcOp::BvSRem
                        | ChcOp::BvSMod
                        | ChcOp::BvAnd
                        | ChcOp::BvOr
                        | ChcOp::BvXor
                        | ChcOp::BvNand
                        | ChcOp::BvNor
                        | ChcOp::BvXnor
                        | ChcOp::BvNot
                        | ChcOp::BvNeg
                        | ChcOp::BvShl
                        | ChcOp::BvLShr
                        | ChcOp::BvAShr
                        | ChcOp::BvULt
                        | ChcOp::BvULe
                        | ChcOp::BvUGt
                        | ChcOp::BvUGe
                        | ChcOp::BvSLt
                        | ChcOp::BvSLe
                        | ChcOp::BvSGt
                        | ChcOp::BvSGe
                        | ChcOp::BvComp
                        | ChcOp::BvConcat
                        | ChcOp::Bv2Nat
                        | ChcOp::BvExtract(_, _)
                        | ChcOp::BvZeroExtend(_)
                        | ChcOp::BvSignExtend(_)
                        | ChcOp::BvRotateLeft(_)
                        | ChcOp::BvRotateRight(_)
                        | ChcOp::BvRepeat(_)
                        | ChcOp::Int2Bv(_) => {
                            features.has_bv = true;
                        }
                        ChcOp::Ite => {
                            features.has_ite = true;
                            if args.len() == 3 {
                                let then_sort = args[1].sort();
                                let else_sort = args[2].sort();
                                if then_sort == else_sort
                                    && matches!(then_sort, ChcSort::Int | ChcSort::Real)
                                {
                                    features.has_negation = true;
                                }
                            }
                        }
                        ChcOp::Mod | ChcOp::Div => features.has_mod_or_div = true,
                        ChcOp::Not => features.has_negation = true,
                        ChcOp::Lt | ChcOp::Gt => features.has_strict_int_comparison = true,
                        ChcOp::Eq if args.len() == 2 => {
                            let s0 = args[0].sort();
                            let s1 = args[1].sort();
                            if (s0 == ChcSort::Bool) != (s1 == ChcSort::Bool)
                                && (matches!(s0, ChcSort::Int | ChcSort::Real)
                                    || matches!(s1, ChcSort::Int | ChcSort::Real))
                            {
                                features.has_mixed_sort_eq = true;
                            }
                        }
                        _ => {}
                    }
                    for a in args {
                        inner(a, features, depth + 1);
                    }
                }
            });
        }

        let mut features = ExprFeatures::default();
        inner(self, &mut features, 0);
        features.close_under_preprocessing();
        features
    }
}
