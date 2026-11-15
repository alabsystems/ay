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

/// Node visits the plain [`ChcExpr::scan_features`] walk makes before it
/// switches to the DAG walk (WP-F F0b).
const SCAN_PLAIN_VISITS: usize = 4096;

/// Operators whose presence marks a bit-vector query.
fn is_bv_op(op: ChcOp) -> bool {
    matches!(
        op,
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
            | ChcOp::Int2Bv(_)
    )
}

/// Set the flags contributed by `expr` itself (not its children).
fn node_features(expr: &ChcExpr, features: &mut ExprFeatures) {
    match expr {
        ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::Real(_, _)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_)
        | ChcExpr::PredicateApp(..) => {}
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
        ChcExpr::ConstArray(_, _) | ChcExpr::ArrayLambda(_) => {
            features.has_array_ops = true;
        }
        ChcExpr::FuncApp(_, sort, _) => {
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
        }
        ChcExpr::Op(op, args) => match op {
            ChcOp::Select | ChcOp::Store => features.has_array_ops = true,
            // A masked `bv2nat` residue is a constant-modulus `mod` the mod
            // pass eliminates (`ChcExpr::masked_int2bv_residue`).
            ChcOp::Bv2Nat
                if args.len() == 1 && ChcExpr::masked_int2bv_residue(&args[0]).is_some() =>
            {
                features.has_bv = true;
                features.has_mod_or_div = true;
            }
            op if is_bv_op(*op) => features.has_bv = true,
            ChcOp::Ite => {
                features.has_ite = true;
                if args.len() == 3 {
                    let then_sort = args[1].sort();
                    let else_sort = args[2].sort();
                    if then_sort == else_sort && matches!(then_sort, ChcSort::Int | ChcSort::Real) {
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
        },
    }
}

fn set_all(features: &mut ExprFeatures) {
    features.has_array_ops = true;
    features.has_bv = true;
    features.has_uf_apps = true;
    features.has_dt = true;
    features.has_mixed_sort_eq = true;
    features.has_ite = true;
    features.has_mod_or_div = true;
    features.has_negation = true;
    features.has_strict_int_comparison = true;
}

impl ChcExpr {
    /// Single-pass feature scan: detect all preprocessing-relevant features
    /// in one tree walk instead of 6-8 individual `contains_*` calls (#6360).
    ///
    /// The returned `ExprFeatures` indicates which preprocessing transformations
    /// are needed, allowing callers to skip both the detection walk and the
    /// transformation walk for features that are absent.
    ///
    /// DAG-linear (WP-F F0b): past [`SCAN_PLAIN_VISITS`] node visits the scan
    /// restarts as a walk over DISTINCT nodes. Its result equals the tree
    /// walk's: the tree walk marks every feature when it reaches depth
    /// `MAX_EXPR_RECURSION_DEPTH` — which happens exactly when some root-to-node
    /// path is that long (or when every feature is already set) — and otherwise
    /// returns the union of per-node flags, which does not depend on how often
    /// a shared node is reached.
    pub(crate) fn scan_features(&self) -> ExprFeatures {
        /// `false` = the plain visit budget ran out (result discarded).
        fn inner(
            expr: &ChcExpr,
            features: &mut ExprFeatures,
            depth: usize,
            visits_left: &mut usize,
        ) -> bool {
            if depth >= MAX_EXPR_RECURSION_DEPTH {
                // Conservative: mark everything present if too deep.
                set_all(features);
                return true;
            }
            // Early exit: if all features are already found, no need to keep walking.
            if features.all_set() {
                return true;
            }
            if *visits_left == 0 {
                return false;
            }
            *visits_left -= 1;
            maybe_grow_expr_stack(|| {
                node_features(expr, features);
                match expr {
                    ChcExpr::ConstArray(_, val) => inner(val, features, depth + 1, visits_left),
                    ChcExpr::ArrayLambda(lambda) => {
                        inner(lambda.body(), features, depth + 1, visits_left)
                            && lambda
                                .captures()
                                .iter()
                                .all(|value| inner(value, features, depth + 1, visits_left))
                    }
                    ChcExpr::FuncApp(_, _, args)
                    | ChcExpr::PredicateApp(_, _, args)
                    | ChcExpr::Op(_, args) => args
                        .iter()
                        .all(|a| inner(a, features, depth + 1, visits_left)),
                    _ => true,
                }
            })
        }

        let mut features = ExprFeatures::default();
        let mut visits_left = SCAN_PLAIN_VISITS;
        if !inner(self, &mut features, 0, &mut visits_left) {
            features = self.scan_features_dag();
        }
        features.close_under_preprocessing();
        features
    }

    /// The DAG form of the [`Self::scan_features`] walk (before closure).
    fn scan_features_dag(&self) -> ExprFeatures {
        let mut features = ExprFeatures::default();
        if super::super::dag::longest_path_at_least(self, MAX_EXPR_RECURSION_DEPTH) {
            set_all(&mut features);
            return features;
        }
        let mut visited: ay_core::kani_compat::DetHashSet<*const ChcExpr> =
            ay_core::kani_compat::DetHashSet::default();
        let mut stack: Vec<&ChcExpr> = vec![self];
        while let Some(expr) = stack.pop() {
            if features.all_set() {
                break;
            }
            node_features(expr, &mut features);
            if let ChcExpr::ArrayLambda(lambda) = expr {
                if visited.insert(std::sync::Arc::as_ptr(lambda.body())) {
                    stack.push(lambda.body());
                }
            }
            for child in super::super::dag::children(expr) {
                if visited.insert(std::sync::Arc::as_ptr(child)) {
                    stack.push(child.as_ref());
                }
            }
        }
        features
    }
}
