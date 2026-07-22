// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ChcExpr constructors, query methods, substitution, and simplification.

use super::{
    extract_int_constant, maybe_grow_expr_stack, walk_linear_expr, ChcExpr, ChcOp, ChcSort, ChcVar,
    LinearTermsProd, MAX_EXPR_RECURSION_DEPTH, MAX_PREPROCESSING_NODES,
};
use crate::PredicateId;

mod conjuncts;
mod constructors;
mod drop_safety;
mod expr_contains;
mod feature_scan;
mod linear_analysis;
mod substitute;

/// Result of a single-pass feature scan over a `ChcExpr` tree (#6360).
///
/// Instead of 6-8 separate `contains_*` tree walks, `scan_features()` detects
/// all preprocessing-relevant features in one traversal. Callers use the flags
/// to skip both the detection and transformation walks for absent features.
#[derive(Debug, Clone, Default)]
pub(crate) struct ExprFeatures {
    pub has_array_ops: bool,
    pub has_bv: bool,
    pub has_uf_apps: bool,
    pub has_dt: bool,
    pub has_mixed_sort_eq: bool,
    pub has_ite: bool,
    pub has_mod_or_div: bool,
    pub has_negation: bool,
    pub has_strict_int_comparison: bool,
}
