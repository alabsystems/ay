// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared helpers for CHC expression extraction.

use ay_core::kani_compat::DetHashSet as FxHashSet;

use crate::ChcExpr;

/// Collect deduplicated variable names referenced by an expression.
#[inline]
pub(crate) fn expr_var_names(expr: &ChcExpr) -> FxHashSet<String> {
    expr.vars().into_iter().map(|v| v.name).collect()
}
