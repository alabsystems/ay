// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array MBP: Model-Based Projection for array-sorted variables.
//!
//! Eliminates array variables from an implicant via three phases:
//! 1. **Equality resolution** — substitute via `a = store(b, i, v)` or `a = b`.
//! 2. **Select factoring** — replace `select(a, idx)` with fresh scalar constants.
//! 3. **Ackermannization** — same model-index => same value constraints.
//!
//! Ref: Z3 `reference/z3/src/qe/mbp/mbp_arrays.cpp`.

use crate::expr::eval_array_select;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, SmtValue};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::sync::Arc;

use super::{Literal, Mbp};

mod factoring;
mod model_eval;
mod resolution;
mod saturation;

/// A `select(array_var, index)` occurrence with its fresh replacement variable.
#[derive(Debug, Clone)]
struct SelectOccurrence {
    index: ChcExpr,
    fresh_var: ChcVar,
    /// `None` when the index expression could not be evaluated under the model.
    /// Occurrences with `None` are never merged (treated as unique), which is
    /// sound: creating extra fresh variables only loses precision, not soundness.
    index_model_value: Option<SmtValue>,
}

/// Partial equality for one-dimensional array store inversion:
/// `lhs ==_diff rhs` means the arrays are equal except possibly at `diff`.
#[derive(Debug, Clone)]
struct PartialArrayEq {
    lhs: ChcExpr,
    rhs: ChcExpr,
    diff_indices: Vec<ChcExpr>,
}
