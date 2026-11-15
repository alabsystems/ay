// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete named model DATA, without equality or solver-evidence authority.

use std::sync::Arc;

use super::ModelValue;

/// One complete interpretation from a currently accepted native model.
///
/// Literal values retain the existing typed representation. Functional arrays
/// retain the entire immutable function, not sampled cells or a parsed lambda.
/// This data does not carry a SAT capability, checked trace, or proof seal:
/// callers must retain the originating solve evidence and independently replay
/// their source witness. Structural inequality is not array disequality.
#[derive(Clone, Debug)]
pub enum CompleteModelValue {
    Literal(ModelValue),
    FunctionalArray(Arc<ay_model_check::ArraySnapshot>),
}
