// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Assume step result type for DPLL(T) with assumptions.

use ay_core::{
    BoundRefinementRequest, DisequalitySplitRequest, ExpressionSplitRequest, ModelEqualityRequest,
    SplitRequest, StringLemma, TheoryLemma,
};
use ay_sat::AssumeResult;

/// Result of a solve step with assumptions, for iterative split handling (#1771).
#[derive(Debug, Clone)]
#[non_exhaustive]
#[must_use = "solve step results must be matched — NeedSplit/NeedStringLemma require action"]
pub enum AssumeStepResult {
    /// Final solve result (with optional unsat core for UNSAT)
    Done(AssumeResult),
    /// Theory needs tighter bound atoms created from implied bounds.
    NeedBoundRefinements(Vec<BoundRefinementRequest>),
    /// Theory needs a split on an integer variable.
    NeedSplit(SplitRequest),
    /// Theory needs a disequality split.
    NeedDisequalitySplit(DisequalitySplitRequest),
    /// Theory needs an expression split.
    NeedExpressionSplit(ExpressionSplitRequest),
    /// String theory needs a lemma clause.
    NeedStringLemma(StringLemma),
    /// Theory needs permanent clause(s) added to the current SAT state.
    NeedLemmas(Vec<TheoryLemma>),
    /// Theory combination needs a speculative model equality (#4906).
    NeedModelEquality(ModelEqualityRequest),
    /// Batch variant: multiple model equalities needed in one pipeline restart (#6303).
    NeedModelEqualities(Vec<ModelEqualityRequest>),
}
