// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solve step result type for DPLL(T).

use ay_core::{
    BoundRefinementRequest, DisequalitySplitRequest, ExpressionSplitRequest, ModelEqualityRequest,
    SplitRequest, StringLemma, TheoryLemma,
};
use ay_sat::SatResult;

/// Result of a solve step, either a final result or a split request
#[derive(Debug, Clone)]
#[non_exhaustive]
#[must_use = "solve step results must be matched — NeedSplit/NeedStringLemma require action"]
pub enum SolveStepResult {
    /// Final solve result
    Done(SatResult),
    /// Theory needs tighter bound atoms created from implied bounds.
    NeedBoundRefinements(Vec<BoundRefinementRequest>),
    /// Theory needs a split on an integer variable.
    /// The executor should create the split atoms and call `apply_split` to continue.
    NeedSplit(SplitRequest),
    /// Theory needs a split to exclude a specific value (disequality).
    /// The executor should create atoms for `x < c` and `x > c` to exclude `x = c`.
    NeedDisequalitySplit(DisequalitySplitRequest),
    /// Theory needs a split on a multi-variable expression disequality (E != F).
    /// The executor should create atoms for `E < F` and `E > F` to exclude `E = F`.
    NeedExpressionSplit(ExpressionSplitRequest),
    /// String theory needs a lemma clause added to the SAT solver.
    /// The executor creates new terms (skolems, concat applications) and adds the clause.
    NeedStringLemma(StringLemma),
    /// Theory needs permanent clause(s) added to the current SAT state.
    NeedLemmas(Vec<TheoryLemma>),
    /// Theory combination needs a speculative model equality (#4906).
    /// The executor should create `(= lhs rhs)`, allocate a SAT variable,
    /// set its phase to true, and continue solving.
    NeedModelEquality(ModelEqualityRequest),
    /// Batch variant: multiple model equalities needed in one pipeline restart (#6303).
    NeedModelEqualities(Vec<ModelEqualityRequest>),
}
