// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared theory-check result enums and step-mode dispatch helpers.

use ay_core::{
    DisequalitySplitRequest, ExpressionSplitRequest, ModelEqualityRequest, SplitRequest,
    StringLemma, TheoryLemma,
};
use ay_sat::{Literal, SatResult};

use crate::SolveStepResult;

/// Result of a solve step, either a final result or a split request
#[derive(Debug, Clone)]
#[non_exhaustive]
#[must_use = "solve step results must be matched — NeedSplit/NeedStringLemma require action"]
pub(crate) enum TheoryCheck {
    /// Theory accepts the model.
    Sat,
    /// Theory returned a SAT conflict clause already mapped to SAT literals.
    Conflict(Vec<Literal>),
    /// Theory could not determine satisfiability on the current state.
    Unknown,
    /// Theory propagated literals - new clauses were added to SAT solver.
    Propagated(usize),
    /// Theory needs to split on an integer variable (for branch-and-bound LIA).
    NeedSplit(SplitRequest),
    /// Theory needs to split on a disequality (x != c).
    NeedDisequalitySplit(DisequalitySplitRequest),
    /// Theory needs to split on a multi-variable expression disequality (E != F).
    NeedExpressionSplit(ExpressionSplitRequest),
    /// String theory needs a lemma clause.
    NeedStringLemma(StringLemma),
    /// Theory needs permanent clause(s) added to the SAT solver.
    NeedLemmas(Vec<TheoryLemma>),
    /// Theory combination needs a speculative model equality (#4906).
    NeedModelEquality(ModelEqualityRequest),
    /// Batch variant: multiple model equalities needed in one pipeline restart (#6303).
    NeedModelEqualities(Vec<ModelEqualityRequest>),
}

/// Result of dispatching a [`TheoryCheck`] in the DPLL(T) loop.
///
/// Centralizes theory-check handling so that adding a new `TheoryCheck`
/// variant requires editing one match block instead of six.
pub(crate) enum TheoryDispatch {
    /// Theory accepts the model.
    Accept,
    /// Theory unknown or split not handled in loop mode.
    Unknown,
    /// Theory needs an integer split (forwarded in step mode).
    NeedSplit(SplitRequest),
    /// Theory needs a disequality split (forwarded in step mode).
    NeedDisequalitySplit(DisequalitySplitRequest),
    /// Theory needs an expression split (forwarded in step mode).
    NeedExpressionSplit(ExpressionSplitRequest),
    /// Theory needs a string lemma (forwarded in step mode).
    NeedStringLemma(StringLemma),
    /// Theory needs permanent clause(s) added in-place.
    NeedLemmas(Vec<TheoryLemma>),
    /// Theory combination needs a speculative model equality (#4906).
    NeedModelEquality(ModelEqualityRequest),
    /// Batch variant: multiple model equalities needed in one pipeline restart (#6303).
    NeedModelEqualities(Vec<ModelEqualityRequest>),
    /// Conflict clause added or propagation occurred; re-solve.
    Continue,
}

/// Result of the final Nelson-Oppen check after `check_during_propagate` accepts.
///
/// Combined theories need a full N-O fixpoint check to forward cross-theory
/// equalities (e.g., EUF congruence → LIA). (#6825)
pub(crate) enum FinalCheckResult {
    /// N-O fixpoint confirmed SAT (or theory doesn't need final check).
    Accept,
    /// Theory returned Unknown or a split we can't handle in loop mode.
    Unknown,
    /// N-O found a conflict; a clause was added to the SAT solver.
    Conflict,
}

impl TheoryDispatch {
    /// Convert to [`SolveStepResult`] for step-mode callers.
    /// Returns `None` for `Continue` (caller should loop).
    pub(crate) fn into_solve_step(self, model: Vec<bool>) -> Option<SolveStepResult> {
        Some(match self {
            Self::Accept => {
                // #7912: Assert model integrity at the theory->step dispatch
                // boundary. The SAT solver verified this model via
                // finalize_sat_model, and the theory solver accepted it.
                debug_assert!(
                    !model.is_empty(),
                    "BUG: TheoryDispatch::Accept with empty SAT model"
                );
                SolveStepResult::Done(SatResult::Sat(model))
            }
            Self::Unknown => SolveStepResult::Done(SatResult::Unknown),
            Self::NeedSplit(s) => SolveStepResult::NeedSplit(s),
            Self::NeedDisequalitySplit(s) => SolveStepResult::NeedDisequalitySplit(s),
            Self::NeedExpressionSplit(s) => SolveStepResult::NeedExpressionSplit(s),
            Self::NeedStringLemma(l) => SolveStepResult::NeedStringLemma(l),
            Self::NeedLemmas(lemmas) => SolveStepResult::NeedLemmas(lemmas),
            Self::NeedModelEquality(e) => SolveStepResult::NeedModelEquality(e),
            Self::NeedModelEqualities(es) => SolveStepResult::NeedModelEqualities(es),
            Self::Continue => return None,
        })
    }
}
