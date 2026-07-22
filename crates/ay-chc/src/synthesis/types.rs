// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Types for structural invariant synthesis.

use crate::{ChcVar, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;

use crate::ChcExpr;

/// Result of structural synthesis attempt.
#[derive(Debug, Clone)]
pub(crate) enum SynthesisResult {
    /// Successfully synthesized and verified an invariant.
    Success(SynthesizedInvariant),
    /// Pattern recognized but invariant not inductive - fall back to PDR.
    NotInductive,
    /// No pattern recognized - fall back to PDR.
    NoPattern,
}

/// A successfully synthesized invariant.
#[derive(Debug, Clone)]
pub(crate) struct SynthesizedInvariant {
    /// Map from predicate ID to its invariant expression.
    pub interpretations: FxHashMap<PredicateId, ChcExpr>,
    /// Pattern that was matched.
    pub pattern: SynthesisPattern,
}

/// Recognized synthesis pattern.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SynthesisPattern {
    /// Bounded increment: `x' = x + K` with `x < N` guard.
    BoundedIncrement,
    /// Bounded decrement: `x' = x - K` with `x > L` guard.
    BoundedDecrement,
    /// Threshold ITE counter relation: `y' = ite(x >= K, y + 1, y)`.
    ThresholdIteEquality,
    /// Safety condition synthesized from a false-query clause.
    QuerySafetyCondition,
    /// Interval from init and guard analysis.
    IntervalBounds,
}

impl std::fmt::Display for SynthesisPattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BoundedIncrement => write!(f, "BoundedIncrement"),
            Self::BoundedDecrement => write!(f, "BoundedDecrement"),
            Self::ThresholdIteEquality => write!(f, "ThresholdIteEquality"),
            Self::QuerySafetyCondition => write!(f, "QuerySafetyCondition"),
            Self::IntervalBounds => write!(f, "IntervalBounds"),
        }
    }
}

/// Detected loop pattern with extracted bounds.
#[derive(Debug, Clone)]
pub(super) struct LoopPattern {
    /// Predicate this pattern was detected for.
    pub(super) pred_id: PredicateId,
    /// Argument position within the predicate.
    pub(super) var_index: usize,
    /// Variable being updated.
    pub(super) var: ChcVar,
    /// Update amount (positive for increment, negative for decrement).
    pub(super) stride: i128,
    /// Upper bound from guard (if any).
    pub(super) upper_bound: Option<i128>,
    /// Lower bound from guard (if any).
    pub(super) lower_bound: Option<i128>,
    /// Initial value (if determinable from fact clause).
    pub(super) init_value: Option<i128>,
    /// Pattern type.
    pub(super) pattern: SynthesisPattern,
}
