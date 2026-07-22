// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Public objective-value type for the optimization (`maximize`/`minimize`) API.

use num_rational::BigRational;

/// The optimum of a single optimization objective after an optimizing check.
///
/// Returned by [`Solver::get_objective_value`](crate::api::Solver::get_objective_value)
/// once [`Solver::optimize_check`](crate::api::Solver::optimize_check) has run.
///
/// AY computes objective optima in the executor's optimization path (Int/Real via
/// exponential + binary / simplex search; BitVec over its finite unsigned
/// domain). A finite optimum is exposed as an exact [`BigRational`] — Int and
/// BitVec optima are whole rationals (the BitVec value is the unsigned integer,
/// matching `(get-objectives)`); Real optima may be proper fractions.
///
/// An objective with no finite optimum is reported as infinity, per SMT-LIB OMT
/// conventions (matching z3): [`PosInfinity`](Self::PosInfinity) for an unbounded
/// `maximize`, [`NegInfinity`](Self::NegInfinity) for an unbounded `minimize`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ObjectiveValue {
    /// An exact finite optimum.
    Finite(BigRational),
    /// `+oo`: the objective is unbounded above (an unbounded `maximize`).
    PosInfinity,
    /// `-oo`: the objective is unbounded below (an unbounded `minimize`).
    NegInfinity,
}

impl ObjectiveValue {
    /// The finite optimum, or `None` if the objective is unbounded.
    #[must_use]
    pub fn as_finite(&self) -> Option<&BigRational> {
        match self {
            Self::Finite(r) => Some(r),
            Self::PosInfinity | Self::NegInfinity => None,
        }
    }

    /// `true` if the optimum is `+oo` or `-oo` (no finite optimum).
    #[must_use]
    pub fn is_infinite(&self) -> bool {
        matches!(self, Self::PosInfinity | Self::NegInfinity)
    }
}
