// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed evidence for theory applications with unconstrained results.

/// The exact theory case for which the evaluator proved that an application's
/// result is unconstrained.
///
/// This is evidence about the input, not authority supplied by a model. The
/// evaluator constructs a variant only after checking the defining condition
/// (a non-finite IEEE value or an exact zero divisor), and still validates the
/// returned value's result sort. Generic applications, finite `fp.to_real`, and
/// nonzero division never reach the typed model-completion hook.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum ProvenUnconstrainedKind {
    /// `fp.to_real` applied to a NaN or either infinity.
    FpToRealNonFinite,
    /// Real division `/` with an exactly zero divisor.
    RealDivByZero,
    /// Integer `div` with an exactly zero divisor.
    IntDivByZero,
    /// Integer `mod` with an exactly zero divisor.
    IntModByZero,
}
