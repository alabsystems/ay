// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared test utilities for ay-sat.

use crate::{Literal, Variable};

/// Create a literal from a variable index and polarity.
///
/// Used extensively in unit tests across the crate.
pub(crate) fn lit(var: u32, positive: bool) -> Literal {
    if positive {
        Literal::positive(Variable(var))
    } else {
        Literal::negative(Variable(var))
    }
}

/// Create a literal from a signed DIMACS-style integer.
///
/// Positive values create positive literals, negative values create negative literals.
/// Variable numbering is 1-based (DIMACS convention).
pub(crate) fn lit_signed(v: i32) -> Literal {
    let var = Variable(v.unsigned_abs() - 1);
    if v > 0 {
        Literal::positive(var)
    } else {
        Literal::negative(var)
    }
}
