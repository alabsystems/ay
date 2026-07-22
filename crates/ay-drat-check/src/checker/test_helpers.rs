// Copyright 2026 Andrew Yates
// Shared test helpers for DRAT checker tests.

use crate::literal::Literal;

/// Create a literal for testing. `var` is 0-indexed, mapped to DIMACS
/// variable `var + 1`.
pub(crate) fn lit(var: u32, positive: bool) -> Literal {
    if positive {
        Literal::from_dimacs(var as i32 + 1)
    } else {
        Literal::from_dimacs(-(var as i32 + 1))
    }
}
