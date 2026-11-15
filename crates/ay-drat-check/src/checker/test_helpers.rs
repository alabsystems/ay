// Copyright 2026 Andrew Yates
// Shared test helpers for DRAT checker tests.

use crate::literal::Literal;

/// Create a literal for testing. `var` is 0-indexed, mapped to DIMACS
/// variable `var + 1`.
pub(crate) fn lit(var: u32, positive: bool) -> Literal {
    // The packed encoding `2 * var + negative` is `from_dimacs(±(var + 1))`
    // for every variable up to `Variable::MAX_ID`, with no DIMACS arithmetic
    // to overflow.
    Literal::from_raw((var << 1) | u32::from(!positive))
}
