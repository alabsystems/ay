// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! String theory pre-registration passes for executor integration.
//!
//! Pre-registers eager decompositions for str.contains, extended function
//! reductions, and overlap constant equalities before the DPLL(T) solve loop.

mod contains;
mod overlap;
mod reductions;
#[cfg(test)]
mod tests;
mod to_int_reductions;

pub(in crate::executor) use reductions::str_p2_enabled;
#[cfg(test)]
pub(in crate::executor) use reductions::STR_P2_TEST_OVERRIDE;
pub(in crate::executor) use to_int_reductions::str_p3_enabled;
#[cfg(test)]
pub(in crate::executor) use to_int_reductions::STR_P3_TEST_OVERRIDE;

/// Result of attempting to merge a prefix and suffix with a fixed target length.
#[derive(Debug)]
pub(super) enum OverlapMergeResult {
    /// The prefix and suffix merge to produce a uniquely determined string.
    Merged(String),
    /// The overlap is provably impossible (overlap chars mismatch, or
    /// target length too short for either prefix or suffix alone).
    Conflict,
    /// Cannot determine: free middle characters or other undetermined case.
    Undetermined,
}
