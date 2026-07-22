// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Gomory cutting plane methods for LRA.
//!
//! Generates and adds Gomory cuts from the simplex tableau for
//! mixed-integer linear programming.

use std::cmp::Ordering;

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermId;
use ay_core::DebugChannel;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::rational::Rational;
use crate::{BoundType, GomoryCut, LinearExpr, LraSolver, TableauRow, VarInfo, VarStatus};

// Cached `--debug gomory` channel (checked once per process). #8858
cached_debug_channel!(debug_gomory, DebugChannel::Gomory);

const MAX_GOMORY_CUTS_PER_CHECK: usize = 2;

#[derive(Clone)]
struct GomoryCandidate {
    row_idx: usize,
    basic_var: u32,
    score: BigRational,
    /// Number of rows referencing this basic variable (Z3 `usage_in_terms`).
    usage: usize,
}

mod generation;
mod support;
#[cfg(test)]
mod tests;
