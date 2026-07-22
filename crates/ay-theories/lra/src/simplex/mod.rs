// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Dual simplex algorithm, pivoting, and conflict generation.

use ay_core::{DebugChannel, FarkasAnnotation, TheoryConflict, TheoryLit, TheoryResult};
use num_rational::BigRational;
use num_traits::{One, Zero};
use tracing::{debug, info, trace};

use crate::rational::Rational;
use crate::types::{ColEntry, ErrorKey, InfRational, RowPrecision};
use crate::{BoundType, LraSolver, TableauRow, VarInfo, VarStatus};

/// After this many consecutive iterations with the same basis hash,
/// switch to Bland's rule for anti-cycling. Reference: Z3 uses 1000
/// (lp_primal_core_solver.h:380-381 `m_bland_mode_threshold`).
const BLAND_THRESHOLD: u32 = 1000;

// Cached `--debug lra` channel (checked once per process). #8858
cached_debug_channel!(debug_lra, DebugChannel::Lra);

pub(crate) mod basis_solve;
mod debug;
mod feasibility;
pub(crate) mod float_layer;
pub(crate) mod float_simplex;
mod pivot;
mod solve;
#[cfg(test)]
mod tests;
mod updates;
