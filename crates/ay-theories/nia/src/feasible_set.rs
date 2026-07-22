// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Feasible-set data structure for NLSAT-style look-ahead and arithmetic
//! propagation branching.
//!
//! This module re-exports the shared implementation from
//! [`ay_nonlinear_common::feasible_set`]. NIA and NRA originally maintained
//! byte-identical ~1090-line copies of this file (#8824); consolidating them
//! keeps fixes and extensions in sync across both theories.

pub(crate) use ay_nonlinear_common::feasible_set::{FeasibilityClass, FeasibleSet};
