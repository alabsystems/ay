// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared data structures for nonlinear arithmetic theory solvers.
//!
//! The NIA (nonlinear integer arithmetic) and NRA (nonlinear real arithmetic)
//! theory solvers share the same underlying feasible-set data structure
//! (interval union over the rationals). This crate hosts that shared module
//! so that fixes and extensions apply to both theories simultaneously.
//!
//! See [`feasible_set`] for the `FeasibleSet`, `FeasibilityClass`, `Interval`,
//! and `Endpoint` types.

#![forbid(unsafe_code)]

pub mod feasible_set;

#[cfg(kani)]
mod verification;
