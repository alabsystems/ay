// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MPS and CPLEX LP parsers.
//!
//! Both read a file exactly into a [`crate::exact::ExactProblem`]
//! ([`parse_mps_exact`], [`parse_lp_exact`]), one documented reading per
//! construct, and refuse what readers in common use read differently;
//! [`parse_mps`] and [`parse_lp`] are its floating-point copy.

pub(crate) mod lp;
pub(crate) mod lp_tok;
pub(crate) mod mps;

pub use lp::{parse_lp, parse_lp_exact};
pub use mps::{parse_mps, parse_mps_exact};
