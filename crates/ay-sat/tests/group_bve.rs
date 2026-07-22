// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr, clippy::print_stdout)]
#![allow(clippy::panic)]

//! BVE (bounded variable elimination) test group for ay-sat.
//!
//! Consolidates BVE-related soundness and regression tests into a single
//! test binary to reduce compilation overhead.

mod common;

#[path = "group_bve/bve_reconstruction_regression_8223.rs"]
mod bve_reconstruction_regression_8223;
#[path = "group_bve/bve_soundness.rs"]
mod bve_soundness;
