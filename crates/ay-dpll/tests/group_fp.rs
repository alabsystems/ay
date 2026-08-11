// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consolidated fp integration tests for ay-dpll.
//! Groups 12 test modules into a single binary to reduce link time.

#![allow(clippy::panic)]

mod common;

#[path = "group_fp/fp_arithmetic_correctness.rs"]
mod fp_arithmetic_correctness;
#[path = "group_fp/fp_congruence.rs"]
mod fp_congruence;
#[path = "group_fp/fp_conversions.rs"]
mod fp_conversions;
#[path = "group_fp/fp_forward_error.rs"]
mod fp_forward_error;
#[path = "group_fp/fp_guard_and_minmax.rs"]
mod fp_guard_and_minmax;
#[path = "group_fp/fp_indexed_special_constants.rs"]
mod fp_indexed_special_constants;
#[path = "group_fp/fp_integration.rs"]
mod fp_integration;
#[path = "group_fp/fp_model_extraction.rs"]
mod fp_model_extraction;
#[path = "group_fp/fp_rem.rs"]
mod fp_rem;
#[path = "group_fp/fp_round_integral.rs"]
mod fp_round_integral;
#[path = "group_fp/fp_rounding_modes.rs"]
mod fp_rounding_modes;
#[path = "group_fp/fp_rounding_tests.rs"]
mod fp_rounding_tests;

#[path = "group_fp/fp_symbolic_rm.rs"]
mod fp_symbolic_rm;
#[path = "group_fp/fp_to_bv.rs"]
mod fp_to_bv;
#[path = "group_fp/fp_to_ieee_bv.rs"]
mod fp_to_ieee_bv;
