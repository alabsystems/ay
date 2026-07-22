// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr, clippy::print_stdout)]
#![allow(clippy::panic)]

//! Soundness test group for ay-sat.
//!
//! Consolidates all soundness regression and verification tests into a
//! single test binary to reduce compilation overhead.

mod common;

#[path = "group_soundness/otfs_soundness.rs"]
mod otfs_soundness;
#[path = "group_soundness/sat_soundness_regression.rs"]
mod sat_soundness_regression;
#[path = "group_soundness/soundness_3309_manol_pipe_c9.rs"]
mod soundness_3309_manol_pipe_c9;
#[path = "group_soundness/soundness_3437_conditioning_gbce.rs"]
mod soundness_3437_conditioning_gbce;
#[path = "group_soundness/soundness_3468_factor_sat.rs"]
mod soundness_3468_factor_sat;
#[path = "group_soundness/soundness_3770_uf200.rs"]
mod soundness_3770_uf200;
#[path = "group_soundness/soundness_3785_circuit_multiplier22.rs"]
mod soundness_3785_circuit_multiplier22;
#[path = "group_soundness/soundness_3913_uf_random.rs"]
mod soundness_3913_uf_random;
#[path = "group_soundness/soundness_6892_bve_factor_shrink.rs"]
mod soundness_6892_bve_factor_shrink;
#[path = "group_soundness/soundness_6999_feature_isolation.rs"]
mod soundness_6999_feature_isolation;
#[path = "group_soundness/soundness_7330_bve_nongate.rs"]
mod soundness_7330_bve_nongate;
#[path = "group_soundness/soundness_7904_drat_sweep.rs"]
mod soundness_7904_drat_sweep;
#[path = "group_soundness/soundness_7904_preprocessing.rs"]
mod soundness_7904_preprocessing;
#[path = "group_soundness/soundness_bve_factor_crn.rs"]
mod soundness_bve_factor_crn;
#[path = "group_soundness/soundness_circuit_equiv.rs"]
mod soundness_circuit_equiv;
#[path = "group_soundness/soundness_comprehensive.rs"]
mod soundness_comprehensive;
#[path = "group_soundness/soundness_expanded_7904.rs"]
mod soundness_expanded_7904;
#[path = "group_soundness/soundness_regression.rs"]
mod soundness_regression;
#[path = "group_soundness/theory_backend_soundness.rs"]
mod theory_backend_soundness;
