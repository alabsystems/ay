// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Grouped QF_LRA integration tests.

#[path = "common/spawn.rs"]
pub mod spawn;

#[path = "group_lra/qf_lra_additive_lane_6579.rs"]
mod qf_lra_additive_lane_6579;

#[path = "group_lra/qf_lra_cli_release_soundness_6564.rs"]
mod qf_lra_cli_release_soundness_6564;

#[path = "group_lra/qf_lra_cli_release_soundness_6582.rs"]
mod qf_lra_cli_release_soundness_6582;

#[path = "group_lra/qf_lra_cli_release_sweep_6564.rs"]
mod qf_lra_cli_release_sweep_6564;
