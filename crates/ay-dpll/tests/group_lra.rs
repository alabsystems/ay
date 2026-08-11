// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consolidated lra integration tests for ay-dpll.
//! Groups 20 test modules into a single binary to reduce link time.

#![allow(clippy::panic)]

mod common;

#[path = "group_lra/lra_atom_normalization_soundness.rs"]
mod lra_atom_normalization_soundness;
#[path = "group_lra/lra_coefficient_split_6155.rs"]
mod lra_coefficient_split_6155;
#[path = "group_lra/lra_incremental_push_pop.rs"]
mod lra_incremental_push_pop;
#[path = "group_lra/lra_incremental_regression_2822.rs"]
mod lra_incremental_regression_2822;
#[path = "group_lra/lra_mixed_diseq_drain_6269.rs"]
mod lra_mixed_diseq_drain_6269;
#[path = "group_lra/lra_performance_pivot.rs"]
mod lra_performance_pivot;
#[path = "group_lra/lra_propagation_always_active_8553.rs"]
mod lra_propagation_always_active_8553;
#[path = "group_lra/lra_sat_model_validation_6210.rs"]
mod lra_sat_model_validation_6210;
#[path = "group_lra/lra_slack_compensation_boundary_6209.rs"]
mod lra_slack_compensation_boundary_6209;
#[path = "group_lra/lra_strict_bound_axiom.rs"]
mod lra_strict_bound_axiom;
#[path = "group_lra/qf_lira_check_sat_assuming.rs"]
mod qf_lira_check_sat_assuming;
#[path = "group_lra/qf_lra_additive_lane_6579.rs"]
mod qf_lra_additive_lane_6579;
#[path = "group_lra/qf_lra_eager_stats_default_6597.rs"]
mod qf_lra_eager_stats_default_6597;
#[path = "group_lra/qf_lra_family_split_6570.rs"]
mod qf_lra_family_split_6570;
#[path = "group_lra/qf_lra_propagation_soundness_8529.rs"]
mod qf_lra_propagation_soundness_8529;
#[path = "group_lra/qf_lra_relative_lane_6586.rs"]
mod qf_lra_relative_lane_6586;
#[path = "group_lra/qf_lra_release_soundness_6564.rs"]
mod qf_lra_release_soundness_6564;
#[path = "group_lra/qf_lra_release_soundness_6582.rs"]
mod qf_lra_release_soundness_6582;
#[path = "group_lra/qf_lra_smtcomp_differential.rs"]
mod qf_lra_smtcomp_differential;
#[path = "group_lra/qf_lra_vpm2_soundness_8347.rs"]
mod qf_lra_vpm2_soundness_8347;
