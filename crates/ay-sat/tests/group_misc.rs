// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr, clippy::print_stdout)]
#![allow(clippy::panic)]

//! Miscellaneous test group for ay-sat.
//!
//! Consolidates remaining integration tests that don't belong to a more
//! specific thematic group into a single test binary.

mod common;

#[path = "group_misc/bcp_profile.rs"]
mod bcp_profile;
#[path = "group_misc/bisect_ibm12.rs"]
mod bisect_ibm12;
#[path = "group_misc/bisect_soundness_p1.rs"]
mod bisect_soundness_p1;
#[path = "group_misc/cadical_cross_validate.rs"]
mod cadical_cross_validate;
#[path = "group_misc/cadical_differential_1k.rs"]
mod cadical_differential_1k;
#[path = "group_misc/clause_trace_boundary.rs"]
mod clause_trace_boundary;
#[path = "group_misc/congruence_default_guard.rs"]
mod congruence_default_guard;
#[path = "group_misc/congruence_high_var_gate_regression.rs"]
mod congruence_high_var_gate_regression;
#[path = "group_misc/constrain_api.rs"]
mod constrain_api;
#[path = "group_misc/contract_postconditions.rs"]
mod contract_postconditions;
#[path = "group_misc/delete_policy_guard.rs"]
mod delete_policy_guard;
#[path = "group_misc/disabled_feature_guards.rs"]
mod disabled_feature_guards;
#[path = "group_misc/finalize_sat_fail_audit.rs"]
mod finalize_sat_fail_audit;
#[path = "group_misc/finalize_sat_fail_paths.rs"]
mod finalize_sat_fail_paths;
#[path = "group_misc/inprocessing_scheduler_source_of_truth.rs"]
mod inprocessing_scheduler_source_of_truth;
#[path = "group_misc/lscb_mli.rs"]
mod lscb_mli;
#[path = "group_misc/mab_integration.rs"]
mod mab_integration;
#[path = "group_misc/new_var_internal_vectors.rs"]
mod new_var_internal_vectors;
#[path = "group_misc/par2_benchmark.rs"]
mod par2_benchmark;
#[path = "group_misc/preprocess_guard.rs"]
mod preprocess_guard;
#[path = "group_misc/propagation_backtrack_coverage.rs"]
mod propagation_backtrack_coverage;
#[path = "group_misc/public_api_set_solution_error.rs"]
mod public_api_set_solution_error;
#[path = "group_misc/repro_7929.rs"]
mod repro_7929;
#[path = "group_misc/repro_crn_watch_bug.rs"]
mod repro_crn_watch_bug;
#[path = "group_misc/scoped_theory_extension_guards.rs"]
mod scoped_theory_extension_guards;
#[path = "group_misc/tla2_trace_validation.rs"]
mod tla2_trace_validation;
#[path = "group_misc/tla_invariant_proptest.rs"]
mod tla_invariant_proptest;
