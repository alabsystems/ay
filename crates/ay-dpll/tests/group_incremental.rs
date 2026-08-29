// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consolidated incremental integration tests for ay-dpll.
//! Groups 7 test modules into a single binary to reduce link time.

#![allow(clippy::panic)]

mod common;

#[path = "group_incremental/bv_congruence_leaks_past_pop_7892.rs"]
mod bv_congruence_leaks_past_pop_7892;
#[path = "group_incremental/core_evolution_push_pop_8311.rs"]
mod core_evolution_push_pop_8311;
#[path = "group_incremental/dt_lazy_incremental_soundness.rs"]
mod dt_lazy_incremental_soundness;
#[path = "group_incremental/ematching_pushscope_repro.rs"]
mod ematching_pushscope_repro;
#[path = "group_incremental/fp_persistent_lane.rs"]
mod fp_persistent_lane;
#[path = "group_incremental/incremental_multi_check_sat_8154.rs"]
mod incremental_multi_check_sat_8154;
#[path = "group_incremental/incremental_needlemmas_proof_6717.rs"]
mod incremental_needlemmas_proof_6717;
#[path = "group_incremental/incremental_needlemmas_proof_6719.rs"]
mod incremental_needlemmas_proof_6719;
#[path = "group_incremental/incremental_push_pop_proof_reconstruction_6716.rs"]
mod incremental_push_pop_proof_reconstruction_6716;
#[path = "group_incremental/incremental_theory_stats_662.rs"]
mod incremental_theory_stats_662;
#[path = "group_incremental/reset_assertions_5850.rs"]
mod reset_assertions_5850;
#[path = "group_incremental/uf_nia_assuming_scoped_fallback.rs"]
mod uf_nia_assuming_scoped_fallback;
#[path = "group_incremental/unsat_core_vacuity_precision.rs"]
mod unsat_core_vacuity_precision;
