// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Consolidated BV (bitvector) CHC integration tests.
//!
//! Each submodule was previously a standalone integration test binary.
//! Grouping them into one binary reduces compilation overhead and prevents
//! OOM during `cargo test`.

#[path = "group_bv/bv_chc_soundness_6848.rs"]
mod bv_chc_soundness_6848;
#[path = "group_bv/bv_clause_splitting_5877.rs"]
mod bv_clause_splitting_5877;
#[path = "group_bv/bv_concat_chc_8631.rs"]
mod bv_concat_chc_8631;
#[path = "group_bv/bv_int_mix_horn_8717.rs"]
mod bv_int_mix_horn_8717;
#[path = "group_bv/bv_modulo_acyclic_safety.rs"]
mod bv_modulo_acyclic_safety;
#[path = "group_bv/bv_mux_complement_soundness_7986.rs"]
mod bv_mux_complement_soundness_7986;
#[path = "group_bv/bv_wrap_offset_overflow_soundness.rs"]
mod bv_wrap_offset_overflow_soundness;
#[path = "group_bv/preprocessing_bv_soundness_6781.rs"]
mod preprocessing_bv_soundness_6781;
