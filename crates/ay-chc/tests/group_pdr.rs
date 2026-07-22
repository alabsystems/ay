// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Consolidated PDR integration tests.
//!
//! Each submodule was previously a standalone integration test binary.
//! Grouping them into one binary reduces compilation overhead and prevents
//! OOM during `cargo test`.

#[path = "group_pdr/pdr_array_diagnostic.rs"]
mod pdr_array_diagnostic;
#[path = "group_pdr/pdr_array_diagnostic2.rs"]
mod pdr_array_diagnostic2;
#[path = "group_pdr/pdr_array_support.rs"]
mod pdr_array_support;
#[path = "group_pdr/pdr_bv_array_sort_bug.rs"]
mod pdr_bv_array_sort_bug;
#[path = "group_pdr/pdr_datatype.rs"]
mod pdr_datatype;
#[path = "group_pdr/pdr_examples.rs"]
mod pdr_examples;
#[path = "group_pdr/pdr_high_arity_timeout.rs"]
mod pdr_high_arity_timeout;
#[path = "group_pdr/pdr_model_verification_negative.rs"]
mod pdr_model_verification_negative;
#[path = "group_pdr/pdr_soundness.rs"]
mod pdr_soundness;
#[path = "group_pdr/pdr_unbounded_loop.rs"]
mod pdr_unbounded_loop;
