// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consolidated theory_misc integration tests for ay-dpll.
//! Groups 10 test modules into a single binary to reduce link time.

#![allow(clippy::panic)]

mod common;

#[path = "group_theory_misc/cross_check_4542.rs"]
mod cross_check_4542;
#[path = "group_theory_misc/ho_seq_refutation.rs"]
mod ho_seq_refutation;
#[path = "group_theory_misc/logic_auto_detection.rs"]
mod logic_auto_detection;
#[path = "group_theory_misc/model_equality_nonconvex_4906.rs"]
mod model_equality_nonconvex_4906;
#[path = "group_theory_misc/model_equality_sort_filter_4906.rs"]
mod model_equality_sort_filter_4906;
#[path = "group_theory_misc/smt_soundness_gate.rs"]
mod smt_soundness_gate;
#[path = "group_theory_misc/soundness_6020.rs"]
mod soundness_6020;
#[path = "group_theory_misc/theory_incremental_model_sync_2824.rs"]
mod theory_incremental_model_sync_2824;
#[path = "group_theory_misc/theory_push_pop_contract.rs"]
mod theory_push_pop_contract;
#[path = "group_theory_misc/theory_smoke_tests.rs"]
mod theory_smoke_tests;
