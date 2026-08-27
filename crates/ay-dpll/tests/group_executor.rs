// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consolidated executor integration tests for ay-dpll.
//! Groups 11 test modules into a single binary to reduce link time.

#![allow(clippy::panic)]

mod common;

#[path = "group_executor/auflia_gate_select_model_a1.rs"]
mod auflia_gate_select_model_a1;
#[path = "group_executor/construction_stats_6364.rs"]
mod construction_stats_6364;
#[path = "group_executor/dt_derived_unit_lemmas_certified.rs"]
mod dt_derived_unit_lemmas_certified;
#[path = "group_executor/dt_ground_conflict_strict_publication.rs"]
mod dt_ground_conflict_strict_publication;
#[path = "group_executor/eager_batch_signal_6503.rs"]
mod eager_batch_signal_6503;
#[path = "group_executor/empty_assertions_gap_a_7912.rs"]
mod empty_assertions_gap_a_7912;
#[path = "group_executor/executor_array_row_case_split_certified.rs"]
mod executor_array_row_case_split_certified;
#[path = "group_executor/executor_eq_diamond20.rs"]
mod executor_eq_diamond20;
#[path = "group_executor/executor_regression_1708_order_dependent.rs"]
mod executor_regression_1708_order_dependent;
#[path = "group_executor/executor_simple_processors_006_002_0008.rs"]
mod executor_simple_processors_006_002_0008;
#[path = "group_executor/expression_split_1915.rs"]
mod expression_split_1915;
#[path = "group_executor/no_diseq_propagation_8455.rs"]
mod no_diseq_propagation_8455;
#[path = "group_executor/shared_disequality_split_6148.rs"]
mod shared_disequality_split_6148;
#[path = "group_executor/split_loop_timing_6503.rs"]
mod split_loop_timing_6503;
#[path = "group_executor/split_loop_timing_accumulation_6503.rs"]
mod split_loop_timing_accumulation_6503;
