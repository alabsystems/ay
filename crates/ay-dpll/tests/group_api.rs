// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consolidated api integration tests for ay-dpll.
//! Groups 6 test modules into a single binary to reduce link time.

#![allow(clippy::panic)]

mod common;

#[path = "group_api/counterexample_benchmark_4522.rs"]
mod counterexample_benchmark_4522;
#[path = "group_api/counterexample_style_public_api.rs"]
mod counterexample_style_public_api;
#[path = "group_api/interface_bridge_5227.rs"]
mod interface_bridge_5227;
#[path = "group_api/interface_bridge_5230.rs"]
mod interface_bridge_5230;
#[path = "group_api/parallel_instance_isolation_6563.rs"]
mod parallel_instance_isolation_6563;
#[path = "group_api/solver_construct_stack_safety.rs"]
mod solver_construct_stack_safety;
#[path = "group_api/step_mode_api_canary_6315.rs"]
mod step_mode_api_canary_6315;
