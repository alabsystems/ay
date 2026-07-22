// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consolidated nonlinear integration tests for ay-dpll.
//! Groups 7 test modules into a single binary to reduce link time.

#![allow(clippy::panic)]

mod common;

#[path = "group_nonlinear/auf_select_nonlinear_8920.rs"]
mod auf_select_nonlinear_8920;
#[path = "group_nonlinear/nia_theory_verification.rs"]
mod nia_theory_verification;
#[path = "group_nonlinear/nra_irrational_soundness.rs"]
mod nra_irrational_soundness;
#[path = "group_nonlinear/nra_scope_leak_6183.rs"]
mod nra_scope_leak_6183;
#[path = "group_nonlinear/nra_sketch_icp.rs"]
mod nra_sketch_icp;
#[path = "group_nonlinear/nra_stack_safety_6765.rs"]
mod nra_stack_safety_6765;
#[path = "group_nonlinear/sign_theory_regression.rs"]
mod sign_theory_regression;
#[path = "group_nonlinear/snia_dispatch_3389.rs"]
mod snia_dispatch_3389;
