// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consolidated differential integration tests for ay-dpll.
//! Groups 4 test modules into a single binary to reduce link time.

#![allow(clippy::panic)]

mod common;

#[path = "group_differential/differential_z3.rs"]
mod differential_z3;
#[path = "group_differential/proptest_strings_soundness.rs"]
mod proptest_strings_soundness;
#[path = "group_differential/proptest_theory_integration.rs"]
mod proptest_theory_integration;
