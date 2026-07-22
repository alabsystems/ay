// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr, clippy::print_stdout)]
#![allow(clippy::panic)]

//! Extended integration test group for ay-sat.
//!
//! Consolidates supplementary integration tests (correctness, extended,
//! proof) that were separate from the main integration.rs test suite.

mod common;

#[path = "group_integration_ext/integration_correctness.rs"]
mod integration_correctness;
#[path = "group_integration_ext/integration_extended.rs"]
mod integration_extended;
#[path = "group_integration_ext/integration_proof.rs"]
mod integration_proof;
