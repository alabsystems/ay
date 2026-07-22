// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Prover audit tests for the strings theory.
//!
//! These tests verify edge cases and regression gaps identified during
//! the strings zone prover audit. Each test documents what it checks
//! and why it matters.

use ay_dpll::Executor;
use ay_frontend::parse;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

#[path = "strings_prover_audit/memory_and_regression.rs"]
mod memory_and_regression;
#[path = "strings_prover_audit/proof_coverage.rs"]
mod proof_coverage;
#[path = "strings_prover_audit/range_and_code.rs"]
mod range_and_code;
#[path = "strings_prover_audit/reduction_and_extf.rs"]
mod reduction_and_extf;
#[path = "strings_prover_audit/replace_and_soundness.rs"]
mod replace_and_soundness;
