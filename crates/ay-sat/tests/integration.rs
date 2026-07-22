// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr, clippy::print_stdout)]
#![allow(clippy::panic)]

//! Integration tests for ay-sat.
//!
//! Tests the SAT solver against DIMACS CNF benchmarks.

mod common;

#[path = "integration/basic.rs"]
mod basic;
#[path = "integration/inprocessing.rs"]
mod inprocessing;
#[path = "integration/model_reconstruction.rs"]
mod model_reconstruction;
#[path = "integration/proofs.rs"]
mod proofs;
