// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kani verification harnesses for ay-strings.
//!
//! Primary harness suite (7 proofs) lives in lib_tests.rs. This module
//! provides a bridge harness for the theory verification hook.

#[cfg(kani)]
use super::*;

#[cfg(kani)]
#[kani::proof]
fn proof_solver_construction_is_safe() {
    let terms = ay_core::term::TermStore::new();
    let _solver = StringSolver::new(&terms);
}
