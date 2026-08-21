// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Grouped SMT-LIB conformance and compliance integration tests.

#[path = "common/spawn.rs"]
pub mod spawn;

#[path = "common/smt.rs"]
mod smt;

#[path = "group_smt/smt_lib_conformance.rs"]
mod smt_lib_conformance;

#[path = "group_smt/smtlib_compliance.rs"]
mod smtlib_compliance;

#[path = "group_smt/smtlib_conformance_runner.rs"]
mod smtlib_conformance_runner;

#[path = "group_smt/smtlib_full_conformance.rs"]
mod smtlib_full_conformance;
