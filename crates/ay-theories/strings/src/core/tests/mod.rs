// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core string solver test suite, organized by subsystem.
//!
//! Split from monolithic `tests.rs` per the module-split design (#4817).

#[allow(unused_imports)]
pub(crate) use super::*;

mod basic;
mod extf;
mod flat_forms;
mod nf_deq;
mod nf_eq;
