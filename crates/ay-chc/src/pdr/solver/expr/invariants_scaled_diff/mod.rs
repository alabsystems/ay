// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Scaled difference invariant discovery.
//!
//! Extracted from `invariants_diff.rs` and later split into focused submodules.
//! Discovers invariants of the form `vi - vj = k * vk` where `k` is a constant
//! coefficient.

mod discovery;
mod extraction;
mod preservation;
