// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ADVERSARIAL VERIFICATION reference for `mpbq`.
//!
//! The independent reference model and its checks live in a private module so
//! each verification phase has a narrow, reviewable responsibility.

#[path = "av_ref/mod.rs"]
mod verification;

fn main() {
    verification::run();
}
