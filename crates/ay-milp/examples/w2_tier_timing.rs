// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Per-phase wall clock for the W2 ledger shape (4 x 24): the implied-box
//! sweep, the float solve, the NS pricing, and the public rigorous query on
//! the first three targets.
//!
//! A timing diagnostic that asserts nothing about the numbers, so it is an
//! example rather than a `#[test]` — which it used to be, carrying
//! `#[ignore]`, so it ran nowhere at all.
//!
//! Run: `cargo run --release -p ay-milp --example w2_tier_timing`

fn main() {
    println!("{}", ay_milp::diag_w2_tier_timing());
}
