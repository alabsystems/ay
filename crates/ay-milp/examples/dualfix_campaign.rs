// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Full-size randomized campaign for the dual-fix rule: 300,000 models over 12
//! seeds, each solved twice and enumerated over the integer lattice to check
//! that the reduction preserves feasibility and the optimum.
//!
//! Minutes of brute force, so it is an example rather than a `#[test]` — which
//! it used to be, carrying `#[ignore]`, so it ran nowhere. The 6,000-model arm
//! still runs on every `cargo test`.
//!
//! Run: `cargo run --release -p ay-milp --example dualfix_campaign`

fn main() {
    println!("{}", ay_milp::diag_dualfix_campaign_at_scale());
}
