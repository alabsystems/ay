// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Measurement backing the coefficient-blow-up claim in `subresultant.rs`.
//!
//! Compares the incumbent rational Gaussian elimination against the
//! fraction-free Bareiss and PRS paths on integer polynomials of growing
//! degree, printing timings and the bit size of the resultant.
//!
//! This is a measurement, not a correctness assertion, so it lives here rather
//! than as an `#[ignore]`d `#[test]` — which the repository's quality gate
//! forbids, and which meant it never ran at all. Agreement between the three
//! paths is still asserted at every degree, so a divergence aborts the run.
//!
//! Run: `cargo run --release -p ay-nra --example subresultant_measurement`

fn main() {
    print!(
        "{}",
        ay_nra::diag_subresultant_incumbent_versus_fraction_free()
    );
}
