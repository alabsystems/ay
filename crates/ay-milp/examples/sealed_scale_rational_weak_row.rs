// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Characterize the exact-rational weak-dual row lane at the sealed VNN-COMP
//! instance's sparse dimensions (7593 columns, 4846 rows, 502260 nonzeros).
//!
//! The certified weak-duality path has two exact-arithmetic phases — build the
//! proposal, then independently recombine it — and both were `BigRational`
//! before the `FastRational` (small-first, promote-on-overflow) rewrite. This
//! times them against each other at one process, on one warm immutable model,
//! with the rational side store populated and two inputs forced past 2^113 so
//! the promoted-slot path is live.
//!
//! It is also a differential oracle, not just a stopwatch: every round asserts
//! that both implementations produce the bit-identical proof object and the
//! bit-identical recombination, and that the proposal verifies against the
//! model. A round that diverges panics — a faster answer that is a different
//! answer is not a speedup. (`cargo test -p ay-milp` runs the same routine at
//! ~1/160 scale, so that contract is checked without this harness.)
//!
//! The shape is representative; the synthetic adjacency, coefficient
//! distribution, and one-hot objective are NOT a replay of the confidential
//! network, so the medians characterize the arithmetic, not that instance.
//! Alternating order and medians reduce (but cannot eliminate) shared-host
//! frequency and scheduling noise — run it on an idle machine, in release.
//!
//! ```text
//! cargo run --release -p ay-milp --example sealed_scale_rational_weak_row
//! ```

fn main() {
    println!("{}", ay_milp::diag_sealed_scale_rational_weak_row());
}
