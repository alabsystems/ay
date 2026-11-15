// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Host-speed invariance qualification, including deliberate slowdown and real
//! backstops. Run explicitly with `targo --unverified bench -p ay-dpll --bench
//! resource_clock_qualification`; ordinary tests retain the counted BCP resume
//! regression without imposing the simulated slow-host workload.

#[path = "resource_clock/certification.rs"]
mod certification;
#[path = "resource_clock/eager_persistent.rs"]
mod eager_persistent;

fn main() {
    certification::run();
    eager_persistent::run();
    eager_persistent::counted_search_reaches_verdict_at_the_bcp_regression_and_forced_slice_sizes();
    println!("resource clock qualification passed");
}
