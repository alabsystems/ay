// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Keep the semantic BCP resume regression in ordinary tests. The deliberately
//! delayed host-speed controls are an explicit qualification benchmark.

#[allow(dead_code)]
#[path = "../benches/resource_clock/eager_persistent.rs"]
mod eager_persistent;

#[test]
fn counted_search_reaches_verdict_at_the_bcp_regression_and_forced_slice_sizes() {
    eager_persistent::counted_search_reaches_verdict_at_the_bcp_regression_and_forced_slice_sizes();
}
