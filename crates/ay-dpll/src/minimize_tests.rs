// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn default_counterexample_style_is_minimal() {
    assert_eq!(CounterexampleStyle::default(), CounterexampleStyle::Minimal);
}
